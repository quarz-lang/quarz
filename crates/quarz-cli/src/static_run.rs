//! Compile-time execution of class bodies' `static` statements (docs/14):
//! the checker hands each statement here once it has checked it; this
//! lowers the statement and what it reaches (asking the checker for the
//! bodies not checked yet), refuses a reach into natives that act on the
//! outside world, and runs it on the interpreter with a time limit.
//!
//! Afterwards, `compile_time_only_calls` tells which `static def`s turn
//! out to be compile-time only (they reach the reflection natives or a
//! `Meta::ClassDef`) and reports the calls of those from ordinary code.

use std::collections::HashMap;
use std::rc::Rc;

use quarz_ir::{shake, ClassId, FuncId, Function, MethodId, RtWorld};
use quarz_lower::Lowerer;
use quarz_syntax::{Diagnostic, SourceFile, Span};
use quarz_types::{
    Checked, ParamInfo, StaticFailure, StaticHost, StaticRunner, StaticStmt, Type, World,
};
use quarz_vm::interp::{Interp, SharedState, StaticEnd};
use quarz_vm::natives::{compile_time_allowed, compile_time_denied_class, compile_time_only};
use quarz_vm::reflect::{Reflect, ReflectField, ReflectKind, ReflectMethod, ReflectParam};
use quarz_vm::value::Value;

/// The time a `static` statement may run (docs/14 §5): 10 seconds, or
/// `QUARZ_STATIC_LIMIT_MS` (for the tests of the limit).
fn limit() -> std::time::Duration {
    std::env::var("QUARZ_STATIC_LIMIT_MS")
        .ok()
        .and_then(|s| s.parse().ok())
        .map(std::time::Duration::from_millis)
        .unwrap_or(std::time::Duration::from_secs(10))
}

pub struct Runner {
    lowerer: Lowerer,
    /// Methods and constants whose on-demand check reported errors: a
    /// statement that reaches one does not run (docs/05 §3: checked code
    /// only).
    bad_methods: std::collections::HashSet<MethodId>,
    bad_consts: std::collections::HashSet<u32>,
    /// The interpreter's state, shared by every statement's run (the
    /// functions are append-only, so each run sees the earlier ones).
    state: Option<SharedState>,
    /// Every function lowered so far, by id.
    functions: Vec<Function>,
    world: Option<RtWorld>,
    files: Vec<SourceFile>,
    prepared: bool,
}

impl Runner {
    pub fn new(files: Vec<SourceFile>) -> Runner {
        Runner {
            lowerer: Lowerer::default(),
            bad_methods: Default::default(),
            bad_consts: Default::default(),
            state: None,
            functions: Vec::new(),
            world: None,
            files,
            prepared: false,
        }
    }

    /// The statement's function and what it reaches, lowered: rounds of
    /// `lower_static`, each followed by the checks it asked for.
    fn lower(&mut self, host: &mut dyn StaticHost, stmt: &StaticStmt, callee: MethodId) -> FuncId {
        loop {
            let round = self.lowerer.lower_static(
                host.world(),
                host.output(),
                &stmt.expr,
                stmt.class,
                stmt.file,
                callee,
                self.files.clone(),
            );
            debug_assert_eq!(self.functions.len(), round.delta.base as usize);
            self.functions.extend(round.delta.functions.iter().cloned());
            let state = self
                .state
                .get_or_insert_with(|| SharedState::with_threads(Box::new(std::io::stderr()), 1))
                .clone();
            // Loads the round's functions into the shared state.
            let _ = Interp::with_state(
                round.delta.world.clone(),
                round.delta.base,
                round.delta.functions,
                Vec::new(),
                Vec::new(),
                state,
            );
            self.world = Some(round.delta.world);
            if round.unchecked.is_empty() && round.unchecked_consts.is_empty() {
                return round.stmt_func;
            }
            for m in round.unchecked {
                let before = host.error_count();
                host.ensure_method_checked(m);
                if host.error_count() > before {
                    self.bad_methods.insert(m);
                }
            }
            for c in round.unchecked_consts {
                let before = host.error_count();
                host.ensure_const_checked(c);
                if host.error_count() > before {
                    self.bad_consts.insert(c);
                }
            }
        }
    }

    /// A method or constant with errors that the statement reaches, named.
    fn bad_reach(&self, root: FuncId) -> Option<String> {
        if self.bad_methods.is_empty() && self.bad_consts.is_empty() {
            return None;
        }
        let world = self.world.as_ref()?;
        let by_name = methods_by_name(world);
        let mut seen = vec![false; self.functions.len()];
        let mut work: Vec<FuncId> = vec![root];
        while let Some(fid) = work.pop() {
            if fid as usize >= seen.len() || seen[fid as usize] {
                continue;
            }
            seen[fid as usize] = true;
            let mut methods: Vec<MethodId> = Vec::new();
            let mut found: Option<String> = None;
            shake::refs(&self.functions[fid as usize], &mut |r| match r {
                shake::Ref::Method(m) => {
                    methods.push(m);
                    methods.extend(overrides_of(world, &by_name, m));
                }
                shake::Ref::Name(n) => {
                    if let Some(ms) = by_name.get(n) {
                        methods.extend(ms.iter().copied().filter(|&o| !denied_owner(world, o)));
                    }
                }
                shake::Ref::Func(f) => work.push(f),
                shake::Ref::Const(c) => {
                    if self.bad_consts.contains(&c) {
                        found = Some(world.consts[c as usize].name.clone());
                    } else if let Some(init) = world.consts.get(c as usize).and_then(|c| c.init) {
                        work.push(init);
                    }
                }
                _ => {}
            });
            if found.is_some() {
                return found;
            }
            for m in methods {
                if self.bad_methods.contains(&m) {
                    return Some(method_name(world, m));
                }
                if let Some(f) = world.methods[m as usize].func {
                    work.push(f);
                }
            }
        }
        None
    }

    /// A native the statement reaches that cannot run at compile time,
    /// with the calls leading to it (innermost last).
    fn impure_reach(&self, root: FuncId) -> Option<Vec<String>> {
        let world = self.world.as_ref()?;
        let by_name = methods_by_name(world);
        let mut seen = vec![false; self.functions.len()];
        // Each function with the path of method names that reached it.
        let mut work: Vec<(FuncId, Vec<String>)> = vec![(root, Vec::new())];
        while let Some((fid, path)) = work.pop() {
            if seen[fid as usize] {
                continue;
            }
            seen[fid as usize] = true;
            let mut methods: Vec<MethodId> = Vec::new();
            let mut funcs: Vec<FuncId> = Vec::new();
            let mut consts: Vec<u32> = Vec::new();
            shake::refs(&self.functions[fid as usize], &mut |r| match r {
                // A method and its overrides: a subclass's runs in its
                // place.
                shake::Ref::Method(m) => {
                    methods.push(m);
                    methods.extend(overrides_of(world, &by_name, m));
                }
                shake::Ref::Name(n) => {
                    if let Some(ms) = by_name.get(n) {
                        methods.extend(ms.iter().copied().filter(|&o| !denied_owner(world, o)));
                    }
                }
                shake::Ref::Func(f) => funcs.push(f),
                shake::Ref::Const(c) => consts.push(c),
                _ => {}
            });
            for m in methods {
                let rm = &world.methods[m as usize];
                let mut p = path.clone();
                p.push(method_name(world, m));
                if let Some(key) = &rm.native_key {
                    if !compile_time_allowed(key) {
                        return Some(p);
                    }
                }
                if let Some(f) = rm.func {
                    work.push((f, p));
                }
            }
            for f in funcs {
                work.push((f, path.clone()));
            }
            for c in consts {
                if let Some(init) = world.consts.get(c as usize).and_then(|c| c.init) {
                    let mut p = path.clone();
                    p.push(world.consts[c as usize].name.clone());
                    work.push((init, p));
                }
            }
        }
        None
    }
}

/// The methods that override `m` in subclasses of its owner (same name,
/// same side), which a call of `m` may run instead.
fn overrides_of(
    world: &RtWorld,
    by_name: &HashMap<&str, Vec<MethodId>>,
    m: MethodId,
) -> Vec<MethodId> {
    let rm = &world.methods[m as usize];
    // An override in a class denied at compile time (`IO#puts` for
    // `Kernel#puts`, `Random#==` for `Object#==`) needs a receiver of
    // that class, which only a denied native can make: not counted. (A
    // denied native reached anyway raises at compile time:
    // `Interp::invoke`.)
    by_name
        .get(rm.name.as_str())
        .map(|ms| {
            ms.iter()
                .copied()
                .filter(|&o| {
                    let om = &world.methods[o as usize];
                    o != m
                        && om.singleton == rm.singleton
                        && world.class_is_a(om.owner, rm.owner)
                        && !denied_owner(world, o)
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Whether `m` belongs to a class denied at compile time: a receiver of
/// it comes only from a denied native, or from a constant whose
/// initializer is one (`STDOUT`), which the walk follows; so a call by
/// name (`==`, `to_s`) cannot reach it otherwise.
fn denied_owner(world: &RtWorld, m: MethodId) -> bool {
    let owner = &world.classes[world.methods[m as usize].owner as usize];
    compile_time_denied_class(owner.name.split("::").next().unwrap_or(""))
}

fn method_name(world: &RtWorld, m: MethodId) -> String {
    let rm = &world.methods[m as usize];
    let sep = if rm.singleton { "." } else { "#" };
    format!("{}{sep}{}", world.classes[rm.owner as usize].name, rm.name)
}

fn methods_by_name(world: &RtWorld) -> HashMap<&str, Vec<MethodId>> {
    let mut out: HashMap<&str, Vec<MethodId>> = HashMap::new();
    for (i, m) in world.methods.iter().enumerate() {
        out.entry(m.name.as_str()).or_default().push(i as MethodId);
    }
    out
}

impl StaticRunner for Runner {
    fn run(
        &mut self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        callee: MethodId,
    ) -> Result<(), StaticFailure> {
        if !self.prepared {
            host.prepare();
            self.prepared = true;
        }
        let errors_before = host.error_count();
        let fid = self.lower(host, stmt, callee);
        let callee_name = host.world().method(callee).name.clone();
        // Code that failed its check does not run (docs/05 §3): neither a
        // statement reaching a method or constant with errors, nor one
        // whose lowering found errors elsewhere (a field default).
        if let Some(bad) = self.bad_reach(fid) {
            return Err(StaticFailure {
                message: format!("`{callee_name}` did not run: it reaches `{bad}`, which has errors (reported above)"),
                notes: Vec::new(),
            });
        }
        if host.error_count() > errors_before {
            return Err(StaticFailure {
                message: format!(
                    "`{callee_name}` did not run: what it reaches has errors (reported above)"
                ),
                notes: Vec::new(),
            });
        }
        if let Some(path) = self.impure_reach(fid) {
            let last = path.last().cloned().unwrap_or_default();
            // The path starts at the callee itself.
            let via = if path.len() > 2 {
                format!(" (via {})", path[1..path.len() - 1].join(", "))
            } else {
                String::new()
            };
            return Err(StaticFailure {
                message: format!(
                    "`{callee_name}` reaches `{last}`{via}, which cannot run at compile time"
                ),
                notes: Vec::new(),
            });
        }
        let reflect: Rc<dyn Reflect> = Rc::new(WorldReflect::snapshot(host.world()));
        let world = self.world.clone().expect("lowered");
        let interp = Interp::with_state(
            world,
            self.functions.len() as FuncId,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            self.state.clone().expect("state"),
        );
        *interp.reflect.borrow_mut() = Some(reflect);
        interp
            .deadline
            .set(Some(std::time::Instant::now() + limit()));
        let result = interp.run_static(fid, Value::Class(stmt.class), stmt.file);
        match result {
            Ok(()) => Ok(()),
            Err(StaticEnd::Raised(exc)) => {
                let class = interp.class_name(&exc);
                let message = interp.exception_message(&exc);
                let mut notes = Vec::new();
                if let Value::Object(o) = &exc {
                    if let Some(bt) = o.backtrace() {
                        notes.extend(bt.iter().map(|l| format!("    from {l}")));
                    }
                }
                Err(StaticFailure {
                    message: format!("`{callee_name}` raised {class}: {message}"),
                    notes,
                })
            }
            Err(StaticEnd::Exited(code)) => Err(StaticFailure {
                message: format!("`{callee_name}` exited with status {code} at compile time"),
                notes: Vec::new(),
            }),
        }
    }

    fn reset(&mut self) {
        *self = Runner::new(std::mem::take(&mut self.files));
    }
}

/// The declarations, as the reflection natives read them: taken when a
/// statement runs, so that every statement of a cog sees the same
/// (docs/14 §2).
struct WorldReflect {
    fields: HashMap<ClassId, Vec<Rc<[ReflectField]>>>,
    methods: HashMap<ClassId, Vec<Rc<[ReflectMethod]>>>,
}

impl WorldReflect {
    fn snapshot(world: &World) -> WorldReflect {
        let mut fields = HashMap::new();
        let mut methods = HashMap::new();
        for class in &world.classes {
            let fs: Vec<ReflectField> = world
                .all_fields(class.id)
                .into_iter()
                .map(|(f, _)| ReflectField {
                    name: f.name.clone(),
                    ty: erase(world, &f.ty),
                    mutable: f.mutable,
                    default: f.default.is_some(),
                })
                .collect();
            fields.insert(class.id, vec![Rc::from(fs)]);
            // The public instance methods, of the class, its superclasses
            // and the modules they include, the most derived definition of
            // each signature, in declaration order (method ids are given
            // in it). `initialize` is not a method of the instances.
            let mut seen: Vec<(String, Vec<ClassId>)> = Vec::new();
            let mut ms: Vec<(MethodId, ReflectMethod)> = Vec::new();
            for (anc, _) in world.ancestors(class.id, &[]) {
                let mut ids: Vec<MethodId> = world
                    .class(anc)
                    .methods
                    .values()
                    .flat_map(|v| v.iter().copied())
                    .collect();
                ids.sort_unstable();
                for mid in ids {
                    let m = world.method(mid);
                    if m.visibility != quarz_syntax::ast::Visibility::Public
                        || m.name == "initialize"
                    {
                        continue;
                    }
                    let key = (
                        m.name.clone(),
                        m.params.iter().map(|p| erase(world, &p.ty)).collect(),
                    );
                    if seen.contains(&key) {
                        continue;
                    }
                    seen.push(key);
                    ms.push((
                        mid,
                        ReflectMethod {
                            name: m.name.clone(),
                            params: m.params.iter().map(|p| reflect_param(world, p)).collect(),
                            ret: erase(world, &m.ret),
                            is_static: m.is_static,
                        },
                    ));
                }
            }
            ms.sort_by_key(|(mid, _)| *mid);
            let ms: Vec<ReflectMethod> = ms.into_iter().map(|(_, m)| m).collect();
            methods.insert(class.id, vec![Rc::from(ms)]);
        }
        WorldReflect { fields, methods }
    }
}

fn reflect_param(world: &World, p: &ParamInfo) -> ReflectParam {
    use quarz_syntax::ast::ParamKind;
    let kind = match p.kind {
        ParamKind::Positional if p.default.is_some() => ReflectKind::Optional,
        ParamKind::Positional => ReflectKind::Required,
        ParamKind::Rest => ReflectKind::Rest,
        ParamKind::KeywordOnly | ParamKind::KeywordRest => ReflectKind::Keyword,
        ParamKind::Block => ReflectKind::Block,
    };
    ReflectParam {
        name: p.name.clone(),
        ty: erase(world, &p.ty),
        kind,
    }
}

/// Whether `t` names the class `cid` anywhere (as it is, in an argument,
/// a union, a tuple or a procedure type).
fn mentions_class(t: &Type, cid: ClassId) -> bool {
    match t {
        Type::Class(id, args) => *id == cid || args.iter().any(|a| mentions_class(a, cid)),
        Type::ClassObject(_, args) => args.iter().any(|a| mentions_class(a, cid)),
        Type::TypeOf(inner) => mentions_class(inner, cid),
        Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(|m| mentions_class(m, cid)),
        Type::Proc(recv, ps, r, _) => {
            recv.as_deref().is_some_and(|r| mentions_class(r, cid))
                || ps.iter().any(|p| mentions_class(p, cid))
                || mentions_class(r, cid)
        }
        Type::Param(_) | Type::Var(_) | Type::Nothing | Type::Void => false,
    }
}

/// The class a type shows as at compile time: arguments erased, `Object`
/// for what is not one class.
fn erase(world: &World, t: &Type) -> ClassId {
    match t {
        Type::Class(id, _) => *id,
        Type::ClassObject(..) | Type::TypeOf(_) => world.builtin.class_,
        Type::Tuple(_) => world.builtin.array,
        Type::Proc(..) => world.builtin.proc_,
        Type::Void => world.builtin.nil,
        _ => world.builtin.object,
    }
}

impl Reflect for WorldReflect {
    fn fields(&self, class: ClassId) -> Vec<ReflectField> {
        self.fields
            .get(&class)
            .and_then(|v| v.first())
            .map(|fs| {
                fs.iter()
                    .map(|f| ReflectField {
                        name: f.name.clone(),
                        ty: f.ty,
                        mutable: f.mutable,
                        default: f.default,
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
    fn methods(&self, class: ClassId) -> Vec<ReflectMethod> {
        self.methods
            .get(&class)
            .and_then(|v| v.first())
            .map(|ms| {
                ms.iter()
                    .map(|m| ReflectMethod {
                        name: m.name.clone(),
                        params: m
                            .params
                            .iter()
                            .map(|p| ReflectParam {
                                name: p.name.clone(),
                                ty: p.ty,
                                kind: p.kind,
                            })
                            .collect(),
                        ret: m.ret,
                        is_static: m.is_static,
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
}

/// The calls, from code that is not static, of `static def`s that are
/// compile-time only: they reach the reflection natives, a
/// `Meta::ClassDef` type, or another such method (docs/14 §3). Each is an
/// error at the call.
pub fn compile_time_only_calls(checked: &Checked, files: &[SourceFile]) -> Vec<(u32, Diagnostic)> {
    let world = &checked.world;
    let statics: Vec<MethodId> = (0..world.methods.len() as MethodId)
        .filter(|m| {
            let m = world.method(*m);
            m.is_static && !m.is_native && m.body.is_some()
        })
        .collect();
    if statics.is_empty() || checked.output.static_calls.is_empty() {
        return Vec::new();
    }
    // Every static def's reach, lowered as for a compile-time run.
    let mut lowerer = Lowerer::default();
    let mut functions: Vec<Function> = Vec::new();
    let mut rt: Option<RtWorld> = None;
    let dummy = quarz_syntax::ast::Expr {
        id: u32::MAX,
        kind: quarz_syntax::ast::ExprKind::Nil,
        span: Span::new(0, 0),
    };
    for &m in &statics {
        let owner = world.method(m).owner;
        let round = lowerer.lower_static(
            world,
            &checked.output,
            &dummy,
            owner,
            world.method(m).file,
            m,
            files.to_vec(),
        );
        functions.extend(round.delta.functions);
        rt = Some(round.delta.world);
    }
    let Some(rt) = rt else {
        return Vec::new();
    };
    let by_name = methods_by_name(&rt);
    let meta = world.builtin.meta_classdef;
    let mentions_meta = |t: &Type| mentions_class(t, meta);
    let mut only: HashMap<MethodId, bool> = HashMap::new();
    for &m in &statics {
        let info = world.method(m);
        let by_signature =
            mentions_meta(&info.ret) || info.params.iter().any(|p| mentions_meta(&p.ty));
        let mut is_only = by_signature;
        if !is_only {
            if let Some(root) = rt.methods[m as usize].func {
                let mut seen = vec![false; functions.len()];
                let mut work = vec![root];
                'walk: while let Some(fid) = work.pop() {
                    if fid as usize >= seen.len() || seen[fid as usize] {
                        continue;
                    }
                    seen[fid as usize] = true;
                    let mut methods: Vec<MethodId> = Vec::new();
                    shake::refs(&functions[fid as usize], &mut |r| match r {
                        shake::Ref::Method(mm) => {
                            methods.push(mm);
                            methods.extend(overrides_of(&rt, &by_name, mm));
                        }
                        shake::Ref::Name(n) => {
                            if let Some(ms) = by_name.get(n) {
                                methods
                                    .extend(ms.iter().copied().filter(|&o| !denied_owner(&rt, o)));
                            }
                        }
                        shake::Ref::Func(f) => work.push(f),
                        _ => {}
                    });
                    for mm in methods {
                        let rm = &rt.methods[mm as usize];
                        if rm.native_key.as_deref().is_some_and(compile_time_only) {
                            is_only = true;
                            break 'walk;
                        }
                        if let Some(f) = rm.func {
                            work.push(f);
                        }
                    }
                }
            }
        }
        only.insert(m, is_only);
    }
    let mut out = Vec::new();
    for (file, span, mid) in &checked.output.static_calls {
        if only.get(mid).copied().unwrap_or(false) {
            let m = world.method(*mid);
            out.push((
                *file,
                Diagnostic::error(
                    format!(
                        "`{}` runs at compile time only (it reflects on a class or builds one): call it in a `static def` or a `static` statement",
                        m.name
                    ),
                    *span,
                ),
            ));
        }
    }
    out
}
