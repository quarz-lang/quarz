//! Compile-time execution of class bodies' `static` statements (docs/14):
//! the checker hands each statement here once it has checked it; this
//! lowers the statement and what it reaches (asking the checker for the
//! bodies not checked yet), refuses a reach into natives that act on the
//! outside world, and runs it on the interpreter with a time limit.
//!
//! Afterwards, `compile_time_only_calls` tells which `static def`s turn
//! out to be compile-time only (they reach the reflection natives or a
//! `Meta::ClassDef`) and reports the calls of those from ordinary code.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use quarz_ir::{shake, ClassId, FuncId, MethodId, RtClassKind, RtWorld};
use quarz_lower::Lowerer;
use quarz_syntax::ast::{ParamKind, Visibility};
use quarz_syntax::{Diagnostic, SourceFile, Span};
use quarz_types::declare::SELF_PARAM;
use quarz_types::{
    Baked, Checked, FieldInfo, Generated, MethodInfo, ParamInfo, StaticFailure, StaticHost,
    StaticRunner, StaticStmt, Synth, Type, TypeParamId, World,
};
use quarz_vm::interp::{Interp, SharedState, StaticEnd};
use quarz_vm::natives::{compile_time_allowed, compile_time_denied_class, compile_time_only};
use quarz_vm::reflect::{
    FieldRequest, GenRequest, Reflect, ReflectField, ReflectKind, ReflectMethod, ReflectParam,
};
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
    /// functions are append-only, so each run sees the earlier ones; the
    /// lowerer keeps them, `Lowerer::done`).
    state: Option<SharedState>,
    world: Option<RtWorld>,
    files: Vec<SourceFile>,
    prepared: bool,
    /// The constants a `def_field` leaves initialized: those of the REPL's
    /// earlier inputs (`continuing`).
    keep_consts: usize,
}

impl Runner {
    /// The lowerer, with every function lowered so far, for the final
    /// lowering to continue (the generated methods' bodies are copied
    /// from them, docs/14 §5).
    pub fn into_lowerer(self) -> Lowerer {
        self.lowerer
    }

    /// The members a statement's run asked for (`def_method`), declared
    /// in the order of the calls, then the classes they went into
    /// checked again.
    fn generate(
        &mut self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        pending: Vec<Pending>,
    ) -> Result<(), StaticFailure> {
        let mut classes: Vec<ClassId> = Vec::new();
        let result = self.generate_each(host, stmt, pending, &mut classes);
        // The classes generated into are checked again, whatever came
        // after the last generation into them.
        if !classes.is_empty() {
            host.recheck_classes(&classes);
        }
        result
    }

    fn generate_each(
        &mut self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        pending: Vec<Pending>,
        classes: &mut Vec<ClassId>,
    ) -> Result<(), StaticFailure> {
        let fail = |message: String| StaticFailure {
            message,
            notes: Vec::new(),
        };
        for g in pending {
            let g = match g {
                Pending::Method(g) => g,
                Pending::Field(f) => {
                    let at = format!("`def_field(:{})`", f.name);
                    let world = host.world();
                    if !world.class(f.ty).type_params.is_empty() {
                        return Err(fail(format!(
                            "{at}: `{}` takes type arguments, which a `Type` value does not carry: a generated field's type is a class without them",
                            world.class(f.ty).name
                        )));
                    }
                    let field = FieldInfo {
                        name: f.name.clone(),
                        ty: Type::Class(f.ty, Vec::new()),
                        mutable: f.mutable,
                        default: None,
                        baked_default: Some(f.default),
                        span: stmt.span,
                    };
                    host.add_generated_field(f.class, field)
                        .map_err(|why| fail(format!("{at}: {why}")))?;
                    // The accessors asked for, as `attr_reader`/`attr_writer`
                    // make them.
                    let ty = Type::Class(f.ty, Vec::new());
                    let accessor =
                        |name: String, params: Vec<ParamInfo>, synth: Synth| MethodInfo {
                            id: 0,
                            name,
                            owner: f.class,
                            singleton: false,
                            type_params: Vec::new(),
                            params,
                            block: None,
                            block_optional: false,
                            block_usings: Vec::new(),
                            ret: ty.clone(),
                            body: None,
                            is_abstract: false,
                            is_native: true,
                            is_static: false,
                            visibility: Visibility::Public,
                            span: stmt.span,
                            extension: None,
                            frame_size: 0,
                            checked: true,
                            synth,
                            alias_of: None,
                            file: stmt.file,
                            generated: None,
                        };
                    if f.reader {
                        let m =
                            accessor(f.name.clone(), Vec::new(), Synth::FieldGet(f.name.clone()));
                        host.add_generated(m)
                            .map_err(|why| fail(format!("{at}: {why}")))?;
                    }
                    if f.writer {
                        let value = ParamInfo {
                            name: "value".to_string(),
                            kind: ParamKind::Positional,
                            ty: ty.clone(),
                            default: None,
                            assigns_ivar: false,
                            span: stmt.span,
                        };
                        let m = accessor(
                            format!("{}=", f.name),
                            vec![value],
                            Synth::FieldSet(f.name.clone()),
                        );
                        host.add_generated(m)
                            .map_err(|why| fail(format!("{at}: {why}")))?;
                    }
                    // The class and its descendants lay their fields out
                    // anew: what was lowered with the old layout goes.
                    let world = host.world();
                    let affected: Vec<ClassId> = world
                        .classes
                        .iter()
                        .filter(|c| world.class_is_a(c.id, f.class))
                        .map(|c| c.id)
                        .collect();
                    self.lowerer.invalidate_layout(&affected);
                    // A constant initialized by an earlier statement may
                    // hold an instance with the old layout: all of them
                    // initialize again when next read.
                    if let Some(state) = &self.state {
                        state.reset_consts_from(self.keep_consts);
                    }
                    if !classes.contains(&f.class) {
                        classes.push(f.class);
                    }
                    continue;
                }
            };
            let at = format!(
                "`{}(:{})`",
                if g.singleton {
                    "def_class_method"
                } else {
                    "def_method"
                },
                g.name
            );
            let reads = quarz_lower::lift::check(&self.lowerer.done, g.func)
                .map_err(|why| fail(format!("{at}: {why}")))?;
            if let Some((d, s)) = reads
                .iter()
                .find(|(d, s)| !g.captures.iter().any(|(cd, cs, _)| (cd, cs) == (d, s)))
            {
                return Err(fail(format!(
                    "{at}: internal: no value recorded for the captured slot {s} at depth {d}"
                )));
            }
            let not_literal = || {
                fail(format!(
                    "{at}: the block must be written at the call: it becomes the method's body"
                ))
            };
            let (call_id, block_span) = *self
                .lowerer
                .block_calls
                .get(&g.func)
                .ok_or_else(not_literal)?;
            let proc_ty = host
                .output()
                .lifted_blocks
                .get(&call_id)
                .cloned()
                .ok_or_else(not_literal)?;
            let Type::Proc(_, param_types, ret, _) = proc_ty else {
                return Err(not_literal());
            };
            if param_types.len() != g.params.len() {
                return Err(fail(format!(
                    "{at}: the block takes {} parameter(s) but {} name(s) were given",
                    param_types.len(),
                    g.params.len()
                )));
            }
            // The signature: the block's type with the `static def`'s type
            // arguments (those of the statement's call) and `Self` (the
            // class generated into) substituted.
            let world = host.world();
            let mut subst: rustc_hash::FxHashMap<TypeParamId, Type> = host
                .output()
                .type_args
                .get(&stmt.expr.id)
                .map(|args| args.iter().cloned().collect())
                .unwrap_or_default();
            let target = world.class(g.class);
            let own: Vec<TypeParamId> = target.type_params.iter().map(|p| p.id).collect();
            subst.insert(
                SELF_PARAM,
                Type::Class(g.class, own.iter().map(|p| Type::Param(*p)).collect()),
            );
            let param_types: Vec<Type> = param_types.iter().map(|t| t.subst(&subst)).collect();
            let ret = ret.subst(&subst);
            if let Some(p) = param_types
                .iter()
                .chain(std::iter::once(&ret))
                .find_map(|t| free_param(t, &own))
            {
                return Err(fail(format!(
                    "{at}: the block's type mentions `{}`, a type parameter the generated method cannot carry (only the `static def` the statement calls has its type arguments)",
                    world.type_name(&Type::Param(p))
                )));
            }
            // The block's type must be settled: a parameter without an
            // annotation or a result nothing constrained is not.
            if param_types
                .iter()
                .chain(std::iter::once(&ret))
                .any(|t| t.has_vars())
            {
                return Err(fail(format!(
                    "{at}: the block's parameter or result type could not be inferred: annotate its parameters (`|x: Int|`)"
                )));
            }
            if let Some((_, dup)) = g
                .params
                .iter()
                .enumerate()
                .find(|(i, n)| g.params[..*i].contains(n))
            {
                return Err(fail(format!(
                    "{at}: the parameter name `{dup}` is given twice"
                )));
            }
            let visibility = match g.visibility.as_str() {
                "private" => Visibility::Private,
                "protected" => Visibility::Protected,
                _ => Visibility::Public,
            };
            let params = g
                .params
                .iter()
                .zip(param_types)
                .map(|(name, ty)| ParamInfo {
                    name: name.clone(),
                    kind: ParamKind::Positional,
                    ty,
                    default: None,
                    assigns_ivar: false,
                    span: stmt.span,
                })
                .collect();
            let info = MethodInfo {
                id: 0,
                name: g.name.clone(),
                owner: g.class,
                singleton: g.singleton,
                type_params: Vec::new(),
                params,
                block: None,
                block_optional: false,
                block_usings: Vec::new(),
                ret,
                body: None,
                is_abstract: false,
                is_native: false,
                is_static: false,
                visibility,
                span: stmt.span,
                extension: None,
                frame_size: 0,
                checked: true,
                synth: Synth::None,
                alias_of: None,
                file: stmt.file,
                generated: Some(Generated {
                    func: g.func,
                    captures: g.captures,
                    by: (stmt.file, stmt.span),
                    block: block_span,
                    doc: g.doc,
                }),
            };
            host.add_generated(info)
                .map_err(|why| fail(format!("{at}: {why}")))?;
            if !classes.contains(&g.class) {
                classes.push(g.class);
            }
        }
        Ok(())
    }

    pub fn new(files: Vec<SourceFile>) -> Runner {
        Runner {
            lowerer: Lowerer::default(),
            bad_methods: Default::default(),
            bad_consts: Default::default(),
            state: None,
            world: None,
            files,
            prepared: false,
            keep_consts: 0,
        }
    }

    /// A runner continuing `lowerer` (whose `done` holds every function
    /// lowered so far, all loaded into `state`) and running on `state`:
    /// the REPL's, whose inputs' statements run in the session itself
    /// (docs/14 §2). The first `keep_consts` constants, the earlier
    /// inputs', stay initialized whatever the statements do.
    pub fn continuing(
        lowerer: Lowerer,
        state: SharedState,
        files: Vec<SourceFile>,
        keep_consts: usize,
    ) -> Runner {
        Runner {
            lowerer,
            state: Some(state),
            keep_consts,
            ..Runner::new(files)
        }
    }

    /// The source files it lowers with, by index.
    pub fn files(&self) -> &[SourceFile] {
        &self.files
    }

    /// The lowerer and the state back (`continuing`).
    pub fn into_parts(self) -> (Lowerer, Option<SharedState>) {
        (self.lowerer, self.state)
    }

    /// The statement's function and what it reaches, lowered: rounds of
    /// `lower_static`, each followed by the checks it asked for.
    fn lower(&mut self, host: &mut dyn StaticHost, stmt: &StaticStmt, callee: MethodId) -> FuncId {
        loop {
            // The classes whose statements are still to run, with their
            // descendants: not reached by name (`Lowerer::static_skip`).
            let world = host.world();
            let pending = host.pending_classes();
            self.lowerer.static_skip = world
                .classes
                .iter()
                .filter(|c| pending.iter().any(|&p| world.class_is_a(c.id, p)))
                .map(|c| c.id)
                .collect();
            let round = self.lowerer.lower_static(
                host.world(),
                host.output(),
                &stmt.expr,
                stmt.class,
                stmt.file,
                callee,
                self.files.clone(),
            );
            debug_assert_eq!(self.lowerer.done.len(), round.delta.base as usize);
            self.lowerer
                .done
                .extend(round.delta.functions.iter().cloned());
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
        let mut seen = vec![false; self.lowerer.done.len()];
        let mut work: Vec<FuncId> = vec![root];
        while let Some(fid) = work.pop() {
            if fid as usize >= seen.len() || seen[fid as usize] {
                continue;
            }
            seen[fid as usize] = true;
            let mut methods: Vec<MethodId> = Vec::new();
            let mut found: Option<String> = None;
            shake::refs(&self.lowerer.done[fid as usize], &mut |r| match r {
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
        let mut seen = vec![false; self.lowerer.done.len()];
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
            shake::refs(&self.lowerer.done[fid as usize], &mut |r| match r {
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
        let reflect = Rc::new(WorldReflect::snapshot(host.world()));
        let world = self.world.clone().expect("lowered");
        let interp = Interp::with_state(
            world,
            self.lowerer.done.len() as FuncId,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            self.state.clone().expect("state"),
        );
        *interp.reflect.borrow_mut() = Some(reflect.clone());
        interp
            .deadline
            .set(Some(std::time::Instant::now() + limit()));
        let result = interp.run_static(fid, Value::Class(stmt.class), stmt.file);
        match result {
            Ok(()) => {
                let pending = std::mem::take(&mut *reflect.generated.borrow_mut());
                drop(interp);
                self.generate(host, stmt, pending)
            }
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

    fn add_file(&mut self, index: u32, file: SourceFile) {
        let i = index as usize;
        if self.files.len() <= i {
            self.files.resize(i + 1, SourceFile::new("", ""));
        }
        self.files[i] = file;
    }
}

/// The declarations, as the reflection natives read them: taken when a
/// statement runs, so that every statement of a cog sees the same
/// (docs/14 §2).
struct WorldReflect {
    fields: HashMap<ClassId, Vec<Rc<[ReflectField]>>>,
    methods: HashMap<ClassId, Vec<Rc<[ReflectMethod]>>>,
    /// What the statement's run asked to generate, in call order.
    generated: RefCell<Vec<Pending>>,
    /// The `doc` given, for the next generation.
    doc: RefCell<Option<String>>,
}

/// A generation a statement's run asked for, in call order.
enum Pending {
    Method(PendingGen),
    Field(PendingField),
}

/// A `def_field` call's request, its default baked.
struct PendingField {
    class: ClassId,
    name: String,
    ty: ClassId,
    default: Baked,
    mutable: bool,
    reader: bool,
    writer: bool,
}

/// A `def_method` call's request, its captured values baked.
struct PendingGen {
    class: ClassId,
    name: String,
    params: Vec<String>,
    singleton: bool,
    visibility: String,
    func: FuncId,
    captures: Vec<(u32, u32, Baked)>,
    doc: Option<String>,
}

/// A compile-time value as a generated method embeds it (docs/14 §5),
/// or why it cannot.
fn bake(interp: &Interp, v: &Value) -> Result<Baked, String> {
    let cannot = |interp: &Interp, v: &Value| {
        Err(format!(
            "a value of class `{}` cannot be baked into a generated method; a block given to `def_method` captures only immutable values (literals, classes, `data`)",
            interp.class_name(v)
        ))
    };
    Ok(match v {
        Value::Nil => Baked::Nil,
        Value::Bool(b) => Baked::Bool(*b),
        Value::Int(i) => Baked::Int(*i),
        Value::Float(f) => Baked::Float(*f),
        Value::Symbol(s) => Baked::Symbol(interp.symbol_name(*s).to_string()),
        Value::Short(_) | Value::Str(_) => Baked::Str(v.as_str().unwrap_or_default().to_string()),
        Value::BigInt(b) => Baked::BigInt {
            digits: b.to_str_radix(10),
            base: 10,
        },
        Value::Class(c) => Baked::Class(*c),
        Value::Bytes(b) => Baked::Bytes(b.to_vec()),
        Value::Regexp(r) => Baked::Regexp {
            source: r.source.clone(),
            flags: r.flags.clone(),
        },
        Value::Array(a) => Baked::Array(
            a.iter()
                .map(|x| bake(interp, &x))
                .collect::<Result<_, _>>()?,
        ),
        Value::Hash(h) => Baked::Hash(
            h.as_map()
                .iter()
                .map(|(k, v)| Ok((bake(interp, k)?, bake(interp, v)?)))
                .collect::<Result<_, String>>()?,
        ),
        Value::Range(r) => {
            let bound = |b: &Value| -> Result<Option<Box<Baked>>, String> {
                Ok(match b {
                    Value::Nil => None,
                    other => Some(Box::new(bake(interp, other)?)),
                })
            };
            Baked::Range {
                lo: bound(&r.lo)?,
                hi: bound(&r.hi)?,
                exclusive: r.exclusive,
            }
        }
        Value::Object(o) => {
            let class = interp.program.world.class(o.class);
            match class.kind {
                RtClassKind::Variant if o.field_count() == 0 => Baked::Variant(o.class),
                RtClassKind::Data | RtClassKind::Variant => Baked::Data(
                    o.class,
                    o.fields()
                        .iter()
                        .map(|f| bake(interp, f))
                        .collect::<Result<_, _>>()?,
                ),
                _ => return cannot(interp, v),
            }
        }
        _ => return cannot(interp, v),
    })
}

/// A type parameter `t` mentions that is not one of `own`.
fn free_param(t: &Type, own: &[TypeParamId]) -> Option<TypeParamId> {
    match t {
        Type::Param(p) => (!own.contains(p)).then_some(*p),
        Type::Class(_, args) | Type::ClassObject(_, args) => {
            args.iter().find_map(|a| free_param(a, own))
        }
        Type::TypeOf(inner) => free_param(inner, own),
        Type::Union(ms) | Type::Tuple(ms) => ms.iter().find_map(|m| free_param(m, own)),
        Type::Proc(recv, ps, r, _) => recv
            .as_deref()
            .and_then(|r| free_param(r, own))
            .or_else(|| ps.iter().find_map(|p| free_param(p, own)))
            .or_else(|| free_param(r, own)),
        Type::Var(_) | Type::Nothing | Type::Void => None,
    }
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
                    default: f.has_default(),
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
        WorldReflect {
            fields,
            methods,
            generated: RefCell::new(Vec::new()),
            doc: RefCell::new(None),
        }
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
    fn generate(&self, interp: &Interp, request: GenRequest) -> Result<(), String> {
        let captures = request
            .captures
            .iter()
            .map(|(d, s, v)| Ok((*d, *s, bake(interp, v)?)))
            .collect::<Result<Vec<_>, String>>()?;
        self.generated
            .borrow_mut()
            .push(Pending::Method(PendingGen {
                class: request.class,
                name: request.name,
                params: request.params,
                singleton: request.singleton,
                visibility: request.visibility,
                func: request.func,
                captures,
                doc: self.doc.borrow_mut().take(),
            }));
        Ok(())
    }
    fn def_field(&self, interp: &Interp, request: FieldRequest) -> Result<(), String> {
        let default = bake(interp, &request.default)?;
        self.generated
            .borrow_mut()
            .push(Pending::Field(PendingField {
                class: request.class,
                name: request.name,
                ty: request.ty,
                default,
                mutable: request.mutable,
                reader: request.reader,
                writer: request.writer,
            }));
        Ok(())
    }
    fn doc(&self, text: String) {
        *self.doc.borrow_mut() = Some(text);
    }
}

/// The calls, from code that is not static, of `static def`s that are
/// compile-time only: they reach the reflection natives, a
/// `Meta::ClassDef` type, or another such method (docs/14 §3). Each is an
/// error at the call.
pub fn compile_time_only_calls(
    checked: &Checked,
    files: &[SourceFile],
    runner: &mut Runner,
) -> Vec<(u32, Diagnostic)> {
    compile_time_only_calls_in(&checked.world, &checked.output, files, runner, &|_, _| true)
}

/// `compile_time_only_calls` on a world and output, reporting only the
/// calls `report` takes (the REPL: those of the input).
pub fn compile_time_only_calls_in(
    world: &World,
    output: &quarz_types::check::Output,
    files: &[SourceFile],
    runner: &mut Runner,
    report: &dyn Fn(u32, Span) -> bool,
) -> Vec<(u32, Diagnostic)> {
    let statics: Vec<MethodId> = (0..world.methods.len() as MethodId)
        .filter(|m| {
            let m = world.method(*m);
            m.is_static && !m.is_native && m.body.is_some()
        })
        .collect();
    if statics.is_empty() || !output.static_calls.iter().any(|(f, s, _)| report(*f, *s)) {
        return Vec::new();
    }
    // Every static def's reach, lowered as for a compile-time run, by the
    // runner's lowerer (the generated methods' bodies are in it). Every
    // statement ran: no class is left out any more.
    let lowerer = &mut runner.lowerer;
    lowerer.static_skip.clear();
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
            output,
            &dummy,
            owner,
            world.method(m).file,
            m,
            files.to_vec(),
        );
        // Loaded into the runner's state, which a REPL goes on running
        // (`continuing`): its functions must be all of `done`.
        if let Some(state) = &runner.state {
            let _ = Interp::with_state(
                round.delta.world.clone(),
                round.delta.base,
                round.delta.functions.clone(),
                Vec::new(),
                Vec::new(),
                state.clone(),
            );
        }
        lowerer.done.extend(round.delta.functions);
        rt = Some(round.delta.world);
    }
    let functions = &lowerer.done;
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
    for (file, span, mid) in &output.static_calls {
        if only.get(mid).copied().unwrap_or(false) && report(*file, *span) {
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
