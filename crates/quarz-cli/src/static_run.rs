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

use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

use quarz_ir::{shake, ClassId, FuncId, MethodId, RtClassKind, RtWorld};
use quarz_lower::erase;
use quarz_lower::Lowerer;
use quarz_syntax::ast::{ParamKind, Visibility};
use quarz_syntax::{Diagnostic, SourceFile, Span};
use quarz_types::declare::SELF_PARAM;
use quarz_types::{
    Baked, Checked, FieldInfo, Generated, LayoutChange, MethodInfo, ParamInfo, StaticFailure,
    StaticHost, StaticRunner, StaticStmt, Synth, Type, TypeParamId, World,
};
use quarz_vm::interp::{Interp, SharedState, StaticEnd};
use quarz_vm::natives::{compile_time_allowed, compile_time_denied_class, compile_time_only};
use quarz_vm::reflect::{
    FieldRequest, GenRequest, Reflect, ReflectField, ReflectKind, ReflectMethod, ReflectParam,
    ReflectType,
};
use quarz_vm::value::Value;

/// The calls of `new` on the receiver (`CallKind::ConstructRecv`) in block
/// function `root` and the blocks it makes: the class each was checked
/// for and the `initialize` it passes arguments for.
fn receiver_news(
    functions: &[quarz_ir::Function],
    root: FuncId,
) -> Vec<(ClassId, Option<MethodId>)> {
    let mut out = Vec::new();
    let mut work = vec![root];
    let mut seen = Vec::new();
    while let Some(fid) = work.pop() {
        if seen.contains(&fid) {
            continue;
        }
        seen.push(fid);
        let Some(f) = functions.get(fid as usize) else {
            continue;
        };
        for b in &f.blocks {
            for inst in &b.insts {
                match inst {
                    quarz_ir::Inst::Call {
                        kind: quarz_ir::CallKind::ConstructRecv { class, init },
                        ..
                    } if !out.contains(&(*class, *init)) => out.push((*class, *init)),
                    quarz_ir::Inst::MakeBlock { func, .. } => work.push(*func),
                    _ => {}
                }
            }
        }
    }
    out
}

/// A method a statement generated, for its handles' check
/// (`Runner::check_handles`): its function, its class, the method, its
/// captures, and the call that made it, for messages.
/// A generation's function, class generated into, method, captures, the
/// call it is named by, and its handles' uses: each captured slot `get`
/// or `set` is called on, with the type the block was checked with for it,
/// substituted as the generated method's signature is (`None`: not
/// known; #918).
type GeneratedHandles = (
    Option<FuncId>,
    ClassId,
    Option<MethodId>,
    Captures,
    String,
    quarz_lower::HandleUses,
);

/// A generated method's captured values: frame depth, slot, value.
type Captures = Vec<(u32, u32, Baked)>;

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
    /// `overrides_of`'s answers across the check's rounds (#1057).
    overrides_kept: OverridesKept,
    lowerer: Lowerer,
    /// Methods and constants whose on-demand check reported errors: a
    /// statement that reaches one does not run (docs/05 §3: checked code
    /// only).
    /// Each with the error count before its check and the errors the
    /// check added (its own, and those of what it checked on first use: a
    /// constant's initializer).
    bad_methods: std::collections::HashMap<MethodId, (usize, Vec<(u32, Diagnostic)>)>,
    bad_consts: std::collections::HashSet<u32>,
    /// The interpreter's state, shared by every statement's run (the
    /// functions are append-only, so each run sees the earlier ones; the
    /// lowerer keeps them, `Lowerer::done`).
    state: Option<SharedState>,
    /// The last round's run-time world, shared with the interpreters
    /// that run on it (#1057: copied for none of them).
    world: Option<std::sync::Arc<RtWorld>>,
    files: Rc<Vec<SourceFile>>,
    /// The safety net refused a row of a compile-time round's tables
    /// (#645): no compile-time code runs any more in this check.
    net_refused: bool,
    prepared: bool,
    /// The constants a `def_field` leaves initialized: those of the REPL's
    /// earlier inputs (`continuing`).
    keep_consts: usize,
    /// The statement values and class-end hooks the statements of the
    /// classes not ended yet registered (docs/14 §5).
    ends: Rc<RefCell<ClassEnds>>,
    /// Which classes the pending statements cover, since the checker's
    /// last `begin` (#717).
    cover: Option<PendingCover>,
    /// The layouts before a later unit's declarations
    /// (`StaticRunner::later_unit`), until they are compared with those
    /// after.
    later_before: Option<Vec<quarz_lower::layout::Layout>>,
    /// The standard-library set's compile-time functions this runner's
    /// lowerer started from (`seeded`, #1097): what `reset` starts from
    /// again.
    seed: Option<Rc<quarz_lower::seed::LowererSeed>>,
    /// The reflection's rows (`reflect_rows`, `unshareable_of`), kept
    /// across statements and rebuilt for the classes the lowering's kept
    /// tables rebuilt (#717).
    reflect_kept: Option<ReflectKept>,
    /// The safety net's verdicts by class, kept across rounds and checked
    /// again for the classes whose rows were rebuilt (#717).
    net_kept: Option<NetKept>,
    /// `compile_time_allowed` by method, across the check's rounds:
    /// `impure_reach` asks it of every native a statement reaches, about
    /// 1,600 each round (#1098). Each entry keeps the key it answered, so
    /// a method id given to another native (the REPL rolling back an
    /// input) is asked again.
    allowed_kept: RefCell<Vec<Option<KeptVerdict>>>,
}

/// A native's key and whether it may run at compile time
/// (`Runner::allowed_kept`).
type KeptVerdict = (Box<str>, bool);

/// `Runner::reflect_kept`.
struct ReflectKept {
    /// What they were made for: the class graph and the extensions active
    /// (the static view the methods' rows read).
    key: (usize, usize, Vec<quarz_types::ExtensionId>),
    /// The lowering's tables' epoch they follow (`Lowerer::tables_epoch`).
    epoch: u64,
    fields: HashMap<ClassId, Rc<[ReflectField]>>,
    methods: HashMap<ClassId, Rc<[ReflectMethod]>>,
    constructors: HashMap<ClassId, Rc<[ReflectMethod]>>,
    unshareable: rustc_hash::FxHashMap<ClassId, String>,
}

/// `Runner::net_kept`.
struct NetKept {
    epoch: u64,
    by_class: HashMap<ClassId, Vec<quarz_types::witness_net::Checked>>,
}

/// The classes pending `static` statements cover (#717): for each
/// statement's class, the classes that are one (`World::classes_it_is`,
/// `class_is_a`'s own rule: its class and the classes under it), whose
/// members it may still add to. Kept as statements finish:
/// `Lowerer::static_skip` and the refusals' labels (`reflect_refusal`)
/// read it, rather than every class being tested against every pending
/// statement in each round.
///
/// What it was built from does not change between two
/// `StaticRunner::begin`s: a run generates members only, never a class or
/// a header. It is built again all the same when the classes, the
/// statements or the active extensions (which `classes_it_is` asks under)
/// differ from those it was built for. Each `cover()` call is in
/// `Runner::lower` or `note_pending`, after the checker has restored the
/// active set `check_static_stmt` changed, so that set is the phase's
/// throughout; the check costs a comparison.
struct PendingCover {
    /// What it was built for: the number of classes, and the extensions
    /// active then.
    classes: usize,
    active: Vec<quarz_types::ExtensionId>,
    /// Whether each statement (by index into `World::static_stmts`) was
    /// pending when last seen.
    pending: Vec<bool>,
    /// Each statement's label, as a refusal names it.
    labels: Vec<Rc<str>>,
    /// The classes under each statement's class.
    under: Rc<FxHashMap<ClassId, FxHashSet<ClassId>>>,
    /// Per class, how many pending statements cover it.
    count: FxHashMap<ClassId, u32>,
    /// The classes some pending statement covers (`count` above zero).
    skip: FxHashSet<ClassId>,
}

impl PendingCover {
    fn build(world: &World, pending: &[usize]) -> PendingCover {
        let stmt_classes: FxHashSet<ClassId> = world.static_stmts.iter().map(|s| s.class).collect();
        let mut under: FxHashMap<ClassId, FxHashSet<ClassId>> = FxHashMap::default();
        for c in &world.classes {
            for k in world.classes_it_is(c.id) {
                if stmt_classes.contains(&k) {
                    under.entry(k).or_default().insert(c.id);
                }
            }
        }
        let labels = world
            .static_stmts
            .iter()
            .map(|s| {
                let call = match &s.expr.kind {
                    quarz_syntax::ast::ExprKind::Call(c) => c.name.clone(),
                    _ => "static".to_string(),
                };
                Rc::from(format!("`{call}` in `{}`", world.class(s.class).name))
            })
            .collect();
        let mut cover = PendingCover {
            classes: world.classes.len(),
            active: world.active_extensions.borrow().clone(),
            pending: vec![false; world.static_stmts.len()],
            labels,
            under: Rc::new(under),
            count: FxHashMap::default(),
            skip: FxHashSet::default(),
        };
        cover.update(world, pending);
        cover
    }

    /// Bring it to the statements pending now.
    fn update(&mut self, world: &World, pending: &[usize]) {
        let mut now = vec![false; self.pending.len()];
        for &i in pending {
            now[i] = true;
        }
        for (i, (&was, &is)) in self.pending.iter().zip(&now).enumerate() {
            if was == is {
                continue;
            }
            let class = world.static_stmts[i].class;
            for &c in self.under.get(&class).into_iter().flatten() {
                let n = self.count.entry(c).or_insert(0);
                if is {
                    *n += 1;
                    self.skip.insert(c);
                } else {
                    *n -= 1;
                    if *n == 0 {
                        self.skip.remove(&c);
                    }
                }
            }
        }
        self.pending = now;
    }

    /// What a run's refusals read: the pending statements, in order, with
    /// the classes each covers.
    fn view(&self, world: &World) -> PendingView {
        PendingView {
            statements: self
                .pending
                .iter()
                .enumerate()
                .filter(|(_, p)| **p)
                .map(|(i, _)| (world.static_stmts[i].class, self.labels[i].clone()))
                .collect(),
            under: self.under.clone(),
        }
    }
}

/// The pending statements as a run sees them (`PendingCover::view`).
#[derive(Default)]
struct PendingView {
    statements: Vec<(ClassId, Rc<str>)>,
    under: Rc<FxHashMap<ClassId, FxHashSet<ClassId>>>,
}

impl PendingView {
    /// The labels of the pending statements covering `class`, in
    /// statement order, each once.
    fn labels(&self, class: ClassId) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        for (p, label) in &self.statements {
            if self.under.get(p).is_some_and(|u| u.contains(&class))
                && !out.iter().any(|l| l.as_str() == &**label)
            {
                out.push(label.to_string());
            }
        }
        out
    }
}

/// What the statements of the classes whose bodies have not ended yet
/// keep for their end (docs/14 §5): live values, kept across the runs
/// (the interpreter's state is shared, `SharedState`).
#[derive(Default)]
struct ClassEnds {
    classes: HashMap<ClassId, ClassEnd>,
}

#[derive(Default)]
struct ClassEnd {
    /// The hooks, in registration order, the first under each key.
    hooks: Vec<Hook>,
    /// The statement values by key: the type they were made with (as
    /// the checker names it) and the values, in statement order.
    values: HashMap<String, (String, Vec<Value>)>,
}

struct Hook {
    key: String,
    block: Value,
    /// The statement whose run registered it, and its callee.
    stmt: StaticStmt,
    callee: MethodId,
}

/// Where a compile-time run is, for the statement values and hooks.
#[derive(Clone, Default)]
struct EndContext {
    /// The statement running (its class, the statement, its callee); none
    /// for a `static(...)`.
    stmt: Option<(StaticStmt, MethodId)>,
    /// The class whose class-end hook runs.
    hook_of: Option<ClassId>,
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

    /// `generate_members`, and in debug builds the check that what it
    /// generated changed no existing layout, once after the last
    /// generation of the statement or hook (#818; #796 option C): but for
    /// the classes a `def_field` added a field to and their subclasses,
    /// whose holders keep them by reference. A generated `==`, `!=` or
    /// `hash` is judged before it is declared and checked after it in
    /// every build (`generate_members`).
    fn generate_each(
        &mut self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        pending: Vec<Pending>,
        classes: &mut Vec<ClassId>,
    ) -> Result<(), StaticFailure> {
        let before = cfg!(debug_assertions).then(|| quarz_lower::layout::compute(host.world()));
        let fields: Vec<ClassId> = pending
            .iter()
            .filter_map(|p| match p {
                Pending::Field(f) => Some(f.class),
                _ => None,
            })
            .collect();
        let result = self.generate_members(host, stmt, pending, classes);
        if let (Some(before), Ok(())) = (&before, &result) {
            let world = host.world();
            let after = quarz_lower::layout::compute(world);
            let moved = quarz_lower::layout::changes(before, &after).find(|(c, _)| {
                !world
                    .superclass_chain(*c)
                    .iter()
                    .any(|s| fields.contains(s))
            });
            assert!(
                moved.is_none(),
                "a generation of a statement of `{}` changed the layout of `{}` (#796)",
                world.class(stmt.class).name,
                moved.map_or(String::new(), |(c, _)| world.class(c).name.clone())
            );
        }
        result
    }

    fn generate_members(
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
        let mut generated: Vec<GeneratedHandles> = Vec::new();
        // The method each generation declared, by its position (what a
        // `def_method`'s handle names).
        let mut declared: Vec<Option<MethodId>> = vec![None; pending.len()];
        let stmt_args = statement_type_args(host, stmt);
        // Which of them took a carried class into their signature: a
        // handle to one, typed by the generic method's `T` as its caller
        // sees it, may be wider than the method.
        let mut carried_gen: Vec<bool> = vec![false; pending.len()];
        for (index, g) in pending.into_iter().enumerate() {
            let g = match g {
                Pending::Method(g) => g,
                // Checked with the class it names (the statement's own).
                Pending::Handle(h) => {
                    let world = host.world();
                    if let Baked::Data(c, fields) = &h {
                        if let (Some(Baked::Class(owner)), Some(Baked::Symbol(name))) =
                            (fields.first(), fields.get(1))
                        {
                            let call = if *c == world.builtin.meta_field_ref {
                                "field_ref"
                            } else if matches!(fields.get(3), Some(Baked::Bool(true))) {
                                "class_method_ref"
                            } else {
                                "method_ref"
                            };
                            let at = format!("`{call}(:{name})`");
                            generated.push((
                                None,
                                *owner,
                                None,
                                vec![(0, 0, h.clone())],
                                at,
                                Vec::new(),
                            ));
                        }
                    }
                    continue;
                }
                Pending::Field(f) => {
                    let at = format!("`def_field(:{})`", f.name);
                    let world = host.world();
                    if !world.class(f.ty).type_params.is_empty() {
                        return Err(fail(format!(
                            "{at}: `{}` takes type arguments, which a `Type` value does not carry: a generated field's type is a class without them",
                            world.class(f.ty).name
                        )));
                    }
                    // (`nullable: true`: a `U?`.)
                    let ty = if f.nullable {
                        Type::union_of(vec![Type::Class(f.ty, Vec::new()), world.nil()])
                    } else {
                        Type::Class(f.ty, Vec::new())
                    };
                    let field = FieldInfo {
                        name: f.name.clone(),
                        ty: ty.clone(),
                        mutable: f.mutable,
                        default: None,
                        baked_default: Some(f.default),
                        span: stmt.span,
                    };
                    host.add_generated_field(f.class, field)
                        .map_err(|why| fail(format!("{at}: {why}")))?;
                    // The accessors asked for, as `attr_reader`/`attr_writer`
                    // make them.
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
                            builds_self: false,
                            needs_includer: None,
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
            let at = if g.initialize {
                "`def_initialize`".to_string()
            } else if let Some(f) = &g.initializes {
                format!("the block given to `def_field(:{f})`")
            } else {
                format!(
                    "`{}(:{})`",
                    if g.singleton {
                        "def_class_method"
                    } else {
                        "def_method"
                    },
                    g.name
                )
            };
            // (As `def_field`'s: an object of a class only.)
            if g.initialize {
                let c = host.world().class(g.class);
                if c.kind != quarz_types::ClassKind::Class {
                    return Err(fail(format!(
                        "{at}: `{}` is not a class: `initialize` is generated into classes only (a `data` type's, an enum's or a module's is its own)",
                        c.name
                    )));
                }
            }
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
            let (call_id, block_span, block_method) = *self
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
            let Type::Proc(_, param_types, ret, _, _) = proc_ty else {
                return Err(not_literal());
            };
            if g.keywords.is_none() && param_types.len() != g.params.len() {
                return Err(fail(format!(
                    "{at}: the block takes {} parameter(s) but {} name(s) were given",
                    param_types.len(),
                    g.params.len()
                )));
            }
            // The signature: the block's type with the `static def`'s type
            // arguments (those of the statement's call, when they hold:
            // `statement_type_args`) and `Self` (the class generated into)
            // substituted.
            let world = host.world();
            let mut subst = stmt_args.clone();
            let target = world.class(g.class);
            let own: Vec<TypeParamId> = target.type_params.iter().map(|p| p.id).collect();
            subst.insert(
                SELF_PARAM,
                Type::Class(g.class, own.iter().map(|p| Type::Param(*p)).collect()),
            );
            // And those of the generic method the call is written in,
            // carried by its `Type[T]` parameters: the classes they had
            // (where the statement's call does not give them).
            if let Some(carried) = self.lowerer.carried_type_params.get(&call_id) {
                let checked = add_carried(world, carried, &g.type_args, &mut subst, &own)
                    .map_err(|why| fail(format!("{at}: {why}")))?;
                // (Only when the signature says one of them.)
                carried_gen[index] = checked.iter().any(|p| {
                    param_types
                        .iter()
                        .chain(std::iter::once(&*ret))
                        .any(|t| t.mentions_param(*p))
                });
            }
            let param_types: Vec<Type> = param_types.iter().map(|t| t.subst(&subst)).collect();
            // (An `initialize`'s result is discarded, as a written one's.)
            let ret = if g.initialize {
                Type::Void
            } else {
                ret.subst(&subst)
            };
            if let Some(f) = &g.initializes {
                field_initializer_refusal(world, g.class, f, &ret)
                    .map_err(|why| fail(format!("{at}: {why}")))?;
            }
            if let Some(p) = param_types
                .iter()
                .chain(std::iter::once(&ret))
                .find_map(|t| free_param(t, &own))
            {
                return Err(fail(format!(
                    "{at}: the block's type mentions `{}`, a type parameter the generated method cannot carry (the `static def` the statement calls has the statement's type arguments unless the program calls it elsewhere by its name; a generic method, the class its `Type[T]` parameter holds, when no other parameter mentions `T`, no bound relates `T` to another type parameter, `T` has no lower bound, the parameter is never assigned, and the call is in its body)",
                    world.type_name(&Type::Param(p))
                )));
            }
            // `JSON.decode[T]` in the body with `T` mentioning a carried
            // type parameter: its descriptor with the classes given here,
            // or an error at the statement (#409).
            let mut decode = Vec::new();
            for (func, idx, t) in self.deferred_decodes(g.func) {
                let t = t.subst(&subst);
                if let Some(p) = free_param(&t, &own) {
                    return Err(fail(format!(
                        "{at}: `JSON.decode` in the block decodes into a type that mentions `{}`, which the generated method cannot carry",
                        world.type_name(&Type::Param(p))
                    )));
                }
                match quarz_types::json_decode::descriptor(world, &t) {
                    Ok(d) => decode.push((func, idx, d)),
                    Err(why) => {
                        return Err(fail(format!(
                            "{at}: `JSON.decode` in the block cannot decode into {}: {why}",
                            world.type_name(&t)
                        )))
                    }
                }
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
            let params = match &g.keywords {
                // `name(*, k1: T1, k2: T2 = <absent>, ...)`: an optional
                // keyword has a default of its own, which the method never
                // evaluates (the body gets the hash of those passed:
                // `Generated::keywords`).
                Some(ks) => {
                    let mut params = Vec::new();
                    for (name, ty, required, nullable, ty_ref) in ks {
                        let t = match ty_ref {
                            // (`type_ref`: the type in full, `type` its
                            // class, #401's D3 (a).)
                            Some(r) => {
                                let t = type_of_ref(world, r, g.class).map_err(|why| {
                                    fail(format!("{at}: the keyword `{name}`'s `type_ref`: {why}"))
                                })?;
                                if *nullable {
                                    return Err(fail(format!(
                                        "{at}: the keyword `{name}` has a `type_ref` and `nullable: true`: say `nil` in the type (`TypeRef#nullable`)"
                                    )));
                                }
                                let erased = erase(world, &t);
                                if erased != *ty {
                                    return Err(fail(format!(
                                        "{at}: the keyword `{name}` is typed `{}` with a `type_ref` of `{}`, whose class is `{}`: make it with `Meta::Keyword.typed`",
                                        world.class(*ty).name,
                                        world.type_name(&t),
                                        world.class(erased).name
                                    )));
                                }
                                t
                            }
                            None => {
                                if !world.class(*ty).type_params.is_empty() {
                                    return Err(fail(format!(
                                        "{at}: the keyword `{name}` is typed `{}`, which takes type arguments a `Type` value does not carry: give it a `type_ref` (`Meta::Keyword.typed`)",
                                        world.class(*ty).name
                                    )));
                                }
                                let t = Type::Class(*ty, Vec::new());
                                if *nullable {
                                    Type::union_of(vec![t, world.nil()])
                                } else {
                                    t
                                }
                            }
                        };
                        params.push(ParamInfo {
                            name: name.clone(),
                            kind: ParamKind::KeywordOnly,
                            ty: t,
                            default: (!required).then(|| {
                                std::rc::Rc::new(quarz_syntax::ast::Expr {
                                    id: 0,
                                    span: stmt.span,
                                    kind: quarz_syntax::ast::ExprKind::Nil,
                                })
                            }),
                            assigns_ivar: false,
                            span: stmt.span,
                        });
                    }
                    params
                }
                None => g
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
                    .collect(),
            };
            let keyword_hash = g.keywords.is_some();
            let (func, class, captures) = (g.func, g.class, g.captures.clone());
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
                    keywords: keyword_hash,
                    initialize: g.initialize,
                    initializes: g.initializes.clone(),
                    decode,
                    written_at: written_at(
                        world,
                        &self.lowerer.done,
                        g.func,
                        block_span,
                        block_method,
                    ),
                }),
                builds_self: false,
                needs_includer: None,
            };
            // #796 (C): whether a field holds a `data` type in place is
            // decided with the declarations as written. A generation that
            // would change it (an `==`, `!=` or `hash` into the type, or into
            // a module it gets methods from) is refused before it is
            // declared: what was lowered or made with the layout keeps it.
            let deciding = !info.singleton && matches!(info.name.as_str(), "==" | "!=" | "hash");
            let layouts_before = deciding.then(|| quarz_lower::layout::compute(host.world()));
            if deciding {
                if let Some(why) = layout_refusal(
                    host.world(),
                    layouts_before.as_deref().unwrap_or_default(),
                    g.class,
                    &info.name,
                ) {
                    return Err(fail(format!("{at}: {why}")));
                }
            }
            let mid = host
                .add_generated(info)
                .map_err(|why| fail(format!("{at}: {why}")))?;
            // What the check judged is what the declaration did, in every
            // build (an internal error, not a wrong layout). Any other
            // generation is checked once per statement in debug builds
            // (`generate_each`).
            if let Some(before) = &layouts_before {
                let after = quarz_lower::layout::compute(host.world());
                if quarz_lower::layout::first_change(before, &after).is_some() {
                    return Err(fail(format!(
                        "{at}: internal error: the generation changed how a field holds a `data` type, which the check before it did not foresee (#796); please report"
                    )));
                }
            }
            declared[index] = Some(mid);
            // `override: true`: the method overrides an inherited one of
            // its name (docs/14 §5, #328).
            if g.override_ {
                generated_override(host.world(), mid)
                    .map_err(|why| fail(format!("{at}: {why}")))?;
            }
            if g.initialize {
                self.check_generated_init(host, stmt, call_id, func, class)
                    .map_err(|why| fail(format!("{at}: {why}")))?;
            }
            // A method that builds an instance of its receiver's class
            // (`new` in a class method's block, `Self.new` in an instance
            // method's): the class's `initialize` and its subclasses' must
            // take what `new` passes.
            for (from, init) in receiver_news(&self.lowerer.done, func) {
                host.generated_new(class, from, mid, init, (stmt.file, stmt.span))
                    .map_err(|why| fail(format!("{at}: {why}")))?;
            }
            // How the block uses the handles it captures, with this
            // generation's own substitution (its statement's type
            // arguments, `Self`, its call's carried classes).
            let uses = quarz_lower::lift::handle_uses(
                &self.lowerer.done,
                g.func,
                &self.lowerer.handle_uses,
            )
            .into_iter()
            .map(|(d, s, t)| (d, s, t.map(|t| t.subst(&subst))))
            .collect();
            generated.push((Some(func), class, Some(mid), captures, at.clone(), uses));
            if !classes.contains(&g.class) {
                classes.push(g.class);
            }
        }
        self.check_handles(host, stmt, &generated).map_err(fail)?;
        self.resolve_method_handles(host, stmt, &generated, &declared, &carried_gen)
            .map_err(fail)
    }

    /// A generated `initialize` (docs/14 §5) in `class`, its block checked
    /// for the class it was bounded by: every field `class` has beyond
    /// those (which the block cannot name) has a default, and a `super`
    /// in it, called as the `initialize` a class directly below the bound
    /// reaches, is one `class`'s own `super` would reach.
    fn check_generated_init(
        &self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        call_id: quarz_syntax::ast::NodeId,
        func: FuncId,
        class: ClassId,
    ) -> Result<(), String> {
        let world = host.world();
        let Some(&bound) = host.output().init_blocks.get(&call_id) else {
            return Err("internal: the block was not checked as an `initialize`".to_string());
        };
        let by = match &stmt.expr.kind {
            quarz_syntax::ast::ExprKind::Call(c) => c.name.clone(),
            _ => "the statement".to_string(),
        };
        let cname = &world.class(class).name;
        let named: Vec<String> = world
            .all_fields(bound)
            .into_iter()
            .map(|(f, _)| f.name)
            .collect();
        for (f, _) in world.all_fields(class) {
            let to_assign = !f.has_default() && (!f.mutable || !world.field_may_stay_nil(&f.ty));
            if to_assign && !named.contains(&f.name) {
                return Err(format!(
                    "the `initialize` generated by `{by}` leaves `@{}` of `{cname}` unassigned: its block assigns the fields of `{}` only, so a field `{cname}` adds needs a default",
                    f.name,
                    world.class(bound).name
                ));
            }
        }
        // `class`'s own `super`: the nearest of its ancestors' groups of
        // `initialize` overloads.
        let mut reached: Option<(ClassId, Vec<MethodId>)> = None;
        let mut cur = world.class(class).superclass.clone();
        while let Some(Type::Class(c, _)) = cur {
            let k = world.class(c);
            if let Some(ids) = k.methods.get("initialize").filter(|ids| !ids.is_empty()) {
                reached = Some((c, ids.clone()));
                break;
            }
            cur = k.superclass.clone();
        }
        let Some(f) = self.lowerer.done.get(func as usize) else {
            return Ok(());
        };
        for b in &f.blocks {
            for inst in &b.insts {
                let quarz_ir::Inst::Call {
                    kind: quarz_ir::CallKind::Super(m),
                    ..
                } = inst
                else {
                    continue;
                };
                if reached.as_ref().is_some_and(|(_, ids)| ids.contains(m)) {
                    continue;
                }
                let owner = &world.class(world.method(*m).owner).name;
                let reach = match &reached {
                    Some((c, _)) => format!("`{}#initialize`", world.class(*c).name),
                    None => "no `initialize`".to_string(),
                };
                return Err(format!(
                    "`super` in the `initialize` generated by `{by}` calls `{owner}#initialize`, but `super` in `{cname}` reaches {reach}: run the statement in a class below `{owner}` with no `initialize` of its own in between"
                ));
            }
        }
        Ok(())
    }

    /// The error for a handle typed with type parameter `p`, which has no
    /// class here: one of the statement's `static def`'s own when the
    /// program also calls a method of its name (docs/14 §5: its type
    /// arguments then do not hold; one such call is named, #417), else
    /// another method's.
    fn unknown_handle_param(
        &self,
        host: &dyn StaticHost,
        stmt: &StaticStmt,
        at: &str,
        shown: &str,
        p: TypeParamId,
    ) -> String {
        use quarz_types::check::CallTarget;
        let world = host.world();
        let param = world.type_name(&Type::Param(p));
        if let Some(CallTarget::Method { method }) = host.output().calls.get(&stmt.expr.id) {
            let callee = world.method(*method);
            if callee.type_params.iter().any(|q| q.id == p) {
                let name = &callee.name;
                // Why the statement's type arguments do not hold
                // (`statement_type_args`), when they do not.
                let plain = name
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_alphabetic() || c == '_');
                let aliased = callee.alias_of.is_some()
                    || world.methods.iter().any(|m| {
                        m.alias_of.is_some_and(|a| world.method(a).name == *name) && m.name != *name
                    });
                let why = if !plain || quarz_ir::shake::RUNTIME_NAMES.contains(&name.as_str()) {
                    Some(format!(
                        "the runtime (or an operator) calls `{name}` by its name, so the type arguments of the statements calling it do not hold (docs/14 §5); give the `static def` another name"
                    ))
                } else if aliased {
                    Some(format!(
                        "`{name}` has an alias, a call of which a statement does not see, so the type arguments of the statements calling it do not hold (docs/14 §5)"
                    ))
                } else {
                    match called_kind(host, *method) {
                        Called::Yes(at_call) => {
                            let place = match at_call.and_then(|(file, span)| {
                                self.files.get(file as usize).map(|f| (f, span))
                            }) {
                                Some((f, span)) => {
                                    format!(" (at {}:{})", f.name, f.line_col(span.start).line)
                                }
                                None => String::new(),
                            };
                            Some(format!(
                                "the program also calls a method named `{name}`{place}, so the type arguments of the statements calling `{name}` do not hold (docs/14 §5, by name over the whole program); give the `static def` a less common name"
                            ))
                        }
                        Called::OnSelf => Some(format!(
                            "`{name}` calls itself on `self` in its own body, with type arguments a statement does not give, so only its receiver's hold (docs/14 §5)"
                        )),
                        Called::No => None,
                    }
                };
                if let Some(why) = why {
                    return format!(
                        "{at}: the handle to `{shown}` is made with `{param}`, a type parameter of `{name}`, which has no class here: {why}"
                    );
                }
            }
        }
        format!(
            "{at}: the handle to `{shown}` is made with `{param}`, a type parameter of another method than the `static def` the statement calls, which does not carry it: a handle's type is written as a type, one of that `static def`'s type parameters, or one its generic method carries (#918: the class its `Type[T]` parameter holds, when no other parameter mentions `T`, no bound relates `T` to another type parameter, `T` has no lower bound, the parameter is never assigned, and the call is in its body)"
        )
    }

    /// The method handles the methods a statement generated captured
    /// (docs/14 §5), resolved now that every member it generates is
    /// declared: a `def_method`'s to the method it made, a `method_ref`'s
    /// to the method of its class by that name whose parameters (all
    /// positional) and result are exactly its `P`'s. The method is written
    /// into the baked handle, for `bind` to be lowered to it
    /// (`lift::handle_registers`).
    fn resolve_method_handles(
        &self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        generated: &[GeneratedHandles],
        declared: &[Option<MethodId>],
        carried_gen: &[bool],
    ) -> Result<(), String> {
        let call_args = statement_type_args(host, stmt);
        let world = host.world();
        let handle = world.builtin.meta_method;
        // `P` of `method_ref[P]` and `class_method_ref[P]`, as recorded.
        let own_p: Vec<TypeParamId> = ["method_ref", "class_method_ref"]
            .iter()
            .filter_map(|n| world.class(world.builtin.meta_classdef).methods.get(*n))
            .flatten()
            .filter_map(|m| world.method(*m).type_params.first().map(|p| p.id))
            .collect();
        let mut updates: Vec<(MethodId, Captures)> = Vec::new();
        for (_, into, mid, captures, at, _) in generated {
            let mut captures = captures.clone();
            let mut changed = false;
            for (_, _, value) in &mut captures {
                let Baked::Data(c, fields) = value else {
                    continue;
                };
                if *c != handle {
                    continue;
                }
                let (
                    Some(Baked::Class(owner)),
                    Some(Baked::Symbol(name)),
                    Some(Baked::Int(site)),
                    Some(Baked::Bool(singleton)),
                    Some(Baked::Int(method)),
                ) = (
                    fields.first(),
                    fields.get(1),
                    fields.get(2),
                    fields.get(3),
                    fields.get(4),
                )
                else {
                    continue;
                };
                let (owner, singleton) = (*owner, *singleton);
                let class = &world.class(owner).name;
                let shown = format!("{class}{}{name}", if singleton { "." } else { "#" });
                // The method is called on the generated method's `self`, an
                // instance of the class generated into (or a subclass), or
                // that class: the handle's class must be it or an ancestor.
                if !world.superclass_chain(*into).contains(&owner) {
                    return Err(format!(
                        "{at}: the handle to `{shown}` is of `{class}`, which `{}` does not inherit from: a generated method calls a method of its own class only",
                        world.class(*into).name
                    ));
                }
                let found = if *method < 0 {
                    // `def_method`'s: the method that generation declared.
                    let i = (-*method - 1) as usize;
                    if carried_gen.get(i).copied().unwrap_or(false) {
                        return Err(format!(
                            "{at}: the handle to `{shown}` is typed with a type parameter its method took a carried class for: use the method by name (`method_ref`) with its type written"
                        ));
                    }
                    match declared.get(i).copied().flatten() {
                        Some(m) => m,
                        None => {
                            return Err(format!(
                                "{at}: the handle to `{shown}` names a method another statement generates: a `def_method`'s handle is used by the statement that made it"
                            ))
                        }
                    }
                } else if *method > 0 {
                    // (Resolved by an earlier statement's check.)
                    continue;
                } else {
                    let p = host
                        .output()
                        .type_args
                        .get(&(*site as quarz_syntax::ast::NodeId))
                        .and_then(|args| args.iter().find(|(p, _)| own_p.contains(p)))
                        .map(|(_, t)| t.subst(&call_args));
                    let Some(p) = p else {
                        return Err(format!(
                            "{at}: the handle to `{shown}` has no recorded type"
                        ));
                    };
                    let fixed: Vec<TypeParamId> = world
                        .class(owner)
                        .type_params
                        .iter()
                        .map(|p| p.id)
                        .collect();
                    if let Some(t) = free_param(&p, &fixed) {
                        return Err(self.unknown_handle_param(host, stmt, at, &shown, t));
                    }
                    let Type::Proc(None, ps, ret, shareable, kws) = &p else {
                        return Err(format!(
                            "{at}: the handle to `{shown}` is made with `{}`, which is not a procedure type (`(A, B) -> R`)",
                            world.type_name(&p)
                        ));
                    };
                    if !kws.is_empty() {
                        return Err(format!(
                            "{at}: the handle to `{shown}` is made with `{}`, which takes keywords: a handle names a method whose parameters are all positional",
                            world.type_name(&p)
                        ));
                    }
                    // A `shareable` handle bound to `self` (`bind`) holds
                    // that `self`: only an instance of a class that promises
                    // Shareable may cross tasks (a class method's `self`, a
                    // class value, always may).
                    if *shareable && !singleton && world.shareable_promise(*into).is_none() {
                        let into = &world.class(*into).name;
                        return Err(format!(
                            "{at}: the handle to `{shown}` is a `{}`, but `{into}` is not Shareable: bound to its `self`, it would carry that `self` across tasks (make the procedure type plain, or have `{into}` include `Shareable`)",
                            world.type_name(&p)
                        ));
                    }
                    let own = Type::Class(
                        owner,
                        world
                            .class(owner)
                            .type_params
                            .iter()
                            .map(|p| Type::Param(p.id))
                            .collect(),
                    );
                    let recv = if singleton {
                        Type::ClassObject(
                            owner,
                            match &own {
                                Type::Class(_, args) => args.clone(),
                                _ => Vec::new(),
                            },
                        )
                    } else {
                        own.clone()
                    };
                    let matching: Vec<_> = world
                        .lookup_methods(&recv, name)
                        .into_iter()
                        .filter(|(m, subst)| {
                            let info = world.method(*m);
                            if info.singleton != singleton
                                || info.block.is_some()
                                || !info.type_params.is_empty()
                                || info.params.len() != ps.len()
                                || info.params.iter().any(|q| q.kind != ParamKind::Positional)
                            {
                                return false;
                            }
                            let mut subst = subst.clone();
                            subst.insert(SELF_PARAM, own.clone());
                            info.params
                                .iter()
                                .zip(ps)
                                .all(|(q, t)| world.same_type(&q.ty.subst(&subst), t))
                                && world.same_type(&info.ret.subst(&subst), ret)
                        })
                        .collect();
                    // The most derived first, as dispatch takes it: a match
                    // of an ancestor is a method it overrides, but two of
                    // one class are as an ambiguous call.
                    let ambiguous = matching.iter().enumerate().any(|(i, (a, _))| {
                        matching[i + 1..]
                            .iter()
                            .any(|(b, _)| world.method(*a).owner == world.method(*b).owner)
                    });
                    if ambiguous {
                        return Err(format!(
                            "{at}: the handle to `{shown}` names two methods of that type of one class: as an ambiguous call, it is an error"
                        ));
                    }
                    let Some((m, _)) = matching.into_iter().next() else {
                        return Err(format!(
                            "{at}: the handle to `{shown}` is a `Meta::Method[{}, {}]`, but `{class}` has no {} `{name}` of that type (by the end of the statement): a handle's type is the method's exactly, its parameters positional",
                            world.type_name(&recv),
                            world.type_name(&p),
                            if singleton { "class method" } else { "method" }
                        ));
                    };
                    m
                };
                // Which method, as a cached file keeps it (a method's id
                // does not stay): its class, and its place among the
                // class's methods of that name.
                let info = world.method(found);
                let table = if info.singleton {
                    &world.class(info.owner).singleton_methods
                } else {
                    &world.class(info.owner).methods
                };
                let Some(k) = table
                    .get(name)
                    .and_then(|ids| ids.iter().position(|i| *i == found))
                else {
                    return Err(format!(
                        "{at}: the handle to `{shown}` names a method of an extension, which a handle cannot call"
                    ));
                };
                fields[4] = Baked::Int(k as i64 + 1);
                fields[5] = Baked::Class(info.owner);
                changed = true;
            }
            if let (true, Some(mid)) = (changed, mid) {
                updates.push((*mid, captures));
            }
        }
        for (mid, captures) in updates {
            host.set_generated_captures(mid, captures);
        }
        Ok(())
    }

    /// The field handles the methods a statement generated captured
    /// (docs/14 §5), resolved now that every member it generates is
    /// declared: each names a field of its class (its own, inherited or
    /// generated) whose declared type is exactly its `U`, and a `var`
    /// one where `set` is called on it.
    fn check_handles(
        &self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        generated: &[GeneratedHandles],
    ) -> Result<(), String> {
        // The statement's call's type arguments, which a handle's `U` may
        // mention (`def_field(n, t, d)` in a `static def gen[V]`).
        let call_args = statement_type_args(host, stmt);
        let world = host.world();
        let handle = world.builtin.meta_field_ref;
        let Some(set) = world
            .class(handle)
            .methods
            .get("set")
            .and_then(|ids| ids.first().copied())
        else {
            return Ok(());
        };
        let get = world
            .class(handle)
            .methods
            .get("get")
            .and_then(|ids| ids.first().copied());
        // `U` of `def_field[U]` and `field_ref[U]`, as recorded at the call.
        let own_u: Vec<TypeParamId> = ["def_field", "field_ref"]
            .iter()
            .filter_map(|n| world.class(world.builtin.meta_classdef).methods.get(*n))
            .flatten()
            .filter_map(|m| world.method(*m).type_params.first().map(|p| p.id))
            .collect();
        for (func, into, _, captures, at, uses) in generated {
            let sets = func
                .map(|f| quarz_lower::lift::handle_sets(&self.lowerer.done, f, set))
                .unwrap_or_default();
            // Every slot the generated code calls `get` or `set` on has its
            // uses recorded by the lowering (`Lowerer::handle_uses`): a
            // missing one would leave a handle unchecked at its use.
            let called = func
                .map(|f| {
                    let methods: Vec<MethodId> = get.into_iter().chain([set]).collect();
                    quarz_lower::lift::handle_calls(&self.lowerer.done, f, &methods)
                })
                .unwrap_or_default();
            for (d, s, value) in captures {
                let Baked::Data(c, fields) = value else {
                    continue;
                };
                if *c != handle {
                    continue;
                }
                let (Some(Baked::Class(owner)), Some(Baked::Symbol(name)), Some(Baked::Int(site))) =
                    (fields.first(), fields.get(1), fields.get(2))
                else {
                    continue;
                };
                let class = &world.class(*owner).name;
                // The field is read where the generated method's `self` is,
                // an instance of the class generated into (or a subclass):
                // the handle's class must be that one or an ancestor.
                if !world.superclass_chain(*into).contains(owner) {
                    return Err(format!(
                        "{at}: the handle to `@{name}` is of `{class}`, which `{}` does not inherit from: a generated method reads a field of its own class only",
                        world.class(*into).name
                    ));
                }
                let Some((field, _)) = world.find_field(*owner, name) else {
                    return Err(format!(
                        "{at}: the handle to `@{name}` names no field of `{class}` (none was declared or generated by the end of the statement)"
                    ));
                };
                let site_id = *site as quarz_syntax::ast::NodeId;
                let site_args = host.output().type_args.get(&site_id);
                // The handle's type as the overload called gives it
                // (`FieldRef[T, U?]` for `def_field(..., nullable: true)`),
                // else `U`.
                let declared = match host.output().calls.get(&site_id) {
                    Some(quarz_types::check::CallTarget::Method { method }) => {
                        match &world.method(*method).ret {
                            Type::Class(_, args) if args.len() == 2 => Some(args[1].clone()),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let wanted = site_args.and_then(|args| {
                    let (p, t) = args.iter().find(|(p, _)| own_u.contains(p))?;
                    let u = match &declared {
                        Some(d) if d.mentions_param(*p) => {
                            let map: rustc_hash::FxHashMap<TypeParamId, Type> =
                                std::iter::once((*p, t.clone())).collect();
                            d.subst(&map)
                        }
                        _ => t.clone(),
                    };
                    Some(u.subst(&call_args))
                });
                let fixed: Vec<TypeParamId> = world
                    .class(*owner)
                    .type_params
                    .iter()
                    .map(|p| p.id)
                    .collect();
                // A handle made in a generic method, with the classes its
                // carried type parameters stood for when it was made, which
                // the handle holds (#918): checked as a generated method's
                // signature takes them (`add_carried`).
                let wanted = match (wanted, self.lowerer.carried_type_params.get(&site_id)) {
                    (Some(u), Some(carried)) => {
                        let classes: Vec<ClassId> = match fields.get(3) {
                            Some(Baked::Array(items)) => items
                                .iter()
                                .map(|b| match b {
                                    Baked::Class(c) => Ok(*c),
                                    _ => Err(format!(
                                        "{at}: internal error: the handle to `@{name}` holds a carried type argument that is not a class"
                                    )),
                                })
                                .collect::<Result<_, _>>()?,
                            _ => Vec::new(),
                        };
                        let mut subst = call_args.clone();
                        add_carried(world, carried, &classes, &mut subst, &fixed)
                            .map_err(|why| format!("{at}: the handle to `@{name}`: {why}"))?;
                        Some(u.subst(&subst))
                    }
                    (wanted, _) => wanted,
                };
                if let Some(u) = wanted {
                    // `U` is concrete, the statement's own type arguments or
                    // classes carried: another type parameter has no value
                    // here.
                    if let Some(p) = free_param(&u, &fixed) {
                        return Err(self.unknown_handle_param(
                            host,
                            stmt,
                            at,
                            &format!("@{name}"),
                            p,
                        ));
                    }
                    if !world.same_type(&field.ty, &u) {
                        return Err(format!(
                            "{at}: the handle to `@{name}` is a `Meta::FieldRef[{class}, {}]`, but the field is declared `{}`: a handle's type is the field's exactly",
                            world.type_name(&u),
                            world.type_name(&field.ty)
                        ));
                    }
                }
                if called.contains(&(*d, *s)) && !uses.iter().any(|(ud, us, _)| (ud, us) == (d, s))
                {
                    return Err(format!(
                        "{at}: internal error: the handle to `@{name}` is read or written with no type recorded for its use"
                    ));
                }
                // At its use: the type each `get` or `set` of the generated
                // method was checked with must be the field's too, with the
                // generation's own substitution (#918). The check above,
                // at its making, judges the handle as `def_field` or
                // `field_ref` typed it (a handle written with a wrong type
                // or an unknown type parameter); this one judges it as the
                // code reading or writing it sees it (a handle whose static
                // type was widened on its way, a helper's result typed
                // with its caller's view of a carried parameter, or one
                // made by another invocation of the helper). Both are
                // needed: the first for a handle no method uses, the second
                // for soundness.
                for (_, _, ty) in uses.iter().filter(|(ud, us, _)| (ud, us) == (d, s)) {
                    let used = match ty {
                        Some(Type::Class(c, args)) if *c == handle && args.len() == 2 => {
                            args[1].clone()
                        }
                        _ => {
                            return Err(format!(
                                "{at}: internal error: the handle to `@{name}` is used with no known `Meta::FieldRef` type"
                            ))
                        }
                    };
                    let fixed: Vec<TypeParamId> = world
                        .class(*owner)
                        .type_params
                        .iter()
                        .map(|p| p.id)
                        .collect();
                    if let Some(p) = free_param(&used, &fixed) {
                        return Err(format!(
                            "{at}: the handle to `@{name}` is used in the generated method as a `Meta::FieldRef[{class}, {}]`, whose `{}` has no class here: a handle is read and written with the type of the field",
                            world.type_name(&used),
                            world.type_name(&Type::Param(p))
                        ));
                    }
                    if !world.same_type(&field.ty, &used) {
                        return Err(format!(
                            "{at}: the handle to `@{name}` is used in the generated method as a `Meta::FieldRef[{class}, {}]`, but the field is declared `{}`: a handle's type is the field's exactly where it is read or written (a handle returned by a generic helper is typed with its caller's view of the helper's type parameter)",
                            world.type_name(&used),
                            world.type_name(&field.ty)
                        ));
                    }
                }
                if sets.contains(&(*d, *s)) && !field.mutable {
                    return Err(format!(
                        "{at}: `@{name}` is not `var`: `set` through a `Meta::FieldRef` needs a `var` field"
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn new(files: Vec<SourceFile>) -> Runner {
        Runner {
            lowerer: Lowerer::default(),
            bad_methods: Default::default(),
            overrides_kept: Default::default(),
            allowed_kept: Default::default(),
            bad_consts: Default::default(),
            state: None,
            world: None,
            files: Rc::new(files),
            net_refused: false,
            prepared: false,
            keep_consts: 0,
            ends: Default::default(),
            cover: None,
            later_before: None,
            seed: None,
            reflect_kept: None,
            net_kept: None,
        }
    }

    /// The reflection of `world` for a run (`reflect_rows` and
    /// `unshareable_of` of every class), from the rows kept since the last
    /// run, those of the classes the lowering's tables rebuilt made again
    /// (#717); compared with the rows made from nothing when the oracle
    /// asks (`QUARZ_VERIFY_STATIC_TABLES`).
    fn snapshot(&mut self, world: &World) -> WorldReflect {
        let key = (
            world.classes.len(),
            world.extensions.len(),
            world.active_extensions.borrow().clone(),
        );
        let changed = match &self.reflect_kept {
            Some(k) if k.key == key => self.lowerer.tables_changed_since(world, k.epoch),
            _ => None,
        };
        let epoch = self.lowerer.tables_epoch();
        match (&mut self.reflect_kept, changed) {
            (Some(k), Some(classes)) => {
                for c in classes {
                    let (fs, ms, cs) = reflect_rows(world, c);
                    k.fields.insert(c, Rc::from(fs));
                    k.methods.insert(c, Rc::from(ms));
                    k.constructors.insert(c, Rc::from(cs));
                    match unshareable_of(world, c) {
                        Some(why) => k.unshareable.insert(c, why),
                        None => k.unshareable.remove(&c),
                    };
                }
                k.epoch = epoch;
            }
            _ => {
                let mut fields = HashMap::new();
                let mut methods = HashMap::new();
                let mut constructors = HashMap::new();
                for c in 0..world.classes.len() as ClassId {
                    let (fs, ms, cs) = reflect_rows(world, c);
                    fields.insert(c, Rc::from(fs));
                    methods.insert(c, Rc::from(ms));
                    constructors.insert(c, Rc::from(cs));
                }
                self.reflect_kept = Some(ReflectKept {
                    key,
                    epoch,
                    fields,
                    methods,
                    constructors,
                    unshareable: unshareable_data(world),
                });
            }
        }
        let k = self.reflect_kept.as_ref().expect("made above");
        if quarz_lower::verify_static_tables() {
            for c in 0..world.classes.len() as ClassId {
                let (fs, ms, cs) = reflect_rows(world, c);
                assert!(
                    *k.fields[&c] == *fs && *k.methods[&c] == *ms && *k.constructors[&c] == *cs,
                    "internal error (QUARZ_VERIFY_STATIC_TABLES): the kept reflection of `{}` differs from the one made from nothing (#717)",
                    world.class(c).name
                );
            }
            assert!(
                k.unshareable == unshareable_data(world),
                "internal error (QUARZ_VERIFY_STATIC_TABLES): the kept unshareable data types differ (#717)"
            );
        }
        WorldReflect::with_rows(
            k.fields
                .iter()
                .map(|(c, f)| (*c, vec![f.clone()]))
                .collect(),
            k.methods
                .iter()
                .map(|(c, m)| (*c, vec![m.clone()]))
                .collect(),
            k.constructors
                .iter()
                .map(|(c, m)| (*c, vec![m.clone()]))
                .collect(),
            k.unshareable.clone(),
        )
    }

    /// The safety net over a round's rows (`quarz_lower::rows_net_of`): the
    /// rows of the classes the lowering's tables rebuilt since the last
    /// round, the others' verdicts kept (a verdict is a function of the
    /// row, #717); every row when the tables were built from nothing.
    fn net(&mut self, world: &World, rt: &RtWorld) -> Vec<quarz_types::FileDiagnostic> {
        let changed = self
            .net_kept
            .as_ref()
            .and_then(|k| self.lowerer.tables_changed_since(world, k.epoch));
        let own = |d| crate::own_in_app(world, d);
        let (checked, errors) = quarz_lower::rows_net_of(world, rt, &own, changed.as_deref());
        let epoch = self.lowerer.tables_epoch();
        let kept = match (&mut self.net_kept, changed) {
            (Some(k), Some(classes)) => {
                for c in classes {
                    k.by_class.remove(&c);
                }
                k.epoch = epoch;
                k
            }
            (slot, _) => slot.insert(NetKept {
                epoch,
                by_class: HashMap::new(),
            }),
        };
        for r in checked {
            kept.by_class.entry(r.class).or_default().push(r);
        }
        if quarz_lower::verify_static_tables() {
            let mut full: HashMap<ClassId, Vec<quarz_types::witness_net::Checked>> = HashMap::new();
            for r in quarz_lower::rows_net_of(world, rt, &own, None).0 {
                full.entry(r.class).or_default().push(r);
            }
            let key = |r: &quarz_types::witness_net::Checked| {
                (r.table, r.req, r.by, format!("{:?}", r.verdict))
            };
            for c in full.keys().chain(kept.by_class.keys()) {
                let a: Vec<_> = kept
                    .by_class
                    .get(c)
                    .into_iter()
                    .flatten()
                    .map(key)
                    .collect();
                let b: Vec<_> = full.get(c).into_iter().flatten().map(key).collect();
                assert!(
                    a == b,
                    "internal error (QUARZ_VERIFY_STATIC_TABLES): the kept net verdicts of `{}` differ: kept {a:?}, checked {b:?} (#717)",
                    world.class(*c).name
                );
            }
        }
        errors
    }

    /// The cover brought to the statements pending now, built on the
    /// first use since `begin` (or once the statements are more).
    fn cover(&mut self, host: &dyn StaticHost) -> &PendingCover {
        let world = host.world();
        let pending = host.pending_statements();
        match &mut self.cover {
            Some(c)
                if c.pending.len() == world.static_stmts.len()
                    && c.classes == world.classes.len()
                    && *world.active_extensions.borrow() == c.active =>
            {
                c.update(world, &pending)
            }
            _ => self.cover = Some(PendingCover::build(world, &pending)),
        }
        self.cover.as_ref().expect("built")
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

    /// A runner for a program that loads a standard-library set made at
    /// first use (#1097): its lowerer starts from the set's compile-time
    /// functions, which its generated methods are lifted from, and its
    /// interpreter state gets them first.
    pub fn seeded(files: Vec<SourceFile>, seed: Rc<quarz_lower::seed::LowererSeed>) -> Runner {
        Runner {
            lowerer: Lowerer::from_seed((*seed).clone()),
            seed: Some(seed),
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
            // (The sites of the methods the last round checked included:
            // the round's rows carry their records, #536 step 6.)
            host.record_inherited_constructors();
            // The classes whose statements are still to run, with their
            // descendants: not reached by name (`Lowerer::static_skip`).
            let skip = self.cover(host).skip.clone();
            self.lowerer.static_skip = skip;
            // (The last round's world goes: the lowerer updates the one
            // it keeps in place when no one else holds it, #1057 PR 4.)
            self.world = None;
            let round = self.lowerer.lower_static(
                host.world(),
                host.output(),
                &stmt.expr,
                stmt.class,
                stmt.file,
                callee,
                self.files.clone(),
            );
            // The safety net over the round's rows, before its tables are
            // loaded and anything runs on them (#645): a refused row is an
            // error at its own place, and no compile-time code runs after
            // (`execute`, `run_hook`). Checked until it first refuses: the
            // check fails then, so later rounds and the final net
            // (`Lowerer::declare`) report nothing again.
            if !self.net_refused {
                let errors = self.net(host.world(), &round.delta.world);
                if !errors.is_empty() {
                    self.net_refused = true;
                    host.report_errors(errors);
                }
            }
            debug_assert_eq!(self.lowerer.done.len(), round.delta.base as usize);
            // (A seeded lowerer's functions go into a new state first.)
            let fresh = self.state.is_none();
            let state = self
                .state
                .get_or_insert_with(|| SharedState::with_threads(Box::new(std::io::stderr()), 1))
                .clone();
            if fresh && round.delta.base > 0 {
                Interp::load_functions(&state, 0, self.lowerer.done.clone());
            }
            self.lowerer
                .done
                .extend(round.delta.functions.iter().cloned());
            // Loads the round's functions into the shared state; the
            // run's interpreter is made over it after (`interp`).
            let world = round.delta.world;
            Interp::load_functions(&state, round.delta.base, round.delta.functions);
            self.world = Some(world);
            if round.unchecked.is_empty() && round.unchecked_consts.is_empty() {
                return round.stmt_func;
            }
            for m in round.unchecked {
                let before = host.error_count();
                host.ensure_method_checked(m);
                if host.error_count() > before {
                    self.bad_methods
                        .insert(m, (before, host.errors_after(before)));
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

    /// Why a statement whose lowering found errors (`errors_before` the
    /// count before it) did not run: a method checked for it with errors,
    /// which the lowering reached (a call's target or an override of it,
    /// or a method of a name called by name: docs/14 §7), named
    /// with its first error, the one checked first; else what was found.
    fn blocked_message(
        &self,
        host: &dyn StaticHost,
        callee_name: &str,
        errors_before: usize,
    ) -> String {
        let blocking = self
            .bad_methods
            .iter()
            .filter(|(_, (n, _))| *n >= errors_before)
            .min_by_key(|(_, (n, _))| *n);
        let Some((&m, _)) = blocking else {
            return format!(
                "{callee_name} did not run: what it reaches has errors (reported above)"
            );
        };
        format!(
            "{callee_name} did not run: {}",
            self.describe_bad(host, m, "it may reach", "")
        )
    }

    /// Why a statement did not run when a method with errors came into its
    /// reach through a call by name (#1037): the call, in `from`, with
    /// where it is; the first such method of the name in source order
    /// (file, then position) with its first error; and how many more of
    /// the name have errors. Every method of the name is in the reach
    /// (docs/14 §7), so the message says which call brought them.
    fn by_name_message(
        &self,
        host: &dyn StaticHost,
        callee_name: &str,
        b: &ByName,
        mut bad: Vec<MethodId>,
        pulled: Option<MethodId>,
    ) -> String {
        let (name, from) = (b.name.as_str(), b.from);
        let world = host.world();
        bad.sort_by_key(|&m| {
            let info = world.method(m);
            (info.file, info.span.start, m)
        });
        let f = &self.lowerer.done[from as usize];
        let line = send_line(f, name);
        // (The program's own call, where it is; else one the runtime makes
        // by name for what that function does: `to_s` for an
        // interpolation, a native's calls, `shake::RUNTIME_NAMES`.)
        let lead = match (self.files.get(f.file as usize), line) {
            (Some(file), Some(l)) => {
                format!("its call of `{name}` by name ({}:{l}) may reach", file.name)
            }
            _ => match b.native.map(|n| world.method(n).native_key(world)) {
                Some(key) => format!(
                    "the native `{key}`, which is taken to call `{name}` by name on the values it is given, may reach"
                ),
                None => format!(
                    "a call of `{name}` the runtime makes by name (for `{}`) may reach",
                    f.name
                ),
            },
        };
        // (Reached from the method of that name the call took: that one,
        // then what has errors.)
        if let (Some(p), Some(&m)) = (pulled, bad.first()) {
            let lead = format!(
                "{lead} {}, a method of that name, which may reach",
                self.method_place(host, p)
            );
            return format!(
                "{callee_name} did not run: {}",
                self.describe_bad(host, m, &lead, "")
            );
        }
        let more = match bad.len() {
            0 | 1 => String::new(),
            2 => " (and 1 more method of that name with errors)".to_string(),
            k => format!(" (and {} more methods of that name with errors)", k - 1),
        };
        let first = bad.first().copied();
        match first {
            Some(m) => format!(
                "{callee_name} did not run: {}{more}",
                self.describe_bad(host, m, &lead, ", a method of that name")
            ),
            None => format!("{callee_name} did not run: {lead} a method with errors"),
        }
    }

    /// Method `m` as an error names it: "`Class#name` (file:line)".
    fn method_place(&self, host: &dyn StaticHost, m: MethodId) -> String {
        let world = host.world();
        let info = world.method(m);
        let name = format!(
            "{}{}{}",
            world.class(info.owner).name,
            if info.singleton { "." } else { "#" },
            info.name
        );
        match self.files.get(info.file as usize) {
            Some(f) => format!("`{name}` ({}:{})", f.name, f.line_col(info.span.start).line),
            None => format!("`{name}`"),
        }
    }

    /// `m`, a method with errors a statement may reach, where it is, and its
    /// first error.
    fn describe_bad(&self, host: &dyn StaticHost, m: MethodId, lead: &str, after: &str) -> String {
        let world = host.world();
        let errors: &[(u32, Diagnostic)] = self
            .bad_methods
            .get(&m)
            .map(|(_, e)| e.as_slice())
            .unwrap_or(&[]);
        let info = world.method(m);
        let at = |file: u32, span: Span| -> String {
            match self.files.get(file as usize) {
                Some(f) => format!("{}:{}", f.name, f.line_col(span.start).line),
                None => String::new(),
            }
        };
        let named = self.method_place(host, m);
        // Its own first error, else the first of what it uses (a
        // constant whose initializer has errors), with where that is.
        let own = errors.iter().find(|(f, d)| {
            *f == info.file && info.span.start <= d.span.start && d.span.end <= info.span.end
        });
        match (own, errors.first()) {
            (Some((_, d)), _) => format!("{lead} {named}{after}, which has errors: {}", d.message),
            (None, Some((f, d))) => format!(
                "{lead} {named}{after}, which uses what has errors: {} ({})",
                d.message,
                at(*f, d.span)
            ),
            (None, None) => {
                format!("{lead} {named}{after}, which has errors (reported with it)")
            }
        }
    }

    /// The deferred `JSON.decode[T]` descriptors of block function `func`
    /// and the blocks it makes: each marker's function and constant, and
    /// its `T` (`Lowerer::decode_markers`, `decode_deferred`).
    fn deferred_decodes(&self, func: FuncId) -> Vec<(FuncId, u32, Type)> {
        let mut out = Vec::new();
        let mut work = vec![func];
        let mut seen = std::collections::HashSet::new();
        while let Some(f) = work.pop() {
            if !seen.insert(f) {
                continue;
            }
            let Some(fun) = self.lowerer.done.get(f as usize) else {
                continue;
            };
            for &(idx, n) in self.lowerer.decode_markers.get(&f).into_iter().flatten() {
                if let Some(t) = self.lowerer.decode_deferred.get(n) {
                    out.push((f, idx, t.clone()));
                }
            }
            for b in &fun.blocks {
                for inst in &b.insts {
                    if let quarz_ir::Inst::MakeBlock { func, .. } = inst {
                        work.push(*func);
                    }
                }
            }
        }
        out
    }

    /// A method (`Ok`) or constant (`Err`, named) with errors that the
    /// statement reaches.
    fn bad_reach(
        &self,
        root: FuncId,
        lifted: &rustc_hash::FxHashSet<FuncId>,
    ) -> Option<Result<BadReach, String>> {
        if self.bad_methods.is_empty() && self.bad_consts.is_empty() {
            return None;
        }
        let world = self.world.as_ref()?;
        self.overrides_kept.sync(world);
        let by_name = self.overrides_kept.by_name();
        // Each function once per bound of its `self` (`reached`).
        let mut seen: rustc_hash::FxHashSet<(FuncId, SelfBound)> = Default::default();
        // (Each item with the call by name it was reached through, if any:
        // what the error names when a method reached from it has errors,
        // #1037.)
        // (Breadth first: a method reached several ways is reached first
        // the shortest way from the statement, whose call by name is the
        // one to name.)
        let mut work: std::collections::VecDeque<(FuncId, SelfBound, Option<std::rc::Rc<Origin>>)> =
            [(root, None, None)].into();
        while let Some((fid, bound, origin)) = work.pop_front() {
            if fid as usize >= self.lowerer.done.len() || !seen.insert((fid, bound.clone())) {
                continue;
            }
            let f = &self.lowerer.done[fid as usize];
            let mut methods: Vec<(MethodId, SelfBound)> = Vec::new();
            let mut found: Option<Result<BadReach, String>> = None;
            // (The methods `f` reaches through a call by name, with the
            // name: what the error names when one of them is the bad one.)
            let mut via_name: Vec<(MethodId, String, Option<MethodId>)> = Vec::new();
            reached(
                world,
                &by_name,
                &self.overrides_kept,
                f,
                &bound,
                &mut methods,
                &mut |r| match r {
                    shake::Ref::Func(g) if !lifted.contains(&g) => work.push_back((
                        g,
                        func_bound(&self.lowerer.done, f, g, &bound),
                        origin.clone(),
                    )),
                    shake::Ref::Const(c) => {
                        if self.bad_consts.contains(&c) {
                            found = Some(Err(world.consts[c as usize].name.clone()));
                        } else if let Some(init) = world.consts.get(c as usize).and_then(|c| c.init)
                        {
                            work.push_back((init, None, origin.clone()));
                        }
                    }
                    _ => {}
                },
                true,
                &mut |m, n, by| {
                    if !via_name.iter().any(|(o, _, _)| *o == m) {
                        via_name.push((m, n.to_string(), by));
                    }
                },
            );
            if found.is_some() {
                return found;
            }
            for (m, b) in methods {
                for &m in std::iter::once(&m).chain(synth_calls(world, m)) {
                    if self.bad_methods.contains_key(&m) {
                        let tag = via_name.iter().find(|(o, _, _)| *o == m).cloned();
                        // (Not itself of the name, but reached from a method
                        // that was: that call, that method, then this one.)
                        if let (None, Some(o)) = (&tag, &origin) {
                            return Some(Ok(BadReach {
                                method: m,
                                by_name: Some(self.by_name_of(&seen, o.from, &o.name, o.native)),
                                reached_bad: vec![m],
                                pulled: Some(o.pulled),
                            }));
                        }
                        // (The program's own call of the name the walk passed,
                        // the first in source order, when there is one: the
                        // one to name, rather than a runtime path the walk
                        // happened to take first.)
                        let by_name =
                            tag.map(|(_, n, native)| self.by_name_of(&seen, fid, &n, native));
                        // (The methods with errors this call of the name
                        // reached, for the message's first and count.)
                        let reached_bad: Vec<MethodId> = match &by_name {
                            Some(b) => via_name
                                .iter()
                                .filter(|(o, n, _)| {
                                    *n == b.name && self.bad_methods.contains_key(o)
                                })
                                .map(|(o, _, _)| *o)
                                .collect(),
                            None => Vec::new(),
                        };
                        return Some(Ok(BadReach {
                            method: m,
                            by_name,
                            reached_bad,
                            pulled: None,
                        }));
                    }
                    if let Some(f) = world.methods[m as usize].func {
                        // (A method taken by a name starts that origin; any
                        // other carries this function's.)
                        let from = match via_name.iter().find(|(o, _, _)| *o == m) {
                            Some((_, n, native)) => Some(std::rc::Rc::new(Origin {
                                name: n.clone(),
                                native: *native,
                                from: fid,
                                pulled: m,
                            })),
                            None => origin.clone(),
                        };
                        work.push_back((f, b.clone(), from));
                    }
                }
            }
        }
        None
    }

    /// The call by name to name for a method that `name` brought into the
    /// reach, walking from `fid` (`seen` the functions walked so far): the
    /// program's own call of the name, the first in source order among
    /// them, when there is one, rather than a runtime path the walk
    /// happened to take first; else the native (`native`) or the runtime's
    /// call in `fid` (#1037).
    fn by_name_of(
        &self,
        seen: &rustc_hash::FxHashSet<(FuncId, SelfBound)>,
        fid: FuncId,
        name: &str,
        native: Option<MethodId>,
    ) -> ByName {
        let own = seen
            .iter()
            .map(|(g, _)| *g)
            .chain(std::iter::once(fid))
            .filter_map(|g| {
                let f = self.lowerer.done.get(g as usize)?;
                send_line(f, name).map(|l| ((f.file, l), g))
            })
            .min();
        ByName {
            from: own.map_or(fid, |(_, g)| g),
            native: native.filter(|_| own.is_none()),
            name: name.to_string(),
        }
    }

    /// `compile_time_allowed(key)` for method `m`, kept (`allowed_kept`).
    fn allowed(&self, m: MethodId, key: &str) -> bool {
        let mut kept = self.allowed_kept.borrow_mut();
        let i = m as usize;
        if let Some(Some((k, ok))) = kept.get(i) {
            if **k == *key {
                return *ok;
            }
        }
        let ok = compile_time_allowed(key);
        if kept.len() <= i {
            kept.resize(i + 1, None);
        }
        kept[i] = Some((key.into(), ok));
        ok
    }

    /// A native the statement reaches that cannot run at compile time,
    /// with the calls leading to it (innermost last).
    fn impure_reach(
        &self,
        root: FuncId,
        lifted: &rustc_hash::FxHashSet<FuncId>,
    ) -> Option<Vec<String>> {
        let world = self.world.as_ref()?;
        self.overrides_kept.sync(world);
        let by_name = self.overrides_kept.by_name();
        // Each function once per bound of its `self` (`reached`).
        let mut seen: rustc_hash::FxHashSet<(FuncId, SelfBound)> = Default::default();
        // The path of method names (and constants) that reached each
        // function, as links to its last step: built into names only
        // when a native denied at compile time is found (#1057).
        enum Step {
            Method(MethodId),
            Const(u32),
        }
        let mut steps: Vec<(Step, Option<usize>)> = Vec::new();
        let path = |steps: &Vec<(Step, Option<usize>)>, mut at: Option<usize>| {
            let mut p: Vec<String> = Vec::new();
            while let Some(k) = at {
                let (step, up) = &steps[k];
                p.push(match step {
                    Step::Method(m) => method_name(world, *m),
                    Step::Const(c) => world.consts[*c as usize].name.clone(),
                });
                at = *up;
            }
            p.reverse();
            p
        };
        // Each function with the bound of its `self` and the last step of
        // the path that reached it.
        let mut work: Vec<(FuncId, SelfBound, Option<usize>)> = vec![(root, None, None)];
        while let Some((fid, bound, at)) = work.pop() {
            if !seen.insert((fid, bound.clone())) {
                continue;
            }
            let f = &self.lowerer.done[fid as usize];
            let mut methods: Vec<(MethodId, SelfBound)> = Vec::new();
            let mut funcs: Vec<FuncId> = Vec::new();
            let mut consts: Vec<u32> = Vec::new();
            reached(
                world,
                &by_name,
                &self.overrides_kept,
                f,
                &bound,
                &mut methods,
                &mut |r| match r {
                    shake::Ref::Func(f) if !lifted.contains(&f) => funcs.push(f),
                    shake::Ref::Const(c) => consts.push(c),
                    _ => {}
                },
                false,
                &mut |_, _, _| {},
            );
            // (In order: a stack, as is `work`.)
            let mut methods: Vec<(MethodId, SelfBound, Option<usize>)> =
                methods.into_iter().rev().map(|(m, b)| (m, b, at)).collect();
            while let Some((m, b, up)) = methods.pop() {
                let rm = &world.methods[m as usize];
                steps.push((Step::Method(m), up));
                let here = Some(steps.len() - 1);
                if let Some(key) = &rm.native_key {
                    if !self.allowed(m, key) {
                        return Some(path(&steps, here));
                    }
                }
                for &i in synth_calls(world, m) {
                    methods.push((i, None, here));
                }
                if let Some(f) = rm.func {
                    work.push((f, b, here));
                }
            }
            for g in funcs {
                work.push((g, func_bound(&self.lowerer.done, f, g, &bound), at));
            }
            for c in consts {
                if let Some(init) = world.consts.get(c as usize).and_then(|c| c.init) {
                    steps.push((Step::Const(c), at));
                    work.push((init, None, Some(steps.len() - 1)));
                }
            }
        }
        None
    }
}

/// What `self` is known to be in a run of a function: an instance of one
/// of these classes or of a subclass (`None`: anything its type allows).
/// A method reached through a call on such a receiver runs with it as
/// `self` (docs/14 §7).
type SelfBound = Option<std::rc::Rc<[ClassId]>>;

/// The first line of `f` that calls `name` by name (`CallKind::Send`).
fn send_line(f: &quarz_ir::Function, name: &str) -> Option<u32> {
    f.blocks
        .iter()
        .flat_map(|b| b.insts.iter().zip(&b.lines))
        .filter_map(|(i, l)| match i {
            quarz_ir::Inst::Call {
                kind: quarz_ir::CallKind::Send(n),
                ..
            } if n == name => Some(*l),
            _ => None,
        })
        .min()
}

/// The method with errors a statement may reach (`Runner::bad_reach`),
/// and the name and function of the call by name that brought it into
/// the reach, when one did (#1037).
struct BadReach {
    method: MethodId,
    by_name: Option<ByName>,
    /// With `by_name`: every method with errors the call took by that name
    /// (`method` among them), those the message names and counts.
    reached_bad: Vec<MethodId>,
    /// The method of that name the call took, when `method` is not one of
    /// them but was reached from it.
    pulled: Option<MethodId>,
}

/// A call by name a walk passed through (`Runner::bad_reach`): its name,
/// the native whose calls named it (none for the program's own call or an
/// instruction's), the function it was made in, and the method of that
/// name taken, from which what follows was reached.
struct Origin {
    name: String,
    native: Option<MethodId>,
    /// The function whose walk took the method by the name.
    from: FuncId,
    pulled: MethodId,
}

/// A call by name that brought methods into a statement's reach: the
/// program's own in `from` (`CallKind::Send`), or one the runtime makes
/// for what `from` does, by a native (`native`, whose `native_calls` name
/// it) or by an instruction.
struct ByName {
    name: String,
    from: FuncId,
    native: Option<MethodId>,
}

/// The methods a run of `f` may call, into `methods`, each with the
/// bound of the `self` it runs with: a method called as resolved and its
/// overrides (a subclass's runs in its place; on a receiver whose static
/// type, or `self_bound` for a call on `self`, bounds it, those its
/// lookup may find), one called exactly (`super`, keeping `self_bound`,
/// a function) alone, those of a name looked up at run time, and for a
/// construction the `initialize` it runs: the class's own (or inherited)
/// for `C.new`, and those of its subclasses too for `new` on a class
/// method's receiver, which may be one. The other references go to
/// `other`. With `by_runtime`, also the methods the runtime calls by name
/// for the instructions and the natives among them (for `bad_reach`
/// only).
/// Each method taken by a name goes to `named` too, with the name and
/// the native whose calls named it (none for the program's own call or
/// an instruction's), for the error that says which call brought it
/// (#1037).
#[allow(clippy::too_many_arguments)]
fn reached<'a>(
    world: &RtWorld,
    by_name: &MethodsByName,
    kept: &OverridesKept,
    f: &'a quarz_ir::Function,
    self_bound: &SelfBound,
    methods: &mut Vec<(MethodId, SelfBound)>,
    other: &mut dyn FnMut(shake::Ref<'a>),
    by_runtime: bool,
    named: &mut dyn FnMut(MethodId, &'a str, Option<MethodId>),
) {
    let first = methods.len();
    // The names the runtime calls for the instructions.
    let mut runtime: Vec<&'static str> = Vec::new();
    shake::reach_refs(f, &mut |r| match r {
        shake::Ref::Method(m) => {
            methods.push((m, None));
            methods.extend(
                kept.overrides(world, by_name, m, &None)
                    .iter()
                    .map(|&o| (o, None)),
            );
        }
        shake::Ref::Bounded {
            method,
            classes,
            on_self,
        } => {
            let bound: SelfBound = match (on_self, self_bound) {
                (true, Some(b)) => Some(b.clone()),
                _ => classes.map(Into::into),
            };
            methods.push((method, bound.clone()));
            methods.extend(
                kept.overrides(world, by_name, method, &bound)
                    .iter()
                    .map(|&o| (o, bound.clone())),
            );
        }
        shake::Ref::Exact { method, on_self } => {
            methods.push((method, if on_self { self_bound.clone() } else { None }))
        }
        // A call on a class value bounded by `classes`: the method, and
        // what a class object of one of them (or of a subclass, or of a
        // class including a module among them) runs in its place, as the
        // runtime finds it (`RtWorld::class_override_rows`, built from
        // `World::class_method_target`); never an instance method of a
        // program class (docs/14 §8, #1173). Each runs with `self`
        // unbounded (an approximation that reaches more).
        shake::Ref::ClassSide { method, classes } => {
            methods.push((method, None));
            methods.extend(
                class_side_targets(world, method, classes)
                    .into_iter()
                    .map(|o| (o, None)),
            );
        }
        shake::Ref::Runtime(n) => {
            if by_runtime {
                runtime.push(n);
            }
        }
        shake::Ref::Name(n) => {
            if let Some(ms) = by_name.get(n) {
                for o in ms.iter().copied().filter(|&o| !denied_owner(world, o)) {
                    named(o, n, None);
                    methods.push((o, None));
                }
            }
        }
        shake::Ref::Construct { class, init, recv } => {
            match init {
                Some(m) => methods.push((m, None)),
                // (None: the class has no `initialize`, and none runs;
                // counted all the same, any ancestor's overload.)
                None => {
                    for &a in &world.classes[class as usize].ancestors {
                        if let Some(ms) = world.classes[a as usize].methods.get("initialize") {
                            methods.extend(ms.iter().map(|&m| (m, None)));
                            break;
                        }
                    }
                }
            }
            if recv {
                if let Some(ms) = by_name.get("initialize") {
                    methods.extend(
                        ms.iter()
                            .copied()
                            .filter(|&o| {
                                let om = &world.methods[o as usize];
                                !om.singleton
                                    && om.owner != class
                                    && world.class_is_a(om.owner, class)
                                    && !denied_owner(world, o)
                            })
                            .map(|o| (o, None)),
                    );
                }
            }
            // The classes it may build: their fields' defaults run, and
            // their `deinitialize` when the object is released.
            for (c, rc) in world.classes.iter().enumerate() {
                let c = c as ClassId;
                if c != class && !(recv && world.class_is_a(c, class)) {
                    continue;
                }
                for f in &rc.fields {
                    if let Some(d) = f.default {
                        other(shake::Ref::Func(d));
                    }
                }
                for &a in &rc.ancestors {
                    if let Some(ms) = world.classes[a as usize].methods.get("deinitialize") {
                        methods.extend(ms.iter().map(|&m| (m, None)));
                    }
                }
            }
            other(shake::Ref::Class(class));
        }
        r => other(r),
    });
    // (Only for the check that no method with errors runs, `bad_reach`:
    // by name, without the values' types, these reach far more than runs,
    // a prelude `inspect` iterating to any `each`. What reaches IO through
    // them is stopped where the native is called, `Interp::invoke`.)
    if !by_runtime {
        return;
    }
    // Then what the runtime calls by name: for the instructions, and for
    // the natives among the methods (found so too). A native found by a
    // name is one the runtime calls for that name (`Object#to_s` for
    // `to_s`), which calls what that name's calls do; another, what its
    // own kind calls (`native_calls`). Each method once.
    let mut seen: rustc_hash::FxHashSet<MethodId> =
        methods[first..].iter().map(|(m, _)| *m).collect();
    let mut work: Vec<(MethodId, Option<&'static str>)> =
        methods[first..].iter().map(|&(m, _)| (m, None)).collect();
    // (Each method found by a name, with it: `named`, for the error that
    // says which call by name brought it, #1037.)
    let mut tagged: Vec<(MethodId, &'static str, Option<MethodId>)> = Vec::new();
    let mut add = |n: &'static str,
                   by: Option<MethodId>,
                   work: &mut Vec<(MethodId, Option<&'static str>)>,
                   methods: &mut Vec<(MethodId, SelfBound)>| {
        if let Some(ms) = by_name.get(n) {
            for &o in ms {
                if !world.methods[o as usize].singleton && !denied_owner(world, o) && seen.insert(o)
                {
                    methods.push((o, None));
                    work.push((o, Some(n)));
                    tagged.push((o, n, by));
                }
            }
        }
    };
    for n in runtime {
        add(n, None, &mut work, methods);
    }
    while let Some((m, by)) = work.pop() {
        if world.methods[m as usize].native_key.is_none() {
            continue;
        }
        // (A native reached by a name: what it calls when called by it,
        // `shake::calls_as`, #394.)
        let names: Vec<&'static str> = match (by, world.methods[m as usize].native_key.as_deref()) {
            (Some(n), Some(key)) => shake::calls_as(key, n).collect(),
            _ => native_calls(world, m).to_vec(),
        };
        for n in names {
            add(n, Some(m), &mut work, methods);
        }
    }
    for (o, n, by) in tagged {
        named(o, n, by);
    }
}

/// The bound of `self` in function `g`, which `f` refers to, run with
/// `bound`: a block of `f`'s has its `self` (where it is another, a block
/// with a receiver, no call in it is marked `on_self`); a method `f`
/// inlined has its own, and a field's default (a construction's) none.
fn func_bound(
    functions: &[quarz_ir::Function],
    f: &quarz_ir::Function,
    g: FuncId,
    bound: &SelfBound,
) -> SelfBound {
    let block = functions
        .get(g as usize)
        .is_some_and(|g| matches!(g.kind, quarz_ir::FuncKind::Block));
    if block && !f.inlined.iter().any(|o| o.callee == g) {
        bound.clone()
    } else {
        None
    }
}

/// The methods synthesized method `m` runs: a data type's `with`, the
/// type's `initialize`s (the one taking the fields builds the copy,
/// `Interp`'s `RtSynth::DataWith`); none for another.
fn synth_calls(world: &RtWorld, m: MethodId) -> &[MethodId] {
    let rm = &world.methods[m as usize];
    match rm.synth {
        quarz_ir::RtSynth::DataWith => world.classes[rm.owner as usize]
            .methods
            .get("initialize")
            .map(|v| v.as_slice())
            .unwrap_or(&[]),
        _ => &[],
    }
}

/// The names native `m` may call by name on the values it is given
/// (`shake::native_calls`): none for a method that is no native.
fn native_calls(world: &RtWorld, m: MethodId) -> &'static [&'static str] {
    match world.methods[m as usize].native_key.as_deref() {
        Some(key) => shake::native_calls(key),
        None => &[],
    }
}

/// `overrides_of`'s answers, kept across a check's rounds (#1057): the
/// runner's walks ask for the same calls' overrides round after round,
/// and the answer changes only when what it reads does. It reads the
/// methods of `m`'s name (their owners, sides and abstractness, fixed
/// for a method, and the override table's pairings among them), the
/// run-time class graph, and the extensions (`may_receive`). So `sync`,
/// the one point that drops answers, called before each walk, drops:
/// - those for a name a method added since has (a generated method, a
///   field's reader or writer, a REPL input's method): only they can
///   change, since overriding is by name;
/// - all of them when the number of classes or extensions changed (a
///   REPL input, a later unit): within a check's static phase the class
///   graph does not change (#802's P1), and a statement cannot add a
///   class, an include or an extension.
///
/// A field a statement generates (a layout change), a class's being
/// abstract or not, and conformance rows are not read. A debug build
/// (or `QUARZ_VERIFY_STATIC_TABLES`) recomputes every kept answer it
/// hands out and compares (`overrides`).
#[derive(Default)]
struct OverridesKept {
    state: RefCell<OverridesState>,
}

#[derive(Default)]
struct OverridesState {
    /// What the answers were made for: the numbers of methods, classes
    /// and extensions of the world at the last `sync`.
    seen: (usize, usize, usize),
    answers: rustc_hash::FxHashMap<(MethodId, SelfBound), Rc<[MethodId]>>,
    /// The methods by name (`methods_by_name`), extended with those added
    /// since: a method is appended, never renamed or removed, within a
    /// check (#1057 PR 3).
    by_name: Rc<MethodsByName>,
}

impl OverridesKept {
    /// Drop the answers that `world` may answer otherwise than the world
    /// they were made in (see the type's comment).
    fn sync(&self, world: &RtWorld) {
        let mut st = self.state.borrow_mut();
        let now = (
            world.methods.len(),
            world.classes.len(),
            world.extensions.len(),
        );
        if now == st.seen {
            return;
        }
        if now.0 < st.seen.0 {
            st.by_name = Rc::new(methods_by_name(world));
        } else {
            let from = st.seen.0;
            add_by_name(Rc::make_mut(&mut st.by_name), world, from);
        }
        if cfg!(debug_assertions) || quarz_lower::verify_static_tables() {
            assert!(
                *st.by_name == methods_by_name(world),
                "internal error: the kept methods by name differ from those of the world (#1057)"
            );
        }
        if now.1 != st.seen.1 || now.2 != st.seen.2 || now.0 < st.seen.0 {
            st.answers.clear();
        } else {
            let names: rustc_hash::FxHashSet<&str> = world.methods[st.seen.0..]
                .iter()
                .map(|m| m.name.as_str())
                .collect();
            st.answers
                .retain(|(m, _), _| !names.contains(world.methods[*m as usize].name.as_str()));
        }
        st.seen = now;
    }

    /// The methods by name of the world last synced.
    fn by_name(&self) -> Rc<MethodsByName> {
        self.state.borrow().by_name.clone()
    }

    /// `overrides_of(world, by_name, m, bound)`, kept.
    fn overrides(
        &self,
        world: &RtWorld,
        by_name: &MethodsByName,
        m: MethodId,
        bound: &SelfBound,
    ) -> Rc<[MethodId]> {
        let key = (m, bound.clone());
        let hit = self.state.borrow().answers.get(&key).cloned();
        match hit {
            Some(kept) => {
                if cfg!(debug_assertions) || quarz_lower::verify_static_tables() {
                    let fresh = overrides_of(world, by_name, m, bound.as_deref());
                    assert!(
                        *kept == *fresh,
                        "internal error: the kept overrides of `{}` (self bound {:?}) differ from those computed afresh: {:?}, {:?} (#1057)",
                        method_name(world, m),
                        bound,
                        kept,
                        fresh
                    );
                }
                kept
            }
            None => {
                let fresh: Rc<[MethodId]> =
                    Rc::from(overrides_of(world, by_name, m, bound.as_deref()));
                self.state.borrow_mut().answers.insert(key, fresh.clone());
                fresh
            }
        }
    }
}

/// The methods that override `m` in subclasses of its owner (same name,
/// same side), which a call of `m` may run instead: with `bound`, on a
/// receiver of one of those classes or a subclass (`may_receive`).
fn overrides_of(
    world: &RtWorld,
    by_name: &MethodsByName,
    m: MethodId,
    bound: Option<&[ClassId]>,
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
                    o != m
                        && !denied_owner(world, o)
                        && quarz_ir::may_dispatch_to(world, o, m)
                        && bound.is_none_or(|b| may_receive(world, o, b))
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Whether a receiver that is an instance of one of `classes` or of a
/// subclass may find `o` by its lookup (`may_receive` in the lowering,
/// alike): `o` belongs to an ancestor of such a class, or to a module
/// an extension makes some class conform to (which the ancestors do not
/// show).
fn may_receive(world: &RtWorld, o: MethodId, classes: &[ClassId]) -> bool {
    let owner = world.methods[o as usize].owner;
    if world.classes[owner as usize].kind == RtClassKind::Module
        && world
            .extensions
            .iter()
            .any(|e| e.includes.iter().any(|&m| world.class_is_a(m, owner)))
    {
        return true;
    }
    let n = world.classes.len() as ClassId;
    classes.iter().any(|&c| {
        world.class_is_a(c, owner)
            || (0..n).any(|d| world.class_is_a(d, c) && world.class_is_a(d, owner))
    })
}

/// What a call of `m` on a class object of one of `classes`, of a
/// subclass of one, or of a class including one (a module), may run
/// instead of `m`: the targets of `RtWorld::class_override_rows` for
/// those class objects (`m` itself where nothing replaces it, without a
/// row). `Object`'s class object stands for every class object.
fn class_side_targets(world: &RtWorld, m: MethodId, classes: &[ClassId]) -> Vec<MethodId> {
    let object = world.builtin.object;
    let mut out: Vec<MethodId> = world
        .class_override_rows
        .iter()
        .filter(|&&(k, b, t)| {
            b == m
                && t != m
                && classes
                    .iter()
                    .any(|&c| c == object || k == c || world.class_is_a(k, c))
        })
        .map(|&(_, _, t)| t)
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// Whether `m` belongs to a class denied at compile time: a receiver of
/// it comes only from a denied native, or from a constant whose
/// initializer is one (`STDOUT`), which the walk follows; so a call by
/// name (`==`, `to_s`) cannot reach it otherwise.
fn denied_owner(world: &RtWorld, m: MethodId) -> bool {
    let owner = &world.classes[world.methods[m as usize].owner as usize];
    compile_time_denied_class(&owner.name)
}

fn method_name(world: &RtWorld, m: MethodId) -> String {
    let rm = &world.methods[m as usize];
    let sep = if rm.singleton { "." } else { "#" };
    format!("{}{sep}{}", world.classes[rm.owner as usize].name, rm.name)
}

/// The methods of each name, in id order (`methods_by_name`, or kept
/// across rounds by `OverridesKept::sync`).
type MethodsByName = rustc_hash::FxHashMap<String, Vec<MethodId>>;

fn methods_by_name(world: &RtWorld) -> MethodsByName {
    let mut out = MethodsByName::default();
    add_by_name(&mut out, world, 0);
    out
}

/// The methods of `world` from `from` on, into `out` by name.
fn add_by_name(out: &mut MethodsByName, world: &RtWorld, from: usize) {
    for (i, m) in world.methods.iter().enumerate().skip(from) {
        match out.get_mut(m.name.as_str()) {
            Some(ids) => ids.push(i as MethodId),
            None => {
                out.insert(m.name.clone(), vec![i as MethodId]);
            }
        }
    }
}

impl Runner {
    /// A statement's or a `static(...)`'s call (docs/14 §2, §8), lowered,
    /// checked for what it reaches, and run: its value, what it asked to
    /// generate, and the interpreter it ran on.
    fn execute(
        &mut self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        callee: MethodId,
        as_statement: bool,
    ) -> Result<(Value, Vec<Pending>, std::rc::Rc<Interp>), StaticFailure> {
        if !self.prepared {
            host.prepare();
            self.prepared = true;
        }
        let errors_before = host.error_count();
        let fid = self.lower(host, stmt, callee);
        // (How the messages name the call, quoted: an `inherited` hook's
        // statement is written nowhere, so its name the hook and the class
        // it ran for, "`Base.inherited`, run for `Post`, raised ...", #421.)
        let callee_name = match stmt.hook {
            Some(h) => {
                let world = host.world();
                format!(
                    "`{}.inherited`, run for `{}`,",
                    world.class(world.method(h).owner).name,
                    world.class(stmt.class).name
                )
            }
            None => format!("`{}`", host.world().method(callee).name),
        };
        if self.net_refused {
            return Err(StaticFailure {
                message: format!(
                    "{callee_name} did not run: the program's conformances make a row the run could reach that the safety net refuses (reported above)"
                ),
                notes: Vec::new(),
            });
        }
        // Code that failed its check does not run (docs/05 §3): neither a
        // statement reaching a method or constant with errors, nor one
        // whose lowering found errors elsewhere (a field default).
        // The blocks given to `def_method` and its kin become method bodies
        // the statement does not run: not in its reach (docs/14 §5).
        let lifted = &self.lowerer.lifted_funcs;
        if let Some(bad) = self.bad_reach(fid, lifted) {
            let message = match bad {
                Ok(BadReach {
                    method,
                    by_name: None,
                    ..
                }) => format!(
                    "{callee_name} did not run: {}",
                    self.describe_bad(host, method, "it may reach", "")
                ),
                Ok(BadReach {
                    by_name: Some(b),
                    reached_bad,
                    pulled,
                    ..
                }) => self.by_name_message(host, &callee_name, &b, reached_bad, pulled),
                Err(c) => format!(
                    "{callee_name} did not run: it reaches `{c}`, which has errors (reported above)"
                ),
            };
            return Err(StaticFailure {
                message,
                notes: Vec::new(),
            });
        }
        if host.error_count() > errors_before {
            return Err(StaticFailure {
                message: self.blocked_message(host, &callee_name, errors_before),
                notes: Vec::new(),
            });
        }
        if let Some(path) = self.impure_reach(fid, lifted) {
            let last = path.last().cloned().unwrap_or_default();
            // The path starts at the callee itself.
            let via = if path.len() > 2 {
                format!(" (via {})", path[1..path.len() - 1].join(", "))
            } else {
                String::new()
            };
            return Err(StaticFailure {
                message: format!(
                    "{callee_name} reaches `{last}`{via}, which cannot run at compile time"
                ),
                notes: Vec::new(),
            });
        }
        let context = EndContext {
            stmt: as_statement.then(|| (stmt.clone(), callee)),
            hook_of: None,
        };
        let mut reflect = self
            .snapshot(host.world())
            .with_ends(&*host, self.ends.clone(), context);
        self.note_pending(host, &mut reflect);
        let reflect = Rc::new(reflect);
        let interp = self.interp(&reflect);
        let result = interp.run_static(fid, Value::Class(stmt.class), stmt.file);
        self.finish(&interp, &reflect, result, &callee_name)
    }

    /// The classes whose statements are still to run, as a message names
    /// them, for `reflect_refusal` (docs/14 §8).
    fn note_pending(&mut self, host: &dyn StaticHost, reflect: &mut WorldReflect) {
        let view = self.cover(host).view(host.world());
        reflect.pending = view;
    }

    /// An interpreter for a compile-time run, on the shared state, with
    /// `reflect` and the time limit.
    fn interp(&self, reflect: &Rc<WorldReflect>) -> std::rc::Rc<Interp> {
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
        // (A compilation does not depend on the machine's zone.)
        interp.local_utc.set(true);
        interp
    }

    /// A compile-time run's outcome (`what` names what ran): its value and
    /// what it asked to generate, or the failure.
    fn finish(
        &self,
        interp: &std::rc::Rc<Interp>,
        reflect: &Rc<WorldReflect>,
        result: Result<Value, StaticEnd>,
        what: &str,
    ) -> Result<(Value, Vec<Pending>, std::rc::Rc<Interp>), StaticFailure> {
        let interp = interp.clone();
        // A refused reflection fails the run, though the code rescued it.
        if let Some(why) = reflect.refused.borrow_mut().take() {
            return Err(StaticFailure {
                message: why,
                notes: Vec::new(),
            });
        }
        // So does a construction the check refused: the code it would run
        // is not the program's (#870).
        if let Some(why) = reflect.refused_construction.borrow_mut().take() {
            return Err(StaticFailure {
                message: format!("{what} did not run: {why}"),
                notes: Vec::new(),
            });
        }
        match result {
            Ok(value) => {
                let pending = std::mem::take(&mut *reflect.generated.borrow_mut());
                Ok((value, pending, interp))
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
                    message: format!("{what} raised {class}: {message}"),
                    notes,
                })
            }
            Err(StaticEnd::Exited(code)) => Err(StaticFailure {
                message: format!("{what} exited with status {code} at compile time"),
                notes: Vec::new(),
            }),
        }
    }
}

impl Runner {
    /// The class-end hooks `hooks` of `last`'s class, run in order, each
    /// generating as the statement that registered it.
    fn run_hooks(
        &mut self,
        host: &mut dyn StaticHost,
        last: &StaticStmt,
        hooks: &[Hook],
    ) -> Result<(), (StaticStmt, StaticFailure)> {
        for hook in hooks {
            self.run_hook(host, last, hook)
                .map_err(|f| (hook.stmt.clone(), f))?;
        }
        Ok(())
    }

    /// One class-end hook, reported (by `run_hooks`) at the statement that
    /// registered it.
    fn run_hook(
        &mut self,
        host: &mut dyn StaticHost,
        last: &StaticStmt,
        hook: &Hook,
    ) -> Result<(), StaticFailure> {
        // The world as the statements left it: the hook's statement
        // lowered again (what it generates is in the class now).
        let _ = self.lower(host, &hook.stmt, hook.callee);
        let callee_name = host.world().method(hook.callee).name.clone();
        if self.net_refused {
            return Err(StaticFailure {
                message: format!(
                    "the class-end hook `:{}` did not run: the program's conformances make a row the run could reach that the safety net refuses (reported above)",
                    hook.key
                ),
                notes: Vec::new(),
            });
        }
        let context = EndContext {
            stmt: None,
            hook_of: Some(last.class),
        };
        let mut reflect = self
            .snapshot(host.world())
            .with_ends(&*host, self.ends.clone(), context);
        self.note_pending(host, &mut reflect);
        let reflect = Rc::new(reflect);
        let interp = self.interp(&reflect);
        let result = interp.run_static_block(hook.block.clone(), vec![Value::Class(last.class)]);
        let what = format!(
            "the class-end hook `:{}` (registered by `{callee_name}`)",
            hook.key
        );
        let (_, pending, interp) = self.finish(&interp, &reflect, result, &what)?;
        drop(interp);
        // Generated as by the statement that registered it (its
        // location, its call's type arguments).
        self.generate(host, &hook.stmt, pending)
            .map_err(|f| StaticFailure {
                message: format!("{what}: {}", f.message),
                notes: f.notes,
            })?;
        Ok(())
    }
}

impl StaticRunner for Runner {
    fn begin(&mut self) {
        self.cover = None;
    }
    fn run(
        &mut self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        callee: MethodId,
    ) -> Result<(), StaticFailure> {
        let (_, pending, interp) = self.execute(host, stmt, callee, true)?;
        drop(interp);
        self.generate(host, stmt, pending)
    }

    fn class_end(
        &mut self,
        host: &mut dyn StaticHost,
        last: &StaticStmt,
    ) -> Result<(), (StaticStmt, StaticFailure)> {
        let hooks = match self.ends.borrow_mut().classes.get_mut(&last.class) {
            Some(end) => std::mem::take(&mut end.hooks),
            None => return Ok(()),
        };
        let result = self.run_hooks(host, last, &hooks);
        // The statement values go with the class's end: nothing of them is
        // in the program but what the hooks generated.
        self.ends.borrow_mut().classes.remove(&last.class);
        result
    }

    fn eval(
        &mut self,
        host: &mut dyn StaticHost,
        stmt: &StaticStmt,
        callee: MethodId,
    ) -> Result<Baked, StaticFailure> {
        let (value, pending, interp) = self.execute(host, stmt, callee, false)?;
        let fail = |message: String| StaticFailure {
            message,
            notes: Vec::new(),
        };
        // (A handle made by name generates nothing.)
        if pending.iter().any(|p| !matches!(p, Pending::Handle(_))) {
            return Err(fail(
                "`static(...)` gives a value: what it calls cannot generate members (`def_method`, `def_field`)".to_string(),
            ));
        }
        // The handles it made are checked as a statement's are.
        let mut classes = Vec::new();
        self.generate_each(host, stmt, pending, &mut classes)?;
        bake(&interp, &unshareable_data(host.world()), &value).map_err(|why| {
            fail(format!(
                "`static(...)` gives a value that cannot be baked into the program: {why}"
            ))
        })
    }

    fn reset(&mut self) {
        let files = Rc::unwrap_or_clone(std::mem::take(&mut self.files));
        *self = match self.seed.take() {
            Some(seed) => Runner::seeded(files, seed),
            None => Runner::new(files),
        };
    }

    fn add_file(&mut self, index: u32, file: SourceFile) {
        let i = index as usize;
        // (Copied only while the lowerer still holds the last round's.)
        let files = Rc::make_mut(&mut self.files);
        if files.len() <= i {
            files.resize(i + 1, SourceFile::new("", ""));
        }
        files[i] = file;
    }

    fn later_unit(&mut self, world: &World, after: bool) -> Option<LayoutChange> {
        let now = quarz_lower::layout::compute(world);
        if !after {
            self.later_before = Some(now);
            return None;
        }
        let before = self.later_before.take()?;
        let (class, index) = quarz_lower::layout::explained_change(&before, &now, |d| {
            world.compared_by(d, &[]).is_some()
        })?;
        let ivar = before[class as usize].ivars.get(index);
        Some(LayoutChange {
            holder: class,
            field: ivar.map(|v| v.name.clone()).unwrap_or_default(),
            data: ivar.and_then(|v| v.flat),
        })
    }
}

/// The declarations, as the reflection natives read them: taken when a
/// statement runs, with what the statements run before it generated (its
/// class's ancestors' among them, docs/14 §2).
struct WorldReflect {
    fields: HashMap<ClassId, Vec<Rc<[ReflectField]>>>,
    methods: HashMap<ClassId, Vec<Rc<[ReflectMethod]>>>,
    /// The signatures `new` takes (`World::constructors`, #1045).
    constructors: HashMap<ClassId, Vec<Rc<[ReflectMethod]>>>,
    /// What the statement's run asked to generate, in call order.
    generated: RefCell<Vec<Pending>>,
    /// The `doc` given, for the next generation.
    doc: RefCell<Option<String>>,
    /// The statements still to run, with the classes each covers (its
    /// class and those under it), as a message names them.
    pending: PendingView,
    /// How many `static(...)` runs inside this compile-time run are under
    /// way (docs/14 §8).
    in_static: std::cell::Cell<u32>,
    /// The first refusal (`reflect_refusal`), which fails the statement
    /// whatever its run rescued.
    refused: RefCell<Option<String>>,
    /// The constructions the check refused (`StaticHost::
    /// refused_constructors`), and the first one the run met, which
    /// fails the statement as `refused` does: it did not run (#870).
    refused_inits: Vec<(ClassId, Option<MethodId>, String)>,
    refused_construction: RefCell<Option<String>>,
    /// The `data` types and enums with a field that is not Shareable,
    /// whose values cannot be baked (`bake`).
    unshareable: rustc_hash::FxHashMap<ClassId, String>,
    /// The statement values and hooks kept across runs (`Runner::ends`).
    ends: Rc<RefCell<ClassEnds>>,
    /// Where this run is.
    context: EndContext,
    /// The `statement_values[U]` calls: their nodes and `U`, as the
    /// checker names it.
    site_types: HashMap<i64, String>,
}

/// A generation a statement's run asked for, in call order.
enum Pending {
    Method(PendingGen),
    Field(PendingField),
    /// A handle made by name (`field_ref`, `method_ref`), checked as a
    /// captured one is.
    Handle(Baked),
}

/// Why generating method `name` into `class` is refused, if it is: it
/// would change how a field of a class laid out with `before` holds a
/// `data` type (#796 (C), docs/14 §5), the field the error names being
/// the one whose type would get the method
/// (`quarz_lower::layout::explained_change`).
fn layout_refusal(
    world: &World,
    before: &[quarz_lower::layout::Layout],
    class: ClassId,
    name: &str,
) -> Option<String> {
    let added = [(class, name)];
    let after = quarz_lower::layout::compute_with(world, &added);
    let (holder, index) = quarz_lower::layout::explained_change(before, &after, |d| {
        world.compared_by(d, &added).is_some()
    })?;
    let ivar = &before[holder as usize].ivars.get(index)?;
    let declarer = world.class(world.field_declarer(holder, &ivar.name));
    let target = &world.class(class).name;
    Some(match ivar.flat {
        Some(d) if d == class => format!(
            "`{target}` is stored in place in the field `@{}` of `{}`, and a type stored in place compares by its fields: a `static` statement cannot give it `==`, `!=` or `hash` (write the method in `{target}`'s body)",
            ivar.name, declarer.name
        ),
        Some(d) => {
            let d = &world.class(d).name;
            format!(
                "`{d}`, which gets the methods of `{target}`, is stored in place in the field `@{}` of `{}`, and a type stored in place compares by its fields: a `static` statement cannot give it `==`, `!=` or `hash` through `{target}` (write the method in `{target}`'s body)",
                ivar.name, declarer.name
            )
        }
        None => format!(
            "internal error: the generation would change how the field `@{}` of `{}` is laid out; please report",
            ivar.name, declarer.name
        ),
    })
}

/// A keyword of `keywords:`: name, class, required, nullable, and the
/// type in full when given one (`Meta::Keyword#type_ref`).
type KeywordSpec = (String, ClassId, bool, bool, Option<ReflectType>);

/// Where a generated method's block is written (`Generated::written_at`):
/// the class or module of the method whose body holds it, as the lowering
/// recorded when it lifted the block (`Lowerer::block_calls`; `None` at
/// a file's top level), its lowered function's file, and the block's
/// position.
fn written_at(
    world: &World,
    done: &[quarz_ir::Function],
    func: FuncId,
    block: Span,
    method: Option<MethodId>,
) -> Option<(Option<ClassId>, u32, u32)> {
    let file = done.get(func as usize)?.file;
    Some((method.map(|m| world.method(m).owner), file, block.start))
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
    nullable: bool,
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
    /// `keywords:`.
    keywords: Option<Vec<KeywordSpec>>,
    /// `def_initialize` (docs/14 §5).
    initialize: bool,
    /// The classes the calling method's carried type parameters stand
    /// for (`Lowerer::carried_type_params`).
    type_args: Vec<ClassId>,
    /// `override: true` (docs/14 §5).
    override_: bool,
    /// `def_field`'s block: the initializer of that field (#890).
    initializes: Option<String>,
}

/// Why `class` cannot take an initializer of its field `@field` whose
/// block gives `ret` (#890, docs/14 §5), if it cannot: the field's type
/// must take the block's result, and every `initialize` of the class must
/// be generated and come after its initializers (each runs them at its
/// end, in declaration order: one generated before would not, and a
/// written one never does).
fn field_initializer_refusal(
    world: &World,
    class: ClassId,
    field: &str,
    ret: &Type,
) -> Result<(), String> {
    let cname = &world.class(class).name;
    if let Some(f) = world.class(class).fields.iter().find(|f| f.name == field) {
        if !world.is_subtype(ret, &f.ty) {
            return Err(format!(
                "the block gives {}, but `@{field}` is {}",
                world.type_name(ret),
                world.type_name(&f.ty)
            ));
        }
    }
    let inits = world.class(class).methods.get("initialize");
    let inits = inits.map(|ms| ms.as_slice()).unwrap_or_default();
    if inits.iter().any(|&m| world.method(m).generated.is_none()) {
        return Err(format!(
            "`{cname}` has a written `initialize`, which does not run initializers: a class with field initializers has only generated `initialize`s (`def_initialize`)"
        ));
    }
    if !inits.is_empty() {
        return Err(format!(
            "`{cname}` already has a generated `initialize`, which would not run the initializer: declare the fields with initializers before `def_initialize`"
        ));
    }
    Ok(())
}

/// A compile-time value as a generated method embeds it (docs/14 §5),
/// or why it cannot.
/// The `data` types and enums of `world` that are not Shareable (a field
/// that is not): their values cannot be baked, so that every baked value
/// is Shareable (docs/14 §5).
fn unshareable_data(world: &World) -> rustc_hash::FxHashMap<ClassId, String> {
    (0..world.classes.len() as ClassId)
        .filter_map(|c| unshareable_of(world, c).map(|why| (c, why)))
        .collect()
}

/// Class `id`'s entry of `unshareable_data`: why its values cannot be
/// baked, for a `data` type or enum with a field that is not Shareable.
fn unshareable_of(world: &World, id: ClassId) -> Option<String> {
    use quarz_types::ClassKind;
    Some(id)
        .map(|id| world.class(id))
        .filter(|c| {
            matches!(
                c.kind,
                ClassKind::Data | ClassKind::Enum | ClassKind::Variant
            ) && c.shareable != Some(true)
        })
        .map(|c| {
            // The field that is not Shareable (its type parameters, which
            // the arguments decide, erased), as the checker names it.
            let enum_params = c.variant_of.map(|e| world.class(e).type_params.clone());
            let erase: HashMap<TypeParamId, Type> = c
                .type_params
                .iter()
                .chain(enum_params.iter().flatten())
                .map(|p| (p.id, Type::Nothing))
                .collect();
            let erase: rustc_hash::FxHashMap<TypeParamId, Type> = erase.into_iter().collect();
            let field = world.all_fields(c.id).into_iter().find_map(|(f, subst)| {
                let ty = f.ty.subst(&subst).subst(&erase);
                (!shareable_as_declared(world, &ty))
                    .then(|| format!("`@{}: {}`", f.name, world.type_name(&ty)))
            });
            let why = match field {
                Some(f) => format!(
                    "`{}` holds {f}, which is not Shareable, so its values cannot be baked",
                    c.name
                ),
                None => format!(
                    "`{}` is not Shareable, so its values cannot be baked",
                    c.name
                ),
            };
            why
        })
}

/// `World::is_shareable` for a declared program, without its memo
/// (which needs the world mutable): a `data` type's or enum's answer as
/// declared (`ensure_shareable_known`), a class's or module's promise
/// (one that breaks it is an error where it is declared), a `shareable`
/// procedure, and collections by their arguments.
fn shareable_as_declared(world: &World, t: &Type) -> bool {
    use quarz_types::ClassKind;
    match t {
        Type::Nothing | Type::Void | Type::Var(_) => true,
        Type::ClassObject(..) | Type::TypeOf(_) => true,
        Type::Union(ms) | Type::Tuple(ms) => ms.iter().all(|m| shareable_as_declared(world, m)),
        Type::Proc(_, _, _, shareable, _) => *shareable,
        Type::Param(_) => false,
        Type::Class(id, args) => {
            let b = &world.builtin;
            if *id == b.meta_field_ref || *id == b.meta_method {
                return true;
            }
            let class = world.class(*id);
            let own = match class.kind {
                ClassKind::Data | ClassKind::Enum | ClassKind::Variant => {
                    class.shareable == Some(true)
                }
                _ => world.shareable_promise(*id).is_some(),
            };
            own && args.iter().all(|a| shareable_as_declared(world, a))
        }
    }
}

fn bake(
    interp: &Interp,
    unshareable: &rustc_hash::FxHashMap<ClassId, String>,
    v: &Value,
) -> Result<Baked, String> {
    let cannot = |interp: &Interp, v: &Value| {
        Err(format!(
            "a value of class `{}` cannot be baked into the program: only immutable values can (literals, classes, `data` of such)",
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
        // Written into the executable, it could never be cleared (#963).
        Value::Secret(_) => {
            return Err(format!(
                "a `{}`: a secret written into the executable could never be wiped",
                interp.class_name(v)
            ))
        }
        Value::Regexp(r) => Baked::Regexp {
            source: r.source.clone(),
            flags: r.flags.clone(),
        },
        Value::Array(a) => Baked::Array(
            a.iter()
                .map(|x| bake(interp, unshareable, &x))
                .collect::<Result<_, _>>()?,
        ),
        Value::Hash(h) => Baked::Hash(
            h.as_map()
                .iter()
                .map(|(k, v)| Ok((bake(interp, unshareable, k)?, bake(interp, unshareable, v)?)))
                .collect::<Result<_, String>>()?,
        ),
        Value::Range(r) => {
            let bound = |b: &Value| -> Result<Option<Box<Baked>>, String> {
                Ok(match b {
                    Value::Nil => None,
                    other => Some(Box::new(bake(interp, unshareable, other)?)),
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
                // A field handle (docs/14 §5): what it names, made again
                // where it is baked (its `get`/`set` lowered in place).
                _ if class.name == "Meta::FieldRef" || class.name == "Meta::Method" => Baked::Data(
                    o.class,
                    o.fields()
                        .iter()
                        .map(|f| bake(interp, unshareable, f))
                        .collect::<Result<_, _>>()?,
                ),
                // (A variant by its own fields, as `is_a?(Shareable)`
                // answers for it.)
                RtClassKind::Data | RtClassKind::Variant if unshareable.contains_key(&o.class) => {
                    return Err(format!(
                        "{} (only literals, classes and `data` of Shareable fields can be)",
                        unshareable[&o.class]
                    ));
                }
                RtClassKind::Data | RtClassKind::Variant => Baked::Data(
                    o.class,
                    o.fields()
                        .iter()
                        .map(|f| bake(interp, unshareable, f))
                        .collect::<Result<_, _>>()?,
                ),
                _ => return cannot(interp, v),
            }
        }
        _ => return cannot(interp, v),
    })
}

/// The type arguments of a statement's call (docs/14 §5) that hold in
/// every invocation of its `static def`: all of them when no code of the
/// program names it as called (a call, `x.:m`, `&:m`, a compound
/// assignment's reader, a `super` in a method of its name, an alias of
/// it) but statements' own calls; the receiver's (a module's `T`, which
/// `include` fixes) when the only others are calls of it on its own
/// `self` in its own body; none otherwise, the `Type[T]` parameters then
/// carrying what they hold. By name over the whole program, so that the
/// result does not depend on what was checked first (more refusals than
/// following what the run reaches, never fewer). A name the runtime
/// calls everywhere, or an operator's, counts as called.
fn statement_type_args(
    host: &dyn StaticHost,
    stmt: &StaticStmt,
) -> rustc_hash::FxHashMap<TypeParamId, Type> {
    use quarz_types::check::CallTarget;
    let out = host.output();
    let world = host.world();
    let Some(CallTarget::Method { method }) = out.calls.get(&stmt.expr.id) else {
        return Default::default();
    };
    let callee_id = *method;
    let callee = world.method(callee_id);
    let all: rustc_hash::FxHashMap<TypeParamId, Type> = out
        .type_args
        .get(&stmt.expr.id)
        .map(|args| args.iter().cloned().collect())
        .unwrap_or_default();
    if all.is_empty() {
        return all;
    }
    let name = callee.name.as_str();
    let plain = name
        .chars()
        .next()
        .is_some_and(|c| c.is_alphabetic() || c == '_');
    if !plain || quarz_ir::shake::RUNTIME_NAMES.contains(&name) {
        return Default::default();
    }
    // (An alias, or a method that has one: its other names are calls of
    // it the scan by name does not see.)
    if callee.alias_of.is_some()
        || world
            .methods
            .iter()
            .any(|m| m.alias_of.is_some_and(|a| world.method(a).name == name) && m.name != name)
    {
        return Default::default();
    }
    let own: Vec<TypeParamId> = callee.type_params.iter().map(|p| p.id).collect();
    let keep = |kind: Called| match kind {
        Called::No => all.clone(),
        Called::OnSelf => all
            .iter()
            .filter(|(p, _)| !own.contains(p))
            .map(|(p, t)| (*p, t.clone()))
            .collect(),
        Called::Yes(_) => Default::default(),
    };
    keep(called_kind(host, callee_id))
}

/// `called_by_name`, once per callee and program: what it reads only
/// grows with declarations, which the key counts.
fn called_kind(host: &dyn StaticHost, callee_id: MethodId) -> Called {
    let world = host.world();
    let key = (
        callee_id,
        world.methods.len(),
        world.static_stmts.len(),
        world.consts.len(),
        world.classes.len(),
    );
    if let Some(kind) = CALLED.with(|c| c.borrow().get(&key).copied()) {
        return kind;
    }
    let kind = called_by_name(host, callee_id);
    CALLED.with(|c| c.borrow_mut().insert(key, kind));
    kind
}

/// Whether the program names a `static def` as called (`statement_type_args`).
#[derive(Clone, Copy)]
enum Called {
    No,
    OnSelf,
    /// With where one such call is (its file and span), when it is one.
    Yes(Option<(u32, Span)>),
}

type CalledKey = (MethodId, usize, usize, usize, usize);

thread_local! {
    static CALLED: std::cell::RefCell<rustc_hash::FxHashMap<CalledKey, Called>> =
        Default::default();
}

fn called_by_name(host: &dyn StaticHost, callee_id: MethodId) -> Called {
    let out = host.output();
    let world = host.world();
    let callee = world.method(callee_id);
    let name = callee.name.as_str();
    let tops: rustc_hash::FxHashSet<quarz_syntax::ast::NodeId> =
        world.static_stmts.iter().map(|s| s.expr.id).collect();
    let mut on_self = false;
    // Whether `exprs` name it otherwise than allowed (`own`: the callee's
    // own body, where a call on `self` is allowed).
    // (`Some`: where, the call's span or, for a `super`, none.)
    let mut named = |exprs: &[quarz_syntax::ast::Expr],
                     extra: &[&quarz_syntax::ast::Expr],
                     own: bool,
                     method_name: Option<&str>|
     -> Option<Option<Span>> {
        let (sites, supers) = quarz_lower::call_sites(exprs, extra, out, world);
        if supers && method_name == Some(name) && !own {
            return Some(None);
        }
        for (id, span, self_call, n) in sites {
            if n != name || tops.contains(&id) {
                continue;
            }
            if own && self_call {
                on_self = true;
            } else {
                return Some(Some(span));
            }
        }
        None
    };
    let at = |file: u32, span: Option<Span>| Called::Yes(span.map(|s| (file, s)));
    for m in &world.methods {
        let Some(def) = m.body.clone() else {
            continue;
        };
        let body: &[quarz_syntax::ast::Expr] = def.body.as_deref().unwrap_or(&[]);
        let defaults: Vec<&quarz_syntax::ast::Expr> = def
            .params
            .list
            .iter()
            .filter_map(|p| p.default.as_ref())
            .collect();
        if let Some(span) = named(body, &defaults, m.id == callee_id, Some(m.name.as_str())) {
            return at(m.file, span);
        }
    }
    for st in &world.static_stmts {
        if let Some(span) = named(std::slice::from_ref(&*st.expr), &[], false, None) {
            return at(st.file, span);
        }
    }
    for c in &world.consts {
        if let Some(v) = &c.value {
            if named(std::slice::from_ref(&**v), &[], false, None).is_some() {
                return Called::Yes(None);
            }
        }
    }
    for k in &world.classes {
        for f in &k.fields {
            if let Some(v) = &f.default {
                if named(std::slice::from_ref(&**v), &[], false, None).is_some() {
                    return Called::Yes(None);
                }
            }
        }
    }
    if on_self {
        Called::OnSelf
    } else {
        Called::No
    }
}

/// Whether generated method `mid` overrides an inherited method of its
/// name (docs/01 §3: it takes every call of one, and its result is the
/// other's or narrower), as `override: true` asks; else why not, naming
/// the inherited signatures and what does not fit.
fn generated_override(world: &World, mid: MethodId) -> Result<(), String> {
    let m = world.method(mid);
    // (The ancestry the override table takes, `World::own_ancestors`: the
    // modules extensions include too, whose methods the class's own
    // override, checked, docs/01 §7.)
    let ancs = world.own_ancestors(m.owner);
    // (The override table, `World::overrides`, #536.)
    let mut overridden = world.overrides(mid);
    let side = if m.singleton { "." } else { "#" };
    // The inherited methods of the name, with their ancestors' arguments.
    let mut inherited: Vec<(MethodId, rustc_hash::FxHashMap<TypeParamId, Type>)> = Vec::new();
    for (anc, args) in &ancs {
        if *anc == m.owner {
            continue;
        }
        let ac = world.class(*anc);
        let table = if m.singleton {
            &ac.singleton_methods
        } else {
            &ac.methods
        };
        for &o in table.get(&m.name).into_iter().flatten() {
            let subst = ac
                .type_params
                .iter()
                .map(|tp| tp.id)
                .zip(args.iter().cloned())
                .collect();
            inherited.push((o, subst));
        }
    }
    // (Of the table's entries, the inherited methods of the name above:
    // not an extension's method, which takes no part in dispatch, nor a
    // class object's `Type` method, which `override:` does not name.)
    overridden.retain(|o| inherited.iter().any(|(i, _)| i == o));
    // A class method: the class methods of the modules the class or an
    // ancestor includes (among the inherited ones above) are overridden
    // when it takes their every call and returns what their callers take
    // (the table's class-method entries are the class object's, not
    // these).
    if m.singleton {
        let no_subst = rustc_hash::FxHashMap::default();
        for (mc, mcargs) in &ancs {
            let mcc = world.class(*mc);
            if mcc.kind != quarz_types::ClassKind::Module {
                continue;
            }
            for &o in mcc.singleton_methods.get(&m.name).into_iter().flatten() {
                let om = world.method(o);
                if om.owner != *mc {
                    continue;
                }
                let subst: rustc_hash::FxHashMap<TypeParamId, Type> = mcc
                    .type_params
                    .iter()
                    .map(|tp| tp.id)
                    .zip(mcargs.iter().cloned())
                    .collect();
                if world.takes_calls_of(m, &no_subst, om, &subst) && !overridden.contains(&o) {
                    overridden.push(o);
                }
            }
        }
    }
    let shown = |o: MethodId| {
        let om = world.method(o);
        let mut params: Vec<String> = Vec::new();
        let mut star = false;
        for p in &om.params {
            let default = if p.default.is_some() { " = ..." } else { "" };
            // (`*xs: T` held as `Array[T]`, `**opts: T` as `Hash[Symbol, T]`.)
            let elem = |i: usize| match &p.ty {
                Type::Class(_, args) if args.len() > i => world.type_name(&args[i]),
                t => world.type_name(t),
            };
            match p.kind {
                ParamKind::Rest => {
                    star = true;
                    params.push(format!("*{}: {}", p.name, elem(0)));
                }
                ParamKind::KeywordRest => params.push(format!("**{}: {}", p.name, elem(1))),
                ParamKind::KeywordOnly => {
                    if !star {
                        params.push("*".to_string());
                        star = true;
                    }
                    params.push(format!("{}: {}{default}", p.name, world.type_name(&p.ty)));
                }
                _ => params.push(format!("{}: {}{default}", p.name, world.type_name(&p.ty))),
            }
        }
        if let Some((name, t)) = &om.block {
            let name = if name == "&" { "" } else { name.as_str() };
            params.push(format!("&{name}: {}", world.type_name(t)));
        }
        format!(
            "`{}{side}{}({}) -> {}`",
            world.class(om.owner).name,
            om.name,
            params.join(", "),
            world.type_name(&om.ret)
        )
    };
    if inherited.is_empty() {
        return Err(format!(
            "`override: true`, but `{}` inherits no method `{}` to override",
            world.class(m.owner).name,
            m.name
        ));
    }
    if overridden.is_empty() {
        let reasons: Vec<String> = inherited
            .iter()
            .map(|(o, subst)| {
                format!(
                    "{}: {}",
                    shown(*o),
                    override_misfit(world, m, world.method(*o), subst)
                )
            })
            .collect();
        return Err(format!(
            "`override: true`, but `{}{side}{}` overrides no inherited method of its name, which would be overloaded instead: {}",
            world.class(m.owner).name,
            m.name,
            reasons.join("; ")
        ));
    }
    // (Its result must be one the callers of the overridden take.)
    for o in overridden {
        let om = world.method(o);
        let subst = inherited
            .iter()
            .find(|(i, _)| *i == o)
            .map(|(_, s)| s.clone())
            .unwrap_or_default();
        let theirs = om.ret.subst(&subst);
        if om.ret.mentions_param(SELF_PARAM) {
            return Err(format!(
                "`override: true`, but {} returns `Self`, which a generated method cannot override (docs/14 §5): its result is a class, not each subclass's own",
                shown(o)
            ));
        }
        if !(m.ret == theirs || world.is_subtype(&m.ret, &theirs)) {
            return Err(format!(
                "`override: true`, but its result {} is not a {}, the result of {}",
                world.type_name(&m.ret),
                world.type_name(&theirs),
                shown(o)
            ));
        }
    }
    Ok(())
}

/// What keeps `m` from taking every call of `o` (`World::takes_calls_of`).
fn override_misfit(
    world: &World,
    m: &quarz_types::MethodInfo,
    o: &quarz_types::MethodInfo,
    osubst: &rustc_hash::FxHashMap<TypeParamId, Type>,
) -> String {
    let (ps, qs) = (o.positional_params(), m.positional_params());
    if ps.len() > qs.len() {
        return format!(
            "it takes {} positional parameter(s), not {}",
            qs.len(),
            ps.len()
        );
    }
    for (p, q) in ps.iter().zip(&qs) {
        if p.kind != q.kind {
            let what = |k: ParamKind| {
                if k == ParamKind::Rest {
                    "a rest parameter"
                } else {
                    "a positional parameter"
                }
            };
            return format!(
                "its parameter `{}` is {}, where the inherited one has {}",
                q.name,
                what(q.kind),
                what(p.kind)
            );
        }
        let pt = p.ty.subst(osubst);
        if !(pt == q.ty || world.is_subtype(&pt, &q.ty)) {
            return format!(
                "its parameter `{}` takes {}, not every {}",
                q.name,
                world.type_name(&q.ty),
                world.type_name(&pt)
            );
        }
    }
    if let Some(q) = qs[ps.len()..]
        .iter()
        .find(|q| q.default.is_none() && q.kind != ParamKind::Rest)
    {
        return format!("its parameter `{}` has no default", q.name);
    }
    for p in o.params.iter().filter(|p| p.kind == ParamKind::KeywordOnly) {
        match m
            .params
            .iter()
            .find(|q| q.kind == ParamKind::KeywordOnly && q.name == p.name)
        {
            None => return format!("it does not take the keyword `{}`", p.name),
            Some(q) => {
                let pt = p.ty.subst(osubst);
                if !(pt == q.ty || world.is_subtype(&pt, &q.ty)) {
                    return format!(
                        "its keyword `{}` takes {}, not every {}",
                        q.name,
                        world.type_name(&q.ty),
                        world.type_name(&pt)
                    );
                }
                if p.default.is_some() && q.default.is_none() {
                    return format!(
                        "its keyword `{}` is required, optional in the inherited one",
                        q.name
                    );
                }
            }
        }
    }
    if let Some(q) = m.params.iter().find(|q| {
        q.kind == ParamKind::KeywordOnly
            && q.default.is_none()
            && !o
                .params
                .iter()
                .any(|p| p.kind == ParamKind::KeywordOnly && p.name == q.name)
    }) {
        return format!(
            "it requires the keyword `{}`, which the inherited one does not take",
            q.name
        );
    }
    if o.params.iter().any(|p| p.kind == ParamKind::KeywordRest)
        && !m.params.iter().any(|q| q.kind == ParamKind::KeywordRest)
    {
        return "it takes no `**` keywords, which the inherited one takes".to_string();
    }
    match (&o.block, &m.block) {
        (Some(_), None) => "it takes no block".to_string(),
        (None, Some(_)) => "it takes a block".to_string(),
        _ => "its parameters do not take every call of the inherited one".to_string(),
    }
}

/// A type parameter `t` mentions that is not one of `own`.
/// The classes `classes` that the carried type parameters `carried` of
/// a call in a generic method stand for (`Lowerer::carried_type_params`,
/// passed under `quarz_ir::TYPE_ARG_VALUES`), added to `subst` where it
/// does not give them already: a class with type parameters is refused
/// (its arguments are not known here), and each bound must hold of its
/// class (a bound naming a type parameter nothing gives here, a module's
/// own `T` that `include` binds, holds of the class the call was checked
/// with: the class is one; one naming only `own`, `Self` of a generic
/// class, is decided with them as they are). What a generated method's
/// signature (`generate_members`) and a field handle's type
/// (`check_handles`, #918) take. The parameters added.
fn add_carried(
    world: &World,
    carried: &[(TypeParamId, Vec<Type>)],
    classes: &[ClassId],
    subst: &mut rustc_hash::FxHashMap<TypeParamId, Type>,
    own: &[TypeParamId],
) -> Result<Vec<TypeParamId>, String> {
    let mut checked: Vec<(TypeParamId, &Vec<Type>, ClassId)> = Vec::new();
    for ((p, bounds), c) in carried.iter().zip(classes) {
        if subst.contains_key(p) {
            continue;
        }
        let k = world.class(*c);
        if !k.type_params.is_empty() {
            return Err(format!(
                "`{}` is `{}`, whose type arguments are not known here: pass them at the statement's call or use a class without type arguments",
                world.type_name(&Type::Param(*p)),
                k.name
            ));
        }
        subst.insert(*p, Type::Class(*c, Vec::new()));
        checked.push((*p, bounds, *c));
    }
    for (p, bounds, c) in &checked {
        let t = Type::Class(*c, Vec::new());
        if let Some(b) = bounds
            .iter()
            .map(|b| b.subst(subst))
            .filter(|b| free_param(b, own).is_none())
            .find(|b| !world.is_subtype(&t, b))
        {
            return Err(format!(
                "`{}` is `{}` here, which is not a `{}`",
                world.type_name(&Type::Param(*p)),
                world.class(*c).name,
                world.type_name(&b)
            ));
        }
    }
    Ok(checked.into_iter().map(|(p, _, _)| p).collect())
}

fn free_param(t: &Type, own: &[TypeParamId]) -> Option<TypeParamId> {
    match t {
        Type::Param(p) => (!own.contains(p)).then_some(*p),
        Type::Class(_, args) | Type::ClassObject(_, args) => {
            args.iter().find_map(|a| free_param(a, own))
        }
        Type::TypeOf(inner) => free_param(inner, own),
        Type::Union(ms) | Type::Tuple(ms) => ms.iter().find_map(|m| free_param(m, own)),
        Type::Proc(recv, ps, r, _, kws) => recv
            .as_deref()
            .and_then(|r| free_param(r, own))
            .or_else(|| ps.iter().find_map(|p| free_param(p, own)))
            .or_else(|| kws.iter().find_map(|k| free_param(&k.ty, own)))
            .or_else(|| free_param(r, own)),
        Type::Var(_) | Type::Nothing | Type::Void => None,
    }
}

/// Class `id`'s rows of the reflection (`Runner::snapshot`): its
/// fields, inherited first, its public instance methods, and the
/// signatures `new` takes (`World::constructors`).
fn reflect_rows(
    world: &World,
    id: ClassId,
) -> (Vec<ReflectField>, Vec<ReflectMethod>, Vec<ReflectMethod>) {
    let class = world.class(id);
    let fs: Vec<ReflectField> = world
        .all_fields(class.id)
        .into_iter()
        .map(|(f, subst)| ReflectField {
            // (As the class has it: an inherited field's type with the
            // superclasses' type arguments, `World::all_fields`'s map.)
            ty_ref: type_ref_of(world, &f.ty.subst(&subst), class.id),
            name: f.name.clone(),
            ty: erase(world, &f.ty),
            mutable: f.mutable,
            default: f.has_default(),
        })
        .collect();
    // The public instance methods, of the class, its superclasses
    // and the modules they include, the most derived definition of
    // each signature, in declaration order (method ids are given
    // in it). `initialize` is not a method of the instances.
    let mut seen: Vec<(String, Vec<ClassId>)> = Vec::new();
    let mut ms: Vec<(MethodId, ReflectMethod)> = Vec::new();
    for (anc, args) in world.ancestors(class.id, &world.own_args(class.id)) {
        // (An inherited method's types as the class has them.)
        let subst = world.class_subst(anc, &args);
        let mut ids: Vec<MethodId> = world
            .class(anc)
            .methods
            .values()
            .flat_map(|v| v.iter().copied())
            .collect();
        ids.sort_unstable();
        for mid in ids {
            let m = world.method(mid);
            if m.visibility != quarz_syntax::ast::Visibility::Public || m.name == "initialize" {
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
                    params: m
                        .params
                        .iter()
                        .map(|p| reflect_param(world, p, m.block_optional, &subst, class.id))
                        .collect(),
                    ret: erase(world, &m.ret),
                    is_static: m.is_static,
                    ret_ref: type_ref_of(world, &m.ret.subst(&subst), class.id),
                },
            ));
        }
    }
    ms.sort_by_key(|(mid, _)| *mid);
    let ms: Vec<ReflectMethod> = ms.into_iter().map(|(_, m)| m).collect();
    // The constructors: as the class has them (its own type parameters as
    // its arguments, an inherited one's types substituted), in
    // declaration order, each returning the class (what `new` makes).
    let instance = Type::Class(id, world.own_args(id));
    let cs: Vec<ReflectMethod> = world
        .constructors(id, &instance)
        .into_iter()
        .map(|(mid, subst)| {
            let m = world.method(mid);
            ReflectMethod {
                name: m.name.clone(),
                params: m
                    .params
                    .iter()
                    .map(|p| reflect_param(world, p, m.block_optional, &subst, class.id))
                    .collect(),
                ret: id,
                is_static: false,
                ret_ref: type_ref_of(world, &instance, class.id),
            }
        })
        .collect();
    (fs, ms, cs)
}

impl WorldReflect {
    /// A reflection over rows made already (`Runner::snapshot`).
    fn with_rows(
        fields: HashMap<ClassId, Vec<Rc<[ReflectField]>>>,
        methods: HashMap<ClassId, Vec<Rc<[ReflectMethod]>>>,
        constructors: HashMap<ClassId, Vec<Rc<[ReflectMethod]>>>,
        unshareable: rustc_hash::FxHashMap<ClassId, String>,
    ) -> WorldReflect {
        WorldReflect {
            unshareable,
            fields,
            methods,
            constructors,
            generated: RefCell::new(Vec::new()),
            doc: RefCell::new(None),
            pending: PendingView::default(),
            in_static: std::cell::Cell::new(0),
            refused: RefCell::new(None),
            refused_inits: Vec::new(),
            refused_construction: RefCell::new(None),
            ends: Default::default(),
            context: EndContext::default(),
            site_types: HashMap::new(),
        }
    }

    /// The run's statement values and hooks: `ends`, from where it is
    /// (`context`), with the `U` of each `statement_values` call.
    fn with_ends(
        mut self,
        host: &dyn StaticHost,
        ends: Rc<RefCell<ClassEnds>>,
        context: EndContext,
    ) -> WorldReflect {
        let world = host.world();
        let out = host.output();
        self.refused_inits = host.refused_constructors().to_vec();
        for (node, args) in &out.type_args {
            let Some(quarz_types::check::CallTarget::Method { method }) = out.calls.get(node)
            else {
                continue;
            };
            let m = world.method(*method);
            if m.owner == world.builtin.meta_classdef && m.name == "statement_values" {
                let u_param = m.type_params.first().map(|p| p.id);
                if let Some((_, u)) = args.iter().find(|(p, _)| Some(*p) == u_param) {
                    self.site_types.insert(*node as i64, world.type_name(u));
                }
            }
        }
        self.ends = ends;
        self.context = context;
        self
    }

    /// The class a statement value or hook may be given to here, or why
    /// none may: the running statement's own (a hook's, for reading).
    fn end_class(&self, class: ClassId, what: &str) -> Result<(), String> {
        match (&self.context.stmt, self.context.hook_of) {
            (_, Some(c)) if c == class => Ok(()),
            (Some((stmt, _)), None) if stmt.class == class => Ok(()),
            (None, None) => Err(format!(
                "{what} belong to a class body's statements, not to `static(...)`"
            )),
            _ => Err(format!("{what} belong to the class whose statement runs")),
        }
    }
}

fn reflect_param(
    world: &World,
    p: &ParamInfo,
    block_optional: bool,
    subst: &FxHashMap<TypeParamId, Type>,
    class: ClassId,
) -> ReflectParam {
    use quarz_syntax::ast::ParamKind;
    let kind = match p.kind {
        ParamKind::Positional if p.default.is_some() => ReflectKind::Optional,
        ParamKind::Positional => ReflectKind::Required,
        ParamKind::Rest => ReflectKind::Rest,
        ParamKind::KeywordOnly | ParamKind::KeywordRest => ReflectKind::Keyword,
        ParamKind::Block => ReflectKind::Block,
    };
    // Whether a call may leave it out (#1060): a parameter with a
    // default, a rest one (`*xs`, `**kw`: none passed), an optional
    // block (the method's `block_optional`).
    let default = match p.kind {
        ParamKind::Positional | ParamKind::KeywordOnly => p.default.is_some(),
        ParamKind::Rest | ParamKind::KeywordRest => true,
        ParamKind::Block => block_optional,
    };
    ReflectParam {
        name: p.name.clone(),
        ty: erase(world, &p.ty),
        kind,
        ty_ref: type_ref_of(world, &p.ty.subst(subst), class),
        default,
    }
}

/// `t`, a type as class `class` has it (its ancestors' type arguments
/// substituted), as `Meta::TypeRef` shows it (docs/14 §4), from the
/// checker's own type: a class with its arguments, a union (flattened
/// by the checker), a type parameter of `class` (the only class whose
/// parameters such a type can still name), else the type's text (a
/// tuple, a procedure type, `Type[X]`, a method's own type parameter,
/// `Self`). `type_of_ref` is its converse where generation takes it.
fn type_ref_of(world: &World, t: &Type, class: ClassId) -> ReflectType {
    let t = world.devoid(t);
    match &t {
        Type::Class(c, args) => ReflectType::Of(
            *c,
            args.iter().map(|a| type_ref_of(world, a, class)).collect(),
        ),
        Type::Union(ms) => {
            ReflectType::Union(ms.iter().map(|m| type_ref_of(world, m, class)).collect())
        }
        Type::Param(p) => world
            .class(class)
            .type_params
            .iter()
            .find(|tp| tp.id == *p)
            .map(|tp| ReflectType::Param(class, tp.name.clone()))
            .unwrap_or_else(|| ReflectType::Other(world.type_name(&t))),
        _ => ReflectType::Other(world.type_name(&t)),
    }
}

/// The type a `Meta::TypeRef` says, for a keyword generated into `class`
/// (`type_ref_of`'s converse), or why generation does not take it: a
/// class given the wrong number of type arguments, an empty union, a type
/// parameter of another class than the one generated into (#401, decided
/// 2026-11-19: D2 (a)), or a type by its text. A type argument's bounds
/// are checked as any declared signature's (`Checker::
/// check_signature_bounds`, at the statement).
fn type_of_ref(world: &World, r: &ReflectType, class: ClassId) -> Result<Type, String> {
    Ok(match r {
        ReflectType::Of(c, args) => {
            let k = world.class(*c);
            if k.type_params.len() != args.len() {
                return Err(format!(
                    "`{}` takes {} type argument{}, not {}",
                    k.name,
                    k.type_params.len(),
                    if k.type_params.len() == 1 { "" } else { "s" },
                    args.len()
                ));
            }
            let args: Result<Vec<Type>, String> =
                args.iter().map(|a| type_of_ref(world, a, class)).collect();
            Type::Class(*c, args?)
        }
        ReflectType::Union(ms) => {
            if ms.is_empty() {
                return Err("an empty union is no type".to_string());
            }
            let ms: Result<Vec<Type>, String> =
                ms.iter().map(|m| type_of_ref(world, m, class)).collect();
            Type::union_of(ms?)
        }
        ReflectType::Param(owner, name) => {
            let found = (*owner == class)
                .then(|| world.class(class).type_params.iter().find(|tp| tp.name == *name))
                .flatten();
            match found {
                Some(tp) => Type::Param(tp.id),
                None => {
                    return Err(format!(
                        "the type parameter `{name}` of `{}` is not one of `{}`, the class generated into",
                        world.class(*owner).name,
                        world.class(class).name
                    ))
                }
            }
        }
        ReflectType::Other(text) => {
            return Err(format!(
                "`{text}` cannot be a generated keyword's type yet: a class with its type arguments, a union or a type parameter of the class generated into can"
            ))
        }
    })
}

/// Whether `t` names the class `cid` anywhere (as it is, in an argument,
/// a union, a tuple or a procedure type).
fn mentions_class(t: &Type, cid: ClassId) -> bool {
    match t {
        Type::Class(id, args) => *id == cid || args.iter().any(|a| mentions_class(a, cid)),
        Type::ClassObject(_, args) => args.iter().any(|a| mentions_class(a, cid)),
        Type::TypeOf(inner) => mentions_class(inner, cid),
        Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(|m| mentions_class(m, cid)),
        Type::Proc(recv, ps, r, _, kws) => {
            recv.as_deref().is_some_and(|r| mentions_class(r, cid))
                || ps.iter().any(|p| mentions_class(p, cid))
                || kws.iter().any(|k| mentions_class(&k.ty, cid))
                || mentions_class(r, cid)
        }
        Type::Param(_) | Type::Var(_) | Type::Nothing | Type::Void => false,
    }
}

impl Reflect for WorldReflect {
    fn refused_construction(&self, class: ClassId, init: Option<MethodId>) -> Option<String> {
        let (_, _, why) = self
            .refused_inits
            .iter()
            .find(|(c, i, _)| (*c, *i) == (class, init))?;
        self.refused_construction
            .borrow_mut()
            .get_or_insert_with(|| why.clone());
        Some(why.clone())
    }
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
                        ty_ref: f.ty_ref.clone(),
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
                                ty_ref: p.ty_ref.clone(),
                                default: p.default,
                            })
                            .collect(),
                        ret: m.ret,
                        is_static: m.is_static,
                        ret_ref: m.ret_ref.clone(),
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
    fn constructors(&self, class: ClassId) -> Vec<ReflectMethod> {
        self.constructors
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
                                ty_ref: p.ty_ref.clone(),
                                default: p.default,
                            })
                            .collect(),
                        ret: m.ret,
                        is_static: m.is_static,
                        ret_ref: m.ret_ref.clone(),
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
    fn generate(&self, interp: &Interp, request: GenRequest) -> Result<usize, String> {
        let captures = request
            .captures
            .iter()
            .map(|(d, s, v)| Ok((*d, *s, bake(interp, &self.unshareable, v)?)))
            .collect::<Result<Vec<_>, String>>()?;
        let mut generated = self.generated.borrow_mut();
        generated.push(Pending::Method(PendingGen {
            class: request.class,
            name: request.name,
            params: request.params,
            singleton: request.singleton,
            visibility: request.visibility,
            func: request.func,
            captures,
            // (An initializer is no documented method: a `doc` before
            // `def_field` stays for the next generation.)
            doc: if request.initializes.is_some() {
                None
            } else {
                self.doc.borrow_mut().take()
            },
            keywords: request.keywords.map(|ks| {
                ks.into_iter()
                    .map(|k| (k.name, k.ty, k.required, k.nullable, k.ty_ref))
                    .collect()
            }),
            initialize: request.initialize,
            type_args: request.type_args,
            override_: request.override_,
            initializes: request.initializes,
        }));
        Ok(generated.len() - 1)
    }
    fn def_field(&self, interp: &Interp, request: FieldRequest) -> Result<(), String> {
        let default = bake(interp, &self.unshareable, &request.default)?;
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
                nullable: request.nullable,
            }));
        Ok(())
    }
    fn static_scope(&self, enter: bool) {
        let n = self.in_static.get();
        self.in_static
            .set(if enter { n + 1 } else { n.saturating_sub(1) });
    }
    fn generated_named(&self, name: &str) -> Vec<(ClassId, bool, Option<usize>)> {
        self.generated
            .borrow()
            .iter()
            .filter_map(|p| match p {
                Pending::Method(g) if g.name == name && !g.initialize => Some((
                    g.class,
                    g.singleton,
                    g.keywords.is_none().then_some(g.params.len()),
                )),
                // A field's reader and writer are methods too.
                Pending::Field(f) if f.reader && f.name == name => Some((f.class, false, Some(0))),
                Pending::Field(f)
                    if f.writer && name.strip_suffix('=') == Some(f.name.as_str()) =>
                {
                    Some((f.class, false, Some(1)))
                }
                _ => None,
            })
            .collect()
    }
    fn reflect_refusal(&self, class: ClassId) -> Option<String> {
        if self.in_static.get() == 0 {
            return None;
        }
        let statements = self.pending.labels(class);
        if statements.is_empty() {
            return None;
        }
        let why = format!(
            "`static(...)` in a compile-time run reflects on a class whose `static` statements have not all run ({}): the program's value, computed when they have, could differ (docs/14 §8)",
            statements.join(", ")
        );
        self.refused.borrow_mut().get_or_insert_with(|| why.clone());
        Some(why)
    }
    fn made_handle(&self, interp: &Interp, handle: &Value) -> Result<(), String> {
        let handle = bake(interp, &self.unshareable, handle)?;
        self.generated.borrow_mut().push(Pending::Handle(handle));
        Ok(())
    }
    fn doc(&self, text: String) {
        *self.doc.borrow_mut() = Some(text);
    }
    fn statement_values(&self, class: ClassId, key: &str, site: i64) -> Result<(), String> {
        self.end_class(class, "statement values")?;
        let ty = self
            .site_types
            .get(&site)
            .cloned()
            .unwrap_or_else(|| "?".to_string());
        let mut ends = self.ends.borrow_mut();
        let end = ends.classes.entry(class).or_default();
        match end.values.get(key) {
            Some((made, _)) if *made != ty => Err(format!(
                "the statement values `:{key}` were made as `StatementValues[{made}]`, and are named here as `StatementValues[{ty}]`: a key has one type"
            )),
            Some(_) => Ok(()),
            None => {
                end.values.insert(key.to_string(), (ty, Vec::new()));
                Ok(())
            }
        }
    }
    fn add_statement_value(&self, class: ClassId, key: &str, value: Value) -> Result<(), String> {
        if self.context.hook_of.is_some() {
            return Err(format!(
                "a class-end hook cannot add statement values (`:{key}`): they are for the class body's statements"
            ));
        }
        self.end_class(class, "statement values")?;
        let mut ends = self.ends.borrow_mut();
        let end = ends.classes.entry(class).or_default();
        match end.values.get_mut(key) {
            Some((_, vs)) => {
                vs.push(value);
                Ok(())
            }
            None => Err(format!("internal: statement values `:{key}` not made")),
        }
    }
    fn statement_value_list(&self, class: ClassId, key: &str) -> Vec<Value> {
        self.ends
            .borrow()
            .classes
            .get(&class)
            .and_then(|e| e.values.get(key))
            .map(|(_, vs)| vs.clone())
            .unwrap_or_default()
    }
    fn at_class_end(&self, class: ClassId, key: &str, hook: Value) -> Result<(), String> {
        if self.context.hook_of.is_some() {
            return Err(format!(
                "a class-end hook cannot register another (`:{key}`)"
            ));
        }
        self.end_class(class, "class-end hooks")?;
        let Some((stmt, callee)) = self.context.stmt.clone() else {
            return Err("class-end hooks belong to a class body's statements".to_string());
        };
        let mut ends = self.ends.borrow_mut();
        let end = ends.classes.entry(class).or_default();
        // The first under a key counts (a DSL of many lines registers
        // once).
        if !end.hooks.iter().any(|h| h.key == key) {
            end.hooks.push(Hook {
                key: key.to_string(),
                block: hook,
                stmt,
                callee,
            });
        }
        Ok(())
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
    // What the statements' runs lowered before the `static(...)` values
    // were known, lowered again with them (docs/14 §8).
    lowerer.relower_static_fallbacks();
    let mut rt: Option<std::sync::Arc<RtWorld>> = None;
    let dummy = quarz_syntax::ast::Expr {
        id: u32::MAX,
        kind: quarz_syntax::ast::ExprKind::Nil,
        span: Span::new(0, 0),
    };
    // (One copy of the files for all the rounds.)
    let files = Rc::new(files.to_vec());
    for &m in &statics {
        let owner = world.method(m).owner;
        let round = lowerer.lower_static(
            world,
            output,
            &dummy,
            owner,
            world.method(m).file,
            m,
            files.clone(),
        );
        // Loaded into the runner's state, which a REPL goes on running
        // (`continuing`): its functions must be all of `done`.
        let world = round.delta.world;
        if let Some(state) = &runner.state {
            Interp::load_functions(state, round.delta.base, round.delta.functions.clone());
        }
        lowerer.done.extend(round.delta.functions);
        rt = Some(world);
    }
    let functions = &lowerer.done;
    let Some(rt) = rt else {
        return Vec::new();
    };
    let by_name = methods_by_name(&rt);
    // (Asked once, for this classification: nothing to keep.)
    let kept = OverridesKept::default();
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
                    // (Without the bounds of `self`, a wider walk.)
                    let mut methods: Vec<(MethodId, SelfBound)> = Vec::new();
                    reached(
                        &rt,
                        &by_name,
                        &kept,
                        &functions[fid as usize],
                        &None,
                        &mut methods,
                        &mut |r| {
                            if let shake::Ref::Func(f) = r {
                                work.push(f)
                            }
                        },
                        false,
                        &mut |_, _, _| {},
                    );
                    for (mm, _) in methods {
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
