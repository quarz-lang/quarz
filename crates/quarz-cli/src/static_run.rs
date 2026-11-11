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
type GeneratedHandles = (Option<FuncId>, ClassId, Option<MethodId>, Captures, String);

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
    world: Option<RtWorld>,
    files: Vec<SourceFile>,
    prepared: bool,
    /// The constants a `def_field` leaves initialized: those of the REPL's
    /// earlier inputs (`continuing`).
    keep_consts: usize,
    /// The statement values and class-end hooks the statements of the
    /// classes not ended yet registered (docs/14 §5).
    ends: Rc<RefCell<ClassEnds>>,
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
                            generated.push((None, *owner, None, vec![(0, 0, h.clone())], at));
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
                let mut checked: Vec<(TypeParamId, &Vec<Type>, ClassId)> = Vec::new();
                for ((p, bounds), c) in carried.iter().zip(&g.type_args) {
                    if subst.contains_key(p) {
                        continue;
                    }
                    let k = world.class(*c);
                    if !k.type_params.is_empty() {
                        return Err(fail(format!(
                            "{at}: `{}` is `{}`, whose type arguments are not known here: pass them at the statement's call or use a class without type arguments",
                            world.type_name(&Type::Param(*p)),
                            k.name
                        )));
                    }
                    subst.insert(*p, Type::Class(*c, Vec::new()));
                    checked.push((*p, bounds, *c));
                }
                // (Only when the signature says one of them.)
                carried_gen[index] = checked.iter().any(|(p, _, _)| {
                    param_types
                        .iter()
                        .chain(std::iter::once(&*ret))
                        .any(|t| t.mentions_param(*p))
                });
                for (p, bounds, c) in checked {
                    let t = Type::Class(c, Vec::new());
                    // (A bound naming a type parameter nothing gives here, a
                    // module's own `T` that `include` binds, holds of the
                    // class the call was checked with: the class is one.
                    // One naming only the target's own, `Self` of a generic
                    // class, is decided with them as they are.)
                    if let Some(b) = bounds
                        .iter()
                        .map(|b| b.subst(&subst))
                        .filter(|b| free_param(b, &own).is_none())
                        .find(|b| !world.is_subtype(&t, b))
                    {
                        return Err(fail(format!(
                            "{at}: `{}` is `{}` here, which is not a `{}`",
                            world.type_name(&Type::Param(p)),
                            world.class(c).name,
                            world.type_name(&b)
                        )));
                    }
                }
            }
            let param_types: Vec<Type> = param_types.iter().map(|t| t.subst(&subst)).collect();
            // (An `initialize`'s result is discarded, as a written one's.)
            let ret = if g.initialize {
                Type::Void
            } else {
                ret.subst(&subst)
            };
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
                    for (name, ty, required, nullable) in ks {
                        if !world.class(*ty).type_params.is_empty() {
                            return Err(fail(format!(
                                "{at}: the keyword `{name}` is typed `{}`, which takes type arguments a `Type` value does not carry: a keyword's type is a class without them",
                                world.class(*ty).name
                            )));
                        }
                        let t = Type::Class(*ty, Vec::new());
                        params.push(ParamInfo {
                            name: name.clone(),
                            kind: ParamKind::KeywordOnly,
                            ty: if *nullable {
                                Type::union_of(vec![t, world.nil()])
                            } else {
                                t
                            },
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
                    decode,
                }),
                builds_self: false,
                needs_includer: None,
            };
            let mid = host
                .add_generated(info)
                .map_err(|why| fail(format!("{at}: {why}")))?;
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
            generated.push((Some(func), class, Some(mid), captures, at.clone()));
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
            "{at}: the handle to `{shown}` is made with `{param}`, a type parameter of another method than the `static def` the statement calls: a handle's type is written as a type or one of that `static def`'s type parameters"
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
        for (_, into, mid, captures, at) in generated {
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
        // `U` of `def_field[U]` and `field_ref[U]`, as recorded at the call.
        let own_u: Vec<TypeParamId> = ["def_field", "field_ref"]
            .iter()
            .filter_map(|n| world.class(world.builtin.meta_classdef).methods.get(*n))
            .flatten()
            .filter_map(|m| world.method(*m).type_params.first().map(|p| p.id))
            .collect();
        for (func, into, _, captures, at) in generated {
            let sets = func
                .map(|f| quarz_lower::lift::handle_sets(&self.lowerer.done, f, set))
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
                if let Some(u) = wanted {
                    // `U` is concrete or the statement's own type arguments:
                    // a helper's type parameter has no value here.
                    let fixed: Vec<TypeParamId> = world
                        .class(*owner)
                        .type_params
                        .iter()
                        .map(|p| p.id)
                        .collect();
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
            bad_consts: Default::default(),
            state: None,
            world: None,
            files,
            prepared: false,
            keep_consts: 0,
            ends: Default::default(),
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
                "`{callee_name}` did not run: what it reaches has errors (reported above)"
            );
        };
        format!(
            "`{callee_name}` did not run: {}",
            self.describe_bad(host, m)
        )
    }

    /// `m`, a method with errors a statement may reach, where it is, and its
    /// first error.
    fn describe_bad(&self, host: &dyn StaticHost, m: MethodId) -> String {
        let world = host.world();
        let errors: &[(u32, Diagnostic)] = self
            .bad_methods
            .get(&m)
            .map(|(_, e)| e.as_slice())
            .unwrap_or(&[]);
        let info = world.method(m);
        let name = format!(
            "{}{}{}",
            world.class(info.owner).name,
            if info.singleton { "." } else { "#" },
            info.name
        );
        let at = |file: u32, span: Span| -> String {
            match self.files.get(file as usize) {
                Some(f) => format!("{}:{}", f.name, f.line_col(span.start).line),
                None => String::new(),
            }
        };
        let place = at(info.file, info.span);
        let place = if place.is_empty() {
            String::new()
        } else {
            format!(" ({place})")
        };
        // Its own first error, else the first of what it uses (a
        // constant whose initializer has errors), with where that is.
        let own = errors.iter().find(|(f, d)| {
            *f == info.file && info.span.start <= d.span.start && d.span.end <= info.span.end
        });
        match (own, errors.first()) {
            (Some((_, d)), _) => format!(
                "it may reach `{name}`{place}, which has errors: {}",
                d.message
            ),
            (None, Some((f, d))) => format!(
                "it may reach `{name}`{place}, which uses what has errors: {} ({})",
                d.message,
                at(*f, d.span)
            ),
            (None, None) => {
                format!("it may reach `{name}`{place}, which has errors (reported with it)")
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
    ) -> Option<Result<MethodId, String>> {
        if self.bad_methods.is_empty() && self.bad_consts.is_empty() {
            return None;
        }
        let world = self.world.as_ref()?;
        let by_name = methods_by_name(world);
        // Each function once per bound of its `self` (`reached`).
        let mut seen: rustc_hash::FxHashSet<(FuncId, SelfBound)> = Default::default();
        let mut work: Vec<(FuncId, SelfBound)> = vec![(root, None)];
        while let Some((fid, bound)) = work.pop() {
            if fid as usize >= self.lowerer.done.len() || !seen.insert((fid, bound.clone())) {
                continue;
            }
            let f = &self.lowerer.done[fid as usize];
            let mut methods: Vec<(MethodId, SelfBound)> = Vec::new();
            let mut found: Option<Result<MethodId, String>> = None;
            reached(
                world,
                &by_name,
                f,
                &bound,
                &mut methods,
                &mut |r| match r {
                    shake::Ref::Func(g) if !lifted.contains(&g) => {
                        work.push((g, func_bound(&self.lowerer.done, f, g, &bound)))
                    }
                    shake::Ref::Const(c) => {
                        if self.bad_consts.contains(&c) {
                            found = Some(Err(world.consts[c as usize].name.clone()));
                        } else if let Some(init) = world.consts.get(c as usize).and_then(|c| c.init)
                        {
                            work.push((init, None));
                        }
                    }
                    _ => {}
                },
                true,
            );
            if found.is_some() {
                return found;
            }
            for (m, b) in methods {
                for &m in std::iter::once(&m).chain(synth_calls(world, m)) {
                    if self.bad_methods.contains_key(&m) {
                        return Some(Ok(m));
                    }
                    if let Some(f) = world.methods[m as usize].func {
                        work.push((f, b.clone()));
                    }
                }
            }
        }
        None
    }

    /// A native the statement reaches that cannot run at compile time,
    /// with the calls leading to it (innermost last).
    fn impure_reach(
        &self,
        root: FuncId,
        lifted: &rustc_hash::FxHashSet<FuncId>,
    ) -> Option<Vec<String>> {
        let world = self.world.as_ref()?;
        let by_name = methods_by_name(world);
        // Each function once per bound of its `self` (`reached`).
        let mut seen: rustc_hash::FxHashSet<(FuncId, SelfBound)> = Default::default();
        // Each function with the bound of its `self` and the path of
        // method names that reached it.
        let mut work: Vec<(FuncId, SelfBound, Vec<String>)> = vec![(root, None, Vec::new())];
        while let Some((fid, bound, path)) = work.pop() {
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
                f,
                &bound,
                &mut methods,
                &mut |r| match r {
                    shake::Ref::Func(f) if !lifted.contains(&f) => funcs.push(f),
                    shake::Ref::Const(c) => consts.push(c),
                    _ => {}
                },
                false,
            );
            // (In order: a stack, as is `work`.)
            let mut methods: Vec<(MethodId, SelfBound, Vec<String>)> = methods
                .into_iter()
                .rev()
                .map(|(m, b)| (m, b, path.clone()))
                .collect();
            while let Some((m, b, mut p)) = methods.pop() {
                let rm = &world.methods[m as usize];
                p.push(method_name(world, m));
                if let Some(key) = &rm.native_key {
                    if !compile_time_allowed(key) {
                        return Some(p);
                    }
                }
                for &i in synth_calls(world, m) {
                    methods.push((i, None, p.clone()));
                }
                if let Some(f) = rm.func {
                    work.push((f, b, p));
                }
            }
            for g in funcs {
                work.push((
                    g,
                    func_bound(&self.lowerer.done, f, g, &bound),
                    path.clone(),
                ));
            }
            for c in consts {
                if let Some(init) = world.consts.get(c as usize).and_then(|c| c.init) {
                    let mut p = path.clone();
                    p.push(world.consts[c as usize].name.clone());
                    work.push((init, None, p));
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
fn reached<'a>(
    world: &RtWorld,
    by_name: &HashMap<&str, Vec<MethodId>>,
    f: &'a quarz_ir::Function,
    self_bound: &SelfBound,
    methods: &mut Vec<(MethodId, SelfBound)>,
    other: &mut dyn FnMut(shake::Ref<'a>),
    by_runtime: bool,
) {
    let first = methods.len();
    // The names the runtime calls for the instructions.
    let mut runtime: Vec<&'static str> = Vec::new();
    shake::reach_refs(f, &mut |r| match r {
        shake::Ref::Method(m) => {
            methods.push((m, None));
            methods.extend(
                overrides_of(world, by_name, m, None)
                    .into_iter()
                    .map(|o| (o, None)),
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
                overrides_of(world, by_name, method, bound.as_deref())
                    .into_iter()
                    .map(|o| (o, bound.clone())),
            );
        }
        shake::Ref::Exact { method, on_self } => {
            methods.push((method, if on_self { self_bound.clone() } else { None }))
        }
        shake::Ref::Runtime(n) => {
            if by_runtime {
                runtime.push(n);
            }
        }
        shake::Ref::Name(n) => {
            if let Some(ms) = by_name.get(n) {
                methods.extend(
                    ms.iter()
                        .copied()
                        .filter(|&o| !denied_owner(world, o))
                        .map(|o| (o, None)),
                );
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
    let mut add = |n: &'static str,
                   work: &mut Vec<(MethodId, Option<&'static str>)>,
                   methods: &mut Vec<(MethodId, SelfBound)>| {
        if let Some(ms) = by_name.get(n) {
            for &o in ms {
                if !world.methods[o as usize].singleton && !denied_owner(world, o) && seen.insert(o)
                {
                    methods.push((o, None));
                    work.push((o, Some(n)));
                }
            }
        }
    };
    for n in runtime {
        add(n, &mut work, methods);
    }
    while let Some((m, by)) = work.pop() {
        if world.methods[m as usize].native_key.is_none() {
            continue;
        }
        let names = match by {
            Some(n) => shake::calls_for(n),
            None => native_calls(world, m),
        };
        for n in names {
            add(n, &mut work, methods);
        }
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

/// The methods that override `m` in subclasses of its owner (same name,
/// same side), which a call of `m` may run instead: with `bound`, on a
/// receiver of one of those classes or a subclass (`may_receive`).
fn overrides_of(
    world: &RtWorld,
    by_name: &HashMap<&str, Vec<MethodId>>,
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
                        && may_dispatch_to(world, o, m)
                        && bound.is_none_or(|b| may_receive(world, o, b))
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Whether a call resolved to `m` may run `o` (of its name), as a
/// receiver's lookup may find it (`is_override` in the lowering, alike):
/// for a module's method or `Object`'s, any; for `Type`'s, a class
/// method (a module's too); for a class method, one of a class below it,
/// or of a module a class below it includes (or, for a module's class
/// method, one of a class or module beside it in an includer); for
/// another class's instance method, one of a class below it, or of a
/// module a class below it includes.
///
/// A reachability superset for static runs only (by name and hierarchy,
/// wider than the override table `RtMethod::overrides`): never consulted
/// for which method runs (#536).
fn may_dispatch_to(world: &RtWorld, o: MethodId, m: MethodId) -> bool {
    let (om, rm) = (&world.methods[o as usize], &world.methods[m as usize]);
    let owner = rm.owner;
    let module = |c: ClassId| world.classes[c as usize].kind == RtClassKind::Module;
    if rm.singleton {
        if !om.singleton {
            return false;
        }
        if !module(om.owner) && !module(owner) {
            return world.class_is_a(om.owner, owner);
        }
        // (A module's class method: on a class that has both.)
        return (0..world.classes.len() as ClassId)
            .any(|c| world.class_is_a(c, owner) && world.class_is_a(c, om.owner));
    }
    // An abstract method's implementation may come from above its owner
    // (a superclass's method of the name).
    if rm.is_abstract && !om.singleton && world.class_is_a(owner, om.owner) {
        return true;
    }
    // `Type`'s (or a subclass's, `Meta::ClassDef`'s), on class objects: a
    // class method (a module's included too) the override table pairs
    // with it (`RtMethod::overrides`: never with `Meta::ClassDef#type`,
    // always the reflection's, #553).
    if world.class_is_a(owner, world.builtin.class_) {
        return (om.singleton && om.overrides.contains(&m)) || world.class_is_a(om.owner, owner);
    }
    if module(owner) || owner == world.builtin.object {
        return true;
    }
    if om.singleton {
        return false;
    }
    world.class_is_a(om.owner, owner)
        || (world.classes[om.owner as usize].kind == RtClassKind::Module
            && (0..world.classes.len() as ClassId)
                .any(|c| world.class_is_a(c, owner) && world.class_is_a(c, om.owner)))
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

fn methods_by_name(world: &RtWorld) -> HashMap<&str, Vec<MethodId>> {
    let mut out: HashMap<&str, Vec<MethodId>> = HashMap::new();
    for (i, m) in world.methods.iter().enumerate() {
        out.entry(m.name.as_str()).or_default().push(i as MethodId);
    }
    out
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
        let callee_name = host.world().method(callee).name.clone();
        // Code that failed its check does not run (docs/05 §3): neither a
        // statement reaching a method or constant with errors, nor one
        // whose lowering found errors elsewhere (a field default).
        // The blocks given to `def_method` and its kin become method bodies
        // the statement does not run: not in its reach (docs/14 §5).
        let lifted = &self.lowerer.lifted_funcs;
        if let Some(bad) = self.bad_reach(fid, lifted) {
            let message = match bad {
                Ok(m) => format!(
                    "`{callee_name}` did not run: {}",
                    self.describe_bad(host, m)
                ),
                Err(c) => format!(
                    "`{callee_name}` did not run: it reaches `{c}`, which has errors (reported above)"
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
                    "`{callee_name}` reaches `{last}`{via}, which cannot run at compile time"
                ),
                notes: Vec::new(),
            });
        }
        let context = EndContext {
            stmt: as_statement.then(|| (stmt.clone(), callee)),
            hook_of: None,
        };
        let mut reflect =
            WorldReflect::snapshot(host.world()).with_ends(&*host, self.ends.clone(), context);
        self.note_pending(host, &mut reflect);
        let reflect = Rc::new(reflect);
        let interp = self.interp(&reflect);
        let result = interp.run_static(fid, Value::Class(stmt.class), stmt.file);
        self.finish(&interp, &reflect, result, &format!("`{callee_name}`"))
    }

    /// The classes whose statements are still to run, as a message names
    /// them, for `reflect_refusal` (docs/14 §8).
    fn note_pending(&self, host: &dyn StaticHost, reflect: &mut WorldReflect) {
        let world = host.world();
        for i in host.pending_statements() {
            let s = &world.static_stmts[i];
            let call = match &s.expr.kind {
                quarz_syntax::ast::ExprKind::Call(c) => c.name.clone(),
                _ => "static".to_string(),
            };
            let label = format!("`{call}` in `{}`", world.class(s.class).name);
            for c in &world.classes {
                if world.class_is_a(c.id, s.class) {
                    let labels = reflect.pending.entry(c.id).or_default();
                    if !labels.contains(&label) {
                        labels.push(label.clone());
                    }
                }
            }
        }
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
        let context = EndContext {
            stmt: None,
            hook_of: Some(last.class),
        };
        let mut reflect =
            WorldReflect::snapshot(host.world()).with_ends(&*host, self.ends.clone(), context);
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
/// statement runs, with what the statements run before it generated (its
/// class's ancestors' among them, docs/14 §2).
struct WorldReflect {
    fields: HashMap<ClassId, Vec<Rc<[ReflectField]>>>,
    methods: HashMap<ClassId, Vec<Rc<[ReflectMethod]>>>,
    /// What the statement's run asked to generate, in call order.
    generated: RefCell<Vec<Pending>>,
    /// The `doc` given, for the next generation.
    doc: RefCell<Option<String>>,
    /// The classes whose `static` statements, or an ancestor's, are still
    /// to run, with those statements as a message names them.
    pending: HashMap<ClassId, Vec<String>>,
    /// How many `static(...)` runs inside this compile-time run are under
    /// way (docs/14 §8).
    in_static: std::cell::Cell<u32>,
    /// The first refusal (`reflect_refusal`), which fails the statement
    /// whatever its run rescued.
    refused: RefCell<Option<String>>,
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
    /// `keywords:`: (name, class, required, nullable).
    keywords: Option<Vec<(String, ClassId, bool, bool)>>,
    /// `def_initialize` (docs/14 §5).
    initialize: bool,
    /// The classes the calling method's carried type parameters stand
    /// for (`Lowerer::carried_type_params`).
    type_args: Vec<ClassId>,
    /// `override: true` (docs/14 §5).
    override_: bool,
}

/// A compile-time value as a generated method embeds it (docs/14 §5),
/// or why it cannot.
/// The `data` types and enums of `world` that are not Shareable (a field
/// that is not): their values cannot be baked, so that every baked value
/// is Shareable (docs/14 §5).
fn unshareable_data(world: &World) -> rustc_hash::FxHashMap<ClassId, String> {
    use quarz_types::ClassKind;
    world
        .classes
        .iter()
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
            (c.id, why)
        })
        .collect()
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
            unshareable: unshareable_data(world),
            fields,
            methods,
            generated: RefCell::new(Vec::new()),
            doc: RefCell::new(None),
            pending: HashMap::new(),
            in_static: std::cell::Cell::new(0),
            refused: RefCell::new(None),
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
        Type::Proc(recv, ps, r, _, kws) => {
            recv.as_deref().is_some_and(|r| mentions_class(r, cid))
                || ps.iter().any(|p| mentions_class(p, cid))
                || kws.iter().any(|k| mentions_class(&k.ty, cid))
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
            doc: self.doc.borrow_mut().take(),
            keywords: request.keywords.map(|ks| {
                ks.into_iter()
                    .map(|k| (k.name, k.ty, k.required, k.nullable))
                    .collect()
            }),
            initialize: request.initialize,
            type_args: request.type_args,
            override_: request.override_,
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
    fn reflect_refusal(&self, class: ClassId) -> Option<String> {
        if self.in_static.get() == 0 {
            return None;
        }
        let statements = self.pending.get(&class)?;
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
                    // (Without the bounds of `self`, a wider walk.)
                    let mut methods: Vec<(MethodId, SelfBound)> = Vec::new();
                    reached(
                        &rt,
                        &by_name,
                        &functions[fid as usize],
                        &None,
                        &mut methods,
                        &mut |r| {
                            if let shake::Ref::Func(f) = r {
                                work.push(f)
                            }
                        },
                        false,
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
