//! `World` (the checker's view) → `RtWorld` (what the runtime needs).

use quarz_ir::*;
use quarz_syntax::ast::ParamKind;
use quarz_types::{self as types, ClassKind, Member, Synth, Type, World};

use crate::Lowerer;

fn param_kind(k: ParamKind) -> RtParamKind {
    match k {
        ParamKind::Positional => RtParamKind::Positional,
        ParamKind::Rest => RtParamKind::Rest,
        ParamKind::KeywordOnly => RtParamKind::KeywordOnly,
        ParamKind::KeywordRest => RtParamKind::KeywordRest,
        ParamKind::Block => RtParamKind::Block,
    }
}

/// What the lowering adds to `declared`'s tables: the classes' fields and
/// their defaults (the layouts), each method's function and whether it is
/// overridden, the constants' functions and the quoted blocks' trees, the
/// file names. Nothing `declared`'s rows read.
pub fn fill(rt: &mut RtWorld, world: &World, lw: &Lowerer, file_names: Vec<String>) {
    // (Per round: the deferred check removes a class from the list during
    // a phase, and the program's final tables have none, every deferred
    // conformance having been checked by then, #801.)
    rt.deferred_conformance = if lw.static_mode {
        world.conformance_deferred.clone()
    } else {
        debug_assert!(
            world.conformance_deferred.is_empty(),
            "a conformance still deferred at the final lowering"
        );
        Vec::new()
    };
    for (c, rc) in world.classes.iter().zip(rt.classes.iter_mut()) {
        let layout = &lw.layouts[c.id as usize];
        // A type with a parameter in it has no name of its own: a
        // parameter prints as its name, which may be a class's
        // (`class Box[String]`).
        let ty_name = |t: &Type| {
            (!t.mentions_any_param() && !t.has_vars()).then(|| world.type_name(&world.devoid(t)))
        };
        // A declared field stored in one physical field keeps its
        // default there; a flattened one runs it through the
        // logical view.
        let ivars: Vec<RtIvar> = layout
            .ivars
            .iter()
            .enumerate()
            .map(|(i, iv)| RtIvar {
                name: iv.name.clone(),
                ty: ty_name(&iv.ty),
                slot: iv.slot,
                flat: iv.flat,
                default: lw.field_default(world, c.id, i),
            })
            .collect();
        let fields: Vec<RtField> = layout
            .slots
            .iter()
            .enumerate()
            .map(|(k, s)| RtField {
                name: s.name.clone(),
                default: ivars
                    .iter()
                    .find(|iv| iv.flat.is_none() && iv.slot as usize == k)
                    .and_then(|iv| iv.default),
                ty: ty_name(&s.ty),
            })
            .collect();
        rc.ivars = ivars;
        rc.fields = fields;
    }
    for (m, rm) in world.methods.iter().zip(rt.methods.iter_mut()) {
        rm.overridden |= lw.overridden.contains(&m.id);
        assert!(!(rm.overridden && rm.is_extension), "an extension's method `{}` is never overridden: the checker refuses an abstract one (#534), the table has none (`RtMethod::dispatch`)", m.name);
        rm.func = lw.method_funcs.get(m.id as usize).copied().flatten();
    }
    rt.consts = world
        .consts
        .iter()
        .map(|c| RtConst {
            name: c.name.clone(),
            owner: c.owner,
            init: lw.const_funcs.get(c.id as usize).copied().flatten(),
            file: c.file,
        })
        .collect();
    // The quoted blocks' trees (docs/14 §6), after the world's.
    rt.consts.extend(lw.quoted_consts.iter().cloned());
    rt.file_names = file_names;
}

/// The runtime's tables the declarations alone decide, with the rows over
/// them (`build_witness_rows`): the classes'
/// ancestors, lookup, class side and methods, the methods' signatures and
/// override table, the extensions and their witnesses. Built once per
/// program after its check (`Lowerer::declare`, where the safety net
/// reads the rows) and completed by the lowering (`fill`); the lowering's
/// fields are empty here.
pub fn declared(world: &World, out: &types::Output) -> RtWorld {
    declared_with(world, out, witness_record(world)).0
}

/// The checker's witness record as the rows read it
/// (`RtWorld::witness_record`): (class, requirement, witness), sorted, one
/// entry per key (#536 step 3's S2).
pub fn witness_record(world: &World) -> Vec<(ClassId, MethodId, Option<MethodId>)> {
    let mut r: Vec<(ClassId, MethodId, Option<MethodId>)> = world
        .witness_record()
        .into_iter()
        .map(|(c, r, w, _)| (c, r, w))
        .collect();
    r.sort_unstable();
    r.dedup();
    r
}

/// Class `c`'s entries of `witness_record` (`World::witnesses_of`), sorted:
/// the record is their concatenation over the classes in order.
pub fn witness_record_of(world: &World, c: ClassId) -> Vec<(ClassId, MethodId, Option<MethodId>)> {
    let mut r: Vec<(ClassId, MethodId, Option<MethodId>)> = world
        .witnesses_of(c)
        .into_iter()
        .map(|(c, r, w, _)| (c, r, w))
        .collect();
    r.sort_unstable();
    r.dedup();
    r
}

/// `declared` with the witness record already made, and the override
/// table it built the method rows with (`World::override_table`).
pub fn declared_with(
    world: &World,
    out: &types::Output,
    record: Vec<(ClassId, MethodId, Option<MethodId>)>,
) -> (RtWorld, Vec<Vec<MethodId>>) {
    let classes: Vec<RtClass> = world
        .classes
        .iter()
        .map(|c| class_row(world, out, c.id))
        .collect();
    // (The override table, once, #536.)
    let table = world.override_table();
    let methods: Vec<RtMethod> = world
        .methods
        .iter()
        .map(|m| method_row(world, m.id, &table[m.id as usize]))
        .collect();
    let rt = declared_rest(world, classes, methods, &table, record);
    (rt, table)
}

/// Class `id`'s row of `RtWorld::classes`, as the declarations decide it
/// (`declared_with`; the lowering's fields are left empty for `fill`).
pub fn class_row(world: &World, out: &types::Output, id: ClassId) -> RtClass {
    let c = world.class(id);
    let members = c
        .members
        .iter()
        .filter_map(|(name, m)| match m {
            Member::Class(id) => Some((name.clone(), *id)),
            _ => None,
        })
        .collect();
    RtClass {
        name: c.name.clone(),
        kind: match c.kind {
            ClassKind::Class => RtClassKind::Class,
            ClassKind::Module => RtClassKind::Module,
            ClassKind::Data => RtClassKind::Data,
            ClassKind::Enum => RtClassKind::Enum,
            ClassKind::Variant => RtClassKind::Variant,
            ClassKind::Main => RtClassKind::Main,
        },
        superclass: match &c.superclass {
            Some(Type::Class(id, _)) => Some(*id),
            _ => None,
        },
        ancestors: {
            // (Every extension's include, whichever are active
            // where the lowering runs, #554.)
            let mut a: Vec<ClassId> = world
                .runtime_ancestors(c.id)
                .into_iter()
                .map(|(id, _)| id)
                .collect();
            // A non-generic `data` type or enum Shareable by its
            // fields is a `Shareable` at run time too (docs/03).
            let marker = world.builtin.shareable;
            if c.type_params.is_empty()
                && !a.contains(&marker)
                && world.derived_shareable(c.id, &[])
            {
                a.push(marker);
            }
            a
        },
        // (Dispatch by name: without the modules of scoped and
        // conditional extensions, docs/01 §7; the marker as above.)
        lookup: {
            let mut l = world.lookup_ancestors(c.id);
            let marker = world.builtin.shareable;
            if c.type_params.is_empty()
                && !l.contains(&marker)
                && world.derived_shareable(c.id, &[])
            {
                l.push(marker);
            }
            l
        },
        fields: Vec::new(),
        ivars: Vec::new(),
        inherited_inits: out
            .inherited_inits
            .iter()
            .filter(|(sub, _, _)| *sub == c.id)
            .map(|(_, init, chosen)| (*init, *chosen))
            .collect(),
        with_init: world.with_initialize(c.id),
        methods: c
            .methods
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
        singleton_methods: c
            .singleton_methods
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
        // (The dispatch order: the top-level unconditional
        // extensions' modules with the own includes, #681.)
        class_side: world.class_dispatch_order(c.id),
        built_by_runtime: world.built_by_runtime(c.id),
        members,
        variants: c.variants.clone(),
        variant_of: c.variant_of,
        structural: matches!(c.kind, ClassKind::Data | ClassKind::Variant),
        key_methods: world.key_methods(c.id),
        is_exception: world.is_exception_class(c.id),
        is_abstract: c.is_abstract,
        objects: world.instances_are_objects(c.id),
        file: c.file,
        cog: c.cog.map(|i| {
            let info = &world.cogs[i as usize];
            (info.name.clone(), info.version.clone())
        }),
    }
}

/// Method `id`'s row of `RtWorld::methods`, with its override table entry
/// `overrides` (`World::overrides`, a row of `override_table`); `func`
/// and the lowering's `overridden` are left for `fill`.
pub fn method_row(world: &World, id: MethodId, overrides: &[MethodId]) -> RtMethod {
    let m = world.method(id);
    let owner = world.class(m.owner);
    let overloaded = owner.methods.get(&m.name).is_some_and(|ids| ids.len() > 1);
    // An abstract method is always dispatched dynamically: its
    // implementation may be a class method of a class that
    // includes the module, which the class hierarchy walk does not see.
    // A class method is dispatched on the class it is called on
    // (`Circle.describe` runs `Circle.label` for an implicit
    // `label` in `Shape.describe`).
    // (`fill` adds the lowering's overridden methods.)
    let overridden = m.is_abstract;
    let synth = match &m.synth {
        Synth::None => RtSynth::None,
        Synth::FieldGet(name) => {
            RtSynth::FieldGet(world.field_index(m.owner, name).unwrap_or(0) as u32)
        }
        Synth::FieldSet(name) => {
            RtSynth::FieldSet(world.field_index(m.owner, name).unwrap_or(0) as u32)
        }
        Synth::DataInit => RtSynth::DataInit,
        Synth::DataWith => RtSynth::DataWith,
        Synth::DataToH => RtSynth::DataToH,
    };
    let fast_op = if m.is_native && (m.owner == world.builtin.int || m.owner == world.builtin.float)
    {
        FastOp::from_name(&m.name)
    } else {
        None
    };
    let mut row = RtMethod {
                shape: NO_SHAPE,
                name: m.name.clone(),
                owner: m.owner,
                singleton: m.singleton,
                params: m
                    .params
                    .iter()
                    .map(|p| RtParam {
                        name: p.name.clone(),
                        kind: param_kind(p.kind),
                        has_default: p.default.is_some(),
                        // (`Void` is `Nil` at run time.)
                        ty: rt_kind(world, &p.ty),
                        default: if m.is_native {
                            let d = p.default.as_deref().and_then(literal_constant);
                            // (A call may skip it to name a later one by
                            // keyword: `Interp::native_positions` passes
                            // only a literal. Only a real native: a
                            // synthesized method binds its own, a data
                            // type's constructor in `Interp::bind_data_args`.)
                            debug_assert!(
                                p.default.is_none()
                                    || d.is_some()
                                    || !later_positional(m, &p.name)
                                    || m.synth != Synth::None,
                                "native `{}`: the default of `{}` is not a literal, though a positional parameter follows it",
                                m.name,
                                p.name
                            );
                            d
                        } else {
                            None
                        },
                    })
                    .collect(),
                has_block: m.block.is_some(),
                func: None,
                native_key: if m.is_native && m.synth == Synth::None {
                    Some(m.native_key(world))
                } else {
                    None
                },
                synth,
                is_abstract: m.is_abstract,
                is_extension: m.extension.is_some(),
                overloaded,
                overridden,
                fast_op,
                file: m.file,
                ret: match &m.ret {
                    Type::Param(_) | Type::Var(_) => None,
                    t => Some(world.type_name(&world.devoid(t))),
                },
                overrides: overrides.to_vec(),
                makes: if m.is_native {
                    let mut out = Vec::new();
                    classes_in(&m.ret, &mut out);
                    if let Some((_, t)) = &m.block {
                        classes_in(t, &mut out);
                    }
                    out.sort_unstable();
                    out.dedup();
                    out
                } else {
                    Vec::new()
                },
                keyword_hash: m.generated.as_ref().is_some_and(|g| g.keywords),
            };
    row.shape = RtMethod::shape_of(&row.params, row.has_block);
    row
}

/// The rest of `declared_with` over the class and method rows: the
/// extensions, the top-level names, the built-in ids, the file mains, the
/// include pairs and the rows over them (`class_override_rows`,
/// `RtWorld::build_witness_rows`).
fn declared_rest(
    world: &World,
    classes: Vec<RtClass>,
    methods: Vec<RtMethod>,
    table: &[Vec<MethodId>],
    record: Vec<(ClassId, MethodId, Option<MethodId>)>,
) -> RtWorld {
    // Every extension is listed: the always-active ones (the prelude's)
    // take part in dispatch by name and come first; any other only
    // through the modules it makes its target conform to (a module method
    // implemented for a class by an extension is found through it).
    let mut extensions: Vec<RtExtension> = Vec::new();
    for always in [true, false] {
        for e in world
            .extensions
            .iter()
            .filter(|e| e.always_active == always)
        {
            extensions.push(RtExtension {
                target: e.target,
                methods: e
                    .methods
                    .iter()
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect(),
                always_active: e.always_active,
                includes: e
                    .includes
                    .iter()
                    .filter_map(|t| match t {
                        Type::Class(id, _) => Some(*id),
                        _ => None,
                    })
                    .collect(),
            });
        }
    }
    let top: quarz_ir::HashMap<String, ClassId> = world
        .top
        .iter()
        .filter_map(|(name, m)| match m {
            Member::Class(id) => Some((name.clone(), *id)),
            _ => None,
        })
        .collect();
    let b = &world.builtin;
    let standard_error = b.standard_error;
    let builtin = RtBuiltin {
        comparable: world.builtin.comparable,
        enumerable: world.builtin.enumerable,
        object: b.object,
        nil: b.nil,
        bool_: b.bool_,
        int: b.int,
        integer: b.integer,
        float: b.float,
        string: b.string,
        symbol: b.symbol,
        array: b.array,
        hash: b.hash,
        set: b.set,
        range: b.range,
        regexp: b.regexp,
        proc_: b.proc_,
        class_: b.class_,
        cog: b.cog,
        task: b.task,
        channel: b.channel,
        atom: b.atom,
        scope: b.scope,
        duration: b.duration,
        bytes: b.bytes,
        time: b.time,
        array_builder: b.array_builder,
        hash_builder: b.hash_builder,
        string_builder: b.string_builder,
        set_builder: b.set_builder,
        bytes_builder: b.bytes_builder,
        match_data: b.match_data,
        bytes_match_data: b.bytes_match_data,
        standard_error,
    };
    let _ = types::ClassId::default();
    let mut file_mains: Vec<Option<ClassId>> = Vec::new();
    for (id, c) in world.classes.iter().enumerate() {
        if c.kind == ClassKind::Main {
            if file_mains.len() <= c.file as usize {
                file_mains.resize(c.file as usize + 1, None);
            }
            file_mains[c.file as usize] = Some(id as ClassId);
        }
    }
    let mut rt = RtWorld {
        classes,
        methods,
        consts: Vec::new(),
        extensions,
        // (The checker's witness record, which the abstract keys of the
        // rows read, #536 step 3's S2.)
        witness_record: record,
        override_rows: Vec::new(),
        witness_rows: Vec::new(),
        class_override_rows: Vec::new(),
        include_overrides: world.include_overrides(),
        top,
        builtin,
        file_names: Vec::new(),
        file_mains,
        // (Per round, `fill`.)
        deferred_conformance: Vec::new(),
    };
    rt.class_override_rows = class_override_rows(world, &rt, table);
    rt.build_witness_rows();
    rt
}

/// The rows of `RtWorld::class_override_rows`: for every key
/// `RtWorld::in_class_override_rows` admits, what a call of the method on
/// the class object runs, by `World::class_method_target` over the
/// override table the methods ship (`table`). The candidates are the class
/// methods of each class object's ancestors and the instance methods of
/// `Type`'s classes named like a class method of its class side; the
/// predicate decides which are keys.
fn class_override_rows(
    world: &World,
    rt: &RtWorld,
    table: &[Vec<MethodId>],
) -> Vec<(ClassId, MethodId, MethodId)> {
    let type_owners = rt.type_side_owners();
    let mut rows: Vec<(ClassId, MethodId, MethodId)> = Vec::new();
    for cid in 0..rt.classes.len() as ClassId {
        rows.extend(class_override_rows_of(world, rt, table, &type_owners, cid));
    }
    rows.sort_unstable();
    rows
}

/// The rows of `class_override_rows` whose class object is `cid`, with
/// `type_owners` (`RtWorld::type_side_owners`) computed once by the
/// caller. Sorted by method; none for a file's top level.
pub fn class_override_rows_of(
    world: &World,
    rt: &RtWorld,
    table: &[Vec<MethodId>],
    type_owners: &[ClassId],
    cid: ClassId,
) -> Vec<(ClassId, MethodId, MethodId)> {
    let method = |id: MethodId| &rt.methods[id as usize];
    let overrides = |m: MethodId| table[m as usize].clone();
    let mut rows: Vec<(ClassId, MethodId, MethodId)> = Vec::new();
    let c = rt.class(cid);
    if c.kind == RtClassKind::Main {
        return rows;
    }
    let mut cands: Vec<MethodId> = Vec::new();
    for &o in std::iter::once(&cid).chain(c.ancestors.iter()) {
        cands.extend(rt.class(o).singleton_methods.values().flatten().copied());
    }
    // (`Type`'s classes' instance methods named like a class method on
    // the class side: each name looked up in their tables.)
    for name in c
        .class_side
        .iter()
        .flat_map(|k| rt.class(*k).singleton_methods.keys())
    {
        for &t in type_owners {
            if let Some(ids) = rt.class(t).methods.get(name) {
                cands.extend(ids.iter().copied().filter(|&m| method(m).owner == t));
            }
        }
    }
    cands.sort_unstable();
    cands.dedup();
    for b in cands {
        if rt.in_class_override_rows_with(&method, Some(type_owners), cid, b) {
            rows.push((cid, b, world.class_method_target(&overrides, cid, b)));
        } else {
            // (Outside the set a call runs the method itself: the
            // function must agree, or the key set and the function
            // have drifted apart.)
            debug_assert_eq!(
                world.class_method_target(&overrides, cid, b),
                b,
                "internal error: `{}` on `{}` is outside the class override rows, \
                     but class_method_target replaces it",
                rt.methods[b as usize].name,
                c.name
            );
        }
    }
    rows.sort_unstable();
    rows
}

/// Whether a positional parameter of `m` follows the one named `name`.
fn later_positional(m: &types::MethodInfo, name: &str) -> bool {
    m.params
        .iter()
        .skip_while(|p| p.name != name)
        .skip(1)
        .any(|p| p.kind == ParamKind::Positional)
}

/// A default written as a literal, as a constant: what a native's
/// skipped parameter takes (`RtParam::default`), and what a `data`
/// construction fills in for its omitted fields (`FnBuilder`'s
/// `fill_literal_defaults`, #921).
pub(crate) fn literal_constant(e: &quarz_syntax::ast::Expr) -> Option<Constant> {
    use quarz_syntax::ast::ExprKind;
    Some(match &e.kind {
        ExprKind::Nil => Constant::Nil,
        ExprKind::True => Constant::Bool(true),
        ExprKind::False => Constant::Bool(false),
        ExprKind::Int(i) => Constant::Int(i.value?),
        ExprKind::Float(f) => Constant::Float(*f),
        ExprKind::Symbol(s) => Constant::Symbol(s.clone()),
        _ => return None,
    })
}

/// A parameter's machine kind (`RtParam::ty`), from the class id: `Int`,
/// `Float`, `Bool` or `Nil` for a parameter declared of that built-in
/// class with no type arguments, `None` for any other type. The set is
/// what the readers match, and no more:
/// - `verify` (an `Int`/`Float` `BinOp`'s right operand through
///   `has_type`, which answers for no other name; an `Arg`): `Int`,
///   `Float`;
/// - `quarz_ir::live::numeric_param_of`: `Int`, `Float`;
/// - the AOT's `unbox`: `bin_types` and `param_num` `Int`, `Float`;
///   `param_bool` `Bool`; `Mach::of` for `typed_sigs`' parameters `Int`,
///   `Float`, `Bool`, `Nil` (`Nil`, as `None`, is boxed there).
fn rt_kind(world: &World, t: &Type) -> Option<String> {
    let b = &world.builtin;
    match t {
        Type::Class(c, args) if args.is_empty() => [
            (b.int, "Int"),
            (b.float, "Float"),
            (b.bool_, "Bool"),
            (b.nil, "Nil"),
        ]
        .iter()
        .find(|(k, _)| k == c)
        .map(|(_, name)| name.to_string()),
        _ => None,
    }
}

/// The classes `t` names (as instances or as class objects).
fn classes_in(t: &Type, out: &mut Vec<ClassId>) {
    match t {
        Type::Class(c, args) | Type::ClassObject(c, args) => {
            out.push(*c);
            for a in args {
                classes_in(a, out);
            }
        }
        Type::TypeOf(t) => classes_in(t, out),
        Type::Union(ts) | Type::Tuple(ts) => {
            for t in ts {
                classes_in(t, out);
            }
        }
        Type::Proc(recv, params, ret, _, kws) => {
            if let Some(r) = recv {
                classes_in(r, out);
            }
            for p in params.iter().chain(kws.iter().map(|k| &k.ty)) {
                classes_in(p, out);
            }
            classes_in(ret, out);
        }
        Type::Nothing | Type::Void | Type::Param(_) | Type::Var(_) => {}
    }
}
