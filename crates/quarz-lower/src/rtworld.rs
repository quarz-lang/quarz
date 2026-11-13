//! `World` (the checker's view) → `RtWorld` (what the runtime needs).

use quarz_ir::*;
use quarz_syntax::ast::ParamKind;
use quarz_types::{self as types, ClassKind, Member, Synth, Type, World};

use crate::Lowerer;

pub fn rt_type(t: &Type) -> RtType {
    match t {
        Type::Nothing => RtType::Nothing,
        Type::Class(id, _) => RtType::Class(*id),
        Type::ClassObject(_, _) | Type::TypeOf(_) => RtType::ClassObject,
        Type::Union(ms) => RtType::Union(ms.iter().map(rt_type).collect()),
        Type::Tuple(ts) => RtType::Tuple(vec![RtType::Any; ts.len()]),
        Type::Proc(..) => RtType::Proc,
        Type::Param(_) | Type::Var(_) => RtType::Any,
        // Only a result (no value's type), so never tested.
        Type::Void => RtType::Any,
    }
}

/// `t` for `as`/`is_a?`: with the elements of built-in collections and
/// tuples checked too (`xs.as(Array[String])`), which their values carry;
/// the checker refuses other type arguments it cannot vouch for.
pub fn rt_type_checked(world: &World, t: &Type) -> RtType {
    let b = &world.builtin;
    match t {
        Type::Class(id, args)
            if [b.array, b.set, b.hash, b.range].contains(id)
                && args.iter().any(|a| !trivial(world, a)) =>
        {
            RtType::Elems(
                *id,
                args.iter().map(|a| rt_type_checked(world, a)).collect(),
            )
        }
        // A class value of a class without type parameters: tested for
        // the class (`Type[Model]`; the checker refuses a generic one).
        Type::ClassObject(id, _) if *id != b.object => RtType::ClassOf(*id),
        Type::Union(ms) => RtType::Union(ms.iter().map(|m| rt_type_checked(world, m)).collect()),
        Type::Tuple(ts) => RtType::Tuple(ts.iter().map(|m| rt_type_checked(world, m)).collect()),
        _ => rt_type(t),
    }
}

fn trivial(world: &World, t: &Type) -> bool {
    matches!(t, Type::Param(_) | Type::Var(_))
        || matches!(t, Type::Class(id, _) if *id == world.builtin.object)
}

fn param_kind(k: ParamKind) -> RtParamKind {
    match k {
        ParamKind::Positional => RtParamKind::Positional,
        ParamKind::Rest => RtParamKind::Rest,
        ParamKind::KeywordOnly => RtParamKind::KeywordOnly,
        ParamKind::KeywordRest => RtParamKind::KeywordRest,
        ParamKind::Block => RtParamKind::Block,
    }
}

/// The runtime's world for a lowering round: what the declarations decide
/// (`declared`), then what the lowering made (`fill`).
pub fn build(world: &World, out: &types::Output, lw: &Lowerer, file_names: Vec<String>) -> RtWorld {
    let mut rt = declared(world, out);
    fill(&mut rt, world, lw, file_names);
    rt
}

/// What the lowering adds to `declared`'s tables: the classes' fields and
/// their defaults (the layouts), each method's function and whether it is
/// overridden, the constants' functions and the quoted blocks' trees, the
/// file names. Nothing `declared`'s rows read.
pub fn fill(rt: &mut RtWorld, world: &World, lw: &Lowerer, file_names: Vec<String>) {
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
        let key = if m.singleton {
            format!("self.{}", m.name)
        } else {
            m.name.clone()
        };
        rm.overridden |= lw.overridden.contains(&(m.owner, key));
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
/// them (`rescan_extensions`, `build_witness_rows`): the classes'
/// ancestors, lookup, class side and methods, the methods' signatures and
/// override table, the extensions and their witnesses. Built once per
/// program after its check (`Lowerer::declare`, where the safety net
/// reads the rows) and completed by the lowering (`fill`); the lowering's
/// fields are empty here.
pub fn declared(world: &World, out: &types::Output) -> RtWorld {
    let classes: Vec<RtClass> = world
        .classes
        .iter()
        .map(|c| {
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
                module_init: !world.has_fields_to_assign(c.id, true),
                inherited_inits: out
                    .inherited_inits
                    .iter()
                    .filter(|(sub, _, _)| *sub == c.id)
                    .map(|(_, init, chosen)| (*init, *chosen))
                    .collect(),
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
                // (The declared view: an extension's conformance brings
                // witnesses, `class_ext_impls`, not dispatch, #504.)
                class_side: world
                    .resolution(c.id, &[], quarz_types::world::View::Declared)
                    .into_iter()
                    .map(|(m, _)| m)
                    .collect(),
                built_by_runtime: world.built_by_runtime(c.id),
                members,
                variants: c.variants.clone(),
                variant_of: c.variant_of,
                structural: matches!(c.kind, ClassKind::Data | ClassKind::Variant),
                // (A file's top-level `def`s are functions, not its
                // object's `==`.)
                declares_eq_hash: c.kind != ClassKind::Main
                    && ["==", "hash"].iter().any(|n| {
                        c.methods.get(*n).is_some_and(|ms| {
                            ms.iter().any(|m| {
                                let m = world.method(*m);
                                !m.singleton && !m.is_native && m.body.is_some()
                            })
                        })
                    }),
                is_exception: world.is_exception_class(c.id),
                is_abstract: c.is_abstract,
                objects: world.instances_are_objects(c.id),
                file: c.file,
                cog: c.cog.map(|i| {
                    let info = &world.cogs[i as usize];
                    (info.name.clone(), info.version.clone())
                }),
            }
        })
        .collect();
    // (The override table, once, #536.)
    let table = world.override_table();
    let methods: Vec<RtMethod> = world
        .methods
        .iter()
        .map(|m| {
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
            let fast_op = if m.is_native
                && (m.owner == world.builtin.int || m.owner == world.builtin.float)
            {
                FastOp::from_name(&m.name)
            } else {
                None
            };
            RtMethod {
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
                        ty: rt_sig_type(world, m, &p.ty),
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
                block_ty: m.block.as_ref().and_then(|(_, t)| rt_sig_type(world, m, t)),
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
                overrides: table[m.id as usize].clone(),
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
            }
        })
        .collect();
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
        ext_impls: {
            // One witness per (class, requirement): the declarer records
            // one where a class's own conformance is checked and R0 one
            // where an extension's is (#632); were they two methods,
            // `find_override` would take whichever came first.
            #[cfg(debug_assertions)]
            for (k, &(c, a, i)) in world.ext_impls.iter().enumerate() {
                if let Some(&(_, _, j)) = world.ext_impls[..k]
                    .iter()
                    .find(|(c2, a2, j)| *c2 == c && *a2 == a && *j != i)
                {
                    panic!(
                        "internal error: two witnesses recorded for `{}`'s `{}`: `{}` and `{}`",
                        world.class(c).name,
                        world.method(a).name,
                        world.method(j).name,
                        world.method(i).name
                    );
                }
            }
            world.ext_impls.clone()
        },
        class_ext_impls: world
            .class_ext_impls
            .iter()
            .map(|w| (w.class, w.method, w.by))
            .collect(),
        ext_rescan: Vec::new(),
        override_rows: Vec::new(),
        witness_rows: Vec::new(),
        class_override_rows: Vec::new(),
        include_overrides: world.include_overrides(),
        class_include_overrides: world.class_include_overrides(),
        top,
        builtin,
        file_names: Vec::new(),
        file_mains,
    };
    // (The scan of the extensions the interpreter made at run time, made
    // once: `RtWorld::ext_rescan`.)
    rt.rescan_extensions();
    rt.build_witness_rows();
    witness_oracle(world, &rt);
    rt
}

/// S1's oracle (#536 step 3), in debug builds: the witness record
/// (`World::witness_record`) against what the run time's rows run
/// (`override_rows`), each record entry resolved for its class as
/// `find_override` resolves a recorded class or module method. Every
/// disagreement is an internal error, except the two families S2 changes
/// (the record is right there; the rows' answer is the bug), told by
/// their shape:
/// - #529: the record's witness and the row are methods of the same name
///   of two different extensions of the same target;
/// - #662: the class has the requirement's module on its own side (the
///   record's conformance is the class's own) and the row is an
///   extension's own method, scoped or top-level.
///
/// `QUARZ_WITNESS_ORACLE=report` prints every disagreement and the
/// counts, the excluded ones by family (a test counts them, so that S2
/// shows them gone). Release builds compute nothing here.
fn witness_oracle(world: &World, rt: &RtWorld) {
    let report = std::env::var("QUARZ_WITNESS_ORACLE").as_deref() == Ok("report");
    if !cfg!(debug_assertions) && !report {
        return;
    }
    let method = |id: MethodId| &rt.methods[id as usize];
    let name = |m: MethodId| {
        let mi = world.method(m);
        format!("{}#{}", world.class(mi.owner).name, mi.name)
    };
    let (mut ext_n, mut own_n, mut ext_bad, mut own_bad, mut ex_529, mut ex_662) =
        (0, 0, 0, 0, 0, 0);
    for (c, r, w, ext) in world.witness_record() {
        // (What runs for the key: the override row, `find_override`'s
        // answer; only keys the rows have, a class whose values exist.)
        if rt.witness_row(c, r).is_none() {
            continue;
        }
        let row = rt.override_row(c, r).filter(|&m| m != r);
        // (A recorded class or module method, resolved for the class as
        // `find_override` resolves it.)
        let expected = w.map(|w| {
            if method(w).is_extension || method(w).is_abstract {
                w
            } else {
                rt.find_override(&method, c, w).unwrap_or(w)
            }
        });
        if ext.is_some() {
            ext_n += 1;
        } else {
            own_n += 1;
        }
        if row == expected {
            continue;
        }
        let ext_of = |m: MethodId| world.method(m).extension;
        let family = match (expected, row) {
            (Some(a), Some(b))
                if ext_of(a).zip(ext_of(b)).is_some_and(|(x, y)| {
                    x != y
                        && world.extensions[x as usize].target
                            == world.extensions[y as usize].target
                        && world.method(a).name == world.method(b).name
                }) =>
            {
                Some(529)
            }
            (_, Some(b)) if ext.is_none() && ext_of(b).is_some() => Some(662),
            _ => None,
        };
        let kind = if ext.is_some() { "ext" } else { "own" };
        let line = format!(
            "witness-oracle: [{kind}] {} {}: record {}, rows {}",
            world.class(c).name,
            name(r),
            expected.map_or("none".to_string(), name),
            row.map_or("none".to_string(), name)
        );
        match family {
            Some(529) => ex_529 += 1,
            Some(_) => ex_662 += 1,
            None => {
                if ext.is_some() {
                    ext_bad += 1;
                } else {
                    own_bad += 1;
                }
                if !report {
                    panic!("internal error: the witness record and the rows disagree: {line}");
                }
            }
        }
        if report {
            let tag = family.map_or(String::new(), |f| format!("  [excluded: #{f}]"));
            eprintln!("{line}{tag}");
        }
    }
    if report {
        eprintln!(
            "witness-oracle: summary  ext {ext_bad}/{ext_n} disagree, own {own_bad}/{own_n} disagree, excluded #529 {ex_529}, #662 {ex_662}"
        );
    }
}

/// Whether a positional parameter of `m` follows the one named `name`.
fn later_positional(m: &types::MethodInfo, name: &str) -> bool {
    m.params
        .iter()
        .skip_while(|p| p.name != name)
        .skip(1)
        .any(|p| p.kind == ParamKind::Positional)
}

/// A default written as a literal, as a constant.
fn literal_constant(e: &quarz_syntax::ast::Expr) -> Option<Constant> {
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

/// A parameter's type as `same_signature` compares it: `None`, which
/// matches anything, where it mentions one of the method's own type
/// parameters or `Self` (another method names them otherwise); a class's
/// type parameter is compared by name, the substituted relation
/// (`overridden_methods`) deciding across instantiations.
fn rt_sig_type(world: &World, m: &types::MethodInfo, t: &Type) -> Option<String> {
    fn open(m: &types::MethodInfo, t: &Type) -> bool {
        match t {
            Type::Param(p) => {
                *p == quarz_types::declare::SELF_PARAM || m.type_params.iter().any(|tp| tp.id == *p)
            }
            Type::Var(_) => true,
            Type::Class(_, args) | Type::ClassObject(_, args) => args.iter().any(|a| open(m, a)),
            Type::Union(ts) | Type::Tuple(ts) => ts.iter().any(|a| open(m, a)),
            Type::TypeOf(t) => open(m, t),
            Type::Proc(r, ps, ret, _, kws) => {
                r.as_deref().is_some_and(|r| open(m, r))
                    || ps.iter().any(|a| open(m, a))
                    || open(m, ret)
                    || kws.iter().any(|k| open(m, &k.ty))
            }
            Type::Nothing | Type::Void => false,
        }
    }
    if open(m, t) {
        None
    } else if t.mentions_any_param() {
        // (A class's type parameter is that class's: by its id, so that a
        // `T` of another class is another type.)
        Some(format!("{:?}", world.devoid(t)))
    } else {
        Some(world.type_name(&world.devoid(t)))
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
