//! `World` (the checker's view) → `RtWorld` (what the runtime needs).

use quarz_ir::*;
use quarz_syntax::ast::ParamKind;
use quarz_types::{self as types, ClassKind, Member, Synth, Type, World};

use crate::Lowerer;

pub fn rt_type(t: &Type) -> RtType {
    match t {
        Type::Nothing => RtType::Nothing,
        Type::Class(id, _) => RtType::Class(*id),
        Type::ClassObject(_, _) => RtType::ClassObject,
        Type::Union(ms) => RtType::Union(ms.iter().map(rt_type).collect()),
        Type::Tuple(ts) => RtType::Tuple(ts.len() as u32),
        Type::Proc(..) => RtType::Proc,
        Type::Param(_) | Type::Var(_) => RtType::Any,
    }
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

pub fn build(world: &World, lw: &Lowerer, file_names: Vec<String>) -> RtWorld {
    let classes: Vec<RtClass> = world
        .classes
        .iter()
        .map(|c| {
            let layout = &lw.layouts[c.id as usize];
            let ty_name = |t: &Type| match t {
                Type::Param(_) | Type::Var(_) => None,
                t => Some(world.type_name(t)),
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
                    default: lw.field_default_funcs.get(&(c.id, i)).copied(),
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
                ancestors: world
                    .ancestors(c.id, &[])
                    .into_iter()
                    .map(|(id, _)| id)
                    .collect(),
                fields,
                ivars,
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
                extends: c
                    .extends
                    .iter()
                    .filter_map(|t| match t {
                        Type::Class(id, _) => Some(*id),
                        _ => None,
                    })
                    .collect(),
                members,
                variants: c.variants.clone(),
                variant_of: c.variant_of,
                structural: matches!(c.kind, ClassKind::Data | ClassKind::Variant),
                is_exception: world.is_exception_class(c.id),
                is_abstract: c.is_abstract,
                objects: world.instances_are_objects(c.id),
                file: c.file,
            }
        })
        .collect();
    let mut ancestors = HashMap::default();
    let methods: Vec<RtMethod> = world
        .methods
        .iter()
        .map(|m| {
            let owner = world.class(m.owner);
            let overloaded = owner.methods.get(&m.name).is_some_and(|ids| ids.len() > 1);
            // An abstract method is always dispatched dynamically: its
            // implementation may be a singleton method of a class that
            // extends the module, which the class hierarchy walk does not see.
            // A class method is dispatched on the class it is called on
            // (`Circle.describe` runs `Circle.label` for an implicit
            // `label` in `Shape.describe`).
            let key = if m.singleton {
                format!("self.{}", m.name)
            } else {
                m.name.clone()
            };
            let overridden = m.is_abstract || lw.overridden.contains(&(m.owner, key));
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
                        ty: match &p.ty {
                            Type::Param(_) | Type::Var(_) => None,
                            t => Some(world.type_name(t)),
                        },
                    })
                    .collect(),
                has_block: m.block.is_some(),
                func: lw.method_funcs.get(m.id as usize).copied().flatten(),
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
                    types::RetType::Known(t) => match t {
                        Type::Param(_) | Type::Var(_) => None,
                        t => Some(world.type_name(t)),
                    },
                    _ => None,
                },
                overrides: overridden_methods(world, m, &mut ancestors),
                makes: if m.is_native {
                    let mut out = Vec::new();
                    if let types::RetType::Known(t) = &m.ret {
                        classes_in(t, &mut out);
                    }
                    if let Some((_, t)) = &m.block {
                        classes_in(t, &mut out);
                    }
                    out.sort_unstable();
                    out.dedup();
                    out
                } else {
                    Vec::new()
                },
            }
        })
        .collect();
    let consts: Vec<RtConst> = world
        .consts
        .iter()
        .map(|c| RtConst {
            name: c.name.clone(),
            owner: c.owner,
            init: lw.const_funcs.get(c.id as usize).copied().flatten(),
            file: c.file,
        })
        .collect();
    // Every extension takes part in dynamic dispatch (a module method
    // implemented for a class by an extension is found through it);
    // the always-active ones come first.
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
    RtWorld {
        classes,
        methods,
        consts,
        extensions,
        top,
        builtin,
        file_names,
    }
}

/// The methods of `m`'s ancestors that `m` overrides: same name, kind of
/// method, parameters (plus optional ones) and block, with each parameter
/// accepting what the ancestor's does (its types instantiated for `m`'s class). A method of
/// the same name that narrows a parameter (`cmp(other: W)` in `W < V`
/// next to `cmp(other: V)`) is an overload, not an override.
fn overridden_methods(
    world: &World,
    m: &types::MethodInfo,
    ancestors: &mut HashMap<ClassId, Vec<(ClassId, Vec<Type>)>>,
) -> Vec<MethodId> {
    // The owner's ancestors with its own type parameters, once per class
    // (the world does not change while the runtime one is built).
    let ancs = ancestors.entry(m.owner).or_insert_with(|| {
        let own_args: Vec<Type> = world
            .class(m.owner)
            .type_params
            .iter()
            .map(|tp| Type::Param(tp.id))
            .collect();
        world.ancestors(m.owner, &own_args)
    });
    let mut out = Vec::new();
    for (anc, anc_args) in ancs.iter() {
        let anc = *anc;
        if anc == m.owner {
            continue;
        }
        let ac = world.class(anc);
        let table = if m.singleton {
            &ac.singleton_methods
        } else {
            &ac.methods
        };
        let Some(ids) = table.get(&m.name) else {
            continue;
        };
        let subst: rustc_hash::FxHashMap<_, _> = ac
            .type_params
            .iter()
            .map(|tp| tp.id)
            .zip(anc_args.iter().cloned())
            .collect();
        for &pid in ids {
            let pm = world.method(pid);
            // The override may add parameters the parent's callers never
            // pass: with defaults, or rest parameters.
            let fits = pm.params.len() <= m.params.len()
                && pm.block.is_some() == m.block.is_some()
                && pm.params.iter().zip(&m.params).all(|(pp, cp)| {
                    let pt = pp.ty.subst(&subst);
                    pp.kind == cp.kind && (pt == cp.ty || world.is_subtype(&pt, &cp.ty))
                })
                && m.params[pm.params.len()..].iter().all(|cp| {
                    cp.default.is_some()
                        || matches!(cp.kind, ParamKind::Rest | ParamKind::KeywordRest)
                });
            if fits {
                out.push(pid);
            }
        }
    }
    out
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
        Type::Union(ts) | Type::Tuple(ts) => {
            for t in ts {
                classes_in(t, out);
            }
        }
        Type::Proc(recv, params, ret, _) => {
            if let Some(r) = recv {
                classes_in(r, out);
            }
            for p in params {
                classes_in(p, out);
            }
            classes_in(ret, out);
        }
        Type::Nothing | Type::Param(_) | Type::Var(_) => {}
    }
}
