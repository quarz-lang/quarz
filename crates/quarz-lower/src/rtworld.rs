//! `World` (the checker's view) → `RtWorld` (what the runtime needs).

use std::collections::HashMap;

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
        Type::Proc(_, _) => RtType::Proc,
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
            let fields = world
                .all_fields(c.id)
                .into_iter()
                .enumerate()
                .map(|(i, (f, _))| RtField {
                    name: f.name,
                    default: lw.field_default_funcs.get(&(c.id, i)).copied(),
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
                methods: c.methods.clone(),
                members,
                variants: c.variants.clone(),
                variant_of: c.variant_of,
                structural: matches!(c.kind, ClassKind::Data | ClassKind::Variant),
                is_exception: world.is_exception_class(c.id),
                file: c.file,
            }
        })
        .collect();
    let methods: Vec<RtMethod> = world
        .methods
        .iter()
        .map(|m| {
            let owner = world.class(m.owner);
            let overloaded = owner.methods.get(&m.name).is_some_and(|ids| ids.len() > 1);
            let overridden = lw.overridden.contains(&(m.owner, m.name.clone()));
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
                methods: e.methods.clone(),
            });
        }
    }
    let top: HashMap<String, ClassId> = world
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
