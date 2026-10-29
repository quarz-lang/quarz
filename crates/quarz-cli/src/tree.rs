//! `quarz check --tree`: a checked program as JSON, for the differential
//! tests of the Lean model of the checker's core (`formal/quarz-core`).
//! Not for users: the format changes with the model, without notice.
//!
//! What it holds: each unit's syntax tree as parsed (the AST's own serde
//! form) and the definitions of the methods they define, the type the
//! checker gave each of their nodes (a variable read's
//! is the type it is narrowed to there; constants' initializers and field
//! defaults are there too), the nodes checked more than once with
//! different types, the expansion each `for` was checked as, what each call resolved to and
//! each constant read names, every class (the
//! built-in ones included: types refer to classes by id), and the
//! methods the units define or call, with their type parameters (and the
//! parameters a class test made, `T & C`: `narrowed_params`; the
//! extensions' too, and the id `Self` goes by). Which
//! programs are in the model's range is for the Lean side to judge.

use serde_json::{json, Map, Value};

use quarz_types::check::{CallTarget, ConstTarget};
use quarz_types::declare::SELF_PARAM;
use quarz_types::types::{MethodId, Type};
use quarz_types::world::{TypeParamInfo, World};
use quarz_types::Checked;

/// The version of the format, bumped when it changes.
const FORMAT: u32 = 4;

pub fn tree(checked: &Checked) -> Value {
    let world = &checked.world;
    let out = &checked.output;
    let units: Vec<Value> = checked
        .units
        .iter()
        .map(|u| {
            json!({
                "file": u.file,
                "name": u.name,
                "main_class": u.main_class,
                "body": serde_json::to_value(&u.body).unwrap_or(Value::Null),
            })
        })
        .collect();
    // The methods the units define (with their definitions: a unit's
    // body holds its top-level statements only).
    let files: Vec<u32> = checked.units.iter().map(|u| u.file).collect();
    let defined: Vec<MethodId> = world
        .methods
        .iter()
        .filter(|m| files.contains(&m.file))
        .map(|m| m.id)
        .collect();
    let defs: Vec<Value> = defined
        .iter()
        .map(|id| match &world.method(*id).body {
            Some(def) => serde_json::to_value(&**def).unwrap_or(Value::Null),
            None => Value::Null,
        })
        .collect();
    // Their constants' initializers and their classes' field defaults,
    // checked apart from the bodies too.
    let consts: Vec<Value> = world
        .consts
        .iter()
        .filter(|c| files.contains(&c.file))
        .map(|c| {
            json!({
                "id": c.id,
                "name": c.name,
                "owner": c.owner,
                "type": c.ty.as_ref().map(ty),
                "value": c.value.as_deref().map(|e| serde_json::to_value(e).unwrap_or(Value::Null)),
            })
        })
        .collect();
    let defaults: Vec<Value> = world
        .classes
        .iter()
        .filter(|c| files.contains(&c.file))
        .flat_map(|c| {
            c.fields.iter().filter_map(move |f| {
                let d = f.default.as_deref()?;
                Some(json!({
                    "class": c.id,
                    "field": f.name,
                    "value": serde_json::to_value(d).unwrap_or(Value::Null),
                }))
            })
        })
        .collect();
    // The nodes of all of these: their types and calls.
    let mut ids = Vec::new();
    for u in &units {
        node_ids(&u["body"], &mut ids);
    }
    for d in defs.iter().chain(&consts).chain(&defaults) {
        node_ids(d, &mut ids);
    }
    ids.sort_unstable();
    ids.dedup();
    let mut node_types = Map::new();
    let mut calls = Map::new();
    let mut const_targets = Map::new();
    let mut methods: Vec<MethodId> = Vec::new();
    for &id in &ids {
        let id32 = id as u32;
        if let Some(t) = out.node_types.get(&id32) {
            node_types.insert(id.to_string(), ty(t));
        }
        if let Some(c) = out.calls.get(&id32) {
            calls.insert(id.to_string(), call(c, &mut methods));
        }
        if let Some(t) = out.const_targets.get(&id32) {
            let (kind, n) = match t {
                ConstTarget::Const(n) => ("const", *n),
                ConstTarget::Class(n) => ("class", *n),
                ConstTarget::VariantSingleton(n) => ("variant", *n),
            };
            const_targets.insert(id.to_string(), json!({ "t": kind, "id": n }));
        }
    }
    let among = |set: &dyn Fn(u32) -> bool| -> Vec<u64> {
        ids.iter().copied().filter(|id| set(*id as u32)).collect()
    };
    let varied = among(&|id| out.varied_types.contains(&id));
    // A `for` holds both its expansions; these were checked as `each`,
    // the others as `comprehension` (the other's nodes have no types).
    let for_each = among(&|id| out.for_loops.contains(&id));
    let definitions: Vec<Value> = defined
        .iter()
        .zip(defs)
        .map(|(id, d)| json!({ "method": id, "def": d }))
        .collect();
    // The methods the units define, and those they call.
    methods.extend(&defined);
    methods.sort_unstable();
    methods.dedup();
    json!({
        "format": FORMAT,
        "units": units,
        "node_types": node_types,
        "varied_types": varied,
        "for_each": for_each,
        "calls": calls,
        "const_targets": const_targets,
        "classes": classes(world),
        "methods": methods.iter().map(|m| method(world, *m)).collect::<Vec<_>>(),
        "definitions": definitions,
        "consts": consts,
        "field_defaults": defaults,
        "narrowed_params": narrowed_params(world),
        "extensions": extensions(world),
        // `Self` in a signature, a type parameter of its own.
        "self_param": SELF_PARAM,
    })
}

/// The extensions, with their type parameters (an extension's method
/// names them: `methods[].extension`) and what they extend.
fn extensions(world: &World) -> Vec<Value> {
    world
        .extensions
        .iter()
        .map(|e| {
            json!({
                "id": e.id,
                "target": e.target,
                "type_params": e.type_params.iter().map(type_param).collect::<Vec<_>>(),
                "target_args": e.target_args.iter().map(ty).collect::<Vec<_>>(),
            })
        })
        .collect()
}

/// A type parameter: its id (what `Type::Param` names), name, variance
/// and bounds; a method's may have a lower bound (`U >: T`).
fn type_param(p: &TypeParamInfo) -> Value {
    json!({
        "id": p.id,
        "name": p.name,
        "variance": format!("{:?}", p.variance),
        "bounds": p.bounds.iter().map(ty).collect::<Vec<_>>(),
        "lower": p.lower.as_ref().map(ty),
    })
}

/// The type parameters a class test made (`x.is_a?(C)` on an `x: T`
/// gives `x` the type `T & C`): each with the parameter it narrows and
/// the bounds it adds.
fn narrowed_params(world: &World) -> Vec<Value> {
    let mut all: Vec<Value> = world
        .narrowed_params()
        .map(|(id, bounds)| {
            json!({
                "id": id,
                "name": world.type_param_name(id),
                "bounds": bounds.iter().map(ty).collect::<Vec<_>>(),
            })
        })
        .collect();
    all.sort_by_key(|v| v["id"].as_u64());
    all
}

/// The ids of the expressions in a serialized tree (objects with an
/// `id`, a `span` and a `kind`).
fn node_ids(v: &Value, ids: &mut Vec<u64>) {
    match v {
        Value::Object(o) => {
            if let (Some(Value::Number(n)), true, true) =
                (o.get("id"), o.contains_key("span"), o.contains_key("kind"))
            {
                if let Some(n) = n.as_u64() {
                    ids.push(n);
                }
            }
            for x in o.values() {
                node_ids(x, ids);
            }
        }
        Value::Array(a) => {
            for x in a {
                node_ids(x, ids);
            }
        }
        _ => {}
    }
}

/// A type, structurally: classes by id (see `classes`).
fn ty(t: &Type) -> Value {
    let all = |ts: &[Type]| ts.iter().map(ty).collect::<Vec<_>>();
    match t {
        Type::Nothing => json!({ "t": "nothing" }),
        Type::Void => json!({ "t": "void" }),
        Type::Class(id, args) => json!({ "t": "class", "id": id, "args": all(args) }),
        Type::ClassObject(id, args) => {
            json!({ "t": "class_object", "id": id, "args": all(args) })
        }
        Type::TypeOf(inner) => json!({ "t": "type_of", "of": ty(inner) }),
        Type::Union(ms) => json!({ "t": "union", "members": all(ms) }),
        Type::Tuple(ms) => json!({ "t": "tuple", "members": all(ms) }),
        Type::Proc(recv, params, ret, shareable) => json!({
            "t": "proc",
            "recv": recv.as_deref().map(ty),
            "params": all(params),
            "ret": ty(ret),
            "shareable": shareable,
        }),
        Type::Param(id) => json!({ "t": "param", "id": id }),
        Type::Var(v) => json!({ "t": "var", "id": format!("{v:?}") }),
    }
}

fn call(c: &CallTarget, methods: &mut Vec<MethodId>) -> Value {
    match c {
        CallTarget::Method { method } => {
            methods.push(*method);
            json!({ "t": "method", "method": method })
        }
        CallTarget::Super { method } => {
            methods.push(*method);
            json!({ "t": "super", "method": method })
        }
        CallTarget::Constructor { class, init } => {
            methods.extend(init);
            json!({ "t": "constructor", "class": class, "init": init })
        }
        CallTarget::ProcCall => json!({ "t": "proc_call" }),
        CallTarget::IsA(t) => json!({ "t": "is_a", "type": ty(t) }),
        CallTarget::As { ty: t, optional } => {
            json!({ "t": "as", "type": ty(t), "optional": optional })
        }
        CallTarget::Constant(b) => json!({ "t": "constant", "value": b }),
        CallTarget::Raise => json!({ "t": "raise" }),
    }
}

fn classes(world: &World) -> Vec<Value> {
    world
        .classes
        .iter()
        .map(|c| {
            json!({
                "id": c.id,
                "name": c.name,
                "kind": format!("{:?}", c.kind),
                "file": c.file,
                "type_params": c.type_params.iter().map(type_param).collect::<Vec<_>>(),
                "superclass": c.superclass.as_ref().map(ty),
                "includes": c.includes.iter().map(ty).collect::<Vec<_>>(),
                "fields": c.fields.iter().map(|f| json!({
                    "name": f.name,
                    "type": ty(&f.ty),
                    "var": f.mutable,
                    "default": f.default.is_some(),
                })).collect::<Vec<_>>(),
            })
        })
        .collect()
}

fn method(world: &World, id: MethodId) -> Value {
    let m = world.method(id);
    json!({
        "id": m.id,
        "name": m.name,
        "owner": m.owner,
        "singleton": m.singleton,
        "file": m.file,
        "native": m.is_native,
        // Made by the checker (a data constructor, a field reader...):
        // no definition.
        "synth": format!("{:?}", m.synth),
        "type_params": m.type_params.iter().map(type_param).collect::<Vec<_>>(),
        "extension": m.extension,
        "params": m.params.iter().map(|p| json!({
            "name": p.name,
            "kind": format!("{:?}", p.kind),
            "type": ty(&p.ty),
            "default": p.default.is_some(),
            "assigns_ivar": p.assigns_ivar,
        })).collect::<Vec<_>>(),
        "block": m.block.as_ref().map(|(name, t)| json!({ "name": name, "type": ty(t) })),
        "block_optional": m.block_optional,
        "ret": ty(&m.ret),
        // Generated by a `static` statement (docs/14 §5): its body is a
        // block of the `static def` the statement called, not here.
        "generated": m.generated.is_some(),
    })
}
