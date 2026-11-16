//! What a run-time type test sees (#536 step 7, tmp/plan-536-step7.md):
//! the one place that decides which part of a type a test checks at run
//! time, for the checker (what it may vouch for: `unverifiable`) and for
//! the lowering (the test it emits: `run_time_test`, recorded by the
//! checker per site in `Output::run_time_tests`).
//!
//! A test sees a value's class; the elements of the built-in collections
//! `Array`, `Set`, `Hash` and `Range` and of tuples, which values carry;
//! and, for a class value, its class. Nothing else: no other class's type
//! arguments, no procedure's parameters, no type parameter.
//!
//! (This is the only reason quarz-types depends on quarz-ir: to build an
//! `RtType`. It reads no runtime table, `RtWorld` or instruction.)

use quarz_ir::RtType;

use crate::{Type, World};

/// The built-in collections whose elements a test checks.
fn elements_checked(world: &World, id: crate::ClassId) -> bool {
    let b = &world.builtin;
    [b.array, b.set, b.hash, b.range].contains(&id)
}

/// The run-time test of the class alone (no elements): for a type the
/// static type already decides, and for a union dispatch's members. It is
/// another test, not another encoding of `seen`'s: where the static type
/// decides the answer, the class is all a test needs to see.
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

/// What the run-time test of `t` checks, and whether that is all of `t`
/// (#536 step 7): one traversal, so that the checker vouches for exactly
/// what the test checks. Each arm emits the test of its part and says
/// whether that test sees the part whole:
/// - a built-in collection (`elements_checked`): its elements' tests when
///   one of them checks something (an `Object`, a type parameter or an
///   inference variable checks nothing), complete when every element is;
/// - another class: its class; complete when each argument is `Object`
///   where the parameter admits it (a value of the class is then one);
/// - a class value of a class without type parameters: the class or a
///   subclass (`Type[Model]`), complete; of a generic class, incomplete
///   (a class value carries no arguments); `Type[Object]`: any class value;
/// - a union or a tuple: its members', complete when each is;
/// - a procedure: a procedure, incomplete (its parameters are not seen);
/// - a type parameter, or a class value of one: anything, incomplete (not
///   known at run time);
/// - an inference variable or `Void`: anything, complete (nothing to see);
///   `Nothing`: nothing.
pub fn seen(world: &World, t: &Type) -> (RtType, bool) {
    match t {
        Type::Class(id, args) if elements_checked(world, *id) => {
            let elems: Vec<(RtType, bool)> = args.iter().map(|a| seen(world, a)).collect();
            let complete = elems.iter().all(|(_, c)| *c);
            let test = if args.iter().any(|a| !trivial(world, a)) {
                RtType::Elems(*id, elems.into_iter().map(|(t, _)| t).collect())
            } else {
                RtType::Class(*id)
            };
            (test, complete)
        }
        Type::Class(id, args) => {
            let object = |a: &Type| matches!(a, Type::Class(o, _) if *o == world.builtin.object);
            let complete = args
                .iter()
                .enumerate()
                .all(|(i, a)| object(a) && world.param_admits_object(*id, i));
            (RtType::Class(*id), complete)
        }
        Type::ClassObject(id, _) => {
            let test = if *id == world.builtin.object {
                RtType::ClassObject
            } else {
                RtType::ClassOf(*id)
            };
            (test, world.class(*id).type_params.is_empty())
        }
        Type::Union(ms) => {
            let parts: Vec<(RtType, bool)> = ms.iter().map(|m| seen(world, m)).collect();
            let complete = parts.iter().all(|(_, c)| *c);
            (
                RtType::Union(parts.into_iter().map(|(t, _)| t).collect()),
                complete,
            )
        }
        Type::Tuple(ts) => {
            let parts: Vec<(RtType, bool)> = ts.iter().map(|m| seen(world, m)).collect();
            let complete = parts.iter().all(|(_, c)| *c);
            (
                RtType::Tuple(parts.into_iter().map(|(t, _)| t).collect()),
                complete,
            )
        }
        Type::Proc(..) => (RtType::Proc, false),
        Type::Param(_) => (RtType::Any, false),
        Type::TypeOf(_) => (RtType::ClassObject, false),
        Type::Var(_) | Type::Void => (RtType::Any, true),
        Type::Nothing => (RtType::Nothing, true),
    }
}

/// The run-time test of `t` for `as`/`is_a?` where the static type does
/// not decide it (`seen`'s test).
pub fn run_time_test(world: &World, t: &Type) -> RtType {
    seen(world, t).0
}

/// Whether the run-time test of `t` leaves part of it unchecked (`seen`'s
/// completeness, negated): the checker refuses a test it cannot vouch for.
pub fn unverifiable(world: &World, t: &Type) -> bool {
    !seen(world, t).1
}

/// An element type that needs no check: anything (`Object`), or what the
/// run time does not know (a type parameter, an inference variable).
fn trivial(world: &World, t: &Type) -> bool {
    matches!(t, Type::Param(_) | Type::Var(_))
        || matches!(t, Type::Class(id, _) if *id == world.builtin.object)
}
