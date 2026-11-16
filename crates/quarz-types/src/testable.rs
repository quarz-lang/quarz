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
/// static type already decides, and for a union dispatch's members.
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

/// The run-time test of `t` for `as`/`is_a?` where the static type does
/// not decide it: with the elements of built-in collections and tuples
/// checked too (`xs.as(Array[String])`), and a class value of a class
/// without type parameters tested for the class (`Type[Model]`). The
/// checker refuses the rest (`unverifiable`).
pub fn run_time_test(world: &World, t: &Type) -> RtType {
    match t {
        Type::Class(id, args)
            if elements_checked(world, *id) && args.iter().any(|a| !trivial(world, a)) =>
        {
            RtType::Elems(*id, args.iter().map(|a| run_time_test(world, a)).collect())
        }
        Type::ClassObject(id, _) if *id != world.builtin.object => RtType::ClassOf(*id),
        Type::Union(ms) => RtType::Union(ms.iter().map(|m| run_time_test(world, m)).collect()),
        Type::Tuple(ts) => RtType::Tuple(ts.iter().map(|m| run_time_test(world, m)).collect()),
        _ => rt_type(t),
    }
}

/// An element type that needs no check: anything (`Object`), or what the
/// run time does not know (a type parameter, an inference variable).
fn trivial(world: &World, t: &Type) -> bool {
    matches!(t, Type::Param(_) | Type::Var(_))
        || matches!(t, Type::Class(id, _) if *id == world.builtin.object)
}

/// Whether the run-time test of `t` leaves part of it unchecked: a type
/// parameter as an argument (the elements' `T` is not known at run time),
/// or arguments of a class other than the built-in collections (whose
/// elements are checked), except `Object` for a covariant parameter.
pub fn unverifiable(world: &World, t: &Type) -> bool {
    let object = |a: &Type| matches!(a, Type::Class(id, _) if *id == world.builtin.object);
    match t {
        Type::Class(id, args) if elements_checked(world, *id) => args
            .iter()
            .any(|a| !object(a) && unverifiable_arg(world, a)),
        Type::Class(id, args) => args
            .iter()
            .enumerate()
            .any(|(i, a)| !(object(a) && world.param_admits_object(*id, i))),
        // A class value is tested for its class (`Type[Model]`: a class
        // `<= Model`), not for type arguments, which it does not carry:
        // a generic class (`Type[Box[Int]]`) is refused.
        Type::ClassObject(id, _) => !world.class(*id).type_params.is_empty(),
        Type::Tuple(ts) | Type::Union(ts) => ts.iter().any(|m| unverifiable(world, m)),
        Type::Proc(..) => true,
        // A type parameter is not known at run time (`o.as(T)`).
        Type::Param(_) | Type::TypeOf(_) => true,
        Type::Nothing | Type::Void | Type::Var(_) => false,
    }
}

/// `unverifiable` for a type argument or element type: a type parameter
/// there is not known at run time.
fn unverifiable_arg(world: &World, t: &Type) -> bool {
    match t {
        Type::Param(_) => true,
        Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(|m| unverifiable_arg(world, m)),
        _ => unverifiable(world, t),
    }
}

/// #536 step 7's oracle (debug builds, removed with the old code): `old`
/// equals `new` at a site of `construct`. With `QUARZ_TESTABLE_ORACLE`
/// naming a file, each construct's count is appended there whenever it
/// reaches a power of two.
#[cfg(debug_assertions)]
pub fn oracle<T: PartialEq + std::fmt::Debug>(construct: &'static str, old: T, new: T) {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Mutex, OnceLock};
    assert_eq!(old, new, "#536 step 7 oracle, {construct}");
    static PATH: OnceLock<Option<String>> = OnceLock::new();
    static COUNTS: OnceLock<Mutex<Vec<(&'static str, AtomicU64)>>> = OnceLock::new();
    let Some(path) = PATH.get_or_init(|| std::env::var("QUARZ_TESTABLE_ORACLE").ok()) else {
        return;
    };
    let counts = COUNTS.get_or_init(|| Mutex::new(Vec::new()));
    let n = {
        let mut c = counts.lock().unwrap_or_else(|e| e.into_inner());
        match c.iter().find(|(k, _)| *k == construct) {
            Some((_, n)) => n.fetch_add(1, Ordering::Relaxed) + 1,
            None => {
                c.push((construct, AtomicU64::new(1)));
                1
            }
        }
    };
    if n.is_power_of_two() {
        use std::io::Write as _;
        if let Ok(mut f) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            let _ = writeln!(f, "{construct} {n}");
        }
    }
}
