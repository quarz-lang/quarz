//! Native implementations of the prelude's `native def` methods, keyed by
//! `Class#method` (instance) or `Class.method` (singleton).

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn, OwnedNativeFn};
use crate::value::Value;
use smallvec::smallvec;

pub mod bytes;
mod collections;
mod concurrency;
mod core;
mod enumerable;
mod io;
mod json;
mod math;
pub mod net;
mod numeric;
pub mod random;
mod string;
mod text;
pub mod time;

pub fn registry() -> HashMap<&'static str, NativeFn> {
    let mut m: HashMap<&'static str, NativeFn> = HashMap::new();
    core::register(&mut m);
    numeric::register(&mut m);
    math::register(&mut m);
    random::register(&mut m);
    string::register(&mut m);
    text::register(&mut m);
    collections::register(&mut m);
    enumerable::register(&mut m);
    concurrency::register(&mut m);
    io::register(&mut m);
    net::register(&mut m);
    bytes::register(&mut m);
    time::register(&mut m);
    json::register(&mut m);
    m
}

/// Natives that update a uniquely owned receiver in place.
pub fn owned_registry() -> HashMap<&'static str, OwnedNativeFn> {
    let mut m: HashMap<&'static str, OwnedNativeFn> = HashMap::new();
    collections::register_owned(&mut m);
    m
}

// ----- argument helpers -------------------------------------------------------

pub fn int(interp: &Interp, v: &Value, what: &str) -> Result<i64, Flow> {
    match v {
        Value::Int(i) => Ok(*i),
        Value::Float(f) if f.fract() == 0.0 => Ok(*f as i64),
        _ => Err(interp.err_type(&format!(
            "{what} must be an Int, got {}",
            interp.class_name(v)
        ))),
    }
}

pub fn float(interp: &Interp, v: &Value, what: &str) -> Result<f64, Flow> {
    match v {
        Value::Int(i) => Ok(*i as f64),
        Value::Float(f) => Ok(*f),
        Value::BigInt(b) => {
            use num_traits::ToPrimitive;
            Ok(b.to_f64().unwrap_or(f64::INFINITY))
        }
        _ => Err(interp.err_type(&format!(
            "{what} must be a number, got {}",
            interp.class_name(v)
        ))),
    }
}

pub fn string(interp: &Interp, v: &Value, what: &str) -> Result<Rc<str>, Flow> {
    match v {
        Value::Str(s) => Ok(s.clone()),
        _ => Err(interp.err_type(&format!(
            "{what} must be a String, got {}",
            interp.class_name(v)
        ))),
    }
}

pub fn block(interp: &Interp, args: &Args) -> Result<Value, Flow> {
    match &args.block {
        Some(b) => Ok(b.clone()),
        None => Err(interp.err_arg("a block is required")),
    }
}

/// Iterate any enumerable value into a vector (fast paths for the built-in
/// collections, `each` otherwise).
pub fn collect(interp: &Interp, recv: &Value) -> Result<Vec<Value>, Flow> {
    match recv {
        Value::Array(a) => Ok(a.iter().cloned().collect()),
        Value::ArrayBuilder(a) => Ok(a.borrow().clone()),
        Value::Set(s) => Ok(s.iter().cloned().collect()),
        Value::SetBuilder(s) => Ok(s.borrow().iter().cloned().collect()),
        Value::Hash(h) => Ok(h
            .iter()
            .map(|(k, v)| Value::array(vec![k.clone(), v.clone()]))
            .collect()),
        Value::Range(r) => collections::range_to_vec(interp, r),
        _ => {
            let out = Rc::new(RefCell::new(Vec::new()));
            let out2 = out.clone();
            let block = interp.native_block(move |_, args| {
                out2.borrow_mut()
                    .push(args.into_iter().next().unwrap_or(Value::Nil));
                Ok(Value::Nil)
            });
            interp.send(recv, "each", smallvec![], Some(block))?;
            let v = out.borrow().clone();
            Ok(v)
        }
    }
}

/// Call `block` for each element; `break` propagates to the caller.
pub fn each_value(
    interp: &Interp,
    items: impl IntoIterator<Item = Value>,
    block: &Value,
) -> Result<(), Flow> {
    for v in items {
        interp.call_block(block, smallvec![v])?;
    }
    Ok(())
}

/// `hash` for the built-in collections (structural).
pub fn core_hash(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    recv.hash(&mut h);
    Ok(Value::Int((h.finish() >> 1) as i64))
}

/// Read a line from standard input (`gets`).
pub fn core_gets(interp: &Interp, raise_on_eof: bool) -> EvalResult {
    interp.flush();
    let mut line = String::new();
    match std::io::stdin().read_line(&mut line) {
        Ok(0) => {
            if raise_on_eof {
                Err(interp.raise(interp.exc.eof_error, "end of file reached"))
            } else {
                Ok(Value::Nil)
            }
        }
        Ok(_) => Ok(Value::string(line)),
        Err(e) => Err(interp.raise(interp.exc.io_error, &e.to_string())),
    }
}
