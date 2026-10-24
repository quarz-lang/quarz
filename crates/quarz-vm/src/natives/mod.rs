//! Native implementations of the prelude's `native def` methods, keyed by
//! `Class#method` (instance) or `Class.method` (singleton).

use crate::rc::Rc;
use std::cell::RefCell;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn, OwnedNativeFn};
use crate::value::Value;
use smallvec::smallvec;

pub mod bytes;
mod collections;
mod concurrency;
mod core;
mod enumerable;
mod fast;
mod io;
mod json;
mod math;
pub mod net;
mod numeric;
pub mod random;
mod string;
mod text;
pub mod time;

/// Natives with their keys (`Class#name`), in the order they are
/// registered (a later one with the same key wins), built at start-up.
/// A compiled program's methods know where theirs are (`positions`, see
/// `crate::methods`), the interpreter's look them up by key (`map`).
pub struct Registry<F> {
    entries: Vec<(&'static str, F)>,
}

/// Which registry: `natives::registry`, `fast_registry`, `owned_registry`.
pub const PLAIN: usize = 0;
pub const FAST: usize = 1;
pub const OWNED: usize = 2;

impl<F: Copy> Registry<F> {
    pub fn insert(&mut self, key: &'static str, f: F) {
        self.entries.push((key, f));
    }

    /// The native `positions` put at `i` (in a registry whose
    /// `fingerprint` the build's matches).
    pub fn get(&self, i: u32) -> Option<F> {
        self.entries.get(i as usize).map(|(_, f)| *f)
    }

    /// The natives by key.
    pub fn map(&self) -> quarz_ir::HashMap<&'static str, F> {
        self.entries.iter().copied().collect()
    }

    /// Its keys in order, hashed: a build and the runtime it links
    /// against must agree on where the natives are.
    pub fn fingerprint(&self, h: &mut impl std::hash::Hasher) {
        for (k, _) in &self.entries {
            h.write(k.as_bytes());
            h.write_u8(0);
        }
    }

    /// Where each key's native is (for a build to record).
    pub fn positions(&self) -> quarz_ir::HashMap<&'static str, u32> {
        self.entries
            .iter()
            .enumerate()
            .map(|(i, (k, _))| (*k, i as u32))
            .collect()
    }
}

fn registry_with<F>(n: usize) -> Registry<F> {
    Registry {
        entries: Vec::with_capacity(n),
    }
}

/// The fingerprint of the three registries (see `Registry::fingerprint`).
pub fn fingerprint_of(
    plain: &Registry<NativeFn>,
    fast: &Registry<crate::interp::FastNativeFn>,
    owned: &Registry<OwnedNativeFn>,
) -> u64 {
    use std::hash::Hasher;
    let mut h = rustc_hash::FxHasher::default();
    plain.fingerprint(&mut h);
    fast.fingerprint(&mut h);
    owned.fingerprint(&mut h);
    h.finish()
}

pub fn fingerprint() -> u64 {
    fingerprint_of(&registry(), &fast_registry(), &owned_registry())
}

/// Where each native of the three registries is, by key (`PLAIN`,
/// `FAST`, `OWNED`): what a build records (see `crate::methods`).
pub fn positions() -> [quarz_ir::HashMap<&'static str, u32>; 3] {
    [
        registry().positions(),
        fast_registry().positions(),
        owned_registry().positions(),
    ]
}

pub fn registry() -> Registry<NativeFn> {
    let mut m: Registry<NativeFn> = registry_with(1024);
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

/// Natives with a by-reference version.
pub fn fast_registry() -> Registry<crate::interp::FastNativeFn> {
    let mut m = registry_with(64);
    fast::register(&mut m);
    m
}

/// Natives that update a uniquely owned receiver in place.
pub fn owned_registry() -> Registry<OwnedNativeFn> {
    let mut m: Registry<OwnedNativeFn> = registry_with(16);
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

pub fn string<'a>(interp: &Interp, v: &'a Value, what: &str) -> Result<&'a str, Flow> {
    match v.as_str() {
        Some(s) => Ok(s),
        None => Err(interp.err_type(&format!(
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
        Value::Array(a) => Ok(a.to_values()),
        Value::ArrayBuilder(a) => Ok(a.borrow().clone()),
        Value::Set(s) => Ok(s.iter().cloned().collect()),
        Value::SetBuilder(s) => Ok(s.borrow().iter().cloned().collect()),
        Value::Hash(h) => Ok(h
            .as_map()
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
    match interp.block_caller(block) {
        Some(caller) => {
            for v in items {
                caller.call(&[v])?;
            }
        }
        None => {
            for v in items {
                interp.call_block(block, smallvec![v])?;
            }
        }
    }
    Ok(())
}

/// Call `block` once per item with one argument, collecting the results.
pub fn map_values(
    interp: &Interp,
    items: impl IntoIterator<Item = Value>,
    block: &Value,
) -> Result<Vec<Value>, Flow> {
    let mut out = Vec::new();
    match interp.block_caller(block) {
        Some(caller) => {
            for v in items {
                out.push(caller.call(&[v])?);
            }
        }
        None => {
            for v in items {
                out.push(interp.call_block(block, smallvec![v])?);
            }
        }
    }
    Ok(out)
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
    match io::stdin_line(interp)? {
        Some(line) => Ok(Value::string(line)),
        None if raise_on_eof => {
            Err(interp.raise(interp.program.exc.eof_error, "end of file reached"))
        }
        None => Ok(Value::Nil),
    }
}

/// The origin of the monotonic clocks (`Process.clock`, `Time.monotonic`):
/// one for every thread, taken at the first reading.
pub(crate) fn clock_start() -> std::time::Instant {
    static START: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
    *START.get_or_init(std::time::Instant::now)
}
