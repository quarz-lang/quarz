//! Native implementations of the prelude's `native def` methods, keyed by
//! `Class#method` (instance) or `Class.method` (singleton).

use crate::rc::Rc;
use std::cell::RefCell;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn, OwnedNativeFn};
use crate::value::Value;
use smallvec::smallvec;

/// Register a native under its keys (one, or a list), as a function of
/// its own named `qzn.` and its first key: a compiled program refers to
/// the natives it uses by these names (see `quarz_aot`), so that the
/// linker leaves out the others.
macro_rules! native {
    ($m:expr, [$first:literal $(, $key:literal)* $(,)?], $f:expr $(,)?) => {{
        #[export_name = concat!("qzn.", $first)]
        fn native(
            i: &crate::interp::Interp,
            r: &crate::value::Value,
            a: crate::interp::Args,
        ) -> crate::interp::EvalResult {
            let f: crate::interp::NativeFn = $f;
            f(i, r, a)
        }
        $m.add(&[$first $(, $key)*], native, concat!("qzn.", $first));
    }};
    ($m:expr, $key:literal, $f:expr $(,)?) => {
        native!($m, [$key], $f)
    };
}

/// `native!` for a by-reference native (`qzf.`).
macro_rules! fast {
    ($m:expr, [$first:literal $(, $key:literal)* $(,)?], $f:expr $(,)?) => {{
        #[export_name = concat!("qzf.", $first)]
        fn native(
            i: &crate::interp::Interp,
            r: &crate::value::Value,
            a: &[&crate::value::Value],
        ) -> Option<crate::interp::EvalResult> {
            let f: crate::interp::FastNativeFn = $f;
            f(i, r, a)
        }
        $m.add(&[$first $(, $key)*], native, concat!("qzf.", $first));
    }};
    ($m:expr, $key:literal, $f:expr $(,)?) => {
        fast!($m, [$key], $f)
    };
}

/// `native!` for an in-place native (`qzo.`).
macro_rules! owned {
    ($m:expr, [$first:literal $(, $key:literal)* $(,)?], $f:expr $(,)?) => {{
        #[export_name = concat!("qzo.", $first)]
        fn native(
            i: &crate::interp::Interp,
            r: crate::value::Value,
            a: crate::interp::Args,
        ) -> Result<crate::value::Value, (crate::interp::Flow, crate::value::Value)> {
            let f: crate::interp::OwnedNativeFn = $f;
            f(i, r, a)
        }
        $m.add(&[$first $(, $key)*], native, concat!("qzo.", $first));
    }};
    ($m:expr, $key:literal, $f:expr $(,)?) => {
        owned!($m, [$key], $f)
    };
}

pub mod bytes;
mod bytes_search;
mod collections;
mod concurrency;
mod core;
mod enumerable;
mod fast;
mod io;
mod json;
mod matching;
mod math;
pub mod net;
mod numeric;
pub mod random;
mod string;
mod text;
pub mod time;

/// Natives with their keys (`Class#name`) and symbols, in the order they
/// are registered (a later one with the same key wins). Only what
/// interprets builds the registries (`all`): a compiled program has a
/// table of the natives it uses, made by its build (`symbols`).
pub struct Registry<F> {
    entries: Vec<(&'static str, F, &'static str)>,
}

/// Which registry: plain natives, by-reference ones, in-place ones.
pub const PLAIN: usize = 0;
pub const FAST: usize = 1;
pub const OWNED: usize = 2;

impl<F: Copy> Registry<F> {
    pub fn add(&mut self, keys: &[&'static str], f: F, symbol: &'static str) {
        for key in keys {
            self.entries.push((key, f, symbol));
        }
    }

    /// The natives by key.
    pub fn map(&self) -> quarz_ir::HashMap<&'static str, F> {
        self.entries.iter().map(|(k, f, _)| (*k, *f)).collect()
    }

    /// The symbols of the natives by key.
    pub fn symbols(&self) -> quarz_ir::HashMap<&'static str, &'static str> {
        self.entries.iter().map(|(k, _, s)| (*k, *s)).collect()
    }
}

fn registry_with<F>(n: usize) -> Registry<F> {
    Registry {
        entries: Vec::with_capacity(n),
    }
}

/// The three registries.
pub struct Natives {
    pub plain: Registry<NativeFn>,
    pub fast: Registry<crate::interp::FastNativeFn>,
    pub owned: Registry<OwnedNativeFn>,
}

pub fn all() -> Natives {
    Natives {
        plain: registry(),
        fast: fast_registry(),
        owned: owned_registry(),
    }
}

/// The symbols of the natives of the three registries (`PLAIN`, `FAST`,
/// `OWNED`), by key: what a build refers to.
pub fn symbols() -> [quarz_ir::HashMap<&'static str, &'static str>; 3] {
    let n = all();
    [n.plain.symbols(), n.fast.symbols(), n.owned.symbols()]
}

fn registry() -> Registry<NativeFn> {
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
    bytes_search::register(&mut m);
    time::register(&mut m);
    json::register(&mut m);
    m
}

/// Natives with a by-reference version.
fn fast_registry() -> Registry<crate::interp::FastNativeFn> {
    let mut m = registry_with(64);
    fast::register(&mut m);
    m
}

/// Natives that update a uniquely owned receiver in place.
fn owned_registry() -> Registry<OwnedNativeFn> {
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
