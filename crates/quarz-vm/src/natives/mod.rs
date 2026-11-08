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
            let out = f(i, r, a);
            // What a key's own `==` or `hash` raised (`crate::keys`).
            if crate::keys::pending() {
                if let Some(e) = crate::keys::take_error() {
                    return match out {
                        Err(f) if !matches!(f, crate::interp::Flow::Raise(_)) => Err(f),
                        _ => Err(e),
                    };
                }
            }
            out
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
            // (No check of `crate::keys::pending`: one that may run a
            // key's `==` or `hash` leaves such a key to the native.)
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
            let out = f(i, r, a);
            if crate::keys::pending() {
                if let Some(e) = crate::keys::take_error() {
                    return match out {
                        Ok(v) | Err((_, v)) => Err((e, v)),
                    };
                }
            }
            out
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
mod digest;
pub(crate) use self::core::system_exit;
pub(crate) use core::raised;
#[cfg(feature = "crypto")]
mod crypto;
mod enumerable;
mod fast;
mod io;
mod json;
mod matching;
mod math;
pub mod net;
mod numeric;
pub mod process;
pub mod random;
pub mod signal;
mod steps;
mod string;
mod text;
pub mod time;
#[cfg(feature = "tls")]
mod tls;
pub mod tls_io;

/// Natives with their keys (`Type#name`) and symbols, in the order they
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

/// Whether a native may run at compile time (docs/14 §3, §5): every
/// native key is classified here (`PURITY_BY_KEY`, else its class's line
/// in `PURITY_BY_CLASS`), and a key with no line is denied: a new native
/// is classified to land (`every_native_is_classified`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Purity {
    /// May run at compile time: depends only on its arguments. Printing
    /// counts (it goes to the compiler's standard error).
    Pure,
    /// Acts on the outside world, waits, or is nondeterministic (the
    /// moment, randomness).
    Denied,
    /// Exists at compile time only: the reflection on a class and the
    /// generation (docs/14 §4, §5). A method reaching one is compile-time
    /// only.
    CompileTimeOnly,
}

use Purity::{CompileTimeOnly as CtOnly, Denied, Pure};

/// The classification by class: the class of a key is its part before
/// `#`, or before `.` after the last `::` (`Crypto::RSA` of
/// `Crypto::RSA.public_der`).
const PURITY_BY_CLASS: &[(&str, Purity)] = &[
    // The world, waiting, the moment, randomness. Their values come only
    // from such natives (or a constant one initialized, `STDOUT`).
    ("IO", Denied),
    ("File", Denied),
    ("Dir", Denied),
    ("Process", Denied),
    ("Process::Child", Denied),
    ("Process::Output", Denied),
    ("Task", Denied),
    ("Task::Scope", Denied),
    ("Channel", Denied),
    ("Channel::Selector", Denied),
    ("Atom", Denied),
    ("Signal", Denied),
    ("Random", Denied),
    ("Socket", Denied),
    ("TCPSocket", Denied),
    ("TCPServer", Denied),
    ("UDPSocket", Denied),
    ("UNIXSocket", Denied),
    ("UNIXServer", Denied),
    ("TLSSocket", Denied),
    // Values and what computes from them.
    ("Object", Pure),
    ("Kernel", Pure),
    ("Nil", Pure),
    ("Bool", Pure),
    ("Int", Pure),
    ("Integer", Pure),
    ("Float", Pure),
    ("Math", Pure),
    ("Comparable", Pure),
    ("String", Pure),
    ("String::Builder", Pure),
    ("Symbol", Pure),
    ("Regexp", Pure),
    ("MatchData", Pure),
    ("Bytes", Pure),
    ("Bytes::Builder", Pure),
    ("Bytes::MatchData", Pure),
    ("Array", Pure),
    ("Array::Builder", Pure),
    ("Hash", Pure),
    ("Hash::Builder", Pure),
    ("Set", Pure),
    ("Set::Builder", Pure),
    ("Range", Pure),
    ("Enumerable", Pure),
    ("Enumerator", Pure),
    ("Proc", Pure),
    ("Exception", Pure),
    ("Duration", Pure),
    // `Time` values made from parts or parsed; reading the clock is not.
    ("Time", Pure),
    ("Type", Pure),
    ("Cog", Pure),
    ("Meta", Pure),
    ("Meta::ClassDef", Pure),
    ("Meta::FieldRef", Pure),
    ("Meta::Method", Pure),
    ("Meta::StatementValues", Pure),
    ("JSON", Pure),
    ("Base64", Pure),
    ("Digest::MD5", Pure),
    ("Digest::SHA256", Pure),
    ("Digest::HMAC", Pure),
    ("Digest::PBKDF2", Pure),
    // Keys and signatures given; sealing with a given nonce. What draws
    // randomness is denied below (AES's `generate` and `encrypt`, and
    // Argon2's salted `hash`, draw it in Quarz through
    // `Crypto.random_bytes`).
    ("Crypto", Pure),
    ("Crypto::AES", Pure),
    ("Crypto::Argon2", Pure),
    ("Crypto::RSA", Pure),
    ("Crypto::RSA::PrivateKey", Pure),
    ("Crypto::RSA::PublicKey", Pure),
    ("TLS::Roots", Pure),
    ("TLS::ServerConfig", Pure),
];

/// The keys classified apart from their class's line.
const PURITY_BY_KEY: &[(&str, Purity)] = &[
    // Of denied classes, what touches nothing: path strings, a data
    // value's accessor.
    ("File.basename", Pure),
    ("File.dirname", Pure),
    ("File.extname", Pure),
    ("File.split", Pure),
    ("File.join", Pure),
    ("Process::Output#success?", Pure),
    ("Kernel#gets", Denied),
    ("Kernel#gets?", Denied),
    ("Kernel#readline", Denied),
    ("Kernel#readlines", Denied),
    ("Kernel#exit", Denied),
    ("Kernel#exit!", Denied),
    ("Kernel#abort", Denied),
    ("Kernel#at_exit", Denied),
    ("Kernel#sleep", Denied),
    ("Kernel#rand", Denied),
    ("Kernel#srand", Denied),
    // (The process's default random generator, seeded from the moment.)
    ("Array#shuffle", Denied),
    ("Array#sample", Denied),
    ("Array::Builder#shuffle!", Denied),
    ("Time.now", Denied),
    ("Time.monotonic", Denied),
    ("Crypto.random_bytes", Denied),
    ("Crypto::RSA.generate_der", Denied),
    // (A random salt.)
    ("Crypto::RSA::PrivateKey#sign_pss", Denied),
    // (On a socket.)
    ("TLS::ServerConfig#accept", Denied),
];

/// The compile-time-only keys (their classes' lines say pure): apart, so
/// that what a compiled program reaches (`compile_time_allowed`, the
/// runtime guard) does not hold their names, which an executable must not
/// contain (`a_static_statement_runs_at_compile_time`).
const COMPILE_TIME_ONLY: &[(&str, Purity)] = &[
    ("Type#fields", CtOnly),
    ("Type#field", CtOnly),
    ("Type#methods", CtOnly),
    ("Type#method?", CtOnly),
    ("Type#includes?", CtOnly),
    ("Meta::ClassDef#def_method", CtOnly),
    ("Meta::ClassDef#def_class_method", CtOnly),
    ("Meta::ClassDef#def_initialize", CtOnly),
    ("Meta::ClassDef#def_field", CtOnly),
    ("Meta::ClassDef#field_ref", CtOnly),
    ("Meta::ClassDef#method_ref", CtOnly),
    ("Meta::ClassDef#class_method_ref", CtOnly),
    ("Meta::ClassDef#doc", CtOnly),
    ("Meta.__static_enter", CtOnly),
    ("Meta.__static_leave", CtOnly),
];

/// The class a native key belongs to (`Crypto::RSA` of
/// `Crypto::RSA.public_der`, `Process::Child` of `Process::Child#wait`).
pub fn native_class(key: &str) -> &str {
    let start = key.rfind("::").map_or(0, |i| i + 2);
    match key[start..].find(['#', '.']) {
        Some(i) => &key[..start + i],
        None => key,
    }
}

/// The classification of native `key`; `None` for a key with no line,
/// which is denied.
pub fn purity(key: &str) -> Option<Purity> {
    if COMPILE_TIME_ONLY.iter().any(|(k, _)| *k == key) {
        return Some(CtOnly);
    }
    run_purity(key)
}

/// `purity`, but a compile-time-only key as its class's line (pure): what
/// the runtime reads.
fn run_purity(key: &str) -> Option<Purity> {
    if let Some((_, p)) = PURITY_BY_KEY.iter().find(|(k, _)| *k == key) {
        return Some(*p);
    }
    let class = native_class(key);
    PURITY_BY_CLASS
        .iter()
        .find(|(c, _)| *c == class)
        .map(|(_, p)| *p)
}

/// Whether the natives of `class` are all denied at compile time (its
/// line, or its outermost module's: `Process::Output` is `Process`'s).
/// Their values come only from such natives (or from a constant
/// initialized by one, `STDOUT`), so their methods (an override of
/// `Object#to_s`, say) cannot be reached otherwise.
pub fn compile_time_denied_class(class: &str) -> bool {
    let line = |c: &str| {
        PURITY_BY_CLASS
            .iter()
            .find(|(n, _)| *n == c)
            .map(|(_, p)| *p)
    };
    line(class) == Some(Denied) || line(class.split("::").next().unwrap_or("")) == Some(Denied)
}

/// Whether a native may run at compile time (docs/14 §3): one classified
/// pure or compile-time only (`purity`); an unclassified one is not.
///
/// `Interp::invoke` refuses a denied plain native under a deadline, as a
/// guard behind the analysis; the `fast!` and `owned!` paths skip that
/// guard, so their keys must all be allowed (`fast_and_owned_natives_are_
/// pure` checks it).
pub fn compile_time_allowed(key: &str) -> bool {
    matches!(run_purity(key), Some(Pure | CtOnly))
}

/// The natives that exist at compile time only: the reflection on a class
/// (docs/14 §4). A method reaching one is compile-time only.
pub fn compile_time_only(key: &str) -> bool {
    purity(key) == Some(CtOnly)
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
    signal::register(&mut m);
    process::register(&mut m);
    bytes::register(&mut m);
    bytes_search::register(&mut m);
    time::register(&mut m);
    json::register(&mut m);
    digest::register(&mut m);
    tls_io::register(&mut m);
    #[cfg(feature = "tls")]
    tls::register(&mut m);
    #[cfg(not(feature = "tls"))]
    no_tls(&mut m);
    #[cfg(feature = "crypto")]
    crypto::register(&mut m);
    #[cfg(not(feature = "crypto"))]
    no_crypto(&mut m);
    m
}

/// Without the `crypto` feature: RSA, AES-GCM, argon2id and random
/// bytes raise.
#[cfg(not(feature = "crypto"))]
fn no_crypto(m: &mut Registry<NativeFn>) {
    native!(
        m,
        [
            "Crypto.random_bytes",
            "Crypto::AES.seal_with",
            "Crypto::AES.open_with",
            "Crypto::Argon2.hash_with",
            "Crypto::Argon2.verify_with",
            "Crypto::Argon2.params_with",
            "Crypto::RSA.private_der",
            "Crypto::RSA.private_pem",
            "Crypto::RSA.public_der",
            "Crypto::RSA.public_pem",
            "Crypto::RSA.public_of",
            "Crypto::RSA.generate_der",
            "Crypto::RSA::PrivateKey#to_pem",
            "Crypto::RSA::PrivateKey#bits",
            "Crypto::RSA::PrivateKey#sign",
            "Crypto::RSA::PrivateKey#sign_pss",
            "Crypto::RSA::PublicKey#to_pem",
            "Crypto::RSA::PublicKey#bits",
            "Crypto::RSA::PublicKey#verify",
            "Crypto::RSA::PublicKey#verify_pss",
            "Crypto::RSA::PublicKey#fingerprint"
        ],
        |i, _, _| {
            Err(i.raise(
                i.program.exc.not_implemented,
                "cryptography is not built in (the `crypto` feature of quarz-vm)",
            ))
        }
    );
}

/// Without the `tls` feature: making a TLS connection raises.
#[cfg(not(feature = "tls"))]
fn no_tls(m: &mut Registry<NativeFn>) {
    native!(
        m,
        [
            "TLSSocket.handshake",
            "TLS::Roots.check",
            "TLS::ServerConfig#accept",
            "TLS::ServerConfig#check"
        ],
        |i, _, _| {
            Err(i.raise(
                i.program.exc.not_implemented,
                "TLS is not built in (the `tls` feature of quarz-vm)",
            ))
        }
    );
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

#[cfg(test)]
mod compile_time_tests {
    use super::*;

    #[test]
    fn fast_and_owned_natives_are_pure() {
        let mut keys: Vec<&str> = fast_registry().entries.iter().map(|e| e.0).collect();
        keys.extend(owned_registry().entries.iter().map(|e| e.0));
        for key in keys {
            assert!(
                compile_time_allowed(key),
                "{key} bypasses the compile-time guard"
            );
        }
    }

    /// Every native key, of the three registries.
    fn every_key() -> Vec<&'static str> {
        let mut keys: Vec<&str> = registry().entries.iter().map(|e| e.0).collect();
        keys.extend(fast_registry().entries.iter().map(|e| e.0));
        keys.extend(owned_registry().entries.iter().map(|e| e.0));
        keys
    }

    /// A new native is classified to land (docs/14 §3): an unclassified
    /// key would be denied at compile time by default, unnoticed.
    #[test]
    fn every_native_is_classified() {
        let missing: Vec<&str> = every_key()
            .into_iter()
            .filter(|k| purity(k).is_none())
            .collect();
        assert!(
            missing.is_empty(),
            "classify these natives in `PURITY_BY_CLASS` or `PURITY_BY_KEY` (natives/mod.rs): {missing:?}"
        );
    }

    /// Each line of the tables names natives that exist (with the
    /// optional features off too: their stubs register the same keys).
    #[test]
    fn every_line_names_a_native() {
        let keys = every_key();
        for (k, _) in PURITY_BY_KEY.iter().chain(COMPILE_TIME_ONLY) {
            assert!(keys.contains(k), "{k} is no native");
        }
        // (A compile-time-only key's class says pure, which the runtime
        // reads for it.)
        for (k, _) in COMPILE_TIME_ONLY {
            assert_eq!(run_purity(k), Some(Pure), "{k}");
        }
        for (c, _) in PURITY_BY_CLASS {
            assert!(
                keys.iter().any(|k| native_class(k) == *c),
                "{c} has no native"
            );
        }
    }

    #[test]
    fn the_registry_is_classified_as_intended() {
        for key in every_key() {
            let class = native_class(key);
            let denied = (matches!(
                class,
                "IO" | "File" | "Dir" | "Process" | "Process::Child" | "Task" | "Channel"
            ) && !matches!(
                key,
                "File.basename" | "File.dirname" | "File.extname" | "File.split" | "File.join"
            )) || matches!(
                key,
                "Time.now"
                    | "Kernel#sleep"
                    | "Kernel#exit"
                    | "Kernel#gets"
                    | "Crypto.random_bytes"
                    | "Crypto::RSA.generate_der"
                    | "Array#shuffle"
                    | "Array#sample"
            );
            if denied {
                assert!(
                    !compile_time_allowed(key),
                    "{key} must be denied at compile time"
                );
            }
            if (matches!(
                class,
                "String" | "Array" | "Hash" | "Int" | "Float" | "Symbol" | "Type" | "JSON"
            ) && !matches!(key, "Array#shuffle" | "Array#sample"))
                || matches!(
                    key,
                    "Kernel#puts"
                        | "Kernel#p"
                        | "Duration#+"
                        | "Time#year"
                        | "Time.at"
                        | "Crypto::RSA::PublicKey#verify"
                        | "Crypto::AES.seal_with"
                )
            {
                assert!(
                    compile_time_allowed(key),
                    "{key} must be allowed at compile time"
                );
            }
        }
        assert_eq!(native_class("Crypto::RSA.public_der"), "Crypto::RSA");
        assert_eq!(native_class("Process::Child#wait"), "Process::Child");
        assert_eq!(native_class("Int#.."), "Int");
    }
}
