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
            crate::natives::keys_raised(f(i, r, a))
        }
        $m.add(&[$first $(, $key)*], native, concat!("qzn.", $first));
    }};
    ($m:expr, $key:literal, $f:expr $(,)?) => {
        native!($m, [$key], $f)
    };
}

/// A native's result, or what a key's own `==` or `hash` raised during
/// it (`crate::keys`): every generic native's wrapper (`native!`,
/// `fast!`).
#[inline]
pub(crate) fn keys_raised(out: crate::interp::EvalResult) -> crate::interp::EvalResult {
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

/// Where `fast!` registers a native: its generic form into the plain
/// registry, its by-reference twin into the fast one, from the same line
/// (#1035), each under its keys once.
pub(crate) trait Sink {
    fn both(
        &mut self,
        keys: &[&'static str],
        generic: NativeFn,
        generic_symbol: &'static str,
        twin: crate::interp::FastNativeFn,
        twin_symbol: &'static str,
    );
}

impl Sink for Registry<NativeFn> {
    fn both(
        &mut self,
        keys: &[&'static str],
        generic: NativeFn,
        generic_symbol: &'static str,
        _: crate::interp::FastNativeFn,
        _: &'static str,
    ) {
        self.add(keys, generic, generic_symbol);
    }
}

impl Sink for Registry<crate::interp::FastNativeFn> {
    fn both(
        &mut self,
        keys: &[&'static str],
        _: NativeFn,
        _: &'static str,
        twin: crate::interp::FastNativeFn,
        twin_symbol: &'static str,
    ) {
        self.add(keys, twin, twin_symbol);
    }
}

/// How compiled code hands a `qzfc.` entry its operands (#795): six
/// register parameters in all, the interpreter, the activation and the
/// registers, then three words that code generation computes as
/// constants (`pack`) and the entry takes apart (`unpack`), in this one
/// place:
/// - `dst`'s word: the destination register (`DST_MASK`), the number of
///   arguments (`N_MASK`), and `DST_EMPTY` when the register's home
///   holds no counted value, so the answer is written without a drop;
/// - the receiver register (`u32::MAX` for the caller's `self`) and the
///   first argument register;
/// - the second and third argument registers.
pub mod fast_call {
    pub const DST_EMPTY: u32 = 1 << 31;
    pub const N_SHIFT: u32 = 29;
    pub const N_MASK: u32 = 0b11 << N_SHIFT;
    pub const DST_MASK: u32 = (1 << N_SHIFT) - 1;

    /// The words for a call with receiver `recv`, arguments `args` (at
    /// most three) and destination `dst` (`empty` as `DST_EMPTY` says).
    pub fn pack(recv: u32, args: &[u32], dst: u32, empty: bool) -> (u32, u64, u64) {
        assert!(
            args.len() <= 3,
            "a fast entry takes at most three arguments"
        );
        assert!(
            dst <= DST_MASK,
            "register {dst} beyond a fast entry's range"
        );
        let a = |k: usize| u64::from(args.get(k).copied().unwrap_or(0));
        let word = dst | (args.len() as u32) << N_SHIFT | if empty { DST_EMPTY } else { 0 };
        (word, u64::from(recv) | a(0) << 32, a(1) | a(2) << 32)
    }

    /// `pack`'s words taken apart: the receiver, the argument registers
    /// (the first `n`), `n`, the destination and whether its home is
    /// empty.
    #[inline(always)]
    pub fn unpack(word: u32, ops0: u64, ops1: u64) -> (u32, [u32; 3], usize, u32, bool) {
        (
            ops0 as u32,
            [(ops0 >> 32) as u32, ops1 as u32, (ops1 >> 32) as u32],
            ((word & N_MASK) >> N_SHIFT) as usize,
            word & DST_MASK,
            word & DST_EMPTY != 0,
        )
    }

    #[cfg(test)]
    mod tests {
        #[test]
        fn pack_round_trips() {
            for args in [&[][..], &[7], &[7, 8], &[7, 8, 9]] {
                for (recv, empty) in [(3, false), (u32::MAX, true)] {
                    let (w, o0, o1) = super::pack(recv, args, super::DST_MASK, empty);
                    let (r, a, n, d, e) = super::unpack(w, o0, o1);
                    assert_eq!((r, &a[..n], d, e), (recv, args, super::DST_MASK, empty));
                }
            }
        }
    }
}

/// `native!` for a by-reference native (`qzf.`), with the entry compiled
/// code calls it through (`qzfc.`, #795): the twin and its entry come from
/// this one line, under its first key.
macro_rules! fast {
    ($m:expr, [$first:literal $(, $key:literal)* $(,)?], $f:expr, generic: $g:expr $(,)?) => {{
        // The twin, once: its `qzf.` export and its `qzfc.` entry both
        // run this body (the entry inlines it rather than calling the
        // export, which a position-independent program reaches through
        // its global offset table).
        #[inline(always)]
        fn body(
            i: &crate::interp::Interp,
            r: &crate::value::Value,
            a: &[&crate::value::Value],
        ) -> Option<crate::value::Value> {
            // (One that may run a key's `==` or `hash` leaves such a key
            // to the native. A walk over a key nested too deeply keeps a
            // `SystemStackError` (#437): the native runs instead, and
            // its wrapper raises it there.)
            let f: crate::interp::FastNativeFn = $f;
            let out = f(i, r, a);
            if crate::keys::pending() {
                return None;
            }
            out
        }
        #[export_name = concat!("qzf.", $first)]
        fn native(
            i: &crate::interp::Interp,
            r: &crate::value::Value,
            a: &[&crate::value::Value],
        ) -> Option<crate::value::Value> {
            body(i, r, a)
        }
        /// Compiled code's call of the twin (#795): the receiver (or the
        /// caller's `self`) and the argument registers borrowed, as
        /// `qz_call_static` lends them, all named in `fast_call`'s words.
        /// 1 when it answered, the value in the destination register; 0
        /// when it declined, nothing touched, and the caller then makes
        /// the call through `qz_call_static`. A destination flagged
        /// `DST_EMPTY` is written without a drop.
        ///
        /// # Safety
        /// As for `qz_call_static`; a `DST_EMPTY` home holds no counted
        /// value.
        #[export_name = concat!("qzfc.", $first)]
        unsafe extern "C" fn entry(
            rt: *const crate::interp::Interp,
            act: *const crate::vm::Activation,
            regs: *mut crate::value::Value,
            word: u32,
            ops0: u64,
            ops1: u64,
        ) -> u8 {
            let (recv, args, n, dst, empty) = crate::natives::fast_call::unpack(word, ops0, ops1);
            // SAFETY: as the caller promises.
            unsafe {
                let recv_ref: &crate::value::Value = if recv == u32::MAX {
                    &(*act).self_val
                } else {
                    &*regs.add(recv as usize)
                };
                // (Without a branch on `n`: the slots past it name nil.)
                const NIL: crate::value::Value = crate::value::Value::Nil;
                let at = |k: usize| -> &crate::value::Value {
                    if k < n {
                        &*regs.add(args[k] as usize)
                    } else {
                        &NIL
                    }
                };
                let refs = [at(0), at(1), at(2)];
                let out = body(&*rt, recv_ref, &refs[..n.min(3)]);
                match out {
                    Some(v) => {
                        let home = regs.add(dst as usize);
                        if empty {
                            std::ptr::write(home, v);
                        } else {
                            *home = v;
                        }
                        1
                    }
                    None => 0,
                }
            }
        }
        let _ = entry;
        /// The generic form (`qzn.`): the twin on the positional
        /// arguments, then, where it declines, `$g`, which raises what
        /// the twin does not answer (a receiver or argument of another
        /// kind) or does what it leaves (#1035).
        #[export_name = concat!("qzn.", $first)]
        fn generic(
            i: &crate::interp::Interp,
            r: &crate::value::Value,
            a: crate::interp::Args,
        ) -> crate::interp::EvalResult {
            if a.kw.is_empty() && a.block.is_none() && a.pos.len() <= 3 {
                let refs: smallvec::SmallVec<[&crate::value::Value; 3]> = a.pos.iter().collect();
                if let Some(v) = body(i, r, &refs) {
                    return Ok(v);
                }
            }
            let g: crate::interp::NativeFn = $g;
            crate::natives::keys_raised(g(i, r, a))
        }
        crate::natives::Sink::both(
            $m,
            &[$first $(, $key)*],
            generic,
            concat!("qzn.", $first),
            native,
            concat!("qzf.", $first),
        );
    }};
    ($m:expr, $key:literal, $f:expr, generic: $g:expr $(,)?) => {
        fast!($m, [$key], $f, generic: $g)
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
pub(crate) mod string;
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
    // (A new key each time.)
    ("TLS::Testing", Denied),
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
    ("Bytes::Secret", Pure),
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
    // (`Date.parse` and `parse?`, natives since #932: a value of a text.)
    ("Date", Pure),
    ("Type", Pure),
    ("Cog", Pure),
    ("Meta", Pure),
    ("Meta::ClassDef", Pure),
    ("Meta::FieldRef", Pure),
    ("Meta::Method", Pure),
    // (`result`, #1011: reads the program's method tables, which a
    // compile-time run has as the program does.)
    ("Meta::MethodRef", Pure),
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
    ("Crypto::AES::GCM", Pure),
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
    ("Crypto.random_secret", Denied),
    ("Crypto::RSA::PrivateKey.generate_with", Denied),
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
    // The generic forms of the natives with a twin (#1035).
    fast::register(&mut m);
    m
}

/// Without the `crypto` feature: RSA, AES-GCM, argon2id, random bytes
/// and comparison in constant time raise.
#[cfg(not(feature = "crypto"))]
fn no_crypto(m: &mut Registry<NativeFn>) {
    native!(
        m,
        [
            "Crypto.random_bytes",
            "Crypto.secure_compare",
            "Crypto::AES::GCM.new",
            "Crypto::AES::GCM#bits",
            "Crypto::AES::GCM#seal",
            "Crypto::AES::GCM#open?",
            "Crypto::AES::GCM#open_secret?",
            "Crypto::AES::GCM#export_key",
            "Crypto::AES::GCM#wipe",
            "Crypto::AES::GCM#wiped?",
            "Crypto::AES::GCM#==",
            "Crypto::Argon2.hash_with",
            "Crypto::Argon2.verify_with",
            "Crypto::Argon2.params_with",
            "Crypto::RSA.public_der",
            "Crypto::RSA.public_pem",
            "Crypto::RSA::PrivateKey.new",
            "Crypto::RSA::PrivateKey.from_pem",
            "Crypto::RSA::PrivateKey.generate_with",
            "Crypto::RSA::PrivateKey#export_der",
            "Crypto::RSA::PrivateKey#export_pem",
            "Crypto::RSA::PrivateKey#public_der",
            "Crypto::RSA::PrivateKey#bits",
            "Crypto::RSA::PrivateKey#wipe",
            "Crypto::RSA::PrivateKey#wiped?",
            "Crypto::RSA::PrivateKey#==",
            "Crypto::RSA::PrivateKey#sign",
            "Crypto::RSA::PrivateKey#sign_pss",
            "Crypto::RSA::PublicKey#to_pem",
            "Crypto::RSA::PublicKey#bits",
            "Crypto::RSA::PublicKey#verify",
            "Crypto::RSA::PublicKey#verify_pss",
            "Crypto::RSA::PublicKey#fingerprint",
            "Crypto.random_secret"
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
            "TLS::ServerConfig#check",
            "TLS::Testing.generate"
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
        // An integral float in `Int`'s range, exactly; one beyond it
        // overflows, as `Float#to_i` does, rather than saturating.
        Value::Float(f) if f.fract() == 0.0 => {
            if (-crate::value::TWO_TO_63..crate::value::TWO_TO_63).contains(f) {
                Ok(*f as i64)
            } else {
                Err(interp.err_overflow())
            }
        }
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
            interp.send_requirement(recv, interp.req_each(), "each", smallvec![], Some(block))?;
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
    /// Every key with a by-reference twin has its generic form in the
    /// plain registry under the same key and the same first key's symbol,
    /// from the same `fast!` line, and is registered once in each (#1035).
    #[test]
    fn twins_have_their_generic_form() {
        let plain = super::registry();
        let fast = super::fast_registry();
        for (key, _, sym) in &fast.entries {
            let generic: Vec<_> = plain.entries.iter().filter(|e| e.0 == *key).collect();
            assert_eq!(generic.len(), 1, "`{key}` in the plain registry");
            assert_eq!(
                generic[0].2.trim_start_matches("qzn."),
                sym.trim_start_matches("qzf."),
                "`{key}`"
            );
            assert_eq!(
                fast.entries.iter().filter(|e| e.0 == *key).count(),
                1,
                "`{key}` twice"
            );
        }
    }

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
                    | "Crypto::RSA::PrivateKey.generate_with"
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
                        | "Crypto::AES::GCM#seal"
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
