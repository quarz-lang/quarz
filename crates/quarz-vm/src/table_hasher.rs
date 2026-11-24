//! The hasher of the run-time tables that hold a program's values
//! (`Hash`, `Set`, the unboxed `Hash[Int, Int]`, and the raw lookups of
//! `keys`): SipHash-1-3 with keys chosen per process, as Rust's own
//! `HashMap` hashes, so that keys a peer prepares in advance do not all
//! collide (#1124). A table iterates in insertion order, so the keys
//! change no program's output.
//!
//! `QUARZ_HASH_SEED=n` fixes the keys, to reproduce a timing; it gives
//! up the protection, and is for measuring and debugging only.

use std::hash::BuildHasher;
use std::sync::OnceLock;

/// The process's two keys: random, or from `QUARZ_HASH_SEED` (a number;
/// anything else is ignored, as unset).
fn keys() -> (u64, u64) {
    static KEYS: OnceLock<(u64, u64)> = OnceLock::new();
    *KEYS.get_or_init(|| {
        let keys = match std::env::var("QUARZ_HASH_SEED")
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
        {
            Some(n) => (n, n ^ 0x9e37_79b9_7f4a_7c15),
            None => {
                // std's random keys, drawn from the system's random source.
                let r = std::collections::hash_map::RandomState::new();
                (r.hash_one(1u64), r.hash_one(2u64))
            }
        };
        report(keys);
        keys
    })
}

/// A debug build's test device: `QUARZ_TEST_TABLE_HASH=text` prints, when
/// the keys are chosen (the process's first table hash), what the tables
/// hash the string `text` to, so that a test can see that two processes
/// hash alike only with `QUARZ_HASH_SEED`. A release build has none.
#[cfg(debug_assertions)]
fn report((k0, k1): (u64, u64)) {
    use std::hash::{Hash, Hasher};
    if let Ok(text) = std::env::var("QUARZ_TEST_TABLE_HASH") {
        let mut h = siphasher::sip::SipHasher13::new_with_keys(k0, k1);
        crate::value::Value::str(&text).hash(&mut h);
        eprintln!("quarz: table hash {}", h.finish());
    }
}

#[cfg(not(debug_assertions))]
fn report(_: (u64, u64)) {}

/// The tables' `BuildHasher`: every table of the process hashes alike,
/// which `keys::table_hash` relies on (a hash computed once, then looked
/// up in a map).
#[derive(Clone, Copy, Default, Debug)]
pub struct TableHasher;

impl BuildHasher for TableHasher {
    type Hasher = siphasher::sip::SipHasher13;
    fn build_hasher(&self) -> Self::Hasher {
        let (k0, k1) = keys();
        siphasher::sip::SipHasher13::new_with_keys(k0, k1)
    }
}
