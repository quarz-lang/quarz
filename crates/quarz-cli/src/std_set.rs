//! The standard-library sets made at first use (#1097, docs/05 §2).
//!
//! `build.rs` precompiles the sets whose modules' code does not call what
//! their `static` statements generate: it has no interpreter to run them.
//! A set whose modules do (`test` parses its options with `CommandLine`,
//! whose statements generate the readers it calls) is made by the first
//! process that loads it: its modules checked in a world of their own,
//! their statements run, as `std_state` does for the others. Its state and
//! the compile-time functions its generated methods are lifted from are
//! kept under `QUARZ_CACHE_DIR` for this build, and later processes read
//! them back.

use std::rc::Rc;
use std::sync::Arc;

use quarz_lower::seed::LowererSeed;
use quarz_syntax::ast::Program;
use quarz_syntax::SourceFile;
use quarz_types::{PreludeState, Unit};

use crate::static_run::Runner;

/// The modules whose code calls what their own statements generate: a
/// program's leading set of standard-library modules that holds one is
/// made at first use, an entry per mix (decided on #1097: `test` with
/// `json`, as most test files load, as well as `test` alone).
pub const MADE_AT_FIRST_USE: &[&str] = &["test"];

/// Whether the leading set `key` (its modules, comma-separated) is made at
/// first use.
pub fn made_at_first_use(key: &str) -> bool {
    key.split(',').any(|m| MADE_AT_FIRST_USE.contains(&m))
}

/// The key of the standard-library modules `units` starts with.
fn leading_key(units: &[Unit]) -> String {
    units
        .iter()
        .take_while(|u| u.name.starts_with("<std:"))
        .map(|u| u.name.trim_start_matches("<std:").trim_end_matches('>'))
        .collect::<Vec<_>>()
        .join(",")
}

/// `QUARZ_NO_STD_CACHE=1`: a set made at first use is not made, read or
/// kept: the program checks its modules from source, statements run, as
/// a module in no set. `QUARZ_NO_PRELUDE_CACHE=1` too, which checks the
/// prelude and every standard-library module from source.
fn off() -> bool {
    let on = |name| std::env::var_os(name).is_some_and(|v| v != "0");
    on("QUARZ_NO_STD_CACHE") || on("QUARZ_NO_PRELUDE_CACHE")
}

/// What an entry is kept under besides the set and the build id
/// (`build_id.txt`, which changes only when `build.rs` or its
/// build-dependencies do): the running executable's size and time, which
/// change whenever any crate that makes the set does (the interpreter,
/// the static runner, this module), the executable being linked again.
/// `None` when they cannot be read: the set is then made and not kept.
fn stamp() -> Option<String> {
    let meta = std::env::current_exe().ok()?.metadata().ok()?;
    let time = meta
        .modified()
        .ok()?
        .duration_since(std::time::UNIX_EPOCH)
        .ok()?;
    Some(format!("{}-{}", meta.len(), time.as_nanos()))
}

/// `QUARZ_VERIFY=std`: a set read back is made again and compared.
fn verify() -> bool {
    std::env::var("QUARZ_VERIFY").is_ok_and(|v| v.split(',').any(|w| w.trim() == "std"))
}

/// What an entry's body holds: the checked state, encoded as a
/// precompiled set's is, and the lowerer's seed (the state's length, the
/// state, the seed).
struct Entry {
    state: Vec<u8>,
    seed: LowererSeed,
}

impl Entry {
    fn encode(&self) -> Vec<u8> {
        let mut bytes = (self.state.len() as u64).to_le_bytes().to_vec();
        bytes.extend_from_slice(&self.state);
        bytes.extend(self.seed.encode());
        bytes
    }

    fn decode(bytes: &[u8]) -> Option<Entry> {
        let len = u64::from_le_bytes(bytes.get(..8)?.try_into().ok()?) as usize;
        let state = bytes.get(8..8usize.checked_add(len)?)?.to_vec();
        let seed = LowererSeed::decode(&bytes[8 + len..])?;
        Some(Entry { state, seed })
    }
}

/// The runner to check `units` with: when they start with a set made at
/// first use, its state is read back (or made, and kept) and handed to the
/// checker (`quarz_types::add_made_std_state`), and the runner's lowerer
/// starts from its compile-time functions. Otherwise a plain runner, and
/// the set, if any, is checked from source.
pub fn runner_for(prelude: &Program, units: &[Unit], files: Vec<SourceFile>) -> Runner {
    let key = leading_key(units);
    if !made_at_first_use(&key) || off() {
        return Runner::new(files);
    }
    match entry(prelude, units, &files, &key) {
        Some((entry, state)) => {
            quarz_types::add_made_std_state(key, Arc::new(entry.state), state);
            Runner::seeded(files, Rc::new(entry.seed))
        }
        None => Runner::new(files),
    }
}

/// The set's entry: read back when this build kept one that fits, else
/// made (and kept when the cache directory takes it). `None` when the set
/// does not check: the program then checks its modules from source, and
/// reports what is wrong there.
fn entry(
    prelude: &Program,
    units: &[Unit],
    files: &[SourceFile],
    key: &str,
) -> Option<(Entry, PreludeState)> {
    let stamp = stamp();
    let read = stamp
        .as_deref()
        .and_then(|s| quarz_types::cache::load_set(key, s))
        .and_then(|bytes| Entry::decode(&bytes))
        .map(|entry| {
            let state = PreludeState::decode(&entry.state);
            (entry, state)
        })
        .filter(|(_, state)| fits(state));
    if let Some((entry, state)) = read {
        if verify() {
            compare(prelude, units, files, key, &entry);
        }
        return Some((entry, state));
    }
    let entry = make(prelude, units, files)?;
    if let Some(stamp) = &stamp {
        quarz_types::cache::store_set(key, stamp, &entry.encode());
    }
    let state = PreludeState::decode(&entry.state);
    Some((entry, state))
}

/// Whether a decoded state starts with this build's prelude (the build id
/// matched already: a mismatch is a bug, an internal error in a debug
/// build).
fn fits(state: &PreludeState) -> bool {
    let ok = quarz_lower::prelude::fits(&state.world) != Some(false);
    debug_assert!(
        ok,
        "internal error: a standard-library set read back does not start with this build's prelude"
    );
    ok
}

/// Make the set: its modules (the first units) checked alone, their
/// statements run by a runner of their own.
fn make(prelude: &Program, units: &[Unit], files: &[SourceFile]) -> Option<Entry> {
    let n = units
        .iter()
        .take_while(|u| u.name.starts_with("<std:"))
        .count();
    let set: Vec<Unit> = units[..n]
        .iter()
        .map(|u| Unit {
            name: u.name.clone(),
            program: u.program.clone(),
            cog: None,
            statements: u.statements,
            declarations_only: false,
            requires: u.requires.clone(),
            tests: None,
            std_mentions: u.std_mentions.clone(),
        })
        .collect();
    let mut runner = Runner::new(files[..=n].to_vec());
    let (checked, _) = quarz_types::check_movement_uncached(prelude, &set, &[], &mut runner);
    let checked = checked?;
    let seed = runner.into_lowerer().seed(&checked.world);
    let state = PreludeState {
        world: checked.world,
        output: checked.output,
        self_news: checked.self_news,
        units: checked.units,
        statements_run: checked.statements_run,
    };
    Some(Entry {
        state: state.encode(),
        seed,
    })
}

/// `QUARZ_VERIFY=std`: the set made again must encode to the entry read
/// back; a difference is an internal error (making a set is a function of
/// the build and the sources).
fn compare(prelude: &Program, units: &[Unit], files: &[SourceFile], key: &str, read: &Entry) {
    let Some(made) = make(prelude, units, files) else {
        panic!("internal error: the standard-library set `{key}` read back does not check when made again");
    };
    assert!(
        made.encode() == read.encode(),
        "internal error: the standard-library set `{key}` read back differs from the set made again (QUARZ_VERIFY=std)"
    );
}
