//! The prelude's share of the runtime's tables, made when `quarz` is
//! built (#551). Its rows of `RtWorld::classes` and `RtWorld::methods`,
//! its entries of the override table, of the witness record, of the
//! include overrides and of the rows over them are what the prelude's
//! declarations alone decide, unless a program changes them
//! (`World::prelude_unchanged`). `rtworld::declared_table` takes them from
//! here and makes the others with the same functions; this module only
//! keeps what those functions made for the prelude (`make`), never a
//! second computation.

use quarz_ir::{ClassId, MethodId, RtClass, RtMethod, RtWorld};
use quarz_types::World;
use serde::{Deserialize, Serialize};

use crate::rtworld;

/// What `rtworld::declared_with` makes for the prelude alone, with the
/// class override rows before `build_witness_rows` filters them.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PreludeRt {
    pub classes: Vec<RtClass>,
    pub methods: Vec<RtMethod>,
    pub table: Vec<Vec<MethodId>>,
    pub record: Vec<(ClassId, MethodId, Option<MethodId>)>,
    pub include_overrides: Vec<(ClassId, MethodId, MethodId)>,
    pub class_override_rows: Vec<(ClassId, MethodId, MethodId)>,
    pub override_rows: Vec<(ClassId, MethodId, MethodId)>,
    pub witness_rows: Vec<(ClassId, MethodId, Option<MethodId>)>,
    /// The names of the prelude's classes and methods, which a program's
    /// world must start with for the ids to be the same.
    pub class_names: Vec<String>,
    pub method_names: Vec<(ClassId, String)>,
    /// The targets of the prelude's extensions, which the program's
    /// world's first extensions must be.
    pub extension_targets: Vec<ClassId>,
}

impl PreludeRt {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serde::encode_to_vec(self, bincode::config::standard())
            .expect("encode the prelude's tables")
    }

    fn decode(bytes: &[u8]) -> PreludeRt {
        bincode::serde::decode_from_slice(bytes, bincode::config::standard())
            .expect("decode the prelude's tables")
            .0
    }
}

/// The snapshot for `world`, the prelude's alone (`build.rs` of
/// `quarz-cli`, with the prelude's checked state).
pub fn make(world: &World, out: &quarz_types::Output) -> PreludeRt {
    let (rt, table) = rtworld::declared_with(world, out, rtworld::witness_record(world));
    let class_override_rows = rtworld::class_override_rows_all(world, &rt, &table);
    PreludeRt {
        class_names: world.classes.iter().map(|c| c.name.clone()).collect(),
        method_names: world
            .methods
            .iter()
            .map(|m| (m.owner, m.name.clone()))
            .collect(),
        extension_targets: world.extensions.iter().map(|e| e.target).collect(),
        classes: rt.classes,
        methods: rt.methods,
        table,
        record: rt.witness_record,
        include_overrides: rt.include_overrides,
        class_override_rows,
        override_rows: rt.override_rows,
        witness_rows: rt.witness_rows,
    }
}

static BYTES: std::sync::OnceLock<&'static [u8]> = std::sync::OnceLock::new();
static SNAPSHOT: std::sync::OnceLock<Option<PreludeRt>> = std::sync::OnceLock::new();

/// The snapshot `quarz` was built with (its `prelude_rt.bin`, of the same
/// build as its prelude state: `quarz_types::set_prelude_cache`). Without
/// it, every table is made at start-up.
pub fn set_snapshot(bytes: &'static [u8]) {
    let _ = BYTES.set(bytes);
}

/// The snapshot, when there is one and `world` may use it: its world
/// starts with the prelude's classes, methods and extensions (the
/// snapshot's, by name and owner, and by target: the ids line up), and
/// the program changes none of the prelude's share
/// (`World::prelude_unchanged`, over those ids). Otherwise why not
/// (`log`'s words).
pub(crate) fn usable(world: &World) -> Result<&'static PreludeRt, &'static str> {
    let Some(snap) = SNAPSHOT
        .get_or_init(|| BYTES.get().map(|b| PreludeRt::decode(b)))
        .as_ref()
    else {
        return Err("none");
    };
    let (pc, pm, pe) = (
        snap.class_names.len(),
        snap.method_names.len(),
        snap.extension_targets.len(),
    );
    let fits = world.classes.len() >= pc
        && world.methods.len() >= pm
        && world.extensions.len() >= pe
        && world.classes[..pc]
            .iter()
            .map(|c| &c.name)
            .eq(snap.class_names.iter())
        && world.methods[..pm]
            .iter()
            .map(|m| (m.owner, &m.name))
            .eq(snap.method_names.iter().map(|(o, n)| (*o, n)))
        && world.extensions[..pe]
            .iter()
            .map(|e| e.target)
            .eq(snap.extension_targets.iter().copied());
    if !fits {
        return Err("refused: the ids do not line up");
    }
    if !world.prelude_unchanged(pc, pm, pe) {
        return Err("refused: prelude_unchanged");
    }
    Ok(snap)
}

/// In a debug build, with `QUARZ_PRELUDE_SNAPSHOT_LOG` naming a file:
/// what `rtworld::declared_table` did with the snapshot, a line appended
/// per call (`taken`, `taken, compared`, `refused: ...`, `none`), for the
/// tests that show the path (`tests/run.rs`) and for counting
/// it over the cogs. Nothing in a release build.
pub(crate) fn log(outcome: &str) {
    if !cfg!(debug_assertions) {
        return;
    }
    let Some(path) = std::env::var_os("QUARZ_PRELUDE_SNAPSHOT_LOG") else {
        return;
    };
    use std::io::Write as _;
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = f.write_all(format!("{outcome}\n").as_bytes());
    }
}

/// Whether the tables taken from the snapshot are made again and
/// compared (`compare`): in a debug build unless `QUARZ_VERIFY=0`, in a
/// release build when `QUARZ_VERIFY` names `prelude` (a comma-separated
/// list).
pub(crate) fn verify() -> bool {
    let var = std::env::var("QUARZ_VERIFY").unwrap_or_default();
    if cfg!(debug_assertions) {
        var != "0"
    } else {
        var.split(',').any(|v| v.trim() == "prelude")
    }
}

/// `made` (from the snapshot) against `again` (every table made at
/// start-up): an internal error naming the first entry that differs.
pub(crate) fn compare(made: &(RtWorld, Vec<Vec<MethodId>>), again: &(RtWorld, Vec<Vec<MethodId>>)) {
    fn first<T: PartialEq + std::fmt::Debug>(what: &str, a: &[T], b: &[T]) {
        if let Some(i) = (0..a.len().max(b.len())).find(|&i| a.get(i) != b.get(i)) {
            panic!(
                "internal error: the prelude's snapshot gave {what}[{i}] = {:?}, made again {:?} (#551)",
                a.get(i),
                b.get(i)
            );
        }
    }
    let ((a, at), (b, bt)) = (made, again);
    first("classes", &a.classes, &b.classes);
    first("methods", &a.methods, &b.methods);
    first("override table", at, bt);
    first("witness_record", &a.witness_record, &b.witness_record);
    first(
        "include_overrides",
        &a.include_overrides,
        &b.include_overrides,
    );
    first("override_rows", &a.override_rows, &b.override_rows);
    first("witness_rows", &a.witness_rows, &b.witness_rows);
    first(
        "class_override_rows",
        &a.class_override_rows,
        &b.class_override_rows,
    );
    first("extensions", &a.extensions, &b.extensions);
    assert!(
        a == b,
        "internal error: the prelude's snapshot gave other tables than made again (#551)"
    );
}
