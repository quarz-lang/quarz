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
    if !fits && std::env::var_os("QUARZ_DIAG1098").is_some() {
        let c1 = world.classes.len() >= pc && world.classes[..pc].iter().map(|c| &c.name).eq(snap.class_names.iter());
        let c2 = world.methods.len() >= pm && world.methods[..pm].iter().map(|m| (m.owner, &m.name)).eq(snap.method_names.iter().map(|(o, n)| (*o, n)));
        let c3 = world.extensions.len() >= pe && world.extensions[..pe].iter().map(|e| e.target).eq(snap.extension_targets.iter().copied());
        eprintln!("DIAG1098 classes={c1} methods={c2} extensions={c3} pc={pc} pm={pm} pe={pe} wc={} wm={} we={}", world.classes.len(), world.methods.len(), world.extensions.len());
        if !c2 {
            if let Some((i, (m, (o, n)))) = world.methods.iter().zip(snap.method_names.iter()).enumerate().find(|(_, (m, (o, n)))| (m.owner, &m.name) != (*o, n)) {
                eprintln!("DIAG1098 method {i}: world {}#{} snap {}#{}", world.class(m.owner).name, m.name, world.class(*o).name, n);
            }
        }
        if !c1 {
            if let Some((i, (c, n))) = world.classes.iter().zip(snap.class_names.iter()).enumerate().find(|(_, (c, n))| &c.name != *n) {
                eprintln!("DIAG1098 class {i}: world {} snap {}", c.name, n);
            }
        }
    }
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

/// PROBE (#551 estimate, not for merging): what of the prelude's share a
/// refused program changes, against the snapshot.
pub(crate) fn probe(world: &World, full: &(RtWorld, Vec<Vec<MethodId>>)) {
    let Some(snap) = SNAPSHOT
        .get_or_init(|| BYTES.get().map(|b| PreludeRt::decode(b)))
        .as_ref()
    else {
        return;
    };
    let (rt, table) = full;
    let pc = snap.classes.len();
    let pm = snap.methods.len();
    let name = |c: ClassId| world.class(c).name.clone();
    let cd: Vec<String> = (0..pc).filter(|&i| rt.classes[i] != snap.classes[i]).map(|i| name(i as ClassId)).collect();
    let md: Vec<usize> = (0..pm).filter(|&i| rt.methods[i] != snap.methods[i]).collect();
    let td: Vec<usize> = (0..pm).filter(|&i| table[i] != snap.table[i]).collect();
    let mut owners: Vec<String> = md.iter().chain(td.iter()).map(|&i| name(world.methods[i].owner)).collect();
    owners.sort(); owners.dedup();
    fn rows<T: Ord + Clone>(a: &[T], b: &[T], keep: impl Fn(&T) -> bool) -> (usize, usize, usize) {
        let mut x: Vec<T> = a.iter().filter(|e| keep(e)).cloned().collect();
        let mut y: Vec<T> = b.iter().filter(|e| keep(e)).cloned().collect();
        x.sort(); y.sort();
        let only_x = x.iter().filter(|e| y.binary_search(e).is_err()).count();
        let only_y = y.iter().filter(|e| x.binary_search(e).is_err()).count();
        (y.len(), only_x, only_y)
    }
    let pre3 = |e: &(ClassId, MethodId, MethodId)| (e.0 as usize) < pc;
    let pre3o = |e: &(ClassId, MethodId, Option<MethodId>)| (e.0 as usize) < pc;
    eprintln!("PROBE551 prelude classes {pc}, methods {pm}; program classes {}, methods {}", world.classes.len() - pc, world.methods.len() - pm);
    eprintln!("PROBE551 class rows differing: {} {:?}", cd.len(), cd);
    eprintln!("PROBE551 method rows differing: {}; table entries differing: {}; their owners: {:?}", md.len(), td.len(), owners);
    eprintln!("PROBE551 (snapshot size, only in full, only in snapshot) for prelude keys:");
    eprintln!("PROBE551   include_overrides {:?}", rows(&rt.include_overrides, &snap.include_overrides, pre3));
    eprintln!("PROBE551   override_rows {:?}", rows(&rt.override_rows, &snap.override_rows, pre3));
    eprintln!("PROBE551   class_override_rows {:?}", rows(&rt.class_override_rows, &snap.class_override_rows, pre3));
    eprintln!("PROBE551   witness_rows {:?}", rows(&rt.witness_rows, &snap.witness_rows, pre3o));
    eprintln!("PROBE551   witness_record {:?}", rows(&rt.witness_record, &snap.record, pre3o));
}

/// PROBE: the snapshot whatever `usable` says.
pub(crate) fn snapshot_any() -> Option<&'static PreludeRt> {
    SNAPSHOT
        .get_or_init(|| BYTES.get().map(|b| PreludeRt::decode(b)))
        .as_ref()
}
