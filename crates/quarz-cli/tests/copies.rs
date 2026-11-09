//! Collections updated in place stay in place: the programs in `copies/`
//! are run with `QUARZ_COUNT_COPIES`, on the VM and compiled, and the
//! number of updates that had to copy a shared
//! collection is checked. A regression here (a reference left behind in
//! a register, an argument copied instead of moved) makes a loop of
//! updates quadratic while its output stays the same, so the other
//! tests cannot see it.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn program(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/copies")
        .join(name)
}

/// The count `QUARZ_COUNT_COPIES` reported on standard error (the line
/// ending in `suffix`).
fn counted(out: &Output, what: &str, suffix: &str) -> u64 {
    assert!(
        out.status.success(),
        "{what} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let err = String::from_utf8_lossy(&out.stderr);
    err.lines()
        .find_map(|l| {
            l.strip_prefix("quarz: ")?
                .strip_suffix(suffix)?
                .parse()
                .ok()
        })
        .unwrap_or_else(|| panic!("{what}: no count in {err:?}"))
}

const COPIES: &str = " copies of shared collections";
const MOVED: &str = " values moved across Task.blocking";

fn on_vm(path: &Path, suffix: &str) -> u64 {
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(path)
        .env("QUARZ_COUNT_COPIES", "1")
        .output()
        .expect("run quarz");
    counted(&out, &format!("quarz run {}", path.display()), suffix)
}

fn compiled(path: &Path, suffix: &str) -> u64 {
    // One directory per program: the tests run in parallel.
    let dir = std::env::temp_dir().join(format!(
        "quarz-copies-test-{}-{}",
        std::process::id(),
        path.file_stem().unwrap().to_string_lossy()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let exe = dir.join(path.file_stem().unwrap());
    let built = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("build")
        .arg(path)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("run quarz build");
    assert!(
        built.status.success(),
        "quarz build {}: {}",
        path.display(),
        String::from_utf8_lossy(&built.stderr)
    );
    let out = Command::new(&exe)
        .env("QUARZ_COUNT_COPIES", "1")
        .output()
        .expect("run the executable");
    let _ = std::fs::remove_dir_all(&dir);
    counted(&out, &format!("{} (compiled)", path.display()), suffix)
}

fn check(name: &str, want: u64) {
    let path = program(name);
    assert_eq!(on_vm(&path, COPIES), want, "{name} on the VM");
    assert_eq!(compiled(&path, COPIES), want, "{name} compiled");
}

#[test]
fn updates_of_unshared_collections_copy_nothing() {
    check("in_place.qz", 0);
}

/// The count itself: each update of a collection still referred to
/// elsewhere copies it once.
#[test]
fn updates_of_shared_collections_copy_once_each() {
    check("shared.qz", 3);
}

#[test]
fn an_early_exit_from_any_or_all_leaves_no_reference_behind() {
    check("early_exit.qz", 0);
}

#[test]
fn a_break_out_of_a_loop_leaves_no_reference_behind() {
    check("break_exit.qz", 0);
}

#[test]
fn a_quoted_block_leaves_no_reference_behind() {
    // The `Quoted` given for a block (docs/14 §6), with its captures and
    // its closure's copies, is released after its call.
    check("quoted.qz", 0);
}

#[test]
fn a_field_read_through_a_handle_copies_nothing() {
    // docs/14 §5: `ref.get(self)` is the field read `@items` is.
    check("handles.qz", 0);
}

#[test]
fn task_blocking_moves_the_captures_its_caller_reads_no_more() {
    // #478: of the fixture's captures, those read again, shared with
    // another closure, read by a handler or by the next turn of a loop
    // are copied; the five others (one per call that is their last use)
    // move, on the VM and compiled.
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/blocking_captures.qz");
    assert_eq!(on_vm(&path, MOVED), 5, "on the VM");
    assert_eq!(compiled(&path, MOVED), 5, "compiled");
}
