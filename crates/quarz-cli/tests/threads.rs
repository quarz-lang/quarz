//! Tasks on several worker threads: the programs in `threads/` run with
//! `QUARZ_THREADS=4`, interpreted and compiled, each a few times (what
//! goes wrong between threads may not go wrong every time), and print
//! the same whatever the scheduling: their `.out`.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const RUNS: usize = 3;

fn program(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/threads")
        .join(name)
}

fn on_vm(path: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(path)
        .env("QUARZ_THREADS", "4")
        .output()
        .expect("run quarz")
}

/// Compile `path` into a directory of its own (the tests run in
/// parallel) and return the executable.
fn compile(path: &Path) -> (PathBuf, PathBuf) {
    let dir = std::env::temp_dir().join(format!(
        "quarz-threads-test-{}-{}",
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
    (dir, exe)
}

/// Run `name` on the VM and compiled, `RUNS` times each, and check each
/// run with `check`.
fn check_runs(name: &str, check: impl Fn(&Output, &str)) {
    let path = program(name);
    for i in 0..RUNS {
        check(&on_vm(&path), &format!("{name} on the VM, run {i}"));
    }
    let (dir, exe) = compile(&path);
    for i in 0..RUNS {
        let out = Command::new(&exe)
            .env("QUARZ_THREADS", "4")
            .output()
            .expect("run the executable");
        check(&out, &format!("{name} compiled, run {i}"));
    }
    let _ = std::fs::remove_dir_all(&dir);
}

fn prints_its_out(name: &str) {
    let want = std::fs::read_to_string(program(name).with_extension("out")).unwrap();
    check_runs(name, |out, what| {
        assert!(
            out.status.success(),
            "{what} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&out.stdout), want, "{what}");
    });
}

#[test]
fn work_spreads_over_workers() {
    prints_its_out("parallel.qz");
}

#[test]
fn channels_and_select_between_workers() {
    prints_its_out("channels.qz");
}

#[test]
fn scopes_cancellation_and_exceptions_between_workers() {
    prints_its_out("scopes.qz");
}

#[test]
fn atoms_and_constants_from_every_worker() {
    prints_its_out("atoms.qz");
}

#[test]
fn shareable_procedures_called_from_every_worker() {
    prints_its_out("shareable_procs.qz");
}

#[test]
fn exit_in_a_task_on_another_worker() {
    check_runs("exit.qz", |out, what| {
        assert_eq!(out.status.code(), Some(7), "{what}");
        assert!(out.stdout.is_empty(), "{what}");
    });
}

#[test]
fn deadlock_across_workers() {
    check_runs("deadlock.qz", |out, what| {
        assert_eq!(out.status.code(), Some(1), "{what}");
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(err.contains("DeadlockError"), "{what}: {err}");
    });
}
