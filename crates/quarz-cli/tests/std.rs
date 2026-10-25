//! The tests of the language and its standard library written in Quarz
//! (`std/test/*_test.qz`, run by `quarz test`): interpreted, compiled,
//! and interpreted with the tests in parallel tasks on four workers.

use std::path::{Path, PathBuf};
use std::process::Command;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn quarz_test(args: &[&str], threads: &str) {
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("test")
        .args(args)
        .arg("std/test")
        .current_dir(root())
        .env("QUARZ_THREADS", threads)
        .output()
        .expect("run quarz test");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    // Every test found and passed: none failed, pending or omitted.
    let summary = stdout
        .lines()
        .find(|l| l.contains(" tests, "))
        .unwrap_or_default();
    let tests: usize = summary
        .split(' ')
        .next()
        .and_then(|n| n.parse().ok())
        .unwrap_or(0);
    assert!(
        out.status.success()
            && tests >= 293
            && summary.contains(" 0 failures, 0 errors, 0 pendings, 0 omissions"),
        "quarz test {args:?} std/test:\n{stdout}{stderr}"
    );
}

#[test]
fn on_the_vm() {
    quarz_test(&[], "1");
}

#[test]
fn compiled() {
    quarz_test(&["--release"], "1");
}

#[test]
fn in_parallel() {
    quarz_test(&["--parallel=8"], "4");
}

/// The examples in the standard library's documentation comments
/// (docs/13-doc-comments.md §4), interpreted and compiled, and its docs'
/// links.
#[test]
fn the_standard_librarys_examples_and_links() {
    for release in [false, true] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_quarz"));
        cmd.arg("test");
        if release {
            cmd.arg("--release");
        }
        let out = cmd
            .args(["--doc", "--std"])
            .current_dir(root())
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            out.status.success()
                && stdout.contains(" 0 failures, 0 errors")
                && !stdout.contains("\n0 tests"),
            "quarz test --doc --std (release: {release}):\n{stdout}{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(["doc", "--std", "--check"])
        .current_dir(root())
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
