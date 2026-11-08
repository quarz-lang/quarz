//! The tests of the language and its standard library written in Quarz
//! (`std/test/*_test.qz`, run by `quarz test`): interpreted, compiled,
//! and interpreted with the tests in parallel tasks on four workers; and
//! the examples in the standard library's documentation comments.
//!
//! The interpreted and compiled runs and the examples run one `quarz`
//! process per test file or module, on a pool of threads, as
//! tests/build.rs does (#455): one process over them all took most of the
//! suite's time.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Run `job` on each of `items` on a pool of threads, and give what each
/// returned, in order; every failure is reported, together.
fn pool<T: Sync>(items: &[T], job: impl Fn(&T) -> Result<usize, String> + Sync) -> Vec<usize> {
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .clamp(1, 4);
    let next = AtomicUsize::new(0);
    let results = Mutex::new(vec![0; items.len()]);
    let failures = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                let Some(item) = items.get(i) else {
                    break;
                };
                match job(item) {
                    Ok(n) => results.lock().unwrap()[i] = n,
                    Err(e) => failures.lock().unwrap().push(e),
                }
            });
        }
    });
    let failures = failures.into_inner().unwrap();
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    results.into_inner().unwrap()
}

/// Run `quarz test ARGS` in the repository's root and give the number of
/// tests its summary reports, when every one passed (none failed,
/// pending or omitted).
fn quarz_test(args: &[&str], threads: &str) -> Result<usize, String> {
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("test")
        .args(args)
        .current_dir(root())
        .env("QUARZ_THREADS", threads)
        .output()
        .expect("run quarz test");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    let summary = stdout
        .lines()
        .find(|l| l.contains(" tests, "))
        .unwrap_or_default();
    let tests: usize = summary
        .split(' ')
        .next()
        .and_then(|n| n.parse().ok())
        .unwrap_or(0);
    if out.status.success() && summary.contains(" 0 failures, 0 errors, 0 pendings, 0 omissions") {
        Ok(tests)
    } else {
        Err(format!("quarz test {args:?}:\n{stdout}{stderr}"))
    }
}

/// `std/test/*_test.qz`, relative to the root.
fn test_files() -> Vec<String> {
    let mut files: Vec<String> = std::fs::read_dir(root().join("std/test"))
        .unwrap()
        .filter_map(|e| e.ok()?.file_name().into_string().ok())
        .filter(|n| n.ends_with("_test.qz"))
        .map(|n| format!("std/test/{n}"))
        .collect();
    files.sort();
    files
}

/// At least as many tests as std/test held when this was written: a file
/// whose tests are no longer found fails.
const STD_TESTS: usize = 461;

/// Each test file in a process of its own; every test found and passed,
/// each file running some.
fn each_test_file(release: bool) {
    let files = test_files();
    let tests: usize = pool(&files, |f| {
        let mut args = Vec::new();
        if release {
            args.push("--release");
        }
        args.push(f.as_str());
        match quarz_test(&args, "1")? {
            0 => Err(format!("quarz test {args:?}: no tests found")),
            n => Ok(n),
        }
    })
    .iter()
    .sum();
    assert!(tests >= STD_TESTS, "{tests} tests in std/test");
}

#[test]
fn on_the_vm() {
    each_test_file(false);
}

#[test]
fn compiled() {
    each_test_file(true);
}

/// One process, as it tests the parallel runner itself.
#[test]
fn in_parallel() {
    let tests = quarz_test(&["--parallel=8", "std/test"], "4").unwrap_or_else(|e| panic!("{e}"));
    assert!(tests >= STD_TESTS, "{tests} tests in std/test");
}

/// The examples in the standard library's documentation comments
/// (docs/13-doc-comments.md §4), interpreted and compiled, one module at
/// a time (`--std=NAME`); and its docs' links.
#[test]
fn the_standard_librarys_examples_and_links() {
    let mut runs: Vec<(String, bool)> = Vec::new();
    for e in std::fs::read_dir(root().join("std")).unwrap() {
        let name = e.unwrap().file_name().into_string().unwrap();
        if let Some(module) = name.strip_suffix(".qz") {
            for release in [false, true] {
                runs.push((module.to_string(), release));
            }
        }
    }
    // One pool for both kinds, the longest first: the prelude's,
    // compiled.
    runs.sort_by_key(|(m, r)| (m != "prelude", !*r, m.clone()));
    let counts = pool(&runs, |(module, release)| {
        let flag = format!("--std={module}");
        let mut args = vec![flag.as_str()];
        if *release {
            args.push("--release");
        }
        quarz_test(&args, "1")
    });
    for release in [false, true] {
        let examples: usize = runs
            .iter()
            .zip(&counts)
            .filter(|((_, r), _)| *r == release)
            .map(|(_, n)| n)
            .sum();
        assert!(examples > 0, "no examples (release: {release})");
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
