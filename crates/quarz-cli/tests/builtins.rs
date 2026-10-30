//! The built-in classes: each fixture under `tests/fixtures/builtins`, and
//! each one directly under `tests/fixtures` with a `.out` file, runs on the
//! VM and must print the contents of its `.out` file.

mod common;

use std::fs;
use std::path::{Path, PathBuf};

fn fixtures() -> Vec<PathBuf> {
    fixtures_in("tests/fixtures/builtins")
}

/// The `.qz` files directly in `dir` (relative to the crate), sorted.
fn fixtures_in(dir: &str) -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(dir);
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("fixtures directory")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "qz"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no fixtures in {}", dir.display());
    paths
}

#[test]
fn builtins_print_their_expected_output() {
    for path in fixtures() {
        let expected = fs::read_to_string(path.with_extension("out")).expect("expected output");
        let (code, out) = common::run_path(&path, &[]);
        assert_eq!(code, 0, "{} exited with {code}:\n{out}", path.display());
        assert_eq!(out, expected, "output of {}", path.display());
    }
}

/// The fixtures directly under `tests/fixtures` (language behavior outside
/// the built-in classes: `exit`, flows through `rescue`, `raise K`), each
/// with its `.out`, and exiting with 0 (control_flow.qz with 3: it ends
/// with `exit 3`).
#[test]
fn top_level_fixtures_print_their_expected_output() {
    let paths = fixtures_in("tests/fixtures");
    assert!(paths.len() >= 4, "{paths:?}");
    for path in paths {
        let expected = fs::read_to_string(path.with_extension("out"))
            .unwrap_or_else(|e| panic!("{}: {e}", path.with_extension("out").display()));
        let (code, out) = common::run_path(&path, &[]);
        let status = if path.ends_with("control_flow.qz") {
            3
        } else {
            0
        };
        assert_eq!(
            code,
            status,
            "{} exited with {code}:\n{out}",
            path.display()
        );
        assert_eq!(out, expected, "output of {}", path.display());
    }
}

/// A program whose objects are released as its top level ends finalizes
/// them itself: none is left queued on the thread for the next program
/// there, which would look its class up in its own, smaller, world.
#[test]
fn the_next_program_on_a_thread_finalizes_nothing_of_the_last() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/builtins");
    let (_, out) = common::run_path(&dir.join("deinitialize_copies.qz"), &[]);
    assert!(out.ends_with("copy\nrelease\n"), "{out}");
    common::expect("p 1", "1\n");
}

/// Nor the cyclic garbage it left uncollected: a later collection on the
/// thread would finalize it by the next program's classes.
#[test]
fn the_next_program_on_a_thread_collects_nothing_of_the_last() {
    let (_, out) = common::run(
        "class Node\n  var @peer: Node? = nil\n  def link(n: Node) -> Void\n    @peer = n\n    nil\n  end\n  \
         def deinitialize -> Void\n    puts \"node\"\n  end\nend\n\
         def pair -> Void\n  a = Node.new\n  b = Node.new\n  a.link(b)\n  b.link(a)\n  nil\nend\n\
         3.times { pair }\nputs \"first\"\n",
        &[],
    );
    assert_eq!(out, "first\n");
    // A class of its own at the same id, which the first program's
    // objects must not be finalized as.
    common::expect(
        "class Other\n  var @peer: Other? = nil\n  def deinitialize -> Void\n    puts \"other\"\n  end\nend\n\
         class Cell\n  var @next: Cell? = nil\nend\n\
         30000.times { Cell.new }\nputs \"second\"\n",
        "second\n",
    );
}

/// A `Task.blocking` helper keeps the interpreter of the program it last
/// ran: another program's image, even one allocated where the first's
/// was, gets one of its own.
#[test]
fn task_blocking_runs_each_programs_own_code() {
    for _ in 0..10 {
        for s in ["A", "B"] {
            common::expect(
                &format!("def a -> String = \"{s}\"\nputs Task.blocking {{ a }}\n"),
                &format!("{s}\n"),
            );
        }
    }
}
