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

/// Many programs run in turn on one thread (as the build tests run the
/// fixtures): each starts the cycle collector afresh, so what earlier
/// programs left live is not walked by its collections, which would make
/// them less frequent (#502): after fixtures that leave live candidates
/// (a fixed few, which touch nothing process-wide: the other tests run
/// fixtures in this process at the same time), a program that makes no
/// candidate leaves none listed.
#[test]
fn the_cycle_collector_starts_afresh_for_each_program_on_a_thread() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/builtins");
    for name in [
        "const_init.qz",
        "collections.qz",
        "case_self.qz",
        "bytes_search.qz",
        "cycles.qz",
    ] {
        let _ = common::run_path(&dir.join(name), &[]);
    }
    let after = quarz_vm::cycles::candidates();
    let (_, out) = common::run("p 1\n", &[]);
    assert_eq!(out, "1\n");
    let left = quarz_vm::cycles::candidates();
    assert_eq!(left, 0, "{after} after the fixtures");
}

/// A native written once (#1035) answers a call that comes with a block
/// or a keyword as its old generic form did, which read only the
/// positional arguments: the generic form hands them to the twin whatever
/// comes with them, and never reaches the twin's "declined" error.
#[test]
fn one_definition_generic_forms_ignore_block_and_keywords() {
    use quarz_vm::interp::{ArgList, Args};
    use quarz_vm::value::Value;
    quarz_vm::Interp::install_interpreter();
    let interp = quarz_vm::Interp::new(common::lower("puts 1\n"), Vec::new());
    let plain = quarz_vm::natives::all().plain.map();
    let s = Value::str("héllo");
    let other = Value::str("abc");
    let arr = Value::array(vec![Value::Int(1), Value::Int(2)]);
    let hash = Value::Hash(quarz_vm::rc::Rc::new(Default::default()));
    let cases: Vec<(&str, &Value, Vec<Value>)> = vec![
        ("String#size", &s, vec![]),
        ("String#length", &s, vec![]),
        ("String#bytesize", &s, vec![]),
        ("String#empty?", &s, vec![]),
        ("String#==", &s, vec![other.clone()]),
        ("String#<", &s, vec![other.clone()]),
        ("String#<=", &s, vec![other.clone()]),
        ("String#>", &s, vec![other.clone()]),
        ("String#>=", &s, vec![other.clone()]),
        ("String#include?", &s, vec![Value::str("ll")]),
        ("String#upcase", &s, vec![]),
        ("String#downcase", &s, vec![]),
        ("String#+", &s, vec![other.clone()]),
        ("String#to_s", &s, vec![]),
        ("Array#size", &arr, vec![]),
        ("Array#length", &arr, vec![]),
        ("Array#empty?", &arr, vec![]),
        ("Hash#size", &hash, vec![]),
        ("Hash#length", &hash, vec![]),
        ("Hash#empty?", &hash, vec![]),
    ];
    for (key, recv, args) in cases {
        let f = plain[key];
        let call = |kw: Vec<_>, block: Option<Value>| {
            f(
                &interp,
                recv,
                Args {
                    pos: ArgList::Borrowed(&args),
                    kw,
                    block,
                },
            )
            .unwrap_or_else(|_| panic!("`{key}` raised"))
        };
        let plain_answer = call(Vec::new(), None);
        let with_extras = call(
            vec![(interp.intern("extra"), Value::Int(1))],
            Some(Value::Nil),
        );
        assert_eq!(
            plain_answer, with_extras,
            "`{key}` with a block and a keyword"
        );
    }
}

/// Each native of `quarz_ir::live::NE_NEGATES_EQ` answers `Value::eq`'s
/// answer for a receiver of its class, and `Object#!=` (`obj_ne`) there is
/// its negation (#795): what lets the lowering rewrite `x != y` into that
/// `==` and a `Not`. Over both forms of a string (inline and counted),
/// byte strings (the same one and an equal one), and other-typed
/// arguments and nil.
#[test]
fn ne_negates_eq() {
    use quarz_vm::interp::{ArgList, Args};
    use quarz_vm::value::Value;
    quarz_vm::Interp::install_interpreter();
    let interp = quarz_vm::Interp::new(common::lower("puts 1\n"), Vec::new());
    let plain = quarz_vm::natives::all().plain.map();
    let obj_ne = plain["Object#!="];
    let long = "a string longer than fourteen bytes";
    let bytes = |s: &str| Value::Bytes(quarz_vm::rc::Rc::from(s.as_bytes()));
    let same_bytes = bytes("abc");
    let strings = vec![
        Value::str(""),
        Value::str("abc"),
        Value::str("abd"),
        Value::str("é"),
        Value::str(long),
        Value::Str(quarz_vm::rc::Rc::from("abc")),
        Value::Str(quarz_vm::rc::Rc::from(long)),
    ];
    let others = vec![Value::Int(1), Value::Nil, Value::Bool(true), bytes("abc")];
    let byte_strings = vec![same_bytes.clone(), bytes("abc"), bytes("abd"), bytes("")];
    let byte_others = vec![Value::str("abc"), Value::Int(1), Value::Nil];
    for key in quarz_ir::live::NE_NEGATES_EQ {
        let (recvs, args): (&[Value], Vec<Value>) = match key {
            "String#==" => (&strings, strings.iter().chain(&others).cloned().collect()),
            "Bytes#==" => (
                &byte_strings,
                byte_strings.iter().chain(&byte_others).cloned().collect(),
            ),
            _ => panic!("`{key}` is listed but not covered by this test"),
        };
        let eq = plain[key];
        for r in recvs {
            for a in &args {
                let call = |f: quarz_vm::interp::NativeFn| {
                    let pos = [a.clone()];
                    f(
                        &interp,
                        r,
                        Args {
                            pos: ArgList::Borrowed(&pos),
                            kw: Vec::new(),
                            block: None,
                        },
                    )
                    .unwrap_or_else(|_| panic!("`{key}` raised"))
                };
                let native = call(eq);
                assert_eq!(
                    native,
                    Value::Bool(r == a),
                    "`{key}` against `Value::eq`: {r:?}, {a:?}"
                );
                assert_eq!(
                    call(obj_ne),
                    Value::Bool(r != a),
                    "`Object#!=`: {r:?}, {a:?}"
                );
            }
        }
    }
}
