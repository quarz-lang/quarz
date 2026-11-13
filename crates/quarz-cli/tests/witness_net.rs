//! The safety net's report (`QUARZ_WITNESS_NET=report`,
//! `quarz_types::witness_net`): every witness row the runtime reads,
//! checked for its own class. A refused row or one with no implementation
//! is a compile error since the error stage (tests/diagnostics.rs); the
//! report lists the rows of the programs the command still runs.

mod common;

use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

/// The net's lines for `quarz run` of `path`, the prelude's own pairs
/// (#622) left out.
fn report_of(path: &Path) -> Vec<String> {
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(path)
        .env("QUARZ_WITNESS_NET", "report")
        .env("QUARZ_NO_CACHE", "1")
        .output()
        .expect("run quarz");
    String::from_utf8_lossy(&out.stderr)
        .lines()
        .filter(|l| l.starts_with("witness-net:"))
        .filter(|l| {
            ![
                "  Set  Enumerable#",
                "  Hash  Enumerable#",
                "  Hash::Builder  Enumerable#",
            ]
            .iter()
            .any(|p| l.contains(p))
        })
        .map(str::to_string)
        .collect()
}

/// `report_of` for a program given as source.
fn report(src: &str) -> Vec<String> {
    static N: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "quarz-witness-net-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.qz");
    std::fs::write(&path, src).unwrap();
    let lines = report_of(&path);
    std::fs::remove_dir_all(&dir).ok();
    lines
}

/// `quarz check` of a program given as source: its exit code and its
/// standard error.
fn check(src: &str) -> (Option<i32>, String) {
    static N: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "quarz-witness-net-check-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.qz");
    std::fs::write(&path, src).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("check")
        .arg(&path)
        .env("QUARZ_NO_CACHE", "1")
        .output()
        .expect("run quarz");
    std::fs::remove_dir_all(&dir).ok();
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// `check` refuses `src` with each of `wants` in its errors.
fn refused(src: &str, wants: &[&str]) {
    let (code, err) = check(src);
    assert_eq!(code, Some(1), "{err}");
    for w in wants {
        assert!(err.contains(w), "missing {w:?} in:\n{err}");
    }
}

/// The error stage (decided on #536): a refused row is a compile error at
/// what makes the conformance. #641: an extension's conformance taking the
/// inherited `Base#get -> String` of `B < Base[String]` for `M#get -> Int`.
#[test]
fn a_refused_row_is_an_error_at_the_extension() {
    refused(
        T2C,
        &[
            "main.qz:18:1: error: `B`'s conformance to `M` runs `Base#get` for `M#get`, which does not take its place for `B`",
            "returns String",
        ],
    );
}
const T2C: &str = "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def get -> T = @v\nend\nclass A < Base[Int]\n  def initialize; super(1); end\nend\nclass B < Base[String]\n  def initialize; super(\"s\"); end\nend\nextension A\n  include M\nend\nextension B\n  include M\nend\ndef via(m: M) -> Int = m.get + 1\nputs via(A.new)\nputs via(B.new)\n";

/// #642: two modules that extensions of a std class include, one's method
/// over the other's, in one extension and in two.
#[test]
fn modules_an_extension_of_a_std_class_includes_are_checked() {
    for src in [S8, S6] {
        refused(
            src,
            &["error: `Int`'s conformance to `N` runs `M#m` for `N#m`, which does not take its place for `Int`"],
        );
    }
}
const S8: &str = "# std class: one extension, two includes (the last include first)\nmodule M\n  def m -> Int = 1\nend\nmodule N\n  def m -> String = \"N\"\n  def nn -> String = m + \"!\"\nend\nextension Int\n  include N\n  include M\nend\ndef via(v: N) -> String = v.nn\nputs via(5)\n";
const S6: &str = "# std class: two top-level extensions' modules, one's method over the other's\nmodule M\n  def m -> Int = 1\nend\nmodule N\n  def m -> String = \"N\"\n  def nn -> String = m + \"!\"\nend\nextension Int\n  include M\nend\nextension Int\n  include N\nend\ndef via(v: N) -> String = v.nn\nputs via(5)\n";

/// #529's row choice (two conditional extensions, the wrong one's method
/// for `PS#parse`) is refused, failing safe; #529 stays open for the
/// choice itself.
#[test]
fn the_529_row_is_refused() {
    refused(
        R529,
        &["error: `Box`'s conformance to `PS` runs `Box#parse` for `PS#parse`"],
    );
}
const R529: &str = "module PI\n  abstract def parse(s: String) -> Int\n  abstract def self.make(s: String) -> Int\nend\nmodule PS\n  abstract def parse(s: String) -> String\n  abstract def self.make(s: String) -> String\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\nend\nextension Box[T <: Int]\n  include PI\n  def parse(s: String) -> Int = @v + s.to_i\n  def self.make(s: String) -> Int = 1\nend\nextension Box[T <: String]\n  include PS\n  def parse(s: String) -> String = @v + s\n  def self.make(s: String) -> String = \"two\"\nend\ndef ps(x: PS) -> String = x.parse(\"!\")\na: PS = Box[String].new(\"x\")\np a.parse(\"1\")\np ps(a)\n";

/// #629's row (the rescan's overload of another parameter type), never
/// read, is refused like any other until #629 is decided.
#[test]
fn the_629_row_is_refused() {
    refused(
        F1,
        &[
            "error: `K`'s conformance to `M` runs `K#m` for `M#m`",
            "takes Int for `x`",
        ],
    );
}
const F1: &str = "# an extension's overload of another parameter type beside the class's own implementation\nmodule M\n  abstract def m(x: String) -> String\n  def mm -> String = m(\"s\") + \"!\"\nend\nclass K\n  def initialize; end\n  def m(x: String) -> String = \"K\"\nend\nmodule Sc\n  extension K\n    include M\n    def m(x: Int) -> String = \"ext#{x + 1}\"\n  end\n  def self.up(k: K) -> M = k\n  def self.n(k: K) -> String = k.m(1)\nend\ndef via(v: M) -> String = v.mm\nputs via(Sc.up(K.new))\nputs Sc.n(K.new)\n";

/// A row with no implementation is an error. #632's shape (a scoped
/// extension's conformance whose witness the class inherits, which the
/// run time does not find yet) says so; the program raised at run time
/// before the error stage.
#[test]
fn a_row_with_no_implementation_is_an_error() {
    refused(
        "module Named\n  abstract def label -> String\nend\nclass A\n  def initialize; end\n  def label -> String = \"a\"\nend\nclass B < A\n  def initialize; end\nend\nmodule Sc\n  extension B\n    include Named\n  end\n  def self.n(x: B) -> Named = x\nend\nputs 1\n",
        &["main.qz:12:3: error: `B`'s conformance to `Named` has no implementation of `Named#label` at run time: the witness is a method `B` has on its own side, which an extension's conformance does not find yet (#632)"],
    );
}

/// A program whose rows all pass checks.
#[test]
fn a_program_whose_rows_pass_checks() {
    let (code, err) = check(
        "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def get -> T = @v\nend\nclass A < Base[Int]\n  def initialize; super(1); end\nend\nextension A\n  include M\nend\ndef via(m: M) -> Int = m.get + 1\nputs via(A.new)\n",
    );
    assert_eq!(code, Some(0), "{err}");
}

/// One method checked in each receiver's frame: `Base#get -> T` for `M#get
/// -> Int` passes for `A < Base[Int]` and is refused for `B < Base[String]`
/// (the class side's form of #608; an extension's method for an own include,
/// #608's own form, is refused at compile time since rule A).
#[test]
fn a_method_is_checked_in_each_receivers_frame() {
    let lines = report(
        "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\n  def get -> T = v\nend\nclass A < Base[Int]\n  include M\n  def initialize; super(1); end\nend\nclass B < Base[String]\n  include M\n  def initialize; super(\"s\"); end\nend\ndef via(m: M) -> Int = m.get + 1\nputs via(A.new)\n",
    );
    let refused: Vec<&String> = lines
        .iter()
        .filter(|l| l.starts_with("witness-net: refused "))
        .collect();
    assert!(
        refused
            .iter()
            .any(|l| l.contains("  B  M#get  by Base#get") && l.contains("returns String")),
        "{lines:#?}"
    );
    assert!(
        !refused.iter().any(|l| l.contains("  A  M#get")),
        "{lines:#?}"
    );
}

/// #604's round 2: a row whose conditional bound fails for the class's own
/// arguments is still reached by variance; here its witness is sound and
/// passes.
#[test]
fn a_row_reached_by_variance_is_checked_and_passes() {
    let lines = report(
        "class Animal\n  def initialize; end\nend\nclass Dog < Animal\n  def initialize; end\nend\nmodule M\n  abstract def m -> Int\nend\nclass Sink[in T]\n  def initialize; end\nend\nextension Sink[T <: Animal]\n  include M\n  def m -> Int = 1\nend\nclass CSub < Sink[Object]\n  def initialize; end\n  def m -> String = \"csub\"\nend\ndef via(x: M) -> Int = x.m + 1\ndef dogs(s: Sink[Dog]) -> Int = via(s)\nputs dogs(CSub.new)\n",
    );
    assert!(
        !lines.iter().any(|l| l.starts_with("witness-net: refused ")),
        "{lines:#?}"
    );
    assert!(lines.iter().any(|l| l.contains("summary")), "{lines:#?}");
}

/// The report over every fixture and example (run on demand: `cargo test
/// --test witness_net -- --ignored --nocapture`): each line, and no row
/// without a frame.
#[test]
#[ignore]
fn report_over_the_fixtures() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files: Vec<std::path::PathBuf> = Vec::new();
    for dir in [root.join("tests/fixtures"), root.join("../../examples")] {
        let mut stack = vec![dir];
        while let Some(d) = stack.pop() {
            for e in std::fs::read_dir(&d).unwrap().flatten() {
                let p = e.path();
                if p.is_dir() {
                    stack.push(p);
                } else if p.extension().is_some_and(|x| x == "qz") {
                    files.push(p);
                }
            }
        }
    }
    files.sort();
    for f in &files {
        for l in report_of(f) {
            assert!(!l.contains("no-frame"), "{}: {l}", f.display());
            if !l.contains("summary") {
                println!("{}: {l}", f.display());
            }
        }
    }
}

/// #599: a gated send's first dispatch for a class outside the witness
/// rows' key set is an internal error (`check_gated_key`): the gate makes
/// it unreachable, so the panic is shown on the function itself, with
/// `Nil`, which is not `Comparable`.
#[test]
#[should_panic(expected = "not a key of the witness rows")]
fn a_gated_send_outside_the_key_set_is_an_internal_error() {
    let module = common::lower("puts 1\n");
    let world = &module.world;
    let cmp = world.builtin.comparable;
    let req = world.class(cmp).methods["<=>"]
        .iter()
        .copied()
        .find(|&m| world.method(m).owner == cmp)
        .expect("Comparable#<=>");
    let method = |id: quarz_ir::MethodId| world.method(id);
    assert!(world.in_witness_rows(&method, world.builtin.int, req));
    quarz_vm::interp::check_gated_key(world, &method, world.builtin.nil, req, "<=>");
}

/// #557's shape (the witness is another module's the extension includes,
/// which the run time does not find yet) is refused and says so; an
/// abstract class's row with no implementation is not an error (no
/// instances; its subclass's row passes).
#[test]
fn rows_with_no_implementation_by_kind() {
    refused(
        "module Named\n  abstract def label -> String\nend\nmodule Gives\n  def label -> String = \"Gives\"\nend\nclass K\n  def initialize; end\nend\nmodule S2\n  extension K\n    include Gives\n    include Named\n  end\n  def self.n(k: K) -> Named = k\nend\nputs 1\n",
        &["`K`'s conformance to `Named` has no implementation of `Named#label` at run time: the witness is `Gives#label` of another module `K` conforms to, which the run time does not find yet (#557)"],
    );
    let (code, err) = check(
        "module M\n  abstract def label -> String\n  def show -> String = label + \"!\"\nend\nabstract class Base\n  def initialize; end\n  abstract def label -> String\nend\nclass Impl < Base\n  def initialize; end\n  def label -> String = \"impl\"\nend\nmodule Sc\n  extension Base\n    include M\n  end\n  def self.b(x: Base) -> M = x\nend\nputs Sc.b(Impl.new).show\n",
    );
    assert_eq!(code, Some(0), "{err}");
}

/// Only no-impl is exempt for an abstract class: a refused row of an
/// abstract class is an error (the concrete `A2` first: the checker checks
/// the pair once, for `A2`, #641).
#[test]
fn a_refused_row_of_an_abstract_class_is_an_error() {
    refused(
        "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def get -> T = @v\nend\nclass A2 < Base[Int]\n  def initialize; super(1); end\nend\nextension A2\n  include M\nend\nabstract class B2 < Base[String]\n  def initialize; super(\"s\"); end\nend\nextension B2\n  include M\nend\nputs 1\n",
        &["main.qz:18:1: error: `B2`'s conformance to `M` runs `Base#get` for `M#get`, which does not take its place for `B2`"],
    );
}
