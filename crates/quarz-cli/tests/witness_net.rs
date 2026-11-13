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

/// #557: another module's witness has a row (R0 records it), checked per
/// class in its own frame: `Holds[T]#get -> T` passes for `Holds[Int]` and
/// is refused for `Holds[String]` (R0's run-time-signature disjunct lets it
/// through, #641's note).
#[test]
fn another_modules_witness_has_a_row_checked_per_class() {
    let base = "module Num\n  abstract def get -> Int\nend\nmodule Holds[T]\n  def get -> T = held\n  abstract def held -> T\nend\nclass K3\n  def initialize; end\n  def held -> Int = 41\nend\nmodule S3\n  extension K3\n    include Holds[Int]\n    include Num\n  end\n  def self.n(x: K3) -> Num = x\nend\n";
    let (code, err) = check(&format!("{base}puts S3.n(K3.new).get + 1\n"));
    assert_eq!(code, Some(0), "{err}");
    refused(
        &format!("{base}class K4\n  def initialize; end\n  def held -> String = \"s\"\nend\nmodule S4\n  extension K4\n    include Holds[String]\n    include Num\n  end\nend\nputs 1\n"),
        &["error: `K4`'s conformance to `Num` runs `Holds#get` for `Num#get`, which does not take its place for `K4`"],
    );
}

/// #632: a scoped extension's conformance whose witness the class
/// inherits has a row (R0 records it), and each class's row is checked in
/// its own frame: `Base#get -> T` passes for `A < Base[Int]` and is refused
/// for `B < Base[String]` (R0's run-time-signature disjunct lets it
/// through, #641's note).
#[test]
fn an_inherited_witness_has_a_row_checked_per_class() {
    let base = "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def get -> T = @v\nend\nclass A < Base[Int]\n  def initialize; super(1); end\nend\nmodule SA\n  extension A\n    include M\n  end\n  def self.m(x: A) -> M = x\nend\n";
    let (code, err) = check(&format!("{base}puts SA.m(A.new).get + 1\n"));
    assert_eq!(code, Some(0), "{err}");
    refused(
        &format!("{base}class B < Base[String]\n  def initialize; super(\"s\"); end\nend\nmodule SB\n  extension B\n    include M\n  end\nend\nputs 1\n"),
        &["error: `B`'s conformance to `M` runs `Base#get` for `M#get`, which does not take its place for `B`"],
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

/// #557's shape (the witness is another module's the extension includes)
/// has a row since R0 records it, and is accepted; an abstract class's row
/// with no implementation is not an error (no instances; its subclass's
/// row passes).
#[test]
fn rows_with_no_implementation_by_kind() {
    let (code, err) = check(
        "module Named\n  abstract def label -> String\nend\nmodule Gives\n  def label -> String = \"Gives\"\nend\nclass K\n  def initialize; end\nend\nmodule S2\n  extension K\n    include Gives\n    include Named\n  end\n  def self.n(k: K) -> Named = k\nend\nputs 1\n",
    );
    assert_eq!(code, Some(0), "{err}");
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

/// `quarz check` of a program of two files, `lib.qz` and `main.qz` (which
/// requires it): exit code and standard error.
fn check_two(lib: &str, main: &str) -> (Option<i32>, String) {
    static N: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "quarz-witness-net-two-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.qz"), lib).unwrap();
    std::fs::write(dir.join("main.qz"), main).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("check")
        .arg(dir.join("main.qz"))
        .env("QUARZ_NO_CACHE", "1")
        .output()
        .expect("run quarz");
    std::fs::remove_dir_all(&dir).ok();
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// #645's library: #642's shape, with a `static def` dispatching through
/// the refused row and a `static def self.` class method doing the same.
const LIB_645: &str = "module M\n  def m -> Int = 1\nend\nmodule N\n  def m -> String = \"N\"\n  def nn -> String = m + \"!\"\nend\nextension Int\n  include N\n  include M\nend\ndef via(v: N) -> String = v.nn\nstatic def nn5 -> String = via(5)\nclass Mac\n  static def self.go -> Void\n    puts via(5)\n  end\nend\n";

/// #645: a compile-time run (`static(call)`, a `static` statement) reaching
/// a row the safety net refuses does not run: the net checks each
/// compile-time round's rows first. The row's error is reported once, at
/// the extension (the final net after the check does not report it again:
/// the check failed), and the run's own error (a `TypeError` before) is
/// not reached.
#[test]
fn a_compile_time_run_reaching_a_refused_row_does_not_run() {
    let net = "`Int`'s conformance to `N` runs `M#m` for `N#m`";
    for (main, at) in [
        (
            "require_relative \"lib\"\nputs static(nn5)\n",
            "main.qz:2:13: error: `nn5` did not run",
        ),
        (
            "require_relative \"lib\"\nclass App < Mac\n  go\nend\nputs 1\n",
            "main.qz:3:3: error: `go` did not run",
        ),
    ] {
        let (code, err) = check_two(LIB_645, main);
        assert_eq!(code, Some(1), "{err}");
        assert_eq!(err.matches(net).count(), 1, "{err}");
        assert!(err.contains("lib.qz:8:1: error: "), "{err}");
        assert!(err.contains(at), "{err}");
        assert!(!err.contains("TypeError"), "{err}");
    }
}

/// The witness record's oracle (#536 step 3, S1) excludes two families
/// from its assertion, by their shape: #529's (two conditional extensions'
/// same-named methods) and #662's (a scoped extension's own method running
/// for a module the class has itself). S2 makes the rows read the record,
/// and these counts go to zero.
#[test]
fn the_witness_oracle_excludes_only_529_and_662() {
    let summary = |src: &str| {
        static N: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "quarz-witness-oracle-{}-{}",
            std::process::id(),
            N.fetch_add(1, Ordering::SeqCst)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("main.qz");
        std::fs::write(&path, src).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
            .arg("check")
            .arg(&path)
            .env("QUARZ_WITNESS_ORACLE", "report")
            .env("QUARZ_NO_CACHE", "1")
            .output()
            .expect("run quarz");
        std::fs::remove_dir_all(&dir).ok();
        String::from_utf8_lossy(&out.stderr)
            .lines()
            .find(|l| l.starts_with("witness-oracle: summary"))
            .unwrap_or_default()
            .to_string()
    };
    let s = summary(R529_ORACLE);
    assert!(
        s.contains("ext 0/") && s.contains("own 0/") && s.contains("excluded #529 1, #662 0"),
        "{s}"
    );
    let s = summary(T3_ORACLE);
    assert!(
        s.contains("ext 0/") && s.contains("own 0/") && s.contains("excluded #529 0, #662 1"),
        "{s}"
    );
}
const R529_ORACLE: &str = "module PI\n  abstract def parse(s: String) -> Int\n  abstract def self.make(s: String) -> Int\nend\nmodule PS\n  abstract def parse(s: String) -> String\n  abstract def self.make(s: String) -> String\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\nend\nextension Box[T <: Int]\n  include PI\n  def parse(s: String) -> Int = @v + s.to_i\n  def self.make(s: String) -> Int = 1\nend\nextension Box[T <: String]\n  include PS\n  def parse(s: String) -> String = @v + s\n  def self.make(s: String) -> String = \"two\"\nend\ndef ps(x: PS) -> String = x.parse(\"!\")\na: PS = Box[String].new(\"x\")\np a.parse(\"1\")\np ps(a)\n";
const T3_ORACLE: &str = "module M\n  abstract def m -> String\nend\nmodule N\n  include M\n  abstract def n -> String\nend\nclass K\n  include M\n  def initialize; end\n  def m -> String = \"own\"\nend\nmodule X\n  extension K\n    include N\n    def m -> String = \"ext-m\"\n    def n -> String = \"ext-n\"\n  end\n  def self.as_n(k: K) -> N = k\n  def self.direct(k: K) -> String = k.m\nend\ndef via_m(x: M) -> String = x.m\ndef via_n(x: N) -> String = x.m + \",\" + x.n\nputs via_m(K.new), via_n(X.as_n(K.new)), X.direct(K.new)\n";
