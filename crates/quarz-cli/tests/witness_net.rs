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

/// #641: an extension's conformance whose only candidate is the inherited
/// `Base#get -> String` of `B < Base[String]` for `M#get -> Int`. Since
/// #656's decision (a), R0 refuses it at the extension (the candidate's
/// result is checked too), before the net would see the row.
#[test]
fn a_refused_row_is_an_error_at_the_extension() {
    refused(
        T2C,
        &["main.qz:18:11: error: this extension includes `M` but nothing here implements `get`: define it in the extension or in `B`"],
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

/// #629's row (the rescan's overload of another parameter type): since
/// #536 step 3's S2 the rows read the witness record, which names the
/// method that takes the requirement's place by type (`K#m`), so the net
/// passes it (the fixture `rescan_overload_is_no_witness` runs it).
#[test]
fn the_629_row_reads_the_record() {
    let (code, err) = check(F1);
    assert_eq!(code, Some(0), "{err}");
}
const F1: &str = "# an extension's overload of another parameter type beside the class's own implementation\nmodule M\n  abstract def m(x: String) -> String\n  def mm -> String = m(\"s\") + \"!\"\nend\nclass K\n  def initialize; end\n  def m(x: String) -> String = \"K\"\nend\nmodule Sc\n  extension K\n    include M\n    def m(x: Int) -> String = \"ext#{x + 1}\"\n  end\n  def self.up(k: K) -> M = k\n  def self.n(k: K) -> String = k.m(1)\nend\ndef via(v: M) -> String = v.mm\nputs via(Sc.up(K.new))\nputs Sc.n(K.new)\n";

/// #557: another module's witness has a row (R0 records it), checked per
/// class in its own frame: `Holds[T]#get -> T` passes for `Holds[Int]`; for
/// `Holds[String]` R0 refuses it at the extension, its result checked too
/// (#656's decision (a)).
#[test]
fn another_modules_witness_has_a_row_checked_per_class() {
    let base = "module Num\n  abstract def get -> Int\nend\nmodule Holds[T]\n  def get -> T = held\n  abstract def held -> T\nend\nclass K3\n  def initialize; end\n  def held -> Int = 41\nend\nmodule S3\n  extension K3\n    include Holds[Int]\n    include Num\n  end\n  def self.n(x: K3) -> Num = x\nend\n";
    let (code, err) = check(&format!("{base}puts S3.n(K3.new).get + 1\n"));
    assert_eq!(code, Some(0), "{err}");
    refused(
        &format!("{base}class K4\n  def initialize; end\n  def held -> String = \"s\"\nend\nmodule S4\n  extension K4\n    include Holds[String]\n    include Num\n  end\nend\nputs 1\n"),
        &["error: this extension includes `Num` but nothing here implements `get`: define it in the extension or in `K4`"],
    );
}

/// #632: a scoped extension's conformance whose witness the class
/// inherits has a row (R0 records it), checked in its own frame: `Base#get
/// -> T` passes for `A < Base[Int]`; for `B < Base[String]` R0 refuses it at
/// the extension, its result checked too (#656's decision (a)).
#[test]
fn an_inherited_witness_has_a_row_checked_per_class() {
    let base = "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def get -> T = @v\nend\nclass A < Base[Int]\n  def initialize; super(1); end\nend\nmodule SA\n  extension A\n    include M\n  end\n  def self.m(x: A) -> M = x\nend\n";
    let (code, err) = check(&format!("{base}puts SA.m(A.new).get + 1\n"));
    assert_eq!(code, Some(0), "{err}");
    refused(
        &format!("{base}class B < Base[String]\n  def initialize; super(\"s\"); end\nend\nmodule SB\n  extension B\n    include M\n  end\nend\nputs 1\n"),
        &["error: this extension includes `M` but nothing here implements `get`: define it in the extension or in `B`"],
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

/// An abstract class's extension whose only candidate does not return what
/// the requirement does (`Base#get -> String` for `M#get -> Int`): refused
/// by R0 at the extension since #656's decision (a), as for a concrete
/// class (the concrete `A2` first, accepted).
#[test]
fn a_refused_row_of_an_abstract_class_is_an_error() {
    refused(
        "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def get -> T = @v\nend\nclass A2 < Base[Int]\n  def initialize; super(1); end\nend\nextension A2\n  include M\nend\nabstract class B2 < Base[String]\n  def initialize; super(\"s\"); end\nend\nextension B2\n  include M\nend\nputs 1\n",
        &["main.qz:18:11: error: this extension includes `M` but nothing here implements `get`: define it in the extension or in `B2`"],
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

/// S2's oracle (#536 step 3): the rows that read the witness record
/// against the rows the run time's dispatch gave before, excluding by shape
/// only S2's two families of answer changes: #662's (an extension's own
/// method ran through a module the class has itself) and #629's (the
/// rescan's overload of another signature). Each family counted on its
/// reproducers, and zero elsewhere; S3 deletes the oracle.
#[test]
fn the_s2_oracle_excludes_only_662_and_629() {
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
    let clean = |s: &str| s.contains(" 0/") && s.contains("#662 0, #629 0");
    let s = summary(R529_ORACLE);
    assert!(clean(&s), "{s}");
    let s = summary(T3_ORACLE);
    assert!(s.contains(" 0/") && s.contains("#662 2, #629 0"), "{s}");
    let s = summary(F1);
    assert!(s.contains(" 0/") && s.contains("#662 0, #629 1"), "{s}");
    // (#662 with a top-level extension: `D < A` includes `M` itself, `A`
    // has its own `m` and a top-level extension of `A` its own `m` too.)
    let s = summary(TOP_662_ORACLE);
    assert!(s.contains(" 0/") && s.contains("#662 2, #629 0"), "{s}");
    // (#672: below an extension's conformance, a top-level extension's
    // module in the subclass's dispatch by name gives the method the table
    // pairs with the requirement; the record walks that order too, with no
    // exclusion.)
    let s = summary(R672_ORACLE);
    assert!(clean(&s), "{s}");
    // (A class's own conformance whose witness is a generic method, its
    // own type parameters standing for the requirement's: the record's
    // rule 3 finds it by type, with no arity resort, and agrees with the
    // rows. The include-pair case of `own_witness` is
    // `a_method_is_checked_in_each_receivers_frame`, refused by the net.)
    let s = summary(GENERIC_OWN_ORACLE);
    assert!(clean(&s), "{s}");
    // (The same method of another result type: refused as an override.)
    refused(
        &R672_ORACLE.replace("def m -> String = \"E\"", "def m -> Int = 1"),
        &["`m` returns Int but `M#m`, which it overrides in `K`, which includes `E`"],
    );
}
const GENERIC_OWN_ORACLE: &str = "module M\n  abstract def h[T <: Comparable[T]](x: T, y: T) -> Bool\nend\nclass A\n  def initialize; end\n  def h[T <: Comparable[T]](x: T, y: T) -> Bool = x < y\nend\nclass C < A\n  include M\n  def initialize; super; end\nend\ndef via(v: M) -> Bool = v.h(1, 2)\nputs via(C.new)\n";
const R672_ORACLE: &str = "module M\n  abstract def m -> String\nend\nmodule E\n  def m -> String = \"E\"\nend\nclass B\nend\nclass K < B\nend\nextension K\n  include E\nend\nmodule Sc\n  extension B\n    include M\n    def m -> String = \"x\"\n  end\n  def self.up(x: B) -> M = x\nend\ndef via(v: M) -> String = v.m\nputs via(Sc.up(B.new)), via(Sc.up(K.new))\n";
const TOP_662_ORACLE: &str = "module M\n  abstract def m -> Int\nend\nclass A\n  def initialize; end\n  def m -> Int = 10\nend\nclass D < A\n  include M\n  def initialize; super; end\nend\nextension A\n  include M\n  def m -> Int = 100\nend\ndef via(v: M) -> Int = v.m\nputs via(D.new)\n";
const R529_ORACLE: &str = "module PI\n  abstract def parse(s: String) -> Int\n  abstract def self.make(s: String) -> Int\nend\nmodule PS\n  abstract def parse(s: String) -> String\n  abstract def self.make(s: String) -> String\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\nend\nextension Box[T <: Int]\n  include PI\n  def parse(s: String) -> Int = @v + s.to_i\n  def self.make(s: String) -> Int = 1\nend\nextension Box[T <: String]\n  include PS\n  def parse(s: String) -> String = @v + s\n  def self.make(s: String) -> String = \"two\"\nend\ndef ps(x: PS) -> String = x.parse(\"!\")\na: PS = Box[String].new(\"x\")\np a.parse(\"1\")\np ps(a)\n";
const T3_ORACLE: &str = "module M\n  abstract def m -> String\nend\nmodule N\n  include M\n  abstract def n -> String\nend\nclass K\n  include M\n  def initialize; end\n  def m -> String = \"own\"\nend\nmodule X\n  extension K\n    include N\n    def m -> String = \"ext-m\"\n    def n -> String = \"ext-n\"\n  end\n  def self.as_n(k: K) -> N = k\n  def self.direct(k: K) -> String = k.m\nend\ndef via_m(x: M) -> String = x.m\ndef via_n(x: N) -> String = x.m + \",\" + x.n\nputs via_m(K.new), via_n(X.as_n(K.new)), X.direct(K.new)\n";
