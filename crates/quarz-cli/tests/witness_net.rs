//! The safety net's report (`QUARZ_WITNESS_NET=report`, report-only,
//! `quarz_types::witness_net`): every witness row the runtime reads,
//! checked for its own class.

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

/// #608: one extension's method checked in each receiver's frame: `A <
/// Base[Int]` passes, `B < Base[String]` is refused.
#[test]
fn an_extensions_method_is_checked_in_each_receivers_frame() {
    let lines = report(
        "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension Base[T]\n  def get -> T = v\nend\nclass A < Base[Int]\n  include M\n  def initialize; super(1); end\nend\nclass B < Base[String]\n  include M\n  def initialize; super(\"s\"); end\nend\ndef via(m: M) -> Int = m.get + 1\nputs via(A.new)\n",
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

/// #600: nothing implements the requirement, listed apart.
#[test]
fn a_requirement_nothing_implements_is_listed_apart() {
    let lines = report(
        "module Named\n  abstract def label -> String\nend\nclass B\n  def initialize; end\nend\nmodule Sc\n  extension B\n    include Named\n  end\n  def self.n(x: B) -> Named = x\nend\nputs 1\n",
    );
    assert!(
        lines
            .iter()
            .any(|l| l.contains("no-impl  [override]  B  Named#label")),
        "{lines:#?}"
    );
    assert!(
        !lines.iter().any(|l| l.starts_with("witness-net: refused ")),
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
