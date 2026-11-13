//! `quarz build`: every example compiles to a native executable whose
//! output and exit code match the VM's.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use quarz_syntax::{parse, SourceFile};
use quarz_types::PRELUDE_SOURCE;

/// Type-check a file (and what it requires) and compile it to `output`.
fn build(path: &Path, output: &Path) {
    let prelude = parse(PRELUDE_SOURCE);
    let (units, diags) = quarz_types::load(path);
    assert!(
        diags.iter().all(|(_, d)| !d.is_error()),
        "load errors in {}",
        path.display()
    );
    let sources: Vec<SourceFile> = units.iter().map(|u| u.source.clone()).collect();
    let to_check: Vec<quarz_types::Unit> = units.into_iter().map(quarz_types::Unit::from).collect();
    let (checked, diags) = quarz_types::check_units(&prelude.program, &to_check);
    let errors: Vec<String> = diags
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(f, d)| d.render(&sources[(*f as usize).saturating_sub(1)]))
        .collect();
    assert!(errors.is_empty(), "check errors:\n{}", errors.join("\n"));
    let mut files = vec![SourceFile::new("<prelude>", PRELUDE_SOURCE)];
    files.extend(sources);
    quarz_cli::build(checked.unwrap(), &files, output).expect("build");
}

/// Compile and run `path` natively, returning the exit code and output.
fn run_native(path: &Path, argv: &[&str]) -> (i32, String) {
    // A directory per build: builds run at once, and each leaves its
    // intermediate files next to its executable.
    static N: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "quarz-build-test-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    fs::create_dir_all(&dir).unwrap();
    let name = path.file_stem().unwrap().to_string_lossy().into_owned();
    let exe: PathBuf = dir.join(name);
    build(path, &exe);
    let output = Command::new(&exe)
        .args(argv)
        .output()
        .expect("run the executable");
    let _ = fs::remove_dir_all(&dir);
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).into_owned(),
    )
}

fn same_as_vm(path: &Path, argv: &[&str]) {
    let (vm_code, vm_out) = common::run_path(path, argv);
    let (native_code, native_out) = run_native(path, argv);
    assert_eq!(native_out, vm_out, "output of {}", path.display());
    assert_eq!(native_code, vm_code, "exit code of {}", path.display());
}

/// `same_as_vm` for each of `cases`, several at once: compiling with
/// clang is most of the time, and the programs are independent. The
/// failures are reported together. A worker stops at its first failure:
/// a panic in the VM may leave its thread's scheduler state behind, which
/// would fail the next programs there too; the others go on, and the
/// cases no worker got to are listed.
fn all_same_as_vm(cases: &[(PathBuf, Vec<String>)]) {
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .clamp(1, 4);
    let next = AtomicUsize::new(0);
    let failures = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                let Some((path, argv)) = cases.get(i) else {
                    break;
                };
                let argv: Vec<&str> = argv.iter().map(String::as_str).collect();
                let result = std::panic::catch_unwind(|| same_as_vm(path, &argv));
                if let Err(e) = result {
                    let message = e
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_default();
                    failures
                        .lock()
                        .unwrap()
                        .push(format!("{}: {message}", path.display()));
                    break;
                }
            });
        }
    });
    let mut failures = failures.into_inner().unwrap();
    let started = next.into_inner().min(cases.len());
    for (path, _) in &cases[started..] {
        failures.push(format!(
            "{}: not run (every worker stopped)",
            path.display()
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

fn example(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../examples/{name}.qz"))
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("tests/fixtures/{name}"))
}

#[test]
fn examples_compile_and_match_the_vm() {
    let mut cases = Vec::new();
    for name in [
        "shapes",
        "pipeline",
        "bank_actor",
        "extension",
        "builder",
        "geometry",
        "multi_file",
        "json_report",
        "markdown",
        "sales_report",
        "workers",
    ] {
        cases.push((example(name), Vec::new()));
    }
    cases.push((example("hello"), vec!["Quarz".to_string()]));
    let files = [fixture("a.txt"), fixture("b.txt")];
    cases.push((
        example("wordcount"),
        files.iter().map(|f| f.display().to_string()).collect(),
    ));
    all_same_as_vm(&cases);
}

#[test]
fn builtins_match_the_vm() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/builtins");
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("fixtures directory")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "qz"))
        .collect();
    paths.sort();
    let cases: Vec<(PathBuf, Vec<String>)> = paths.into_iter().map(|p| (p, Vec::new())).collect();
    all_same_as_vm(&cases);
}

/// Every `.qz` directly under `tests/fixtures`: its output and exit code
/// (control_flow.qz exits with 3).
#[test]
fn top_level_fixtures_match_the_vm() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("fixtures directory")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "qz"))
        .collect();
    paths.sort();
    assert!(paths.contains(&fixture("control_flow.qz")), "{paths:?}");
    let cases: Vec<(PathBuf, Vec<String>)> = paths.into_iter().map(|p| (p, Vec::new())).collect();
    all_same_as_vm(&cases);
}

/// A compiled function that reads its activation's frame word (the
/// fourth of the 32-byte `[args, self, nargs, frame]` slot) stores it
/// first: a block whose only use of its activation is an in-place update
/// of a captured variable read it uninitialized (#474).
#[test]
fn frame_word_is_set_before_it_is_read() {
    let path = fixture("owned_call_frame.qz");
    let dir = std::env::temp_dir().join(format!("quarz-frame-word-test-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let exe = dir.join("owned_call_frame");
    let built = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("build")
        .arg(&path)
        .arg("-o")
        .arg(&exe)
        .env("QUARZ_KEEP_IR", "1")
        .output()
        .expect("run quarz build");
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let ir = fs::read_to_string(exe.with_extension("ll")).unwrap();
    let _ = fs::remove_dir_all(&dir);
    // `ptrs` is a compiled function's sixth stack slot (after the
    // registers, the scratch list, the activation buffer, the result
    // slot and the body pointer: gen.rs); its frame word is at 24.
    if ir.contains("i8*") {
        eprintln!("skipped: clang 14's typed-pointer IR");
        return;
    }
    let mut reads = 0;
    let mut unset = Vec::new();
    for func in ir.split("\ndefine ").skip(1) {
        let body = func.split("\n}").next().unwrap();
        if !body.contains("%slot5 = alloca [32 x i8], align 8") {
            continue;
        }
        let words: Vec<&str> = body
            .lines()
            .filter_map(|l| {
                l.trim()
                    .strip_suffix("= getelementptr i8, ptr %slot5, i64 24")
            })
            .map(str::trim)
            .collect();
        let read = words
            .iter()
            .any(|w| body.contains(&format!("load ptr, ptr {w},")));
        let written = words.iter().any(|w| {
            body.lines()
                .any(|l| l.trim().starts_with("store ptr ") && l.contains(&format!(", ptr {w},")))
        });
        if read {
            reads += 1;
            if !written {
                unset.push(func.split('(').next().unwrap().to_string());
            }
        }
    }
    assert!(reads > 0, "no function of the fixture reads its frame word");
    assert!(unset.is_empty(), "frame word read unset in {unset:?}");
}

/// `QUARZ_AOT_OPT` picks clang's level (0 and 2 both build a program
/// that runs as the VM does); anything but 0 to 3 is an error naming it.
#[test]
fn aot_opt_levels() {
    let path = fixture("control_flow.qz");
    let want = fs::read_to_string(path.with_extension("out")).unwrap();
    let dir = std::env::temp_dir().join(format!("quarz-aot-opt-test-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let build = |level: &str, exe: &Path| {
        Command::new(env!("CARGO_BIN_EXE_quarz"))
            .arg("build")
            .arg(&path)
            .arg("-o")
            .arg(exe)
            .env("QUARZ_AOT_OPT", level)
            .output()
            .expect("run quarz build")
    };
    for level in ["0", "2"] {
        let exe = dir.join(format!("control_flow_{level}"));
        let built = build(level, &exe);
        assert!(
            built.status.success(),
            "QUARZ_AOT_OPT={level}: {}",
            String::from_utf8_lossy(&built.stderr)
        );
        let out = Command::new(&exe).output().expect("run the executable");
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            want,
            "QUARZ_AOT_OPT={level}"
        );
    }
    let built = build("x", &dir.join("control_flow_x"));
    let _ = fs::remove_dir_all(&dir);
    let err = String::from_utf8_lossy(&built.stderr);
    assert!(!built.status.success(), "QUARZ_AOT_OPT=x built");
    assert!(
        err.contains("QUARZ_AOT_OPT") && err.contains("\"x\""),
        "{err}"
    );
}

/// #630, compiled: an abstract method reached at run time is a violation
/// under `QUARZ_VERIFY` and a `TypeError` without it, as on the VM
/// (tests/verify.rs). No program the `quarz` command accepts reaches one
/// any more (#600's is refused by R0, #557's by the safety net's error
/// stage): #557's program is lowered through the library API, which runs
/// no net, and compiled.
#[test]
fn an_abstract_method_reached_compiled() {
    let dir = std::env::temp_dir().join(format!("quarz-abstract-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let src = "module Named\n  abstract def label -> String\nend\nmodule Gives\n  def label -> String = \"Gives\"\nend\nclass K\n  def initialize; end\nend\nmodule S2\n  extension K\n    include Gives\n    include Named\n  end\n  def self.n(k: K) -> Named = k\nend\ndef via(n: Named) -> String = n.label\nputs via(S2.n(K.new))\n";
    let exe = dir.join("main");
    quarz_aot::build(&common::lower(src), &exe).expect("build");
    for (verify, code, want) in [
        ("moves", 101, "QIR fact violated: abstract method `label` called on K, which no check saw implemented"),
        ("0", 1, "TypeError: abstract method `label` called on K, which no check saw implemented"),
    ] {
        let out = Command::new(&exe)
            .env("QUARZ_VERIFY", verify)
            .output()
            .expect("run the executable");
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(code), "{verify}: {err}");
        assert!(err.contains(want), "{verify}: {err}");
    }
    fs::remove_dir_all(&dir).ok();
}
