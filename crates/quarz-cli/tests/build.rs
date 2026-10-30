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
