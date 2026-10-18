//! `quarz build`: every example compiles to a native executable whose
//! output and exit code match the VM's.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

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
    let to_check: Vec<quarz_types::Unit> = units
        .into_iter()
        .map(|u| quarz_types::Unit {
            name: u.name,
            program: u.program,
        })
        .collect();
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
    let dir = std::env::temp_dir().join(format!("quarz-build-test-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let name = path.file_stem().unwrap().to_string_lossy().into_owned();
    let exe: PathBuf = dir.join(name);
    build(path, &exe);
    let output = Command::new(&exe)
        .args(argv)
        .output()
        .expect("run the executable");
    let _ = fs::remove_file(&exe);
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

fn example(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../examples/{name}.qz"))
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("tests/fixtures/{name}"))
}

#[test]
fn examples_compile_and_match_the_vm() {
    for name in [
        "shapes",
        "pipeline",
        "bank_actor",
        "extension",
        "builder",
        "geometry",
        "multi_file",
        "json_report",
    ] {
        same_as_vm(&example(name), &[]);
    }
    same_as_vm(&example("hello"), &["Quarz"]);
    let a = fixture("a.txt");
    let b = fixture("b.txt");
    same_as_vm(
        &example("wordcount"),
        &[a.to_str().unwrap(), b.to_str().unwrap()],
    );
    same_as_vm(&fixture("json.qz"), &[]);
}

#[test]
fn control_flow_matches_the_vm() {
    same_as_vm(&fixture("control_flow.qz"), &[]);
}
