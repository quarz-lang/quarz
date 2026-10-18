//! The built-in classes: each fixture under `tests/fixtures/builtins` runs
//! on the VM and must print the contents of its `.out` file.

mod common;

use std::fs;
use std::path::{Path, PathBuf};

fn fixtures() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/builtins");
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
