//! Helpers shared by the interpreter tests.

use quarz_syntax::{parse, SourceFile};
use quarz_types::PRELUDE_SOURCE;

/// Type-check and run a program, returning the exit code and its standard
/// output. Panics on compile errors.
pub fn run(src: &str, argv: &[&str]) -> (i32, String) {
    let prelude = parse(PRELUDE_SOURCE);
    let parsed = parse(src);
    let file = SourceFile::new("test", src);
    let errors: Vec<String> = parsed
        .diagnostics
        .iter()
        .filter(|d| d.is_error())
        .map(|d| d.render(&file))
        .collect();
    assert!(errors.is_empty(), "parse errors:\n{}", errors.join("\n"));
    let (checked, diags) = quarz_types::check(&prelude.program, &parsed.program);
    let errors: Vec<String> = diags
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(_, d)| d.render(&file))
        .collect();
    assert!(errors.is_empty(), "check errors:\n{}", errors.join("\n"));
    let argv = argv.iter().map(|s| s.to_string()).collect();
    quarz_vm::run_capturing(checked.unwrap(), argv)
}

/// Run and assert the output.
#[allow(dead_code)]
pub fn expect(src: &str, expected: &str) {
    let (code, out) = run(src, &[]);
    assert_eq!(code, 0, "exit code for {src:?}, output: {out:?}");
    assert_eq!(out, expected, "output for {src:?}");
}
