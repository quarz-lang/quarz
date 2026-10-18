//! The example programs produce their expected output.

mod common;

use std::fs;
use std::path::Path;

fn example(name: &str, argv: &[&str]) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../examples/{name}.qz"));
    let src = fs::read_to_string(&path).unwrap();
    let (code, out) = common::run(&src, argv);
    assert_eq!(code, 0, "{name} exited with {code}; output:\n{out}");
    out
}

#[test]
fn hello() {
    assert_eq!(example("hello", &[]), "Hello, world!\n");
    assert_eq!(example("hello", &["Quarz"]), "Hello, Quarz!\n");
}

#[test]
fn shapes() {
    assert_eq!(
        example("shapes", &[]),
        "circle(r=1.0): 3.14\nrect(2.0x3.0): 6.0\ntriangle: 6.0\nlargest: rect(2.0x3.0)\nnegative\nint 42\nstring of 5\nnothing\n"
    );
}

#[test]
fn wordcount() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let a = dir.join("a.txt");
    let b = dir.join("b.txt");
    let out = example("wordcount", &[a.to_str().unwrap(), b.to_str().unwrap()]);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines[0].split_whitespace().collect::<Vec<_>>(),
        vec!["the", "3"]
    );
    assert_eq!(
        lines[1].split_whitespace().collect::<Vec<_>>(),
        vec!["a", "2"]
    );
    assert_eq!(lines.len(), 6);
}

#[test]
fn pipeline() {
    let out = example("pipeline", &[]);
    assert_eq!(out.lines().count(), 21);
    assert!(out.ends_with("received 20 results\n"));
    assert!(out.contains("worker 0: JOB-0\n"));
    assert!(out.contains("JOB-19\n"));
}

#[test]
fn bank_actor() {
    assert_eq!(
        example("bank_actor", &[]),
        "withdrew, balance now 70\nfinal: 70\n" // the failure message goes to stderr via `warn`
    );
}

#[test]
fn extension() {
    assert_eq!(
        example("extension", &[]),
        "the integer 42\nthe string \"quarz\"\nthe integer 1, the integer 2, the integer 3\nHELLO!\n"
    );
}

#[test]
fn builder() {
    assert_eq!(
        example("builder", &[]),
        "0\n-1\n100001\n[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]\nalice\ta@example.com\nbob\tb@example.com\n0\n"
    );
}
