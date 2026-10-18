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
fn multi_file() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/multi_file.qz");
    let (code, out) = common::run_path(&path, &[]);
    assert_eq!(code, 0);
    assert_eq!(
        out,
        "geometry loaded\n(3.0, 4.0)\n(6.0, 8.0)\n5.0\n(3.0, 4.0) is 5.0 units from the origin\n"
    );
}

#[test]
fn json_report() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/json_report.qz");
    let (code, out) = common::run_path(&path, &[]);
    assert_eq!(code, 0, "output:\n{out}");
    assert_eq!(
        out,
        concat!(
            "quarz, released Monday 2026-10-19\n",
            "- lexer: done (12.5h)\n- parser: done (30.0h)\n- jit: todo\n",
            "total: 42.5h\n",
            "{\n  \"project\": \"quarz\",\n  \"done\": 2,\n  \"pending\": [\n    \"jit\"\n  ],\n",
            "  \"total_hours\": 42.5,\n  \"next_release\": \"2026-11-18T12:00:00Z\"\n}\n",
            "map with project, released, tasks\nlist of 3\nfloat 12.5\nint 30\nnull\n",
        )
    );
}

#[test]
fn builder() {
    assert_eq!(
        example("builder", &[]),
        "0\n-1\n100001\n[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]\nalice\ta@example.com\nbob\tb@example.com\n0\n"
    );
}
