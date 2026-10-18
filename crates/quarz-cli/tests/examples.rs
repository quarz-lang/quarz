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

#[test]
fn markdown() {
    assert_eq!(example("markdown", &[]), "<h1>Quarz</h1>\n<p>A <em>small</em> language with <strong>static</strong> classes and <code>immutable</code> data.</p>\n<h2>Features</h2>\n<ul>\n  <li>Ruby-like syntax</li>\n  <li>Lightweight tasks (see <a href=\"docs/04-concurrency.md\">the docs</a>)</li>\n  <li>One runtime for <code>quarz run</code> and <code>quarz build</code></li>\n</ul>\n<ol>\n  <li>Parse</li>\n  <li>Check</li>\n  <li>Lower &amp; run</li>\n</ol>\n<hr>\n<pre><code class=\"language-ruby\">def greet(name: String) -&gt; String\n  \"Hello, &lt;#{name}&gt;!\"\nend</code></pre>\n");
}

#[test]
fn sales_report() {
    // Uses `require "json"`, so it goes through the loader.
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/sales_report.qz");
    let (code, out) = common::run_path(&path, &[]);
    assert_eq!(code, 0, "output:\n{out}");
    assert_eq!(out, "By region\nkey           units    revenue orders       avg\nwest             26     161.50      2     80.75\nnorth             7     129.50      1    129.50\neast             17      95.97      3     31.99\n\nBy product\nkey           units    revenue orders       avg\ngadget           10     189.47      2     94.73\ngizmo             1      99.00      1     99.00\nwidget           39      98.50      3     32.83\n\nperiod: 2026-10-01 .. 2026-10-07 (6.0 days)\nbusiest day: 2026-10-02 with 2 orders\n{\n  \"total_revenue\": \"386.97\",\n  \"regions\": [\n    {\n      \"key\": \"west\",\n      \"revenue\": 161.5\n    },\n    {\n      \"key\": \"north\",\n      \"revenue\": 129.5\n    },\n    {\n      \"key\": \"east\",\n      \"revenue\": 95.97\n    }\n  ],\n  \"top_product\": \"gadget\"\n}\n");
}

#[test]
fn workers() {
    assert_eq!(example("workers", &[]), "job 0: 0\njob 1: 789294\njob 2: 89373\njob 3: 169805\njob 4: 533665\njob 6: 923401\njob 7: 482822\njob 8: 454426\njob 9: 440983\njob 10: 896322\njob 11: 570044\njob 5 failed: size must be positive\ndone: 11, failed: 1, retried: [1, 3, 7, 9, 11]\n");
}
