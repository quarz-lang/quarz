//! The REPL keeps declarations, variables and tasks across inputs.

use std::cell::RefCell;
use std::io::Write;
use std::rc::Rc;

use quarz_vm::repl::{Outcome, Repl};

struct Shared(Rc<RefCell<Vec<u8>>>);

impl Write for Shared {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.borrow_mut().extend_from_slice(buf);
        Ok(buf.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn values(lines: &[&str]) -> (Vec<String>, String) {
    let buffer = Rc::new(RefCell::new(Vec::new()));
    let mut repl = Repl::new(Box::new(Shared(buffer.clone()))).unwrap();
    let mut out = Vec::new();
    for line in lines {
        match repl.feed_line(line) {
            Outcome::Incomplete => out.push("...".to_string()),
            Outcome::Errors(errs) => out.push(format!(
                "error: {}",
                errs.join("").lines().next().unwrap_or("")
            )),
            Outcome::Value(Some(v)) => out.push(format!("=> {v}")),
            Outcome::Value(None) => out.push(String::new()),
            Outcome::Exit(code) => out.push(format!("exit {code}")),
        }
    }
    let printed = String::from_utf8_lossy(&buffer.borrow()).into_owned();
    (out, printed)
}

#[test]
fn require_loads_libraries_once() {
    let (out, printed) = values(&[
        "require \"json\"",
        "JSON.parse(\"[1, 2]\").size",
        "require \"json\"",
        "require \"nope\"",
        "JSON.generate([1, nil])",
        "require_relative \"../../examples/geometry\"",
        "Geometry.distance(Point.new(3.0, 4.0), Geometry::ORIGIN)",
        "require_relative \"../../examples/geometry\"",
    ]);
    assert_eq!(
        out,
        vec![
            "",
            "=> 2",
            "",
            "error: <repl>:1:1: error: unknown library `nope`",
            "=> \"[1,null]\"",
            "",
            "=> 5.0",
            "",
        ]
    );
    assert_eq!(printed, "geometry loaded\n");
}

#[test]
fn state_persists_across_inputs() {
    let (out, printed) = values(&[
        "x = 1",
        "def double(n: Int) -> Int = n * 2",
        "double(x) + 40",
        "data P(a: Int)",
        "p = P.new(3)",
        "p.a + x",
        "y = [",
        " 1,",
        " 2",
        "]",
        "y.sum",
        "puts \"side effect\"",
        "x = \"s\"",
        "xs = []",
        "xs = xs.push(1)",
        "xs",
    ]);
    assert_eq!(
        out,
        vec![
            "=> 1",
            "",
            "=> 42",
            "",
            "=> P(a: 3)",
            "=> 4",
            "...",
            "...",
            "...",
            "=> [1, 2]",
            "=> 3",
            "=> nil",
            "error: <repl>:1:5: error: cannot assign String to `x` of type Int",
            "=> []",
            "=> [1]",
            "=> [1]",
        ]
    );
    assert_eq!(printed, "side effect\n");
}

#[test]
fn tasks_outlive_inputs() {
    let (out, _) = values(&[
        "t = spawn { Task.sleep(5.ms); 99 }",
        "t.await",
        "ch = Channel[Int].new(capacity: 1)",
        "ch.send(5)",
        "ch.receive",
        "raise \"boom\"",
        "1 + 1",
    ]);
    assert_eq!(out[1], "=> 99");
    assert_eq!(out[4], "=> 5");
    assert_eq!(out[5], "");
    assert_eq!(out[6], "=> 2");
}

#[test]
fn errors_and_exit() {
    let (out, _) = values(&[
        "undefined_thing",
        "class C\n",
        "end",
        "C.new.class.name",
        "exit(3)",
    ]);
    assert!(out[0].starts_with("error: <repl>:1:1: error: undefined local variable or method"));
    assert_eq!(out[1], "...");
    assert_eq!(out[2], "");
    assert_eq!(out[3], "=> \"C\"");
    assert_eq!(out[4], "exit 3");
}
