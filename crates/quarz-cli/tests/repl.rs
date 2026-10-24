//! The REPL keeps declarations, variables and tasks across inputs.

use std::io::Write;
use std::sync::{Arc, Mutex};

use quarz_cli::session::{needs_more, unfinished, Outcome, Repl, Unfinished};

struct Shared(Arc<Mutex<Vec<u8>>>);

impl Write for Shared {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(buf);
        Ok(buf.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn values(lines: &[&str]) -> (Vec<String>, String) {
    let buffer = Arc::new(Mutex::new(Vec::new()));
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
    let printed = String::from_utf8_lossy(&buffer.lock().unwrap()).into_owned();
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
        "data P = (a: Int)",
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

#[test]
fn line_editor_continues_unfinished_inputs() {
    // What the line editor asks: does the entry go on on the next line?
    for text in [
        "def f",
        "def f(n: Int) -> Int\n  n",
        "[1,",
        "foo(",
        "\"abc",
        "1 +",
        "Task.scope do |s|",
    ] {
        assert!(needs_more(text, &[]), "{text:?} should go on");
    }
    for text in [
        "",
        "1 + 2",
        "def f = 1",
        "def f\nend",
        "[1,\n 2]",
        "1)",
        "end",
    ] {
        assert!(!needs_more(text, &[]), "{text:?} should not");
    }
    // Code goes on indented as wide as the prompt; a string as it is.
    assert_eq!(
        unfinished("class Foo\n         def bar", &[]),
        Unfinished::Code
    );
    assert_eq!(unfinished("x = \"one", &[]), Unfinished::String);
    // Inside an interpolation it is code again.
    assert_eq!(unfinished("def f\n  \"a #{1", &[]), Unfinished::Code);
    assert_eq!(unfinished("def f\n  \"a #{1} b", &[]), Unfinished::String);
}

#[test]
fn completion_offers_what_the_session_knows() {
    let buffer = Arc::new(Mutex::new(Vec::new()));
    let mut repl = Repl::new(Box::new(Shared(buffer.clone()))).unwrap();
    for line in [
        "class Point\n  @x: Int\n  def initialize(@x: Int); end\n  def x_value -> Int = @x\n  def self.origin -> Point = Point.new(0)\nend",
        "name = \"quarz\"",
        "pt = Point.new(1)",
        "maybe: String? = nil",
        "def greet(who: String) -> String = \"hi #{who}\"",
    ] {
        let _ = repl.feed_line(line);
    }
    let c = repl.completions();
    let has = |line: &str, start: usize, want: &[&str]| {
        let (s, names) = c.complete(line, line.len());
        assert_eq!(s, start, "where {line:?} completes");
        for w in want {
            assert!(
                names.iter().any(|n| n == w),
                "{line:?}: {w} not in {names:?}"
            );
        }
    };
    // Locals, top-level methods, keywords and constants.
    has("na", 0, &["name"]);
    has("gre", 0, &["greet"]);
    has("wh", 0, &["when", "while"]);
    has("Poi", 0, &["Point"]);
    // Methods of a local's type (declared, `String?` here), of a class,
    // of literals.
    has("name.up", 5, &["upcase"]);
    has("x = name.st", 9, &["strip", "start_with?"]);
    has("pt.x_", 3, &["x_value"]);
    has("maybe.emp", 6, &["empty?"]);
    has("Point.or", 6, &["origin"]);
    has("Point.ne", 6, &["new"]);
    has("\"a\".len", 4, &["length"]);
    has("[1].fir", 4, &["first"]);
    has("3.ti", 2, &["times"]);
    has(":ab.to_", 4, &["to_s"]);
    // Constants inside a class or module.
    has("Task::", 6, &["Cancelled", "Timeout"]);
    has("Result::O", 8, &["Ok"]);
    // Only names that complete the word; operators are not offered.
    let (_, names) = c.complete("pt.", 3);
    assert!(
        names
            .iter()
            .all(|n| !n.starts_with(|ch: char| !ch.is_alphabetic() && ch != '_')),
        "{names:?}"
    );
    assert!(
        c.complete("name", 4).1.is_empty(),
        "a complete word has nothing to add"
    );
}

#[test]
fn highlighting_colors_tokens() {
    use quarz_cli::highlight::highlight;
    let h = highlight("def f = \"n=#{x + 1}\" # note");
    assert!(h.starts_with("\x1b[35mdef\x1b[0m"), "{h:?}");
    assert!(
        h.contains("\x1b[32m\"n=#{\x1b[0mx + \x1b[36m1\x1b[0m\x1b[32m}\"\x1b[0m"),
        "{h:?}"
    );
    assert!(h.ends_with("\x1b[90m# note\x1b[0m"), "{h:?}");
    let h = highlight("Foo.new(:sym, nil, @iv)");
    for part in [
        "\x1b[1;34mFoo",
        "\x1b[33m:sym",
        "\x1b[1;36mnil",
        "\x1b[34m@iv",
    ] {
        assert!(h.contains(part), "{part:?} in {h:?}");
    }
    // An unfinished input is highlighted as far as it goes; the text is
    // kept as it is.
    let h = highlight("\"open #{");
    assert!(h.contains("\x1b[32m"), "{h:?}");
    let plain: String = {
        let mut out = String::new();
        let mut esc = false;
        for ch in highlight("x = [1, \"é\", :a] # ü").chars() {
            match (esc, ch) {
                (false, '\x1b') => esc = true,
                (true, 'm') => esc = false,
                (true, _) => {}
                (false, c) => out.push(c),
            }
        }
        out
    };
    assert_eq!(plain, "x = [1, \"é\", :a] # ü");
}

#[test]
fn prelude_methods_first_used_in_a_later_input() {
    // The prelude is lowered as far as the inputs so far reach: what a
    // later input first calls (directly, by `&:name`, or through another
    // prelude method) is lowered then.
    let (out, _) = values(&[
        "x = 1",
        "[1, 1, 2].tally",
        "[1, 2, 3, 4].partition { |n| n.even? }",
        "[1, 2, 4, 5].chunk_while { |a, b| b == a + 1 }",
        "[:x, :y].map(&:to_s).group_by(&:size)",
    ]);
    assert_eq!(
        out,
        [
            "=> 1",
            "=> {1 => 2, 2 => 1}",
            "=> [[2, 4], [1, 3]]",
            "=> [[1, 2], [4, 5]]",
            "=> {1 => [\"x\", \"y\"]}",
        ]
    );
}

#[test]
fn standard_library_without_require() {
    let (out, _) = values(&[
        "JSON.generate([1, 2])",
        "require \"json\"",
        "JSON.parse(\"[3]\")[0].as_i",
    ]);
    assert_eq!(out, vec!["=> \"[1,2]\"", "", "=> 3"]);
}
