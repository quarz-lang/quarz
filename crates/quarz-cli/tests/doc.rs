//! `quarz doc` and the examples in documentation comments
//! (docs/13-doc-comments.md): the API of `doc_cmd/app` as text, JSON and
//! HTML, `--check` and `--missing`, the examples run by `quarz test`
//! (passing, failing, not compiling, in a library), and a script's.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU32, Ordering};

fn app() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/doc_cmd/app")
}

fn quarz_in(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(args)
        .current_dir(dir)
        .output()
        .expect("run quarz")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

fn expected(name: &str) -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/doc_cmd")
            .join(name),
    )
    .unwrap()
}

/// A temporary directory.
struct Dir(PathBuf);

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

impl Dir {
    fn new() -> Dir {
        static N: AtomicU32 = AtomicU32::new(0);
        let dir = std::env::temp_dir().join(format!(
            "quarz-doc-{}-{}",
            std::process::id(),
            N.fetch_add(1, Ordering::SeqCst)
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        Dir(dir)
    }

    fn write(&self, rel: &str, text: &str) {
        let path = self.0.join(rel);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
}

#[test]
fn the_api_as_text() {
    let out = quarz_in(&app(), &["doc"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), expected("listing.out"));
    // A trailing comment documents nothing; `:nodoc:` hides.
    assert!(!stdout(&out).contains("debug_dump"));
    let out = quarz_in(&app(), &["doc", "Stack#pop"]);
    assert_eq!(stdout(&out), expected("pop.out"));
    let out = quarz_in(&app(), &["doc", "Stack.new"]);
    assert_eq!(
        stdout(&out),
        "Stack.new  def self.new(items: Array[T] = …) -> Stack[T]\n\n  An empty stack, or one holding items.\n"
    );
    let out = quarz_in(&app(), &["doc", "LIMIT"]);
    assert_eq!(
        stdout(&out),
        "LIMIT: Int\n\n  The largest stack size this program makes.\n"
    );
    // The standard library's names are found from a cog too.
    let out = quarz_in(&app(), &["doc", "JSON.parse"]);
    assert!(
        stdout(&out).contains("def self.parse(text: String) -> JSON::Value"),
        "{}",
        stdout(&out)
    );
    let out = quarz_in(&app(), &["doc", "Stack#nope"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(stderr(&out).contains("no documentation for `Stack#nope`"));
}

#[test]
fn check_and_missing() {
    let out = quarz_in(&app(), &["doc", "--check"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let out = quarz_in(&app(), &["doc", "--missing"]);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    for name in ["Point#x", "Point#y", "Stack#empty?", "Suit::Spades"] {
        assert!(
            err.contains(&format!("`{name}` has no documentation comment")),
            "{err}"
        );
    }
    assert!(!err.contains("Stack#size"), "{err}");
    let d = Dir::new();
    d.write("bad.qz", "# See `Nope#x` and `#size`, `Array#push`, `T`.\n#\n# ```\n# puts 1 # => 1\n# ```\nclass Bag\n  # Unclosed:\n  #\n  # ```\n  # 1\n  def size -> Int = 0\nend\n");
    let out = quarz_in(&d.0, &["doc", "bad.qz", "--check"]);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    assert!(
        err.contains("bad.qz:1: warning: `Nope#x` (in the doc of `Bag`) names nothing"),
        "{err}"
    );
    assert!(err.contains("`# =>` after `puts` or `print`"), "{err}");
    assert!(
        err.contains("bad.qz:7: warning: a code fence in the doc of `Bag#size` is not closed"),
        "{err}"
    );
    assert!(
        !err.contains("`#size`") && !err.contains("`Array#push`") && !err.contains("`T`"),
        "{err}"
    );
}

#[test]
fn json() {
    let out = quarz_in(&app(), &["doc", "--json"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(text.starts_with("[\n") && text.ends_with("]\n"), "{text}");
    assert!(text.contains("\"name\": \"Stack#pop\""), "{text}");
    assert!(
        text.contains("\"signature\": \"def pop -> [Stack[T], T]\""),
        "{text}"
    );
    assert!(
        text.contains("\"summary\": \"The stack without its top, and the top.\""),
        "{text}"
    );
}

#[test]
fn html() {
    let d = Dir::new();
    let site = d.0.join("site");
    let out = quarz_in(&app(), &["doc", "--html", "-o", site.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    for f in [
        "index.html",
        "Stack.html",
        "Stack--Empty.html",
        "Point.html",
        "Shout.html",
        "Suit.html",
        "style.css",
        "search.js",
        "search-index.js",
    ] {
        assert!(site.join(f).is_file(), "{f}");
    }
    let index = std::fs::read_to_string(site.join("index.html")).unwrap();
    // The README is the front page, its HTML shown as text.
    assert!(
        index.contains("&lt;script&gt;alert(1)&lt;/script&gt;"),
        "{index}"
    );
    assert!(!index.contains("<script>alert"), "{index}");
    assert!(
        index.contains("<a href=\"Stack.html#method-pop\"><code>Stack#pop</code></a>"),
        "{index}"
    );
    assert!(index.contains("<code>LIMIT: Int</code>"), "{index}");
    let stack = std::fs::read_to_string(site.join("Stack.html")).unwrap();
    assert!(
        stack.contains("<h1><code>class Stack[T]</code></h1>"),
        "{stack}"
    );
    assert!(stack.contains("id=\"method-pop\""), "{stack}");
    assert!(stack.contains("id=\"class-method-new\""), "{stack}");
    assert!(
        stack.contains("<a href=\"Stack--Empty.html\"><code>Empty</code></a>"),
        "{stack}"
    );
    assert!(!stack.contains("debug_dump"), "{stack}");
    // The list of pages folds, closed at first on a narrow screen: search
    // results stay outside it, and the script that folds it follows it.
    assert!(
        stack.contains(
            "<ul id=\"results\"></ul>\n<details id=\"pages\" open>\n<summary>Classes and modules</summary>"
        ),
        "{stack}"
    );
    assert!(
        stack.contains("</details>\n<script>(function () { var narrow = window.matchMedia(\"(max-width: 48rem)\")"),
        "{stack}"
    );
    let point = std::fs::read_to_string(site.join("Point.html")).unwrap();
    assert!(point.contains("<p class=\"admonition note\">"), "{point}");
    let index_js = std::fs::read_to_string(site.join("search-index.js")).unwrap();
    assert!(
        index_js.contains("[\"Stack#pop\",\"Stack.html#method-pop\"]"),
        "{index_js}"
    );
}

#[test]
fn examples_run_with_the_tests() {
    let out = quarz_in(&app(), &["test"]);
    assert!(out.status.success(), "{}{}", stdout(&out), stderr(&out));
    assert!(
        stdout(&out).contains("3 tests, 6 assertions, 0 failures, 0 errors"),
        "{}",
        stdout(&out)
    );
    let out = quarz_in(&app(), &["test", "--list"]);
    assert_eq!(
        stdout(&out),
        "Point#example 1\nString#shout#example 1\nStack#example 1\n"
    );
    let out = quarz_in(&app(), &["test", "--release"]);
    assert!(
        stdout(&out).contains("3 tests, 6 assertions, 0 failures, 0 errors"),
        "{}{}",
        stdout(&out),
        stderr(&out)
    );
}

#[test]
fn failing_and_broken_examples() {
    let d = Dir::new();
    d.write("Cog.toml", "[cog]\nname = \"calc\"\nversion = \"0.1.0\"\n");
    d.write("src/main.qz", "p Calc.add(1, 2)\n");
    d.write(
        "src/calc.qz",
        "# Sums.\n#\n# ```\n# Calc.add(1, 2)   # => 4\n# Calc.add(2, 2)   # => 4\n# ```\n#\n# ```quarz no_run\n# loop { sleep(1.seconds) }\n# ```\n#\n# ```text\n# not Quarz\n# ```\nmodule Calc\n  # Adds.\n  def self.add(a: Int, b: Int) -> Int = a + b\nend\n",
    );
    let out = quarz_in(&d.0, &["test"]);
    assert_eq!(out.status.code(), Some(1));
    let text = stdout(&out);
    assert!(
        text.contains("2 tests, 1 assertions, 1 failures, 0 errors"),
        "{text}"
    );
    assert!(text.contains("calc.qz:4: expected => 4, was 3"), "{text}");
    // A compile error is reported at its line in the comment.
    d.write(
        "src/calc.qz",
        "# Sums.\n#\n# ```\n# x = 1\n# Calc.nope(x)\n# ```\nmodule Calc\n  # Adds.\n  def self.add(a: Int, b: Int) -> Int = a + b\nend\n",
    );
    let out = quarz_in(&d.0, &["test"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        stderr(&out).contains("calc.qz:5: error: undefined method `nope`")
            && stderr(&out).contains("(in an example)"),
        "{}",
        stderr(&out)
    );
    let out = quarz_in(&d.0, &["test", "--no-doc"]);
    assert!(stderr(&out).contains("no test files"), "{}", stderr(&out));
}

#[test]
fn a_library_example_names_the_module() {
    let d = Dir::new();
    d.write("Cog.toml", "[cog]\nname = \"mathx\"\nversion = \"0.1.0\"\n");
    d.write(
        "src/mathx.qz",
        "# The square of `x`.\n#\n# ```\n# Mathx.square(3)   # => 9\n# ```\ndef self.square(x: Int) -> Int = x * x\n\n# A pair.\n#\n# ```\n# Mathx::Pair.new(1, 2).b   # => 2\n# ```\ndata Pair = (a: Int, b: Int)\n",
    );
    d.write("test/mathx_test.qz", "class MathxTest < Test::Case\n  def test_square\n    assert_equal(4, Mathx.square(2))\n  end\nend\n");
    let out = quarz_in(&d.0, &["test"]);
    assert!(out.status.success(), "{}{}", stdout(&out), stderr(&out));
    assert!(
        stdout(&out).contains("3 tests, 3 assertions, 0 failures"),
        "{}",
        stdout(&out)
    );
    // The root module's functions are documented, and their examples run.
    let out = quarz_in(&d.0, &["test", "--doc"]);
    assert!(
        stdout(&out).contains("2 tests, 2 assertions, 0 failures"),
        "{}",
        stdout(&out)
    );
    let out = quarz_in(&d.0, &["doc"]);
    assert!(stdout(&out).contains("module Mathx"), "{}", stdout(&out));
    assert!(
        stdout(&out).contains("  Mathx.square  The square of x."),
        "{}",
        stdout(&out)
    );
    let out = quarz_in(&d.0, &["doc", "Mathx::Pair"]);
    assert!(
        stdout(&out).starts_with("data Mathx::Pair(a: Int, b: Int)"),
        "{}{}",
        stdout(&out),
        stderr(&out)
    );
}

#[test]
fn a_scripts_examples() {
    let d = Dir::new();
    d.write("lib.qz", "# Twice `x`.\n#\n# ```\n# twice(2)  # => 4\n# ```\nmodule Lib\n  # Twice.\n  #\n  # ```\n  # Lib.twice(2)   # => 4\n  # ```\n  def self.twice(x: Int) -> Int = x * 2\nend\n");
    d.write("lib_test.qz", "require_relative \"lib\"\n\nclass LibTest < Test::Case\n  def test_twice\n    assert_equal(6, Lib.twice(3))\n  end\nend\n");
    // The module's example calls `twice` bare: an error, at its line.
    let out = quarz_in(&d.0, &["test", "lib_test.qz"]);
    assert!(
        stderr(&out).contains("lib.qz:4: error: undefined"),
        "{}",
        stderr(&out)
    );
    d.write("lib.qz", "# Doubling.\nmodule Lib\n  # Twice.\n  #\n  # ```\n  # Lib.twice(2)   # => 4\n  # ```\n  def self.twice(x: Int) -> Int = x * 2\nend\n");
    let out = quarz_in(&d.0, &["test", "lib_test.qz"]);
    assert!(
        stdout(&out).contains("2 tests, 2 assertions, 0 failures"),
        "{}{}",
        stdout(&out),
        stderr(&out)
    );
    let out = quarz_in(&d.0, &["doc", "lib.qz", "Lib.twice"]);
    assert_eq!(
        stdout(&out),
        "Lib.twice  def self.twice(x: Int) -> Int\n\n  Twice.\n\n      Lib.twice(2)   # => 4\n"
    );
}

#[test]
fn checks_on_any_statement() {
    let d = Dir::new();
    d.write(
        "e.qz",
        "# Checks.\n#\n# ```\n# [1, 2,\n#  3].sum # => 6\n# [1, 2,\n#  3].sum\n# # => 6\n# # a comment\n# [1, 2].map do |x|\n#   x * 2\n# end # => [2, 4]\n# LIMIT2 = 5 # => 5\n# s = 'a # => b'\n# s.size # => 8\n# \"\\\\\".size # => 1\n# /\"/.source # => \"\\\"\"\n# x = 1; y = 2 # => 2\n# raise ArgumentError.new(\"x\") # raises ArgumentError\n# ```\nmodule M\nend\n",
    );
    d.write("e_test.qz", "require_relative \"e\"\n");
    let out = quarz_in(&d.0, &["test", "e_test.qz"]);
    assert!(
        stdout(&out).contains("1 tests, 9 assertions, 0 failures, 0 errors"),
        "{}{}",
        stdout(&out),
        stderr(&out)
    );
    assert!(!stderr(&out).contains("warning"), "{}", stderr(&out));
    // A check that does not hold is reported, wherever its quotes are.
    d.write(
        "w.qz",
        "# Wrong.\n#\n# ```\n# \"\\\\\".size # => 99\n# ```\nmodule W\nend\n",
    );
    d.write("w_test.qz", "require_relative \"w\"\n");
    let out = quarz_in(&d.0, &["test", "w_test.qz"]);
    assert!(
        stdout(&out).contains("w.qz:4: expected => 99, was 1"),
        "{}",
        stdout(&out)
    );
}

#[test]
fn edge_cases_of_the_output() {
    let d = Dir::new();
    // Constants alone: valid JSON.
    d.write("k.qz", "# Limit.\nLIMIT = 3\np LIMIT\n");
    let out = quarz_in(&d.0, &["doc", "k.qz", "--json"]);
    assert_eq!(
        stdout(&out).split_whitespace().collect::<String>(),
        "[{\"doc\":\"Limit.\",\"kind\":\"constant\",\"location\":\"k.qz:2\",\"name\":\"LIMIT\",\"signature\":\"LIMIT:Int\",\"summary\":\"Limit.\"}]"
    );
    // `:nodoc:` on a constant and a variant; a shebang is no doc; a
    // `javascript:` link goes nowhere.
    d.write(
        "n.qz",
        "#!/usr/bin/env quarz\n# A [link](javascript:alert(1)) and [one](https://example.com).\nmodule N\n  # :nodoc:\n  HIDDEN = 1\n  SHOWN = 2\nend\n\n# Colors.\nenum Color\n  # :nodoc:\n  variant Hidden\n  variant Red\nend\n",
    );
    let out = quarz_in(&d.0, &["doc", "n.qz"]);
    let text = stdout(&out);
    assert!(
        text.contains("N::SHOWN") && !text.contains("HIDDEN"),
        "{text}"
    );
    assert!(
        text.contains("Color::Red") && !text.contains("Color::Hidden"),
        "{text}"
    );
    d.write("s.qz", "#!/usr/bin/env quarz\nclass Shebang\nend\n");
    let out = quarz_in(&d.0, &["doc", "s.qz"]);
    assert_eq!(stdout(&out), "class Shebang  \n");
    let site = d.0.join("site");
    let out = quarz_in(
        &d.0,
        &["doc", "n.qz", "--html", "-o", site.to_str().unwrap()],
    );
    assert!(out.status.success(), "{}", stderr(&out));
    let n = std::fs::read_to_string(site.join("N.html")).unwrap();
    assert!(n.contains("<a href=\"#\">link</a>"), "{n}");
    assert!(n.contains("<a href=\"https://example.com\">one</a>"), "{n}");
    // `:ditto:` holds for a method looked up by name.
    let out = quarz_in(&d.0, &["doc", "Int#ceil"]);
    assert!(
        stdout(&out).contains("Rounding to a negative number of digits"),
        "{}",
        stdout(&out)
    );
}

#[test]
fn checks_that_go_where_they_can_and_cannot() {
    let d = Dir::new();
    let run = |code: &str| {
        let body: String = code.lines().map(|l| format!("# {l}\n")).collect();
        d.write(
            "z.qz",
            &format!("# Ex.\n#\n# ```\n{body}# ```\nmodule Z\nend\n"),
        );
        d.write("z_test.qz", "require_relative \"z\"\n");
        let out = quarz_in(&d.0, &["test", "z_test.qz"]);
        format!("{}{}", stdout(&out), stderr(&out))
    };
    // A declaration sharing a line with a statement; a heredoc.
    let out = run("X = 1; X # => 1\ndef ff -> Int = 1; ff # => 1\ns = <<~EOS # => \"hi\\n\"\n  hi\nEOS\ns.size # => 3");
    assert!(out.contains("1 tests, 4 assertions, 0 failures"), "{out}");
    // A check inside a block, or on a block's first line, checks nothing:
    // an error at its line.
    let out = run("a = 1\n[1].each do |x|\n  x + 1\n  # => 2\nend");
    assert!(
        out.contains("z.qz:7: error: a check (`# =>`, `# raises`) goes at the end"),
        "{out}"
    );
    let out = run("[1].map do |x| # => [2]\n  x * 2\nend");
    assert!(out.contains("z.qz:4: error: a check"), "{out}");
    let out = run("A = Integer.parse(\"x\") # raises ArgumentError");
    assert!(
        out.contains("z.qz:4: error: `# raises` goes after a statement, not a declaration"),
        "{out}"
    );
}

#[test]
fn a_librarys_root_and_extension_methods() {
    let d = Dir::new();
    d.write("Cog.toml", "[cog]\nname = \"mathx\"\nversion = \"0.1.0\"\n");
    d.write("README.md", "# mathx\n\nSquares.\n");
    d.write(
        "src/mathx.qz",
        "# The square.\ndef self.square(x: Int) -> Int = x * x\n",
    );
    // The root module has no declaration to document: not missing.
    let out = quarz_in(&d.0, &["doc", "--missing"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let out = quarz_in(&d.0, &["doc", "--json"]);
    assert!(!stdout(&out).contains("<prelude>"), "{}", stdout(&out));
    let site = d.0.join("site");
    quarz_in(&d.0, &["doc", "--html", "-o", site.to_str().unwrap()]);
    let page = std::fs::read_to_string(site.join("Mathx.html")).unwrap();
    assert!(
        page.contains("<p>Squares.</p>") && !page.contains("prelude"),
        "{page}"
    );
    let out = quarz_in(&app(), &["doc", "String#shout"]);
    assert!(
        stdout(&out).starts_with("String#shout  def shout -> String\n  (extension String)"),
        "{}",
        stdout(&out)
    );
}
