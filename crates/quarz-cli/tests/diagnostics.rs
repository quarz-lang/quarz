//! What the checker rejects, in programs too large for
//! quarz-types/tests/check.rs. The language's and the standard
//! library's behaviour is tested in Quarz, `std/test` (tests/std.rs).

mod common;

/// Blocks with a receiver: what the checker rejects.
#[test]
fn receiver_block_errors() {
    let out = common::diagnostics(
        r#"class Box
  var @n: Int = 0
  def bump(&b: Box.() -> Void) -> Void
    instance_exec(&b)
  end
  def n -> Int = @n
end
Box.new.bump { @n = 1 }
def run(&b: Box.() -> Void) -> Void
  yield
end
f: (Int) -> Int = -> (x: Int) { x }
g: Box.() -> Void = f
Box.new.bump { nothing_here }
class Outer
  def n -> Int = 42
  def go -> Void = Box.new.bump { n }
end
class Inner
  include DslScope
  def leaf -> Int = 1
end
class Builder
  include DslScope
  def item -> Int = 2
  def inner(&b: Inner.() -> Int) -> Int = Inner.new.instance_exec(&b)
end
Builder.new.instance_exec { inner { item } }
"#,
    )
    .join("\n");
    assert!(out.contains("not accessible from this block"), "{out}");
    assert!(
        out.contains("`yield` cannot run a block with a receiver"),
        "{out}"
    );
    assert!(
        out.contains("cannot assign (Int) -> Int to `g` of type Box.() -> Void"),
        "{out}"
    );
    assert!(
        out.contains("undefined local variable or method `nothing_here` for Box"),
        "{out}"
    );
    assert!(out.contains("warning: `n` is a method of both"), "{out}");
    assert!(
        out.contains("undefined local variable or method `item` for Inner"),
        "{out}"
    );
}

/// `using` in bodies and on block parameters is lexically scoped.
#[test]
fn using_scoping() {
    let out = common::diagnostics(
        r#"module Shout
  extension String
    def shout -> String = upcase + "!"
  end
end
def a -> String
  using Shout
  "x".shout
end
def b -> String = "y".shout
v = using Shout { "z".shout }
w = "w".shout
def c(&: () -> String using Shout) -> String = yield
p c { "c".shout }
f = -> { "f".shout }
p c(&f)
"#,
    )
    .join("\n");
    assert!(
        out.contains("test:10:19: error: undefined method `shout` for String"),
        "{out}"
    );
    assert!(
        out.contains("test:12:5: error: undefined method `shout` for String"),
        "{out}"
    );
    assert!(
        out.contains("test:15:10: error: undefined method `shout` for String"),
        "{out}"
    );
    assert!(!out.contains("test:8:"), "{out}");
    assert!(!out.contains("test:11:"), "{out}");
    assert!(!out.contains("test:14:"), "{out}");
    // A declaration error is reported where the parameter is.
    let out =
        common::diagnostics("def d(&: () -> String using String) -> String = yield\n").join("\n");
    assert!(
        out.contains("test:1:7: error: `using String`: not a module"),
        "{out}"
    );
}

/// `x.foo!` as `x = x.foo`: what the checker rejects.
#[test]
fn bang_assign_errors() {
    let out = common::diagnostics(
        r#"s = "abc"
s.size!
xs = [1]
xs.nope!
[1, 2].push!(3)
class C
  @n: Int = 0
  def bump -> Void
    @n.succ!
  end
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("test:2:1: error: `.size!` would assign Int to `s` of type String"),
        "{out}"
    );
    assert!(
        out.contains("test:4:1: error: undefined method `nope!` for Array[Int]"),
        "{out}"
    );
    assert!(
        out.contains("test:5:1: error: `push!` is not a method of Array[Int]; `.push!` assigns the result of `push` back, but the receiver is not a variable or a field"),
        "{out}"
    );
    assert!(
        out.contains("test:9:5: error: field `@n` is immutable"),
        "{out}"
    );
}

/// Expansive inheritance through a class of a required file.
#[test]
fn expansive_inheritance_across_files() {
    let dir = std::env::temp_dir().join(format!("quarz-expansive-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.qz"), "class N[in Z]\nend\n").unwrap();
    std::fs::write(
        dir.join("app.qz"),
        "require_relative \"lib\"\nclass C[X] < N[N[C[C[X]]]]\nend\ndef f(x: C[Int]) -> N[C[Int]] = x\n",
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(["check", "app.qz"])
        .current_dir(&dir)
        .env("QUARZ_NO_CACHE", "1")
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success());
    assert!(err.contains("expansive inheritance"), "{err}");
}

/// An error in a required file's type parameters is reported in that
/// file (they are declared before the headers, file by file).
#[test]
fn a_type_parameter_error_in_a_required_file() {
    let dir = std::env::temp_dir().join(format!("quarz-tparam-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.qz"), "class Box[Int]\nend\n").unwrap();
    std::fs::write(dir.join("app.qz"), "require_relative \"lib\"\np 1\n").unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(["check", "app.qz"])
        .current_dir(&dir)
        .env("QUARZ_NO_CACHE", "1")
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success());
    assert!(
        err.contains("lib.qz:1:11: error: `Int` cannot be a type parameter name"),
        "{err}"
    );
}

/// A 63-deep covariant coercion (the subtype checks' defensive depth
/// limit is far above it).
#[test]
fn a_deep_coercion_is_checked() {
    let dir = std::env::temp_dir().join(format!("quarz-deep-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (mut t, mut u, mut v) = ("Int".to_string(), "Int?".to_string(), "1".to_string());
    for _ in 0..63 {
        t = format!("Array[{t}]");
        u = format!("Array[{u}]");
        v = format!("[{v}]");
    }
    std::fs::write(
        dir.join("deep.qz"),
        format!("def g(x: {t}) -> {u} = x\np g({v}).size\n"),
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(["check", "deep.qz"])
        .current_dir(&dir)
        .env("QUARZ_NO_CACHE", "1")
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// A block's or a lambda's parameters take no default (docs/01 §9): the
/// error is at the default, also one holding a `|` or a block.
#[test]
fn block_and_lambda_parameters_take_no_default() {
    let out = common::diagnostics(
        "def f(&b: (Int) -> Int) -> Int = b.call(5)\np f { |x = 1| x }\np f { |x = [1].map { |y| y | 1 }.first| x | 8 }\nl = ->(x: Int = 7) { x }\np [1, 2].map { |x| x | 4 }\n",
    )
    .join("\n");
    assert_eq!(
        out.matches("a block's parameters take no default: the block's type gives every argument")
            .count(),
        2,
        "{out}"
    );
    assert!(
        out.contains("a lambda's parameters take no default: each call gives every argument"),
        "{out}"
    );
    assert!(!out.contains("expected"), "{out}");
}

/// A positional argument after a keyword argument is a syntax error: it
/// would bind to the keyword's parameter, dropping the keyword's value.
#[test]
fn positional_after_keyword() {
    let out = common::diagnostics(
        "def g(a: Int, b: String = \"d\") -> String = \"#{a} #{b}\"\nputs g(a: 1, 2)\nTime.utc(year: 2020, 3)\nputs g(2, b: \"x\")\n",
    )
    .join("\n");
    let msg = "error: positional argument after a keyword argument; keyword arguments go last";
    assert_eq!(out.matches(msg).count(), 2, "{out}");
    assert!(out.contains(":2:14:") && out.contains(":3:22:"), "{out}");
}

/// What a procedure type's keywords and a block's or a lambda's keyword
/// parameters cannot be (docs/02 §1): a default in a written type, a
/// `*rest` in a type, `**` in a block, a duplicate, a missing `->`.
#[test]
fn procedure_type_keyword_syntax() {
    let out = common::diagnostics(
        "a: (Int, *, k: Int = 1) -> Int = ->(x: Int, *, k: Int = 1) { x }\nb: (*xs) -> Int = -> { 1 }\nc = [1].map { |x, **o| x }\nd: (*, k: Int, k: Int) -> Int = ->(*, k: Int) { k }\ne: (Int, *, k: Int) = 1\nok = ->(x: Int, *, k: Int = 2) { x + k }\n",
    )
    .join("\n");
    for msg in [
        "a procedure type lists its required keywords only",
        "a procedure type has no `*rest` parameter",
        "a procedure takes no `**rest`",
        "keyword `k` is listed twice",
        "expected `->` after a procedure type's parameters",
    ] {
        assert!(out.contains(msg), "{msg:?} in {out}");
    }
    assert!(!out.contains("take no default"), "{out}");
}

/// A field default's error and a required field's are reported in the
/// class's own file, whatever unit is checked last: with a standard
/// library required, they were at its line 1 (#405).
#[test]
fn field_errors_in_their_own_file_with_a_library_required() {
    let dir = std::env::temp_dir().join(format!("quarz-field-file-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let body = "data D = (a: Int, b: Int = a * 2)\nclass C\n  @x: Int\nend\n";
    let mut outs = Vec::new();
    for (name, head) in [("with.qz", "require \"base64\"\n"), ("without.qz", "\n")] {
        std::fs::write(dir.join(name), format!("{head}{body}")).unwrap();
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_quarz"))
            .args(["check", name])
            .current_dir(&dir)
            .env("QUARZ_NO_CACHE", "1")
            .output()
            .unwrap();
        assert!(!out.status.success());
        let err = String::from_utf8_lossy(&out.stderr).replace(name, "FILE");
        outs.push(err);
    }
    let _ = std::fs::remove_dir_all(&dir);
    for err in &outs {
        assert!(
            err.contains("FILE:2:28: error: a field's default cannot use the object"),
            "{err}"
        );
        assert!(
            err.contains("FILE:4:3: error: field `@x` has no default and `C` has no `initialize` to assign it"),
            "{err}"
        );
    }
    assert_eq!(outs[0], outs[1]);
}

/// An extension's include brings no class methods (#494): a module with
/// abstract class methods cannot be included there, since a `Type[M]`
/// value could then hold a class without them.
#[test]
fn an_extension_cannot_include_a_module_with_abstract_class_methods() {
    let out = common::diagnostics(
        r#"module M
  abstract def self.x -> String
  def self.y -> String = "y"
  def m -> Int = 1
end
module N
  def self.y -> String = "y"
  def n -> Int = 1
end
class Foo
end
extension Foo
  include M
end
class Bar
end
extension Bar
  include N
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("an extension's include brings no class methods; `M` has abstract class methods (`x`) a class including it must implement"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 1, "{out}");
}
