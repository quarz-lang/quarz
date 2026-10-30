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
