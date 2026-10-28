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
def n -> Int = 42
Box.new.bump { n }
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
