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

/// An extension's include brings the module's class methods (#504): an
/// abstract one is required of the target class, implemented by the
/// extension's own `def self.` or the class's, else an error at the
/// extension; a module with only concrete ones needs nothing.
#[test]
fn an_extension_must_implement_an_included_modules_abstract_class_methods() {
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
class Baz
  def self.x -> String = "own"
end
extension Baz
  include M
end
class Qux
end
extension Qux
  include M
  def self.x -> String = "extension's"
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("`Foo` must implement `self.x` (abstract in `M`, which this extension includes): define `def self.x` in the extension or in `Foo`"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 1, "{out}");
}

#[test]
fn a_generic_module_is_conformed_to_with_one_set_of_arguments() {
    // #504: a class conforms to a generic module with one set of
    // arguments across its includes and extensions (the class-side
    // witnesses are per module and class), the error naming the other.
    let out = common::diagnostics(
        r#"module Parsable[U]
  abstract def self.parse(s: String) -> U
  def self.again(s: String) -> U = parse(s)
end
class Num
end
module X
  extension Num
    include Parsable[String]
    def self.parse(s: String) -> String = s + "!"
  end
end
extension Num
  include Parsable[Int]
  def self.parse(s: String) -> Int = s.to_i
end
class Own
  include Parsable[String]
  def self.parse(s: String) -> String = s
end
extension Own
  include Parsable[Int]
end
class Same
end
extension Same
  include Parsable[Int]
  def self.parse(s: String) -> Int = s.to_i
end
module Y
  extension Same
    include Parsable[Int]
    def self.parse(s: String) -> Int = s.to_i + 1
  end
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("`Num` already conforms to `Parsable[String]` through another extension (`extension Num` in `X`): this extension cannot make `Num` conform to `Parsable[Int]`, a generic module `Parsable` is included with one set of arguments"),
        "{out}"
    );
    assert!(
        out.contains("`Own` already includes `Parsable` (through its own `include`): an extension cannot include it again; override its methods in `Own` itself"),
        "{out}"
    );
    // (The same arguments twice: a second conformance, #517.)
    assert!(
        out.contains("31:13: error: `Same` already conforms to `Parsable[Int]` through another extension (a top-level `extension Same`): this extension cannot include it again; a class conforms to a module once"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 3, "{out}");
}

#[test]
fn a_conditional_extensions_include_brings_class_methods_where_its_bound_holds() {
    // #504: `extension Box[T <: Int]; include Parsable[Int]` gives
    // `Box[Int]` the module's class methods, not `Box[String]`.
    let out = common::diagnostics(
        r#"module Parsable[U]
  abstract def self.parse(s: String) -> U
  def self.again(s: String) -> U = parse(s)
end
class Box[T]
  @v: T
  def initialize(@v: T); end
end
extension Box[T <: Int]
  include Parsable[Int]
  def self.parse(s: String) -> Int = s.to_i
end
p Box[Int].again("5") + 1
p Box[String].again("5")
"#,
    )
    .join("\n");
    assert!(
        out.contains("undefined method `again` for Type[Box[String]]"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 1, "{out}");
}

#[test]
fn a_witness_of_an_extensions_conformance_is_checked_at_the_extension() {
    // #504: a superclass's class method is the witness of a module's for
    // the class an extension makes conform, checked as an override where
    // the extension is (wherever it is active).
    let out = common::diagnostics(
        r#"module Parsable
  def self.describe -> String = "parsable"
end
class A
  def self.describe -> Int = 1
end
class B < A
end
module X
  extension B
    include Parsable
  end
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("10:13: error: `describe` returns Int but `Parsable.describe`, which it overrides, returns String"),
        "{out}"
    );
}

#[test]
fn an_extension_conformance_takes_the_modules_new_arguments() {
    // #504: a module's default class method calling `new`, which a class
    // conforming through an extension (or its subclass) reaches, is
    // checked against the class's `initialize` as for a class's own
    // include.
    let out = common::diagnostics(
        r#"module Made
  def self.make -> Self = new
end
class Num
  @v: Int
  def initialize(@v: Int); end
end
extension Num
  include Made
end
class Base
  def initialize; end
end
extension Base
  include Made
end
class Sub < Base
  @w: String
  def initialize(@w: String); end
end
def g(k: Type[Made]) -> Made = k.make
g(Num)
g(Sub)
"#,
    )
    .join("\n");
    assert!(
        out.contains("`Num#initialize` does not take the arguments of `new` in `Made.make`, which runs for `Num` through its conformance by an extension"),
        "{out}"
    );
    assert!(
        out.contains("`Sub#initialize` does not take the arguments of `new` in `Made.make`, which runs for `Sub` through its conformance by an extension"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 2, "{out}");
}

#[test]
fn a_superclass_extensions_conformance_fixes_a_generic_modules_arguments() {
    // #504: witnesses are found up the superclass chain, so a subclass's
    // extension cannot conform to the module with other arguments.
    let out = common::diagnostics(
        r#"module Parsable[U]
  abstract def self.parse(s: String) -> U
end
class Top
end
class Low < Top
end
extension Top
  include Parsable[String]
  def self.parse(s: String) -> String = s
end
extension Low
  include Parsable[Int]
  def self.parse(s: String) -> Int = s.to_i
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("`Top` already conforms to `Parsable[String]` through another extension (a top-level `extension Top`): this extension cannot make `Low` conform to `Parsable[Int]`"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 1, "{out}");
}

#[test]
fn one_set_of_arguments_compares_parameters_through_the_targets_arguments() {
    // #514's review: an extension's `T` is its target's `T` (through the
    // target's arguments), and a superclass's parameters are the
    // subclass's instantiation of them (`Box`'s extension is refused
    // as including what `Box` includes itself, #504).
    let out = common::diagnostics(
        r#"module Parsable[U]
  def self.again(s: String) -> String = s
end
class Box[T]
  include Parsable[T]
  def initialize; end
end
extension Box[T]
  include Parsable[T]
end
class Pair[A]
  def initialize; end
end
extension Pair[X]
  include Parsable[X]
end
module Q
  extension Pair[Y]
    include Parsable[Y]
  end
end
class Low[Z] < Pair[Z]
end
extension Low[W]
  include Parsable[W]
end
class Bad < Pair[Int]
end
extension Bad
  include Parsable[String]
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("`Pair` already conforms to `Parsable[Int]` through another extension (a top-level `extension Pair`): this extension cannot make `Bad` conform to `Parsable[String]`"),
        "{out}"
    );
    assert!(
        out.contains("`Box` already includes `Parsable` (through its own `include`): an extension cannot include it again"),
        "{out}"
    );
    // (`Pair[X]` and `Pair[Y]` both including `Parsable` of the target's
    // parameter: a second conformance, #517.)
    assert!(
        out.contains("18:13: error: `Pair` already conforms to `Parsable[A]` through another extension (a top-level `extension Pair`): this extension cannot include it again; a class conforms to a module once"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 3, "{out}");
}

#[test]
fn an_extension_cannot_include_what_the_class_includes_itself() {
    // #504 (the user's decision): a class that has the module through its
    // own or a superclass's own `include` conforms already and overrides
    // with its own `def self.`; a superclass's conformance through an
    // extension does not count, so a subclass may conform on its own.
    let out = common::diagnostics(
        r#"module M
  def self.describe -> String = "M"
end
class Base
  include M
end
class A < Base
end
extension A
  include M
  def self.describe -> String = "extA"
end
class Own
  include M
end
extension Own
  include M
end
class C
end
extension C
  include M
end
class D < C
end
extension D
  include M
  def self.describe -> String = "D"
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("9:11: error: `A` already includes `M` (through `Base`'s `include`): an extension cannot include it again; override its methods in `A` itself"),
        "{out}"
    );
    assert!(
        out.contains("16:11: error: `Own` already includes `M` (through its own `include`)"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 2, "{out}");
}

#[test]
fn what_an_extensions_include_brings_counts_for_the_rules() {
    // #514's review: the one-arguments rule covers the generic modules an
    // include brings (`Gen[String]` through `Wrap[String]`), on the class
    // side and the instance side.
    for (src, want) in [
        (r#"module Gen[T]
  abstract def self.zero -> T
end
module Wrap[U]
  include Gen[U]
end
class C
end
extension C
  include Gen[Int]
  def self.zero -> Int = 0
end
module Y
  extension C
    include Wrap[String]
    def self.zero -> String = "s"
  end
  def self.z[T <: Wrap[String]](t: Type[T]) -> String = t.zero
  def self.w(t: Type[Wrap[String]]) -> String = t.zero
  def self.run -> Void
    s = z(C)
    puts s
    puts s.size
    puts w(C).size
  end
end
def zi[T <: Gen[Int]](t: Type[T]) -> Int = t.zero
puts zi(C) + 1
Y.run
"#, "14:13: error: `C` already conforms to `Gen[Int]` through another extension (a top-level `extension C`): this extension cannot make `C` conform to `Gen[String]` (through `Wrap[String]`)"),
        (r#"module Gen[T]
  abstract def zero -> T
end
module Wrap[U]
  include Gen[U]
end
class C
end
extension C
  include Gen[Int]
  def zero -> Int = 0
end
module Y
  extension C
    include Wrap[String]
    def zero -> String = "s"
  end
  def self.z[T <: Wrap[String]](t: T) -> String = t.zero
  def self.run -> Void
    s = z(C.new)
    puts s.size
  end
end
Y.run
"#, "14:13: error: `C` already conforms to `Gen[Int]` through another extension"),
            ] {
        let out = common::diagnostics(src).join("\n");
        assert!(out.contains(want), "{out}");
        assert_eq!(out.matches("error:").count(), 1, "{out}");
    }
}

#[test]
fn one_set_of_arguments_holds_within_an_extension() {
    // #514's review: two includes of one extension that bring a generic
    // module with other arguments.
    let out = common::diagnostics(
        r#"module Gen[T]
  def self.tag -> String = "gen"
end
module Wrap[U]
  include Gen[U]
end
class C
end
extension C
  include Gen[Int]
  include Gen[String]
end
def zi[T <: Gen[Int]](t: Type[T]) -> String = t.tag
def zs[T <: Gen[String]](t: Type[T]) -> String = t.tag
puts zi(C), zs(C)
"#,
    )
    .join("\n");
    assert!(
        out.contains("9:11: error: `C` already conforms to `Gen[Int]` through an earlier `include` of this extension: this extension cannot make `C` conform to `Gen[String]`"),
        "{out}"
    );
}

#[test]
fn witnesses_through_a_module_and_a_generic_superclass_are_checked() {
    // #514's review: an extension of a module including a module with
    // class methods is refused (#530); a generic superclass's class method
    // is checked as the class sees it.
    let out = common::diagnostics(
        r#"module M
  abstract def self.make -> Self
end
module Mid
end
extension Mid
  include M
  def self.make -> Self = new
end
class K
  include Mid
  @x: Int
  def initialize(@x: Int); end
  def self.make -> Self = new(1)
  def x -> Int = @x
end
def h[T <: M](t: Type[T]) -> T = t.make
p h(K).as(K).x + 1
"#,
    )
    .join("\n");
    assert!(
        out.contains("an extension of the module `Mid` cannot include `M`: `M` has class methods (not supported yet, #530)"),
        "{out}"
    );
    let out = common::diagnostics(
        r#"module Maker[T]
  abstract def self.make(x: T) -> Self
end
class Base[T]
  @x: T
  def initialize(@x: T); end
  def self.make(x: T) -> Self = new(x)
  def x -> T = @x
end
class C < Base[Int]
end
extension C
  include Maker[String]
end


"#,
    )
    .join("\n");
    assert!(
        out.contains("12:11: error: `make` takes Int for `x` but `Maker.make`, which it overrides, is given String"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 1, "{out}");
}

#[test]
fn a_generic_class_witness_is_checked_in_its_own_parameters() {
    // #514's review: a generic class's own (or superclass's) class method
    // taken as the witness is checked in the class's parameters, not the
    // extension's. (The module-witness cases of this review are refused
    // as extensions of a module, #530.)
    for src in [
        r#"module Maker[T]
  abstract def self.make(x: T) -> Self
end
class Base[T]
  @x: T
  def initialize(@x: T); end
  def self.make(x: T) -> Self = new(x)
  def x -> T = @x
end
class G[U] < Base[U]
end
extension G[U]
  include Maker[U]
end
def mk3[U](t: Type[Maker[U]], v: U) -> Maker[U] = t.make(v)
p mk3(G[String], "a").class
"#,
        r#"module Maker[T]
  abstract def self.make(x: T) -> Self
end
class G[U]
  @x: U
  def initialize(@x: U); end
  def self.make(x: U) -> Self = new(x)
  def x -> U = @x
end
extension G[U]
  include Maker[U]
end
def mk3[U](t: Type[Maker[U]], v: U) -> Maker[U] = t.make(v)
p mk3(G[String], "a").class
"#,
    ] {
        let out = common::diagnostics(src).join("\n");
        assert!(!out.contains("error:"), "{out}");
    }
}

#[test]
fn witness_matrix_refusals() {
    // The refusals of the #504 witness matrix (the runs: the
    // `witness_matrix_*.qz` fixtures and cogs.rs), per target (class,
    // generic class, module): an extension including what the class
    // includes itself, an abstract class method without a witness, a
    // witness of another type and `new` arguments per witness source, two
    // argument sets. (A witness of another type is said once: at the
    // method where the class side's override check said it, else at the
    // extension, #525.)
    let cells: &[(&str, &str, &str)] = &[
        (
            "refused include (class)",
            r#"module M
  def self.d -> String = "M"
end
class X
  include M
  def initialize; end
end
extension X
  include M
end
"#,
            "already includes `M` (through its own `include`): an extension cannot include it again",
        ),
        (
            "abstract without witness (class)",
            r#"module M
  abstract def self.d -> String
end
class X
  def initialize; end
end
extension X
  include M
end
"#,
            "`X` must implement `self.d` (abstract in `M`, which this extension includes)",
        ),
        (
            "witness of another type, ext (class)",
            r#"module M
  def self.d -> String = "M"
end
class X
  def initialize; end
end
extension X
  include M
  def self.d -> Int = 1
end
"#,
            "`d` returns Int but `M.d`, which it overrides, returns String",
        ),
        (
            "witness of another type, own (class)",
            r#"module M
  def self.d -> String = "M"
end
class X
  def initialize; end
  def self.d -> Int = 1
end
extension X
  include M
end
"#,
            "`d` returns Int but `M.d`, which it overrides, returns String",
        ),
        (
            "witness of another type, sup (class)",
            r#"module M
  def self.d -> String = "M"
end
class B
  def initialize; end
  def self.d -> Int = 1
end
class X < B
  def initialize; end
end
extension X
  include M
end
"#,
            "`d` returns Int but `M.d`, which it overrides, returns String",
        ),
        (
            "witness of another type, nmod (class)",
            r#"module M
  def self.d -> String = "M"
end
module N
  include M
  def self.d -> Int = 1
end
class X
  def initialize; end
end
extension X
  include N
end
"#,
            "`d` returns Int but `M.d`, which it overrides, returns String",
        ),
        (
            "new arguments, ext (class)",
            r#"module M
  abstract def self.make -> Self
end
class X
  def initialize; end
end
extension X
  include M
  def self.make -> Self = new
end
class S < X
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `X.make`",
        ),
        (
            "new arguments, own (class)",
            r#"module M
  abstract def self.make -> Self
end
class X
  def initialize; end
  def self.make -> Self = new
end
extension X
  include M
end
class S < X
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `X.make`",
        ),
        (
            "new arguments, sup (class)",
            r#"module M
  abstract def self.make -> Self
end
class B
  def initialize; end
  def self.make -> Self = new
end
class X < B
  def initialize; end
end
extension X
  include M
end
class S < X
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `B.make`",
        ),
        (
            "new arguments, nmod (class)",
            r#"module M
  abstract def self.make -> Self
end
module N
  include M
  def self.make -> Self = new
end
class X
  def initialize; end
end
extension X
  include N
end
class S < X
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `N.make`",
        ),
        (
            "new arguments, default (class)",
            r#"module M
  def self.make -> Self = new
end
class X
  def initialize; end
end
extension X
  include M
end
class S < X
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `M.make`",
        ),
        (
            "two argument sets (class)",
            r#"module G[T]
  def self.d(x: T) -> String = "G"
end
class X
  def initialize; end
end
extension X
  include G[Int]
end
module Y
  extension X
    include G[String]
  end
end
"#,
            "a generic module `G` is included with one set of arguments",
        ),
        (
            "refused include (generic)",
            r#"module M
  def self.d -> String = "M"
end
class X[U]
  include M
  def initialize; end
end
extension X[V]
  include M
end
"#,
            "already includes `M` (through its own `include`): an extension cannot include it again",
        ),
        (
            "abstract without witness (generic)",
            r#"module M
  abstract def self.d -> String
end
class X[U]
  def initialize; end
end
extension X[V]
  include M
end
"#,
            "`X` must implement `self.d` (abstract in `M`, which this extension includes)",
        ),
        (
            "witness of another type, ext (generic)",
            r#"module M
  def self.d -> String = "M"
end
class X[U]
  def initialize; end
end
extension X[V]
  include M
  def self.d -> Int = 1
end
"#,
            "`d` returns Int but `M.d`, which it overrides, returns String",
        ),
        (
            "witness of another type, own (generic)",
            r#"module M
  def self.d -> String = "M"
end
class X[U]
  def initialize; end
  def self.d -> Int = 1
end
extension X[V]
  include M
end
"#,
            "`d` returns Int but `M.d`, which it overrides, returns String",
        ),
        (
            "witness of another type, sup (generic)",
            r#"module M
  def self.d -> String = "M"
end
class B[U]
  def initialize; end
  def self.d -> Int = 1
end
class X[U] < B[U]
  def initialize; end
end
extension X[V]
  include M
end
"#,
            "`d` returns Int but `M.d`, which it overrides, returns String",
        ),
        (
            "witness of another type, nmod (generic)",
            r#"module M
  def self.d -> String = "M"
end
module N
  include M
  def self.d -> Int = 1
end
class X[U]
  def initialize; end
end
extension X[V]
  include N
end
"#,
            "`d` returns Int but `M.d`, which it overrides, returns String",
        ),
        (
            "new arguments, ext (generic)",
            r#"module M
  abstract def self.make -> Self
end
class X[U]
  def initialize; end
end
extension X[V]
  include M
  def self.make -> Self = new
end
class S < X[Int]
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `X.make`",
        ),
        (
            "new arguments, own (generic)",
            r#"module M
  abstract def self.make -> Self
end
class X[U]
  def initialize; end
  def self.make -> Self = new
end
extension X[V]
  include M
end
class S < X[Int]
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `X.make`",
        ),
        (
            "new arguments, sup (generic)",
            r#"module M
  abstract def self.make -> Self
end
class B[U]
  def initialize; end
  def self.make -> Self = new
end
class X[U] < B[U]
  def initialize; end
end
extension X[V]
  include M
end
class S < X[Int]
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `B.make`",
        ),
        (
            "new arguments, nmod (generic)",
            r#"module M
  abstract def self.make -> Self
end
module N
  include M
  def self.make -> Self = new
end
class X[U]
  def initialize; end
end
extension X[V]
  include N
end
class S < X[Int]
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `N.make`",
        ),
        (
            "new arguments, default (generic)",
            r#"module M
  def self.make -> Self = new
end
class X[U]
  def initialize; end
end
extension X[V]
  include M
end
class S < X[Int]
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "`S#initialize` does not take the arguments of `new` in `M.make`",
        ),
        (
            "two argument sets (generic)",
            r#"module G[T]
  def self.d(x: T) -> String = "G"
end
class X[U]
  def initialize; end
end
extension X[V]
  include G[Int]
end
module Y
  extension X[V]
    include G[String]
  end
end
"#,
            "a generic module `G` is included with one set of arguments",
        ),
        (
            "abstract without witness (module)",
            r#"module M
  abstract def self.d -> String
end
module Mid
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include M
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
        (
            "witness of another type, ext (module)",
            r#"module M
  def self.d -> String = "M"
end
module Mid
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include M
  def self.d -> Int = 1
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
        (
            "witness of another type, own (module)",
            r#"module M
  def self.d -> String = "M"
end
module Mid
  def self.d -> Int = 1
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include M
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
        (
            "witness of another type, nmod (module)",
            r#"module M
  def self.d -> String = "M"
end
module N
  include M
  def self.d -> Int = 1
end
module Mid
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include N
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
        (
            "new arguments, ext (module)",
            r#"module M
  abstract def self.make -> Self
end
module Mid
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include M
  def self.make -> Self = new
end
class S < K
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
        (
            "new arguments, own (module)",
            r#"module M
  abstract def self.make -> Self
end
module Mid
  def self.make -> Self = new
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include M
end
class S < K
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
        (
            "new arguments, nmod (module)",
            r#"module M
  abstract def self.make -> Self
end
module N
  include M
  def self.make -> Self = new
end
module Mid
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include N
end
class S < K
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
        (
            "new arguments, default (module)",
            r#"module M
  def self.make -> Self = new
end
module Mid
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include M
end
class S < K
  @x: Int
  def initialize(@x: Int); end
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
        (
            "two argument sets (module)",
            r#"module G[T]
  def self.d(x: T) -> String = "G"
end
module Mid
end
class K
  include Mid
  def initialize; end
end
extension Mid
  include G[Int]
end
module Y
  extension Mid
    include G[String]
  end
end
"#,
            "an extension of the module `Mid` cannot include",
        ),
    ];
    for (label, src, want) in cells {
        let out = common::diagnostics(src).join("\n");
        assert!(out.contains(want), "{label}: {out}");
    }
}

#[test]
fn a_super_in_a_fixed_witness_is_checked_for_new() {
    // #514's review: a fixed witness runs for `Sub` through `Type[M]`, so
    // `Sub`'s own `make` does not excuse the `new` the witness's `super`
    // reaches (`C.make`'s, or the extension's own).
    for (src, want) in [
        // (Two witnesses of `make` for two modules: the higher one's
        // `super`, whichever extension comes first.)
        (r#"module M1
  abstract def self.make -> Self
end
module M2
  abstract def self.make -> Self
end
class Base
  def self.make -> Self = new
end
class Mid < Base
  def self.make -> Self = super
end
class C < Mid
  def self.make -> Self = raise "no"
end
module X
  extension C
    include M1
  end
  extension Mid
    include M2
  end
  def self.t -> Type[M2] = Sub
end
class Sub < C
  @x: Int
  def initialize(@x: Int); end
  def self.make -> Self = new(1)
  def x -> Int = @x
end
def f(t: Type[M2]) -> M2 = t.make
puts f(X.t).as(Sub).x + 1
"#, "`super` in `Mid.make` runs `new` in `Base.make` with `Sub` for `self`"),
        (r#"module M
  abstract def self.make -> Self
end
class Base
  def self.make -> Self = new
end
class C < Base
  def self.make -> Self = super
end
module X
  extension C
    include M
  end
  def self.t -> Type[M] = Sub
end
class Sub < C
  @x: Int
  def initialize(@x: Int); end
  def self.make -> Self = new(1)
  def x -> Int = @x
end
def f(t: Type[M]) -> M = t.make
puts f(X.t).as(Sub).x + 1
"#, "`super` in `C.make` runs `new` in `Base.make` with `Sub` for `self`, but `Sub#initialize` does not take its arguments"),
        (r#"module M
  abstract def self.make -> Self
end
class C
  def self.make -> Self = new
end
module X
  extension C
    include M
    def self.make -> Self = super
  end
  def self.t -> Type[M] = Sub
end
class Sub < C
  @x: Int
  def initialize(@x: Int); end
  def self.make -> Self = new(1)
  def x -> Int = @x
end
def f(t: Type[M]) -> M = t.make
puts f(X.t).as(Sub).x + 1
"#, "`Sub#initialize` does not take the arguments of `new` in `C.make`"),
    ] {
        let out = common::diagnostics(src).join("\n");
        assert!(out.contains(want), "{out}");
    }
}

#[test]
fn one_set_of_arguments_counts_extensions_of_included_modules() {
    // #514's review: an extension of a module the class includes
    // (`extension Mid; include P[String]`) beside one of the class
    // (`include P[Int]`): such an extension of a module is refused (#530),
    // in either order.
    let out = common::diagnostics(
        r#"module P[T]
  def self.d(x: T) -> T = x
end
module Mid
end
extension Mid
  include P[String]
  def self.d(x: String) -> String = x + "!"
end
class K
  include Mid
  def initialize; end
end
extension K
  include P[Int]
  def self.d(x: Int) -> Int = x * 2
end
def g(t: Type[P[String]]) -> String = t.d("a")
puts g(K)
"#,
    )
    .join("\n");
    assert!(
        out.contains("an extension of the module `Mid` cannot include `P`: `P` has class methods (not supported yet, #530)"),
        "{out}"
    );
    let out = common::diagnostics(
        r#"module P[T]
  def self.d(x: T) -> T = x
end
module Mid
end
extension K
  include P[Int]
  def self.d(x: Int) -> Int = x * 2
end
extension Mid
  include P[String]
  def self.d(x: String) -> String = x + "!"
end
class K
  include Mid
  def initialize; end
end
def g(t: Type[P[String]]) -> String = t.d("a")
puts g(K)
"#,
    )
    .join("\n");
    assert!(
        out.contains("an extension of the module `Mid` cannot include `P`: `P` has class methods (not supported yet, #530)"),
        "{out}"
    );
}

#[test]
fn an_extension_declares_no_abstract_method() {
    // #534: an `abstract def` in an extension, whatever its target and on
    // either side, is an error at the declaration (nothing would
    // implement it: the requirement belongs to the module or abstract
    // class itself).
    let out = common::diagnostics(
        r#"module P
end
extension P
  abstract def self.make -> Self
  abstract def foo -> Int
end
class C
end
extension C
  abstract def self.make -> Self
  abstract def foo -> Int
end
abstract class A
end
extension A
  abstract def foo -> Int
end
"#,
    )
    .join("\n");
    for line in [4, 5, 10, 11, 16] {
        assert!(
            out.contains(&format!(
                "{line}:12: error: an extension cannot declare an abstract method"
            )),
            "{line}: {out}"
        );
    }
    assert_eq!(out.matches("error:").count(), 5, "{out}");
}

#[test]
fn a_synthesized_method_is_checked_as_an_override() {
    // #532: `attr_reader`, `attr_accessor`, `attr_writer` and a `data`
    // type's accessors are paired and checked as overrides as written
    // methods are (the runtime dispatches to them alike).
    for (src, want) in [
        (
            r#"class A
  def name -> String = "a"
end
class B < A
  @name: Int
  attr_reader :name
  def initialize; @name = 1; end
end
def g(a: A) -> String = a.name
puts g(B.new).size
"#,
            "6:3: error: `name` returns Int but `A#name`, which it overrides, returns String",
        ),
        (
            r#"class A
  def name -> String = "a"
  def name=(v: String) -> Void; end
end
class B < A
  var @name: Int
  attr_accessor :name
  def initialize; @name = 1; end
end
"#,
            "7:3: error: `name` returns Int but `A#name`, which it overrides, returns String",
        ),
        (
            r#"class A
  def name=(v: Int) -> String = "a"
end
class B < A
  var @name: Int
  attr_writer :name
  def initialize; @name = 1; end
end
def g(a: A) -> Int = (a.name = 2).size
p g(B.new)
"#,
            "6:3: error: `name=` returns Int but `A#name=`, which it overrides, returns String",
        ),
        (
            r#"module Named
  def name -> String = "named"
end
data P(name: Int)
  include Named
end
def g(n: Named) -> String = n.name
puts g(P.new(1)).size
"#,
            "4:8: error: `name` returns Int but `Named#name`, which it overrides, returns String",
        ),
    ] {
        let out = common::diagnostics(src).join("\n");
        assert!(out.contains(want), "{out}");
        assert_eq!(out.matches("error:").count(), 1, "{out}");
    }
}

#[test]
fn a_conditional_extensions_bound_is_tested_along_the_superclass_chain() {
    // #516: `extension Box[T <: Int]` makes `Box[Int]` and a subclass of
    // `Box[Int]` conform, not `Box[String]` nor a subclass of it, on the
    // instance side and the class side.
    let out = common::diagnostics(
        r#"module Parsable[U]
  abstract def parse(s: String) -> U
end
module Maker[U]
  abstract def self.make(s: String) -> U
  def self.again(s: String) -> U = make(s)
end
class Box[T]
  @v: T
  def initialize(@v: T); end
end
extension Box[T <: Int]
  include Parsable[Int]
  include Maker[Int]
  def parse(s: String) -> Int = @v + s.to_i
  def self.make(s: String) -> Int = s.to_i
end
class SI < Box[Int]
  def initialize; super(1); end
end
class SS < Box[String]
  def initialize; super("s"); end
end
def gen[T <: Maker[Int]](t: Type[T]) -> Int = t.again("6")
a: Parsable[Int] = Box[Int].new(1)
b: Parsable[Int] = SI.new
p SI.again("2"), gen(SI), a.parse("1"), b.parse("1")
c: Parsable[Int] = SS.new
d: Parsable[Int] = Box[String].new("t")
p SS.again("2")
p gen(SS)
"#,
    )
    .join("\n");
    assert!(
        out.contains("cannot assign SS to `c` of type Parsable[Int]"),
        "{out}"
    );
    assert!(
        out.contains("cannot assign Box[String] to `d` of type Parsable[Int]"),
        "{out}"
    );
    assert!(
        out.contains("undefined method `again` for Type[SS]"),
        "{out}"
    );
    assert!(
        out.contains("type argument SS for `T` does not satisfy the bound Maker[Int]"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 4, "{out}");
}

#[test]
fn a_class_a_conditional_extension_does_not_reach_needs_no_new_check() {
    // #516: `SB < Box[String]` does not conform to `N` through
    // `extension Box[T <: Int]`, so no `Type[N]` holds it and `N.make`'s
    // `new` is not checked against its `initialize`.
    let out = common::diagnostics(
        r#"module N
  def self.make -> Self = new
end
class Box[T]
  def initialize; end
end
class SB < Box[String]
  @x: Int
  def initialize(@x: Int); end
  def x -> Int = @x
end
extension Box[T <: Int]
  include N
end
def f(t: Type[N]) -> N = t.make
p f(Box[Int])
p SB.new(3).x
"#,
    )
    .join("\n");
    assert!(!out.contains("error:"), "{out}");
}

#[test]
fn a_module_bound_met_elsewhere_keeps_the_new_check() {
    // #516: `extension Box[T <: Q]`'s bound is met for `SB < Box[String]`
    // where `extension String; include Q` is active (in `X`), where a
    // `Type[N]` may hold `SB`: `N.make`'s `new` is checked against it.
    let out = common::diagnostics(
        r#"module Q
end
module N
  def self.make -> Self = new
end
class Box[T]
  def initialize; end
end
class SB < Box[String]
  @x: Int
  def initialize(@x: Int); end
  def x -> Int = @x
end
module X
  extension String
    include Q
  end
  extension Box[T <: Q]
    include N
  end
  def self.t -> Type[N] = SB
  def self.go -> Int
    v = t.make
    v.as(SB).x + 1
  end
end
p X.go
"#,
    )
    .join("\n");
    assert!(
        out.contains("`SB#initialize` does not take the arguments of `new` in `N.make`"),
        "{out}"
    );
}

#[test]
fn a_nested_argument_not_inferred_yet_meets_a_conditional_bound() {
    // #516 (#518's review): `Bx.new([])` is a `Bx[Array[?]]`; an argument
    // with an inference variable at any depth counts as meeting
    // `extension Bx[T <: Array[Int]]`'s bound, as method lookup treats it
    // (assigned to `Summ` and passed as `Summ`); #519 tightens both.
    let out = common::diagnostics(
        r#"module Summ
  abstract def total -> Int
end
class Bx[T]
  @v: T
  def initialize(@v: T); end
  def v -> T = @v
end
extension Bx[T <: Array[Int]]
  include Summ
  def total -> Int = v.sum
end
def tk(s: Summ) -> Int = s.total
w: Summ = Bx.new([])
p w.total, tk(Bx.new([])), tk(Bx.new([1, 2]))
y = Bx.new([])
p y.total
"#,
    )
    .join("\n");
    assert!(!out.contains("error:"), "{out}");
}

#[test]
fn an_argument_not_inferred_yet_meets_a_bound_only_if_it_still_can() {
    // #518's review: an argument not inferred yet meets a bound when it
    // does with its variables filled with `Nothing` or with `Object`:
    // `Bx[Array[Array[?]]]` can never meet `T <: Array[Int]` (refused as a
    // `Summ`); a bound naming a variable (`B <: Array[A]`) is met.
    let out = common::diagnostics(
        r#"module Summ
  abstract def total -> Int
end
class Bx[T]
  @v: T
  def initialize(@v: T); end
  def v -> T = @v
end
extension Bx[T <: Array[Int]]
  include Summ
  def total -> Int = v.sum
end
w: Summ = Bx.new([[]])
p w.total
def tk(s: Summ) -> Int = s.total
p tk(Bx.new([[]]))
"#,
    )
    .join("\n");
    assert!(
        out.contains("cannot assign Bx[Array[Array[?1]]] to `w` of type Summ"),
        "{out}"
    );
    let out = common::diagnostics(
        r#"module Cnt
  abstract def cnt -> Int
end
class P[A, B]
  @a: A
  @b: B
  def initialize(@a: A, @b: B); end
  def b -> B = @b
end
extension P[A, B <: Array[A]]
  include Cnt
  def cnt -> Int = b.size
end
def tk(s: Cnt) -> Int = s.cnt
x = P.new([], [[1]])
p x.cnt
p tk(P.new([], [[1]]))
w: Cnt = P.new([], [[1]])
p w.cnt
"#,
    )
    .join("\n");
    assert!(!out.contains("error:"), "{out}");
    // (Method lookup alike, #542: `Bx.new([[]]).total` is refused.)
    let out = common::diagnostics(
        r#"module Summ
  abstract def total -> Int
end
class Bx[T]
  @v: T
  def initialize(@v: T); end
  def v -> T = @v
end
extension Bx[T <: Array[Int]]
  include Summ
  def total -> Int = v.sum
end
y = Bx.new([[]])
p y.total
"#,
    )
    .join("\n");
    assert!(
        out.contains("`total` requires T to be Array[Int] (found Array[Array[?1]])"),
        "{out}"
    );
    // (A union with a variable: `Array[Array[?] | String]` can never be an
    // `Array[Int]`.)
    let out = common::diagnostics(
        r#"module Summ
  abstract def total -> Int
end
class Bx[T]
  @v: T
  def initialize(@v: T); end
  def v -> T = @v
end
extension Bx[T <: Array[Int]]
  include Summ
  def total -> Int = v.sum
end
w: Summ = Bx.new([[], "a"])
p w.total
"#,
    )
    .join("\n");
    assert!(
        out.contains("cannot assign Bx[Array[Array[?1] | String]] to `w` of type Summ"),
        "{out}"
    );
    // (`Array[Foo | ?]` with `Foo` not shareable meets `T <: Shareable`
    // with neither fill: refused, and `Object`'s overload runs.)
    let out = common::diagnostics(
        r#"module Summ
  abstract def total -> Int
end
class Bx[T]
  @v: T
  def initialize(@v: T); end
  def v -> T = @v
end
extension Bx[T <: Shareable]
  include Summ
  def total -> Int = 1
end
class Foo
  var @n: Int
  def initialize; @n = 0; end
end
def mk[A] -> Array[Foo | A] = [Foo.new]
def f(s: Summ) -> String = "summ"
def f(o: Object) -> String = "obj"
p f(Bx.new(mk))
w: Summ = Bx.new(mk)
"#,
    )
    .join("\n");
    assert!(
        out.contains("cannot assign Bx[Array[Foo | ?4]] to `w` of type Summ"),
        "{out}"
    );
}

#[test]
fn a_rescue_class_is_a_run_time_test() {
    // #533: a `rescue` class goes through the testability check as
    // `is_a?` does (docs/02 §7): the test sees the class, not its type
    // arguments, so `rescue MyErr[Int]` is an error (alone or beside
    // another class); a generic exception class is rescued through a
    // non-generic superclass (the fixture `rescue_generic_superclass.qz`).
    let out = common::diagnostics(
        r#"class MyErr[T <: Shareable] < StandardError
  @payload: T
  def initialize(@payload: T); super("e"); end
  def payload -> T = @payload
end
begin
  raise MyErr[String].new("s")
rescue MyErr[Int] => e
  p e.payload + 1
end
"#,
    )
    .join("\n");
    assert!(
        out.contains("8:8: error: `rescue` cannot check at run time that a value of type Exception is a MyErr[Int] (type arguments are not known then)"),
        "{out}"
    );
    let out = common::diagnostics(
        r#"class MyErr[T <: Shareable] < StandardError
  @payload: T
  def initialize(@payload: T); super("e"); end
  def payload -> T = @payload
end
begin
  raise MyErr[String].new("s")
rescue ArgumentError, MyErr[String] => e
  p e.message
end
"#,
    )
    .join("\n");
    assert!(
        out.contains(
            "`rescue` cannot check at run time that a value of type Exception is a MyErr[String]"
        ),
        "{out}"
    );
}

#[test]
fn a_modules_new_reaching_a_runtime_built_class_is_refused() {
    // #535: a module's class method calling `new` cannot build a class the
    // runtime builds (`World::built_by_runtime`: `Time` and the other
    // built-in values; `Array`, `Random` and the classes with a native
    // `self.new`), reached through an extension's conformance; every such
    // class is in quarz-types' generated test.
    for (src, class) in [
        (
            r#"module M
  def self.make -> Self = new
end
extension Time
  include M
end
def mk(t: Type[M]) -> M = t.make
x = mk(Time).as(Time)
puts "made"
p x.to_i
"#,
            "Time",
        ),
        (
            r#"module M
  def self.make -> Self = new
end
extension Array[T]
  include M
end
def mk(t: Type[M]) -> M = t.make
x = mk(Array[Int]).as(Array[Int])
p x.size
"#,
            "Array",
        ),
        (
            r#"module M
  def self.make -> Self = new
end
extension Random
  include M
end
def mk(t: Type[M]) -> M = t.make
x = mk(Random).as(Random)
p x.rand(10) < 10
"#,
            "Random",
        ),
    ] {
        let out = common::diagnostics(src).join("\n");
        assert!(
            out.contains(&format!(
                "2:27: error: `new` in `M.make` reaches `{class}`, whose values the runtime makes"
            )),
            "{out}"
        );
    }
    // (A subclass too: a user's `MyR < Random` and `MyIO < IO`, written
    // `new` included; std's `TCPSocket < IO` likewise, with `require`.)
    for (src, want) in [
        (
            r#"module M
  def self.make -> Self = new
end
class MyR < Random
  include M
end
def mk(t: Type[M]) -> M = t.make
x = mk(MyR).as(MyR)
puts "made"
p x.rand(10)
"#,
            "`new` in `M.make` reaches `MyR`, whose values the runtime makes",
        ),
        (
            r#"class MyIO < IO
end
x = MyIO.new
puts "made"
x.puts "hi"
"#,
            "`MyIO` is not built with `new`",
        ),
    ] {
        let out = common::diagnostics(src).join("\n");
        assert!(out.contains(want), "{out}");
    }
}

#[test]
fn the_class_relative_override_pairs_are_checked() {
    // #536 step 1: a later-included module's method over an earlier one's,
    // a superclass's method implementing an included module's abstract
    // one, and the class-side pair, all from the one override table, are
    // checked as overrides (result type), once each.
    for (src, want) in [
        (r#"module M1
  def m -> String = "a"
end
module M2
  def m -> Int = 1
end
class C
  include M1
  include M2
  def initialize; end
end
"#, "5:3: error: `m` returns Int but `M1#m`, which it overrides in `C`, which includes `M2`, returns String"),
        (r#"module AK
  abstract def m -> String
end
class AB
  def initialize; end
  def m -> Int = 1
end
class AS < AB
  include AK
end
"#, "6:3: error: `m` returns Int but `AK#m`, which it overrides, returns String"),
        (r#"module K1
  def self.label -> String = "a"
end
module K2
  def self.label -> Int = 1
end
class KC
  include K1
  include K2
end
"#, "5:3: error: `label` returns Int but `K1.label`, which it overrides, returns String"),
    ] {
        let out = common::diagnostics(src).join("\n");
        assert!(out.contains(want), "{out}");
        assert_eq!(out.matches("error:").count(), 1, "{out}");
    }
}

/// #536 (g) on the std side: what a std class's own includes bring over a
/// module an extension includes is checked at the extension.
#[test]
fn a_std_include_over_an_extensions_module_is_checked() {
    let out = common::diagnostics(
        "module OM\n  def first -> String = \"om\"\nend\nextension Set[T]\n  include OM\nend\n",
    );
    assert!(
        out.iter()
            .any(|d| d.contains("`first` returns T? but `OM#first`, which it overrides")),
        "{out:?}"
    );
    // A std ancestor implementing the module's abstract method.
    let out = common::diagnostics(
        "module OM\n  abstract def hash -> String\nend\nextension Int\n  include OM\nend\n",
    );
    assert!(
        out.iter()
            .any(|d| d.contains("`hash` returns Int but `OM#hash`, which it overrides")),
        "{out:?}"
    );
}

/// #525: a witness of another type is reported once, at the method where
/// the class side's own check reported it (for some extension active
/// there); a class whose method no such report names gets its report at
/// the extension.
#[test]
fn a_witness_of_another_type_is_reported_once() {
    let out = common::diagnostics(
        "module M\n  def self.d -> String = \"M\"\nend\nclass X\n  def initialize; end\n  def self.d -> Int = 1\nend\nextension X\n  include M\nend\n",
    );
    let n = out
        .iter()
        .filter(|d| d.contains("`d` returns Int but `M.d`"))
        .count();
    assert_eq!(n, 1, "{out:?}");
    let out = common::diagnostics(
        "module M\n  def self.d -> String = \"M\"\nend\nclass X\n  def initialize; end\n  def self.d -> Int = 1\nend\nclass Y\n  def initialize; end\n  def self.d -> Int = 2\nend\nextension X\n  include M\nend\nmodule Sc\n  extension Y\n    include M\n  end\nend\n",
    );
    let n = out
        .iter()
        .filter(|d| d.contains("`d` returns Int but `M.d`"))
        .count();
    assert_eq!(n, 2, "{out:?}");
}

/// #522: `super` passes over an abstract declaration; with no method with
/// a body after it, the call is an error as an undefined `super` is.
#[test]
fn super_past_an_abstract_declaration_with_nothing_after() {
    let out = common::diagnostics(
        "module P\n  abstract def parse(s: String) -> String\nend\nclass Num\n  include P\n  def initialize; end\n  def parse(s: String) -> String = super(s)\nend\n",
    );
    assert!(
        out.iter()
            .any(|d| d.contains("no superclass method `parse`")),
        "{out:?}"
    );
}

/// #577: two active scoped extensions whose includes give the class a
/// method of the name, neither overriding the other: the call is
/// ambiguous, naming both extensions and modules, wherever the `using`s
/// are and on both sides.
#[test]
fn two_active_extensions_includes_are_ambiguous() {
    let base = "module M1\n  def it -> String = \"M1\"\n  def self.tag -> String = \"M1\"\nend\nmodule M2\n  def it -> Int = 2\n  def self.tag -> Int = 2\nend\nclass C\n  def initialize; end\nend\n";
    let exts = "module S1\n  extension C\n    include M1\n  end\nend\nmodule S2\n  extension C\n    include M2\n  end\nend\n";
    let both = "module Both\n  extension C\n    include M1\n  end\n  extension C\n    include M2\n  end\nend\n";
    let cases = [
        format!("{base}{exts}def f -> Object\n  using S1\n  using S2\n  C.new.it\nend\n"),
        format!("{base}{exts}def f -> Object\n  using S2\n  using S1\n  C.new.it\nend\n"),
        format!("{base}{exts}using S1\nusing S2\nx = C.new.it\n"),
        format!("{base}{both}def f -> Object\n  using Both\n  C.new.it\nend\n"),
        format!("{base}{exts}def f -> Object\n  using S1\n  using S2\n  C.tag\nend\n"),
        // A receiver of a bounded type parameter, a method reference,
        // `&:name`, an interpolation, `super` in another extension's
        // method, a `for` loop's `each`.
        format!("{base}{exts}def f[T <: C](x: T) -> Object\n  using S1\n  using S2\n  x.it\nend\n"),
        format!("{base}{exts}def f -> Object\n  using S1\n  using S2\n  m = C.new.:it\n  m.call\nend\n"),
        format!("{base}{exts}def f -> Object\n  using S1\n  using S2\n  [C.new].map(&:it)\nend\n"),
        format!("{base}{exts}def f -> Object\n  using S1\n  using S2\n  \"#{{C.new}}\"\nend\n").replace("def it ->", "def to_s ->").replace(".map(&:it)", ""),
        format!("{base}{exts}module S3\n  using S1\n  using S2\n  extension C\n    def it -> Object = super\n  end\nend\n"),
    ];
    for src in &cases {
        let out = common::diagnostics(src);
        assert!(
            out.iter().any(|d| d.contains("is ambiguous: ")
                && d.contains("extension")
                && d.contains("`M1`")
                && d.contains("`M2`")),
            "{src}\n{out:?}"
        );
    }
}

/// #577: a scoped conditional extension's include beside another scoped
/// one's, both active and the bound holding: ambiguous; with the bound
/// failing (`Box[String]`), the other's alone.
#[test]
fn a_conditional_extensions_include_beside_a_scoped_one_is_ambiguous() {
    let src = "module M1\n  def it -> String = \"M1\"\nend\nmodule M2\n  def it -> String = \"M2\"\nend\nclass Box[T]\n  def initialize; end\nend\nmodule S1\n  extension Box[T <: Int]\n    include M1\n  end\nend\nmodule S2\n  extension Box[T]\n    include M2\n  end\nend\ndef f -> String\n  using S1\n  using S2\n  Box[Int].new.it\nend\ndef g -> String\n  using S1\n  using S2\n  Box[String].new.it\nend\n";
    let out = common::diagnostics(src);
    let amb: Vec<_> = out.iter().filter(|d| d.contains("is ambiguous")).collect();
    assert_eq!(amb.len(), 1, "{out:?}");
    assert!(amb[0].contains("the extension of `Box` in `S1`"), "{out:?}");
}

/// #577: the pair named is two the others do not override (M2 overrides
/// M1, which it includes, but ties with M3), and a module that comes
/// through an extension's include is said to be brought. (A third
/// extension including M1 itself, the cell before #517, would bring M1 to
/// `C` a second time: refused since #517.)
#[test]
fn an_ambiguity_names_the_tied_modules() {
    let src = "module M1\n  def it -> String = \"M1\"\nend\nmodule M2\n  include M1\n  def it -> String = \"M2\"\nend\nmodule M3\n  def it -> String = \"M3\"\nend\nmodule N3\n  include M3\nend\nclass C\n  def initialize; end\nend\nmodule S2\n  extension C\n    include M2\n  end\nend\nmodule S3\n  extension C\n    include N3\n  end\nend\ndef f -> String\n  using S2\n  using S3\n  C.new.it\nend\n";
    let out = common::diagnostics(src);
    assert!(
        out.iter()
            .any(|d| d.contains("in `S2` includes `M2`") && d.contains("in `S3` brings `M3`")),
        "{out:?}"
    );
}

/// #577: a `for` loop whose `each` two active extensions' modules give
/// reports the ambiguity, not its fallback's error.
#[test]
fn a_for_loop_over_an_ambiguous_each_says_so() {
    let src = "module M1\n  def each(&: (Int) -> Void) -> Void\n    yield 1\n  end\nend\nmodule M2\n  def each(&: (Int) -> Void) -> Void\n    yield 2\n  end\nend\nclass C\n  def initialize; end\nend\nmodule S1\n  extension C\n    include M1\n  end\nend\nmodule S2\n  extension C\n    include M2\n  end\nend\ndef f -> Void\n  using S1\n  using S2\n  for x in C.new\n    puts x\n  end\nend\n";
    let out = common::diagnostics(src);
    assert!(
        out.iter()
            .any(|d| d.contains("the call of `each` is ambiguous")),
        "{out:?}"
    );
}

/// #577: compound assignment and `&:name` on a union element, where two
/// active extensions' modules give the operator or method, are ambiguous
/// too; and a trial of `&:name` that an overload discards counts for no
/// `for` loop (one over another overload's result is accepted).
#[test]
fn compound_assignment_and_union_symbols_are_ambiguous() {
    let base = "module M1\n  def +(o: Int) -> C = C.new\n  def it -> String = \"M1\"\nend\nmodule M2\n  def +(o: Int) -> C = C.new\n  def it -> String = \"M2\"\nend\nclass C\n  def initialize; end\nend\nclass D\n  def initialize; end\n  def it -> String = \"D\"\nend\nmodule S1\n  extension C\n    include M1\n  end\nend\nmodule S2\n  extension C\n    include M2\n  end\nend\n";
    for body in [
        "def f -> Object\n  using S1\n  using S2\n  x = C.new\n  x += 1\n  x\nend\n",
        "def f -> Object\n  using S1\n  using S2\n  xs: Array[C | D] = [C.new, D.new]\n  xs.map(&:it)\nend\n",
    ] {
        let out = common::diagnostics(&format!("{base}{body}"));
        assert!(
            out.iter().any(|d| d.contains("is ambiguous: the extension of `C` in `S")),
            "{body}\n{out:?}"
        );
    }
}

/// #577 (quarz-manager's review): a class object of a type parameter, two
/// top-level conditional extensions, and a method reference whose rival
/// modules' overloads differ in parameters (no arguments to choose with)
/// are ambiguous too.
#[test]
fn more_forms_of_two_extensions_are_ambiguous() {
    let hdr = "module M1\n  def it -> String = \"M1\"\n  def self.tag -> String = \"M1t\"\nend\nmodule M2\n  def it -> String = \"M2\"\n  def self.tag -> String = \"M2t\"\nend\nclass C\n  def initialize; end\nend\nmodule S1\n  extension C\n    include M1\n  end\nend\nmodule S2\n  extension C\n    include M2\n  end\nend\n";
    let cases = [
        format!("{hdr}def g[T <: C](k: Type[T]) -> String\n  using S1\n  using S2\n  k.tag\nend\n"),
        "module M1\n  def it -> String = \"M1\"\nend\nmodule M2\n  def it -> String = \"M2\"\nend\nclass Box[T]\n  def initialize; end\nend\nextension Box[T <: Int]\n  include M1\nend\nextension Box[T <: Comparable[T]]\n  include M2\nend\nputs Box[Int].new.it\n".to_string(),
        "module M1\n  def it(x: Int) -> String = \"M1\"\nend\nmodule M2\n  def it(x: Float) -> String = \"M2\"\nend\nclass K\n  def initialize; end\nend\nmodule S1\n  extension K\n    include M1\n  end\nend\nmodule S2\n  extension K\n    include M2\n  end\nend\ndef f -> Object\n  using S1\n  using S2\n  K.new.:it\nend\n".to_string(),
    ];
    for src in &cases {
        let out = common::diagnostics(src);
        assert!(
            out.iter().any(|d| d.contains("is ambiguous: ")),
            "{src}\n{out:?}"
        );
    }
}

/// #577: an ambiguity inside an overload trial that is discarded counts
/// for no `for` loop: the loop over the other overload's result falls back
/// as without it.
#[test]
fn a_discarded_trials_ambiguity_leaves_a_for_loop_alone() {
    let src = "module M1\n  def it -> String = \"M1\"\nend\nmodule M2\n  def it -> String = \"M2\"\nend\nclass C\n  def initialize; end\nend\nclass Z\n  def initialize; end\n  def it -> String = \"Z\"\nend\nmodule S1\n  extension C\n    include M1\n  end\nend\nmodule S2\n  extension C\n    include M2\n  end\nend\nclass W\n  def initialize; end\n  def map(&b: (Int) -> Object) -> Array[Object] = [b.call(1)]\nend\ndef pick(&b: (C) -> String) -> W = W.new\ndef pick(&b: (Z) -> String) -> W = W.new\ndef f -> Void\n  using S1\n  using S2\n  for x in pick { |c| c.it }\n    puts x\n  end\nend\n";
    let out = common::diagnostics(src);
    assert!(
        !out.iter().any(|d| d.contains("undefined method `each`")),
        "{out:?}"
    );
}

/// #577: a module credited to a top-level conditional extension only where
/// its bound holds for the receiver: an extension of the superclass that
/// does not apply does not hide the rivalry of the class's own one with a
/// scoped one.
#[test]
fn an_inapplicable_conditional_extension_hides_no_rivalry() {
    let src = "module A\n  def foo -> String = \"A\"\nend\nmodule M2\n  def foo -> String = \"M2\"\nend\nclass Base[T]\n  def initialize(v: T); end\nend\nclass Sub[T] < Base[T]\n  def initialize(v: T); end\nend\nextension Base[T <: String]\n  include A\nend\nextension Sub[T <: Int]\n  include A\nend\nmodule S\n  extension Sub[T]\n    include M2\n  end\nend\ndef r1\n  using S\n  puts Sub.new(1).foo\nend\nr1\n";
    let out = common::diagnostics(src);
    assert!(
        out.iter()
            .any(|d| d.contains("is ambiguous: the top-level extension of `Sub`")),
        "{out:?}"
    );
}

/// #580: under `using`, `C.tag` on a class written by name is typed as the
/// extension's module's class method, which runs: its Object result is not
/// a String.
#[test]
fn a_class_call_under_using_is_typed_as_the_extensions_module() {
    let src = "module A\n  def self.tag -> Object = \"A\"\nend\nclass P\n  def self.tag -> String = \"P\"\nend\nclass C < P\nend\nmodule Sa\n  extension C\n    include A\n  end\nend\ndef f -> String\n  using Sa\n  s: String = C.tag\n  s\nend\n";
    let out = common::diagnostics(src);
    assert!(
        out.iter()
            .any(|d| d.contains("cannot assign Object to `s`")),
        "{out:?}"
    );
}

/// #585: `super` in an extension's method, with two other extensions of
/// the target active where it is declared that define the method with the
/// same parameters, neither overriding the other: ambiguous, naming both.
#[test]
fn super_between_two_other_extensions_is_ambiguous() {
    let src = "class Base\n  def f(x: Int) -> String = \"Base\"\nend\nclass A < Base\n  def initialize; end\nend\nmodule Y\n  extension A\n    def f(x: Int) -> String = \"Y/\" + super(x)\n  end\nend\nmodule W\n  extension A\n    def f(x: Int) -> String = \"W/\" + super(x)\n  end\nend\nmodule X\n  using Y\n  using W\n  extension A\n    def f(x: Int) -> String = \"X/\" + super(x)\n  end\nend\n";
    let out = common::diagnostics(src);
    assert!(
        out.iter().any(|d| d.contains("the call of `f` is ambiguous: the extension of `A` in `Y` and the extension of `A` in `W`")),
        "{out:?}"
    );
}

/// #585: a `super` that would take a method of an extension reaching its
/// own back (no order between them) is an error at the `super`: two
/// top-level extensions, two scoped ones whose modules `using` each other,
/// and two extensions of one class in the same module (siblings).
#[test]
fn super_between_extensions_reaching_each_other_is_refused() {
    for src in ["class A\n  def initialize; end\nend\nextension A\n  def f(x: Int) -> String = \"T1/\" + super(x, x)\nend\nextension A\n  def f(x: Int, y: Int) -> String = \"T2/\" + super(x)\nend\nputs A.new.f(1, 2).size\n", "class A\n  def initialize; end\n  def f(x: Int) -> String = \"A\"\nend\nmodule Y\n  using X\n  extension A\n    def f(x: Int) -> String = \"Y/\" + super(x)\n  end\nend\nmodule X\n  using Y\n  extension A\n    def f(x: Int) -> String = \"X/\" + super(x)\n  end\nend\nmodule Z\n  using X\n  def self.go -> String = A.new.f(1)\nend\nputs Z.go.size\n"] {
        let out = common::diagnostics(src);
        assert!(
            out.iter().any(|d| d.contains("which reaches this one back: there is no order between them")),
            "{src}\n{out:?}"
        );
    }
    let sib = "class A\n  def initialize; end\n  def f(x: Int) -> String = \"A\"\nend\nmodule Both\n  extension A\n    def f(x: Int) -> String = \"E1/\" + super(x)\n  end\n  extension A\n    def f(x: Int) -> String = \"E2\"\n  end\nend\nmodule Z\n  using Both\n  def self.go -> String = A.new.f(1)\nend\n";
    let out = common::diagnostics(sib);
    assert!(
        out.iter()
            .any(|d| d.contains("which reaches this one back")),
        "{out:?}"
    );
}

/// #585: extensions in one cycle hide none of each other (three in a
/// cycle, all reached by a fourth: no order, the ambiguity), and a cycle's
/// candidate tied with another (a sibling and an unordered other) makes
/// the `super` an error rather than being left out.
#[test]
fn cycles_hide_nothing_and_ties_with_them_are_errors() {
    let out = common::diagnostics("# Y -> W -> V -> Y (a cycle, each reaching the next directly only);\n# X reaches all three and is outside the cycle.\nclass A\n  def initialize; end\n  def f(x: Int) -> String = \"A\"\nend\nmodule Y\n  using W\n  extension A\n    def f(x: Int) -> String = \"Y\"\n  end\nend\nmodule W\n  using V\n  extension A\n    def f(x: Int) -> String = \"W\"\n  end\nend\nmodule V\n  using Y\n  extension A\n    def f(x: Int) -> String = \"V\"\n  end\nend\nmodule X\n  using Y\n  using W\n  using V\n  extension A\n    def f(x: Int) -> String = \"X/\" + super(x)\n  end\nend\nmodule Z\n  using X\n  def self.go -> String = A.new.f(1)\nend\nputs Z.go\n");
    assert!(
        out.iter()
            .any(|d| d.contains("the call of `f` is ambiguous")),
        "{out:?}"
    );
    let out = common::diagnostics("class A\n  def initialize; end\n  def f(x: Int) -> String = \"A\"\nend\nmodule V\n  extension A\n    def f(x: Int) -> String = \"V\"\n  end\nend\nmodule N\n  extension A\n    def f(x: Int) -> String = \"Y\"\n  end\n  using V\n  extension A\n    def f(x: Int) -> String = \"X/\" + super(x)\n  end\nend\nmodule Z\n  using N\n  def self.go -> String = \"ok\"\nend\nputs Z.go\n");
    assert!(
        out.iter()
            .any(|d| d.contains("which reaches this one back")),
        "{out:?}"
    );
}

/// #515: a run-time test of a module an extension with bounds brings is
/// refused wherever the value may be of a class whose answer depends on
/// type arguments the run time does not see: each written form, a call
/// on a union, `!` on a union; a test that holds statically (`D[Int]`, a
/// `B` through `C[T <: Int]`) but which the run time, seeing only the
/// class, would answer otherwise; a subclass seen through its superclass.
#[test]
fn runtime_tests_the_class_does_not_answer_are_refused() {
    let base = "module Num\n  def n -> Int = 1\n  def ! -> Bool = true\nend\nmodule N2\n  def n -> Int = 2\n  def ! -> Bool = false\nend\nclass Box[T]\n  include N2\n  @v: T\n  def initialize(@v: T); end\nend\nextension Box[T <: Int]\n  include Num\nend\n";
    let cases = [
        (
            "def f(x: Object) -> Bool = x.is_a?(Num)\n",
            "`is_a?` cannot check at run time",
        ),
        (
            "def f(x: Object) -> Num = x.as(Num)\n",
            "`as` cannot check at run time",
        ),
        (
            "def f(x: Object) -> Num? = x.as?(Num)\n",
            "`as?` cannot check at run time",
        ),
        (
            "def f(x: Object) -> Int\n  case x\n  when Num then 1\n  else 0\n  end\nend\n",
            "`when` cannot check at run time",
        ),
        (
            "def f(x: Object) -> Int\n  case x\n  in Num then 1\n  else 0\n  end\nend\n",
            "`in` cannot check at run time",
        ),
        (
            "def f(x: Num | N2) -> Int = x.n\n",
            "a call on a union cannot check at run time",
        ),
        (
            "def f(x: Num | N2) -> Bool = !x\n",
            "cannot check at run time",
        ),
    ];
    for (body, want) in cases {
        let src = format!("{base}{body}");
        let out = common::diagnostics(&src);
        assert!(
            out.iter()
                .any(|d| d.contains(want) && d.contains("the run time sees only the class `Box`")),
            "{src}\n{out:?}"
        );
    }
    // Statically true, which the run time would answer `false`.
    let d = "module B\n  def it -> String = \"B\"\nend\nclass C[T]\n  def initialize; end\nend\nextension C[T <: Int]\n  include B\nend\nclass D[T] < C[T]\n  def initialize; end\nend\ndef f(x: D[Int]) -> Bool = x.is_a?(B)\n";
    let out = common::diagnostics(d);
    assert!(
        out.iter()
            .any(|m| m
                .contains("a value of type D[Int] is a B: the run time sees only the class `D`")),
        "{out:?}"
    );
    // A module type whose arguments fix the answer, which the table, by
    // the class alone (`Holder`'s walk sees `Seq[T]`), answers otherwise.
    let seq = "module Num\n  def n -> Int = 1\nend\nmodule Seq[T]\nend\nextension Seq[T <: Int]\n  include Num\nend\nclass Holder[T]\n  include Seq[T]\n  @v: T\n  def initialize(@v: T); end\nend\ndef through_module(x: Seq[Int]) -> Bool = x.is_a?(Num)\n";
    let out = common::diagnostics(seq);
    assert!(
        out.iter()
            .any(|m| m.contains("a value of type Holder[Int] is a Num")),
        "{out:?}"
    );
    // A subclass whose arguments the static type does not fix.
    let sub = "module Num\n  def n -> Int = 1\nend\nclass Base\nend\nclass Sub[T] < Base\n  @v: T\n  def initialize(@v: T); end\nend\nextension Sub[T <: Int]\n  include Num\nend\ndef f(x: Base) -> Bool = x.is_a?(Num)\n";
    let out = common::diagnostics(sub);
    assert!(
        out.iter()
            .any(|m| m.contains("a value of type Sub[T] is a Num")),
        "{out:?}"
    );
}

/// #515, from the review: a module an extension with bounds brings through
/// an extension of a module it includes; a module type only an extension
/// with bounds brings (its classes are values of it); the elements a test
/// checks (`as?(Array[Num])`); a class value's test (`Type[Num]`): each
/// refused, as each would answer wrongly at run time.
#[test]
fn runtime_tests_through_extensions_elements_and_class_values_are_refused() {
    // (A module target's extension declares the requirement it brings
    // `abstract`: an extension completes the conformance it makes, R0.)
    for src in ["module M\n  abstract def m -> Int\nend\nmodule X\n  abstract def m -> Int\nend\nextension X\n  include M\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension Box[T <: Int]\n  include X\n  def m -> Int = v + 1\nend\ndef f(o: Object) -> Int\n  if o.is_a?(M)\n    o.m\n  else\n    0\n  end\nend\nputs f(Box.new(41))\nputs f(Box.new(\"s\"))\n", "# a module type K a conditional extension brings: classes_a_value_may_hold misses Box\nmodule K\nend\nmodule Num\n  abstract def n -> Int\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension Box[T <: Int]\n  include K\nend\nextension Box[T <: String]\n  include Num\n  def n -> Int = v.size\nend\ndef f(x: K) -> Int\n  if x.is_a?(Num)\n    x.n\n  else\n    -1\n  end\nend\nputs f(Box.new(5))\n", "# element tests: Array[Num], tuple, against a module a conditional extension brings\nmodule Num\n  abstract def n -> Int\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension Box[T <: Int]\n  include Num\n  def n -> Int = v + 1\nend\no: Object = [Box.new(\"s\")]\na = o.as?(Array[Num])\nputs a ? a[0].n : -1\n", "# class objects against a module a conditional extension brings\nmodule Num\n  def self.tag -> String = \"num\"\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\nend\nextension Box[T <: Int]\n  include Num\nend\nclass Other\nend\no: Object = Box\nputs o.is_a?(Type[Num])\nk = o.as?(Type[Num])\nputs k ? k.tag : \"nil\"\no2: Object = Other\nputs o2.is_a?(Type[Num])\n"] {
        let out = common::diagnostics(src);
        assert!(
            out.iter().any(|d| d.contains("cannot check at run time that a value of type")),
            "{src}\n{out:?}"
        );
    }
}

/// #515, from #596's second review: a covariant static type holding a
/// subclass with other arguments (`Box[Object]` holding a `D[Int]`), a
/// union argument (`Box[Int | String]`), and a generic module type whose
/// arguments fail the bound (`K[String]`): each would answer wrongly at
/// run time, and is refused.
#[test]
fn runtime_tests_through_variance_unions_and_generic_modules_are_refused() {
    // (As above: `K`'s extension implements the `n` it brings, R0.)
    for src in ["# skip of a concrete-argument class under covariance: D[U] < Box[Int], D[U <: String] brings Num\nmodule Num\n  abstract def n -> Int\nend\nclass Box[out T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nclass D[U] < Box[Int]\n  @u: U\n  def initialize(@u: U); super(1); end\n  def u -> U = @u\nend\nextension D[U <: String]\n  include Num\n  def n -> Int = u.size\nend\ndef f(x: Box[Object]) -> Int\n  y = x.as?(Num)\n  y ? y.n : -1\nend\nputs f(D.new(\"abc\"))\nputs f(D.new(7))\n", "module Num\n  abstract def n -> Int\nend\nclass Box[out T]\n  def initialize; end\nend\nclass D[U] < Box[Int]\n  @u: U\n  def initialize(@u: U); end\n  def u -> U = @u\nend\nextension D[U <: String]\n  include Num\n  def n -> Int = u.size\nend\ndef f(x: Box[Int | String]) -> Bool = x.is_a?(Num)\nputs f(D.new(7))\n", "# always shortcut through a generic module whose bounded extension brings Num\nmodule Num\n  abstract def n -> Int\nend\nmodule K[T]\nend\nextension K[T <: Int]\n  include Num\n  def n -> Int = 0\nend\nclass G[T]\n  include K[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension G[T <: Int]\n  include Num\n  def n -> Int = v + 1\nend\ndef f(x: K[String]) -> Int\n  y = x.as?(Num)\n  y ? y.n : -1\nend\nputs f(G.new(\"s\"))\n"] {
        let out = common::diagnostics(src);
        assert!(
            out.iter().any(|d| d.contains("cannot check at run time that a value of type")),
            "{src}\n{out:?}"
        );
    }
}

/// #515, from quarz-manager's review of #596: the elements' static type is
/// the static type's only when every member of it is that collection (a
/// tuple of that arity); a union with another member (`Array[Int] |
/// Enumerable[Box[String]]`, a tuple beside an `Array`) tests elements of
/// any type, so a test of a module an extension with bounds brings is
/// refused.
#[test]
fn element_tests_through_another_member_are_refused() {
    for src in ["module Num\n  def n -> Int = 1\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension Box[T <: Int]\n  include Num\n  def n -> Int = v + 1\nend\nclass SI < Box[Int]\n  def initialize; super(1); end\nend\n# element test through a non-Array member of the static type\ndef f(x: Array[Int] | Enumerable[Box[String]]) -> Int\n  a = x.as?(Array[Num])\n  a ? a.map { |e| e.n }.sum : -1\nend\np f([Box.new(\"s\")])\n", "module Num\n  abstract def n -> Int\nend\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension Box[T <: Int]\n  include Num\n  def n -> Int = v + 1\nend\ndef g(x: [Int, Int] | Array[Box[String] | Int]) -> Int\n  case x\n  in [Num => a, Int] then a.n\n  else -1\n  end\nend\np g([Box.new(\"s\"), 1])\n"] {
        let out = common::diagnostics(src);
        assert!(
            out.iter().any(|d| d.contains("cannot check at run time that a value of type")),
            "{src}\n{out:?}"
        );
    }
}

#[test]
fn a_class_conforms_to_a_module_once() {
    // #517: a second extension of a class including a module the class
    // already conforms to through another extension is an error at the
    // later one, naming the other: on both sides, whatever the bounds,
    // wherever declared, directly or through a module it includes.
    let refused: &[(&str, &str, &str)] = &[
        (
            "class side (the issue's reproducer)",
            r#"module Parsable
  def self.describe -> String = "Parsable"
end
class Same
end
module X
  extension Same
    include Parsable
    def self.describe -> String = "X"
  end
end
module Y
  extension Same
    include Parsable
    def self.describe -> String = "Y"
  end
  def self.direct -> String = Same.describe
  def self.t -> Type[Parsable] = Same
end
"#,
            "13:13: error: `Same` already conforms to `Parsable` through another extension (`extension Same` in `X`): this extension cannot include it again; a class conforms to a module once",
        ),
        (
            "instance side",
            r#"module Named
  abstract def name -> String
end
class Same
  def initialize; end
end
module X
  extension Same
    include Named
    def name -> String = "X"
  end
end
module Y
  extension Same
    include Named
    def name -> String = "Y"
  end
end
"#,
            "14:13: error: `Same` already conforms to `Named` through another extension (`extension Same` in `X`)",
        ),
        (
            "top-level, then scoped",
            r#"module Named
  abstract def name -> String
end
class C
  def initialize; end
end
extension C
  include Named
  def name -> String = "top"
end
module Y
  extension C
    include Named
    def name -> String = "Y"
  end
end
"#,
            "12:13: error: `C` already conforms to `Named` through another extension (a top-level `extension C`)",
        ),
        (
            "scoped, then top-level",
            r#"module Named
  abstract def name -> String
end
class C
  def initialize; end
end
module Y
  extension C
    include Named
    def name -> String = "Y"
  end
end
extension C
  include Named
  def name -> String = "top"
end
"#,
            "13:11: error: `C` already conforms to `Named` through another extension (`extension C` in `Y`)",
        ),
        (
            "conditional, disjoint bounds",
            r#"module Named
  abstract def name -> String
end
class Box[T]
  @v: T
  def initialize(@v: T)
  end
  def v -> T = @v
end
extension Box[T <: Int]
  include Named
  def name -> String = (v + 1).to_s
end
extension Box[T <: String]
  include Named
  def name -> String = v
end
"#,
            "14:11: error: `Box` already conforms to `Named` through another extension (a top-level `extension Box`)",
        ),
        (
            "through a module it includes",
            r#"module Named
  abstract def name -> String
end
module Wrap
  include Named
end
class C
  def initialize; end
end
extension C
  include Named
  def name -> String = "top"
end
module Y
  extension C
    include Wrap
  end
end
"#,
            "15:13: error: `C` already conforms to `Named` through another extension (a top-level `extension C`): this extension cannot bring it again through `Wrap`",
        ),
    ];
    for (label, src, want) in refused {
        let out = common::diagnostics(src).join("\n");
        assert!(out.contains(want), "{label}: {out}");
        assert_eq!(out.matches("error:").count(), 1, "{label}: {out}");
    }
    // A superclass's conformance through an extension does not count: a
    // subclass may conform on its own.
    let out = common::diagnostics(
        r#"module Named
  abstract def name -> String
end
class Base
  def initialize; end
end
class Sub < Base
end
extension Base
  include Named
  def name -> String = "base"
end
extension Sub
  include Named
  def name -> String = "sub"
end
"#,
    )
    .join("\n");
    assert!(!out.contains("error:"), "{out}");
}

#[test]
fn enumerables_select_is_typed_as_an_enumerable() {
    // #622: `Enumerable#select` (and `filter`, `reject`, `find_all`)
    // returns `Enumerable[T]`: through `Enumerable` the result may be a
    // `Set` (whose `select` returns a `Set`), so array methods on it are
    // refused.
    let out = common::diagnostics(
        "def firsts(e: Enumerable[Int]) -> Int\n  a = e.select { |x| x > 0 }\n  a[0]\nend\nputs firsts(Set[3, 1, 2])\n",
    )
    .join("\n");
    assert!(
        out.contains("3:3: error: undefined method `[]` for Enumerable[Int]"),
        "{out}"
    );
    assert_eq!(out.matches("error:").count(), 1, "{out}");
}

#[test]
fn a_hashs_include_tests_a_pair() {
    // #622: `include?`/`member?` on a `Hash` or `Hash::Builder` test
    // whether a pair is an element; an argument that cannot be a pair is
    // refused, pointing at `key?`.
    let refused = [
        ("h = {\"a\" => 1}\np h.include?(\"a\")\n", "2:3"),
        ("h = {\"a\" => 1}\np h.member?(\"a\")\n", "2:3"),
        ("h = {\"a\" => 1}\np h.include?(value: \"a\")\n", "2:3"),
        (
            "b = Hash::Builder[String, Int].new\np b.include?(\"a\")\n",
            "2:3",
        ),
        (
            "def f(h: Hash[Symbol, Int], k: Symbol) -> Bool = h.include?(k)\n",
            "1:50",
        ),
    ];
    for (src, at) in refused {
        let out = common::diagnostics(src).join("\n");
        assert!(
            out.contains(&format!(
                "{at}: error: a Hash's `{}` tests whether a pair is an element; use `key?` for a key",
                if src.contains("member?") { "member?" } else { "include?" }
            )),
            "{src}\n{out}"
        );
        assert_eq!(out.matches("error:").count(), 1, "{src}\n{out}");
    }
    // A pair, or anything that may be one, is accepted.
    let accepted = [
        "h = {\"a\" => 1}\np h.include?([\"a\", 1])\n",
        "h = {\"a\" => 1}\no: Object = [\"a\", 1]\np h.include?(o)\n",
        "def f[X](h: Hash[String, Int], x: X) -> Bool = h.include?(x)\n",
        "def f(h: Hash[String, Int], x: [String, Int] | String) -> Bool = h.include?(x)\n",
        "h = {\"a\" => 1}\np h.key?(\"a\"), h.has_key?(\"a\")\n",
    ];
    for src in accepted {
        let out = common::diagnostics(src).join("\n");
        assert!(!out.contains("error:"), "{src}\n{out}");
    }
}

#[test]
fn an_extension_completes_the_conformance_it_makes() {
    // R0 (the user's rule on #555, 2026-11-13): an extension that includes
    // a module implements each of its abstract methods where it is
    // declared, from the extension's own methods, the modules its includes
    // bring, or the target's own side (own methods, own includes,
    // superclasses; an `abstract def` there counts); otherwise an error at
    // the extension, whatever its bounds.
    let named = "module Named\n  abstract def label -> String\nend\n";
    let msg = "this extension includes `Named` but nothing here implements `label`";
    let refused = [
        // #600: nothing implements it.
        format!("{named}class B\n  def initialize; end\nend\nmodule Sc\n  extension B\n    include Named\n  end\nend\n"),
        // Only another extension's module gives it (#522's witness part).
        format!("{named}module Giver\n  def label -> String = \"g\"\nend\nclass B\n  def initialize; end\nend\nmodule S1\n  extension B\n    include Named\n  end\nend\nmodule S2\n  extension B\n    include Giver\n  end\nend\n"),
        // An `abstract def` on the target of another signature only.
        format!("{named}abstract class B\n  abstract def label(x: Int) -> String\nend\nclass C < B\n  def initialize; end\n  def label(x: Int) -> String = \"c\"\nend\nextension B\n  include Named\nend\n"),
        // Only an overload of another parameter type.
        "module M\n  abstract def m(x: String) -> String\nend\nmodule N\n  def m(x: Int) -> String = \"n\"\nend\nclass B\n  def initialize; end\nend\nextension B\n  include M\n  include N\nend\n".to_string(),
    ];
    for src in &refused {
        let out = common::diagnostics(src).join("\n");
        let want = if src.contains("module M\n") {
            "nothing here implements `m`"
        } else {
            msg
        };
        assert!(out.contains(want), "{src}\n{out}");
    }
    // #555: a conditional extension too, whatever its bound.
    let out = common::diagnostics(
        "module EM\n  abstract def m(x: Int) -> String\nend\nabstract class Box[T]\n  def initialize; end\nend\nextension Box[T <: Int]\n  include EM\nend\nclass Sub[U] < Box[U]\n  def initialize; end\nend\n",
    )
    .join("\n");
    assert!(
        out.contains("this extension includes `EM` but nothing here implements `m`"),
        "{out}"
    );
    let accepted = [
        // (1) The extension's own method, written after its `include` (the
        // check runs once the extension's body is declared).
        format!("{named}class B\n  def initialize; end\nend\nmodule Sc\n  extension B\n    include Named\n    def label -> String = \"e\"\n  end\nend\n"),
        // (2) A module the same extension includes.
        format!("{named}module Giver\n  def label -> String = \"g\"\nend\nclass B\n  def initialize; end\nend\nextension B\n  include Named\n  include Giver\nend\n"),
        // (3) The target's own method, own include, and an `abstract def`
        // of the target (its concrete subclass implements it).
        format!("{named}class B\n  def initialize; end\n  def label -> String = \"b\"\nend\nextension B\n  include Named\nend\n"),
        format!("{named}module Giver\n  def label -> String = \"g\"\nend\nclass B\n  include Giver\n  def initialize; end\nend\nextension B\n  include Named\nend\n"),
        format!("{named}abstract class B\n  abstract def label -> String\nend\nclass C < B\n  def initialize; end\n  def label -> String = \"c\"\nend\nextension B\n  include Named\nend\n"),
        // (3) A method the target inherits from a superclass: accepted by
        // the rule; under a scoped extension the run time does not find it
        // yet (#632).
        format!("{named}class A\n  def initialize; end\n  def label -> String = \"a\"\nend\nclass B < A\n  def initialize; end\nend\nmodule Sc\n  extension B\n    include Named\n  end\nend\n"),
    ];
    for src in &accepted {
        let out = common::diagnostics(src).join("\n");
        assert!(!out.contains("error:"), "{src}\n{out}");
    }
}

#[test]
fn an_own_includes_requirement_is_implemented_on_the_class_side() {
    // Rule A (the user's decision, 2026-11-13): an abstract method of a
    // module a class includes itself is implemented by the class's own
    // methods, own includes or superclasses; an extension's method is not
    // its implementation (#605, #607, #608).
    let named = "module Named\n  abstract def label -> String\nend\n";
    let refused = [
        // A top-level extension's method.
        format!("{named}class B\n  include Named\n  def initialize; end\nend\nextension B\n  def label -> String = \"e\"\nend\n"),
        // A conditional extension's method (#607).
        format!("{named}class K[T]\n  include Named\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension K[T <: Int]\n  def label -> String = \"int#{{v + 1}}\"\nend\n"),
        // An extension of a superclass (#608).
        "module M\n  abstract def get -> Int\nend\nclass Base[T]\n  @v: T\n  def initialize(@v: T); end\n  def v -> T = @v\nend\nextension Base[T]\n  def get -> T = v\nend\nclass A < Base[Int]\n  include M\n  def initialize; super(1); end\nend\n".to_string(),
    ];
    for src in &refused {
        let out = common::diagnostics(src).join("\n");
        assert!(out.contains("itself, so `"), "{src}\n{out}");
        assert!(out.contains("is implemented in `"), "{src}\n{out}");
    }
    // A scoped extension's method is no implementation either: the class
    // must implement it (the contract's own error).
    let out = common::diagnostics(&format!(
        "{named}class B\n  include Named\n  def initialize; end\nend\nmodule Sc\n  extension B\n    def label -> String = \"e\"\n  end\nend\n"
    ))
    .join("\n");
    assert!(out.contains("`B` must implement `label`"), "{out}");
    let accepted = [
        // The class's own method, an own include's, a superclass's.
        format!("{named}class B\n  include Named\n  def initialize; end\n  def label -> String = \"b\"\nend\n"),
        format!("{named}module Giver\n  def label -> String = \"g\"\nend\nclass B\n  include Named\n  include Giver\n  def initialize; end\nend\n"),
        format!("{named}class A\n  def label -> String = \"a\"\nend\nclass B < A\n  include Named\n  def initialize; end\nend\n"),
        // An extension that includes the module itself implements it (R0).
        format!("{named}class B\n  def initialize; end\nend\nextension B\n  include Named\n  def label -> String = \"e\"\nend\n"),
    ];
    for src in &accepted {
        let out = common::diagnostics(src).join("\n");
        assert!(!out.contains("error:"), "{src}\n{out}");
    }
}
