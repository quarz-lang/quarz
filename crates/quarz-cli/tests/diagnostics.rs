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
    assert_eq!(out.matches("error:").count(), 2, "{out}");
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
    assert_eq!(out.matches("error:").count(), 2, "{out}");
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
    // argument sets. (A witness of another type is said twice, by the
    // class side's override check and at the extension: a follow-up.)
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
