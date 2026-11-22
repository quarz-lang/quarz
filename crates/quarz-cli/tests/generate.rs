//! Members generated at compile time by class bodies' `static` statements
//! (`Meta::ClassDef#def_method`, docs/14 §5): through the `quarz` command.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

struct Dir(PathBuf);

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn dir() -> Dir {
    static N: AtomicU32 = AtomicU32::new(0);
    let d = std::env::temp_dir().join(format!(
        "quarz-generate-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    Dir(d)
}

fn write(dir: &Path, name: &str, text: &str) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, text).unwrap();
    p
}

/// `quarz ARGS` in `dir`: exit status, stdout, stderr (paths in the
/// output made relative to `dir`).
fn quarz(dir: &Path, args: &[&str], env: &[(&str, &str)]) -> (bool, String, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_quarz"));
    cmd.args(args).current_dir(dir).env("QUARZ_THREADS", "1");
    for (k, v) in env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("quarz");
    let prefix = format!("{}/", dir.display());
    let clean = |b: &[u8]| String::from_utf8_lossy(b).replace(&prefix, "");
    (out.status.success(), clean(&out.stdout), clean(&out.stderr))
}

const LIB: &str = r##"abstract class Model
  @id: Int
  def initialize(@id: Int); end
  def id -> Int = @id
  abstract def self.table_name -> String
  static def self.has_many[T <: Model](target: Type[T], fk: Symbol) -> Void
    f = target.field(:id)
    raise "no id" unless f
    names = ["a", "b"]
    table = target.table_name
    doc "many #{target.name}"
    def_method("#{target.name.downcase}_class".to_sym) { target }
    def_method(:same) { self }
    def_method(:info) { "#{f.name}:#{f.mutable}:#{names.map { |s| s + id.to_s }.join(",")}:#{table}" }
    def_method(:pair, [:x, :y]) { |x: Int, y: String| "#{x}#{y}#{fk}" }
    def_method(:hidden, visibility: :private) { 42 }
    def_class_method(:fk_name) { fk.to_s }
  end
end
"##;

const APP: &str = r##"require_relative "lib"
class Comment < Model
  def self.table_name -> String = "comments"
end
class Post < Model
  def self.table_name -> String
    return "posts"
    "never"
  end
  has_many Comment, :post_id
end
post = Post.new(7)
puts post.comment_class.name
puts post.same.id
puts post.info
puts post.pair(1, "z")
puts Post.fk_name
"##;

const EXPECTED: &str = "Comment\n7\nid:false:a7,b7:comments\n1zpost_id\npost_id\n";

#[test]
fn generated_methods_run_the_same_interpreted_and_compiled() {
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    let app = write(&d.0, "app.qz", APP);
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    // Cold, then warm: the same result and the same diagnostics (the
    // warning in `Post.table_name`, which `has_many` reaches, once).
    let cold = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    assert_eq!(
        cold.2.matches("warning: unreachable code").count(),
        1,
        "{}",
        cold.2
    );
    let warm = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, EXPECTED);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), EXPECTED);
    // A change of what the dependency generates reaches the cached file.
    write(
        &d.0,
        "lib.qz",
        &LIB.replace("def_method(:info)", "def_method(:info2)"),
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(!ok);
    assert!(err.contains("undefined method `info` for Post"), "{err}");
    // The tree marks generated methods, without a body.
    write(&d.0, "lib.qz", LIB);
    let (ok, out, _) = quarz(&d.0, &["check", "--tree", app.to_str().unwrap()], &env);
    assert!(ok);
    assert!(out.contains(r#""name":"info","native":false"#), "{out}");
    assert!(out.contains(r#""generated":true"#), "{out}");
    // `quarz doc` runs the statements too.
    let (ok, _, err) = quarz(&d.0, &["doc", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
}

/// #810: a `==` and `hash` that `def_method` generates are the type's own,
/// as written ones are (docs/03 §6): hash keys and set members compare and
/// hash by them, and so does a `data` holder's field holding the type by
/// reference (`D` has a `String` field, so no field holds it in place).
/// Cells: `Set` members, `Hash` keys (lookup and insertion), a `data`
/// holder's `==` and `hash`, an array's `include?` (which always asked
/// the element's `==`); interpreted and compiled.
#[test]
fn generated_eq_and_hash_are_the_keys_own() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"module ByX
  abstract def x -> Int
  static def self.by_x -> Void
    def_method(:==, :other) do |other: Object|
      case other
      in D => o then o.x == x
      else false
      end
    end
    def_method(:hash) { x.hash }
  end
end
data D(x: Int, s: String)
  include ByX
end
module Go
  static def self.go -> Void
    D.by_x
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        r##"require_relative "lib"

class Gen
  include Go
  go
end

data E = (d: D, n: Int)

a = D.new(1, "a")
b = D.new(1, "b")
c = D.new(2, "a")
puts a == b
puts a == c
puts Set[a, b, c].size
h = {a => "first"}
puts h[b]
puts h.put(b, "second").size
puts E.new(a, 3) == E.new(b, 3)
puts E.new(a, 3) == E.new(c, 3)
puts Set[E.new(a, 3), E.new(b, 3)].size
puts [a].include?(b)
"##,
    );
    let expected = "true\nfalse\n2\nfirst\n1\ntrue\nfalse\n1\ntrue\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
}

#[test]
fn what_a_lifted_block_cannot_do() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Plain
  @n: Int
  def initialize(@n: Int); end
end
abstract class Model
  @id: Int
  def initialize(@id: Int); end
  def id -> Int = @id
  def self.tag -> String = "t"
  static def self.count_fields -> Int = fields.size
  static def self.bad_assign(name: Symbol) -> Void
    n = 1
    def_method(name) { n = 2; n }
  end
  static def self.bad_return(name: Symbol) -> Void
    def_method(name) { return 1 }
  end
  static def self.bad_outer(name: Symbol) -> Void
    def_method(name) { fields.size }
  end
  static def self.bad_self(name: Symbol) -> Void
    def_method(name) { tag }
  end
  static def self.bad_proc(name: Symbol) -> Void
    f = ->(x: Int) -> Int { x + 1 }
    def_method(name) { f.call(1) }
  end
  static def self.bad_break(name: Symbol) -> Void
    def_method(name) { break }
  end
  static def self.bad_object(name: Symbol) -> Void
    o: Object = Plain.new(1)
    def_method(name) { o.to_s }
  end
  static def self.bad_static(name: Symbol) -> Void
    def_method(name) { Model.count_fields }
  end
  static def self.twice(name: Symbol) -> Void
    def_method(name) { 1 }
    def_method(name) { 2 }
  end
  static def self.helper[U <: Model](name: Symbol, t: Type[U], u: U?) -> Void
    def_method(name) { t }
  end
  static def self.free_param(target: Type[Model]) -> Void
    helper(:via_helper, target, nil)
  end
  static def self.private_one -> Void
    def_method(:secret, visibility: :private) { 1 }
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Model\n  bad_assign :a\n  bad_return :b\n  bad_outer :c\n  bad_self :d\n  bad_proc :e\n  bad_break :f\n  bad_object :g\n  bad_static :s\n  twice :h\n  free_param Model\n  private_one\nend\nputs A.new(1).secret\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    for expected in [
        "cannot assign to `n` from a block given to `def_method`",
        "`return` in a block given to `def_method`",
        "`fields` is a method of the enclosing `self`, which a block given to `def_method` cannot use",
        "`tag` is a method of the enclosing `self`",
        "`f` has type (Int) -> Int, whose values cannot be baked into a generated method",
        "`break` in a block given to `def_method`",
        "`o` has type Plain, whose values cannot be baked",
        "app.qz:11:3: error: `def_method(:h)`: `A` already has a method `h` (generated by an earlier `static` statement)",
        "app.qz:12:3: error: `def_method(:via_helper)`: the block's type mentions `U`, a type parameter the generated method cannot carry",
        "app.qz:15:6: error: `secret` is private",
    ] {
        assert!(err.contains(expected), "missing {expected:?} in\n{err}");
    }
    // A lifted block is run-time code: a compile-time-only `static def`
    // it calls is reported once the program is lowered.
    write(
        &d.0,
        "lib2.qz",
        "class Model\n  static def self.count_fields -> Int = fields.size\n  static def self.bad_static(name: Symbol) -> Void\n    def_method(name) { Model.count_fields }\n  end\nend\n",
    );
    let app2 = write(
        &d.0,
        "app2.qz",
        "require_relative \"lib2\"\nclass B < Model\n  bad_static :s\nend\nputs B.new.s\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app2.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("lib2.qz:4:24: error: `count_fields` runs at compile time only"),
        "{err}"
    );
}

/// `...` in a block given to `def_method` forwards the block's
/// parameters, which become the generated method's (docs/14 §5; #511):
/// the variables themselves (one reassigned, one hidden in a block
/// inside), interpreted and compiled; in a block given to
/// `def_initialize`, `super(...)` passes them to the bound's
/// `initialize`. With `keywords:` what the method takes is known only
/// when the statement runs: an error.
#[test]
fn forwarding_in_a_generated_method() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Base
  @a: Int
  @b: Int
  def initialize(@a: Int, @b: Int)
  end
  def both(x: Int, y: Int) -> Int = x * 10 + y + @a
  def one(x: Int) -> Int = x * @b
  static def self.gen -> Void
    def_method(:f, params: [:x, :y]) do |x: Int, y: Int| -> Int
      x = 100
      both(...) + [1].map { |x| both(...) }.first.as(Int)
    end
    def_method(:g, param: :x) do |x: Int| -> Int
      one(...)
    end
    def_initialize(params: [:p, :q]) do |p: Int, q: Int|
      super(...)
    end
  end
  static def self.kw -> Void
    def_method(:h, keywords: [Meta::Keyword.new(:k, Int, true)]) do |opts|
      one(...)
    end
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass B < Base\n  gen\nend\nb = B.new(1, 2)\nputs b.f(3, 4)\nputs b.g(5)\n",
    );
    let expected = "2010\n10\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    let app2 = write(
        &d.0,
        "app2.qz",
        "require_relative \"lib\"\nclass C < Base\n  kw\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app2.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("lib.qz:21:11: error: `...` in a block given with `keywords:`: the generated method's keywords are known only when the statement runs; read them from the block's hash"),
        "{err}"
    );
}

#[test]
fn what_cannot_be_generated() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Model
  static def self.init -> Void
    def_method(:initialize) { 1 }
  end
  static def self.ctor -> Void
    def_class_method(:new) { 1 }
  end
  static def self.untyped(name: Symbol) -> Void
    def_method(name, :x) { |x| x }
  end
  static def self.splat(name: Symbol) -> Void
    def_method(name, :xs) { |*xs: Int| xs.size }
  end
  static def self.dup(name: Symbol) -> Void
    def_method(name, [:x, :x]) { |a: Int, b: Int| a + b }
  end
  static def self.big(name: Symbol) -> Void
    b: Integer = 12345678901234567890123
    bs = "ab".to_bytes
    def_method(name) { "#{b}:#{bs.size}" }
  end
  static def self.eq -> Void
    def_method(:==, :o) { |o: Int| o == 1 }
  end
  static def self.sealed -> Void
    def_method(:nil?) { true }
  end
  static def self.sealed_class -> Void
    def_class_method(:is_a?) { true }
  end
  static def self.sealed_new -> Void
    def_method(:class) { 1 }
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Model\n  init\n  ctor\n  untyped :u\n  dup :d\n  big :b\n  eq\n  sealed\nend\nclass B < Model\n  splat :s\nend\nclass C < Model\n  sealed_class\nend\nclass D < Model\n  sealed_new\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    for expected in [
        "app.qz:3:3: error: `def_method(:initialize)`: `initialize` cannot be generated",
        "app.qz:4:3: error: `def_class_method(:new)`: `new` cannot be generated",
        "app.qz:5:3: error: `def_method(:u)`: the block's parameter or result type could not be inferred",
        "app.qz:6:3: error: `def_method(:d)`: the parameter name `x` is given twice",
        "app.qz:8:3: error: `def_method(:==)`: `==` takes one parameter of type `Object`",
        "app.qz:9:3: error: `def_method(:nil?)`: `nil?` cannot be redefined: types are narrowed by it",
        // (A class method too, #948: it was let through before.)
        "app.qz:15:3: error: `def_class_method(:is_a?)`: `is_a?` cannot be redefined: types are narrowed by it",
        "app.qz:18:3: error: `def_method(:class)`: `class` cannot be redefined: it is the value's class, which the runtime knows",
        "a block given to `def_method` takes plain parameters only (no `*rest`, keywords, defaults or `&block`)",
    ] {
        assert!(err.contains(expected), "missing {expected:?} in\n{err}");
    }
    assert!(!err.contains("`b`") && !err.contains("`bs`"), "{err}");
    // Integer and Bytes captures bake.
    write(
        &d.0,
        "lib2.qz",
        "class Model\n  static def self.big(name: Symbol) -> Void\n    b: Integer = 12345678901234567890123\n    bs = \"ab\".to_bytes\n    def_method(name) { \"#{b}:#{bs.size}\" }\n  end\nend\n",
    );
    let app2 = write(
        &d.0,
        "app2.qz",
        "require_relative \"lib2\"\nclass C < Model\n  big :b\nend\nputs C.new.b\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app2.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "12345678901234567890123:2\n");
}

/// #812: the warning for a `==` without a `hash` (or the other way round)
/// counts what the statements generate, and is given once, after them,
/// for a class whose ancestors have statements: a subclass writing `==`
/// over a superclass's generated `hash` gets none, the superclass (`hash`
/// alone) one; a class writing `==` alone and generating something else
/// gets it once, not again when the statement generated into it. Such
/// classes (`World::conformance_deferred`) are warned by
/// `Declarer::recheck_conformance`, after their file's statements; a class
/// with no statements above it (`Plain`) when declared, once.
#[test]
fn the_eq_hash_warning_sees_generated_methods_once() {
    let d = dir();
    write(
        &d.0,
        "gen.qz",
        "module GenH\n  static def self.gen_hash -> Void\n    def_method(:hash) { 1 }\n  end\nend\nmodule GenFoo\n  static def self.gen_foo -> Void\n    def_method(:foo) { 1 }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"gen\"\nclass Base\n  include GenH\n  gen_hash\nend\nclass Sub < Base\n  def ==(other: Object) -> Bool = true\nend\nclass Own\n  include GenFoo\n  def ==(other: Object) -> Bool = true\n  gen_foo\nend\nclass Plain\n  def ==(other: Object) -> Bool = true\nend\nputs Set[Sub.new, Sub.new].size\nputs Own.new.foo\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    let warnings: Vec<&str> = err.lines().filter(|l| l.contains("warning:")).collect();
    assert_eq!(
        warnings,
        [
            "app.qz:15:3: warning: `Plain` defines `==` but not `hash`: as a Hash key or a Set member, equal values must hash the same",
            "app.qz:4:3: warning: `Base` defines `hash` but not `==`: as a Hash key or a Set member, equal values must hash the same",
            "app.qz:11:3: warning: `Own` defines `==` but not `hash`: as a Hash key or a Set member, equal values must hash the same",
        ],
        "{err}"
    );
}

/// #814: a class another file's statement generates into is checked at its
/// declaration and again after the generation (`recheck_classes`); its
/// warnings are given once, with the cache off, cold and warm.
#[test]
fn a_class_another_files_statement_generates_into_warns_once() {
    let d = dir();
    write(
        &d.0,
        "genfoo.qz",
        "module GenFoo\n  static def self.gen_foo -> Void\n    def_method(:foo) { 1 }\n  end\nend\n",
    );
    write(
        &d.0,
        "vlib.qz",
        "require_relative \"genfoo\"\nclass Victim\n  include GenFoo\n  def ==(other: Object) -> Bool = true\nend\nmodule Go\n  static def self.go -> Void\n    Victim.gen_foo\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"vlib\"\nclass Driver\n  include Go\n  go\nend\nputs Victim.new.foo\n",
    );
    let cache = d.0.join("cache");
    let cache = cache.to_str().unwrap();
    let want = ["vlib.qz:4:3: warning: `Victim` defines `==` but not `hash`: as a Hash key or a Set member, equal values must hash the same"];
    for env in [
        [("QUARZ_NO_CACHE", "1"), ("QUARZ_CACHE_DIR", cache)],
        [("QUARZ_NO_CACHE", ""), ("QUARZ_CACHE_DIR", cache)],
        [("QUARZ_NO_CACHE", ""), ("QUARZ_CACHE_DIR", cache)],
    ] {
        let env: Vec<(&str, &str)> = env.into_iter().filter(|(_, v)| !v.is_empty()).collect();
        let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
        assert!(ok, "{err}");
        assert_eq!(out, "1\n");
        let warnings: Vec<&str> = err.lines().filter(|l| l.contains("warning:")).collect();
        assert_eq!(warnings, want, "{env:?}: {err}");
    }
}

/// #796 (C): whether a field holds a `data` type in place is decided with
/// the declarations as written, and a generation that would change it is
/// refused at its statement, before it is declared, naming the field
/// whose type would get the method (docs/14 §5). Cells: #796's reproducer,
/// after a statement that lowered the holder's methods and without it; the holder a
/// class, a `data` type holding it (`E`, inside `H`), an enum variant, a
/// generic class, a superclass's field (named at it), a class of a later
/// file; the method `==`/`hash` or `!=`, into the type, into a module it
/// includes or one an unconditional extension includes into it; the
/// module the type includes after (or before) a module requiring `==`,
/// whose abstract `==` the generated one then implements; the
/// generation by a statement or by a class-end hook (reported at the
/// statement that registered it); after a statement whose generated body
/// builds a holder (`make`), whose hook captured one, or whose
/// `def_field` baked one (#796's survivors (a), (b), (c)).
#[test]
fn a_generation_that_would_change_a_layout_is_refused() {
    const COMMON: &str = r##"module GenEq
  static def self.gen_eq -> Void
    def_method(:==, :other) { |other: Object| true }
    def_method(:hash) { 42 }
  end
end
module GenNe
  static def self.gen_ne -> Void
    def_method(:!=, :other) { |other: Object| false }
  end
end
"##;
    let cases: [(&str, &str, &str, &str, &str); 17] = [
        (
            "req_then_m",
            r##"module Req
  abstract def ==(other: Object) -> Bool
end
module M
  include GenEq
end
data D(x: Int)
  include Req
  include M
end
data E = (d: D, n: Int)
module Go
  static def self.go -> Void
    M.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
puts E.new(D.new(1), 3) == E.new(D.new(2), 3)
puts E.new(D.new(1), 3).d.x
"##,
            "app.qz:4:3: error: ",
            "`D`, which gets the methods of `M`, is stored in place in the field `@d` of `E`",
        ),
        (
            "m_then_req",
            r##"module Req
  abstract def ==(other: Object) -> Bool
end
module M
  include GenEq
end
data D(x: Int)
  include M
  include Req
end
data E = (d: D, n: Int)
module Go
  static def self.go -> Void
    M.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
puts E.new(D.new(1), 3) == E.new(D.new(2), 3)
puts E.new(D.new(1), 3).d.x
"##,
            "app.qz:4:3: error: ",
            "`D`, which gets the methods of `M`, is stored in place in the field `@d` of `E`",
        ),
        (
            "ext_m",
            r##"module Req
  abstract def ==(other: Object) -> Bool
end
module M
  include GenEq
end
data D(x: Int)
  include Req
end
extension D
  include M
end
data E = (d: D, n: Int)
module Go
  static def self.go -> Void
    M.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
puts E.new(D.new(1), 3) == E.new(D.new(2), 3)
puts E.new(D.new(1), 3).d.x
"##,
            "app.qz:4:3: error: ",
            "`D`, which gets the methods of `M`, is stored in place in the field `@d` of `E`",
        ),
        (
            "reproducer",
            r##"data D(x: Int, y: Int)
  include GenEq
end
class H
  @d: D
  @n: Int
  def initialize(@d: D, @n: Int)
  end
  def d -> D = @d
  def n -> Int = @n
end
module Warm
  static def self.warm -> Void
    h = H.new(D.new(3, 30), 4)
    raise "warm" unless h.d.x == 3 && h.n == 4
  end
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class W
  include Warm
  warm
end
class C
  include Go
  go
end
h = H.new(D.new(5, 50), 6)
puts h.d.x, h.d.y, h.n, h.d == D.new(9, 90)
"##,
            "app.qz:8:3: error: ",
            "`def_method(:==)`: `D` is stored in place in the field `@d` of `H`, and a type stored in place compares by its fields: a `static` statement cannot give it `==`, `!=` or `hash` (write the method in `D`'s body)",
        ),
        (
            "reproducer_cold",
            r##"data D(x: Int, y: Int)
  include GenEq
end
class H
  @d: D
  @n: Int
  def initialize(@d: D, @n: Int)
  end
  def d -> D = @d
  def n -> Int = @n
end
module Warm
  static def self.warm -> Void
    h = H.new(D.new(3, 30), 4)
    raise "warm" unless h.d.x == 3 && h.n == 4
  end
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
h = H.new(D.new(5, 50), 6)
puts h.d.x, h.d.y, h.n, h.d == D.new(9, 90)
"##,
            "app.qz:4:3: error: ",
            "`def_method(:==)`: `D` is stored in place in the field `@d` of `H`, and a type stored in place compares by its fields: a `static` statement cannot give it `==`, `!=` or `hash` (write the method in `D`'s body)",
        ),
        (
            "nested",
            r##"data D(x: Int)
  include GenEq
end
data E = (d: D, n: Int)
class H
  @e: E
  def initialize(@e: E); end
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
"##,
            "app.qz:4:3: error: ",
            "`def_method(:==)`: `D` is stored in place in the field `@d` of `E`",
        ),
        (
            "later_file",
            r##"data D(x: Int)
  include GenEq
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
class Late
  @d: D
  def initialize(@d: D); end
end
"##,
            "app.qz:4:3: error: ",
            "`D` is stored in place in the field `@d` of `Late`",
        ),
        (
            "enum",
            r##"data D(x: Int)
  include GenEq
end
enum S
  variant Dot(p: D)
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
"##,
            "app.qz:4:3: error: ",
            "`D` is stored in place in the field `@p` of `S::Dot`",
        ),
        (
            "generic",
            r##"data D(x: Int)
  include GenEq
end
class G[T]
  @d: D
  @t: T
  def initialize(@d: D, @t: T); end
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
"##,
            "app.qz:4:3: error: ",
            "`D` is stored in place in the field `@d` of `G`",
        ),
        (
            "inherit",
            r##"data D(x: Int)
  include GenEq
end
class Base
  @d: D
  def initialize(@d: D); end
end
class Sub < Base
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
"##,
            "app.qz:4:3: error: ",
            "`D` is stored in place in the field `@d` of `Base`",
        ),
        (
            "module",
            r##"module M
  include GenEq
end
data D(x: Int)
  include M
end
data E = (d: D, n: Int)
module Go
  static def self.go -> Void
    M.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
"##,
            "app.qz:4:3: error: ",
            "`D`, which gets the methods of `M`, is stored in place in the field `@d` of `E`, and a type stored in place compares by its fields: a `static` statement cannot give it `==`, `!=` or `hash` through `M` (write the method in `M`'s body)",
        ),
        (
            "ext_module",
            r##"module M
  include GenEq
end
data D = (x: Int)
extension D
  include M
end
data E = (d: D, n: Int)
module Go
  static def self.go -> Void
    M.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
"##,
            "app.qz:4:3: error: ",
            "`D`, which gets the methods of `M`, is stored in place in the field `@d` of `E`",
        ),
        (
            "ne",
            r##"data D(x: Int)
  include GenNe
end
data E = (d: D, n: Int)
module Go
  static def self.go -> Void
    D.gen_ne
  end
end
"##,
            r##"require_relative "lib"
class C
  include Go
  go
end
"##,
            "app.qz:4:3: error: ",
            "`def_method(:!=)`: `D` is stored in place in the field `@d` of `E`",
        ),
        (
            "survivor_a",
            r##"data D(x: Int, y: Int)
  include GenEq
end
data E = (d: D, n: Int)
module Mk
  static def self.make_it -> Void
    def_method(:make) do -> E
      E.new(D.new(1, 2), 3)
    end
  end
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class R
  include Mk
  include Go
  make_it
  go
end
puts R.new.make.d.y
"##,
            "app.qz:6:3: error: ",
            "`D` is stored in place in the field `@d` of `E`",
        ),
        (
            "survivor_b",
            r##"data D(x: Int, y: Int)
  include GenEq
end
data E = (d: D, n: Int)
module Hk
  static def self.hook_it -> Void
    e = E.new(D.new(1, 2), 3)
    at_class_end(:k) { |cls| puts "hook: #{e.d.x} #{e.d.y} #{e.n}" }
  end
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class R
  include Hk
  include Go
  hook_it
  go
end
"##,
            "app.qz:6:3: error: ",
            "`D` is stored in place in the field `@d` of `E`",
        ),
        (
            "survivor_c",
            r##"data D(x: Int, y: Int)
  include GenEq
end
data E = (d: D, n: Int)
module Fd
  static def self.field_it -> Void
    def_field(:e, E, E.new(D.new(1, 2), 3), reader: true)
  end
end
module Go
  static def self.go -> Void
    D.gen_eq
  end
end
"##,
            r##"require_relative "lib"
class R
  include Fd
  include Go
  field_it
  go
end
puts R.new.e.d.y
"##,
            "app.qz:6:3: error: ",
            "`D` is stored in place in the field `@d` of `E`",
        ),
        (
            "hook_gen",
            r##"data D(x: Int)
  include GenEq
end
data E = (d: D, n: Int)
module Hg
  static def self.later -> Void
    at_class_end(:k) { |cls| D.gen_eq }
  end
end
"##,
            r##"require_relative "lib"
class R
  include Hg
  later
end
"##,
            "app.qz:4:3: error: ",
            "the class-end hook `:k` (registered by `later`): `def_method(:==)`: `D` is stored in place in the field `@d` of `E`",
        ),
    ];
    for (name, lib, app, at, message) in cases {
        let d = dir();
        write(&d.0, "lib.qz", &format!("{COMMON}{lib}"));
        let app = write(&d.0, "app.qz", app);
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{name}: {err}");
        let line = err
            .lines()
            .find(|l| l.starts_with(at))
            .unwrap_or_else(|| panic!("{name}: no error at {at}: {err}"));
        assert!(line.contains(message), "{name}: {err}");
    }
}

/// `def_field` generates into a class only, which a holder keeps by
/// reference: one into a `data` type (by another class's statement: a
/// `data` body takes none), which a holder may hold in place, is refused at
/// the statement. That is what lets a debug build's
/// per-statement layout check (#818) except only the field's class and its
/// subclasses.
#[test]
fn a_field_is_generated_into_a_class_only() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "module AddField\n  static def self.add_field -> Void\n    def_field(:extra, Int, 0)\n  end\nend\ndata D(x: Int)\n  include AddField\nend\nmodule Go\n  static def self.go -> Void\n    D.add_field\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\ndata H = (d: D, n: Int)\nclass Driver\n  include Go\n  go\nend\np H.new(D.new(1), 2)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok, "{err}");
    assert!(
        err.contains("`D` is not a class: fields are generated into classes only"),
        "{err}"
    );
}

/// An `initialize` is generated into a class only: neither `def_initialize`
/// nor `def_method(:initialize)` reaches a `data` type, whose `with` builds
/// through the body's own `initialize` (`World::with_initialize`,
/// `RtClass::with_init`). So what `with` runs is fixed before the
/// statements run, and the kept tables need no edge for it (#536 step 6).
#[test]
fn an_initialize_is_generated_into_a_class_only() {
    for (gen, want) in [
        (
            "def_initialize(:x) do |x: Int|\n      @x = x * 10\n    end",
            "`def_initialize`: `D` is not a class: `initialize` is generated into classes only",
        ),
        (
            "def_method(:initialize, :x) do |x: Int|\n      nil\n    end",
            "`def_method(:initialize)`: `initialize` cannot be generated: `def_initialize` generates its overloads",
        ),
    ] {
        let d = dir();
        write(
            &d.0,
            "lib.qz",
            &format!("data D(x: Int)\n  static def self.gen_init -> Void\n    {gen}\n  end\nend\nmodule Go\n  static def self.go -> Void\n    D.gen_init\n  end\nend\n"),
        );
        let app = write(
            &d.0,
            "app.qz",
            "require_relative \"lib\"\nclass Driver\n  include Go\n  go\nend\np D.new(1).with(x: 2).x\n",
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{err}");
        assert!(err.contains(want), "{err}");
    }
}

/// #796 (C): a generation into a `data` type no field holds in place is
/// accepted, and the type is compared by the generated `==` and `hash`
/// everywhere, a holder's fields included (each holding it by reference).
/// Cells: no holder; a nilable field (`D?`); a generic `data` type's
/// parameter (`P[D]`); interpreted and compiled.
#[test]
fn a_generation_into_a_type_held_by_reference_is_accepted() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "module GenEq\n  static def self.gen_eq -> Void\n    def_method(:==, :other) { |other: Object| true }\n    def_method(:hash) { 42 }\n  end\nend\ndata D(x: Int)\n  include GenEq\nend\ndata Q = (d: D?, n: Int)\ndata P[T] = (v: T, n: Int)\nmodule Go\n  static def self.go -> Void\n    D.gen_eq\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass C\n  include Go\n  go\nend\nputs D.new(1) == D.new(2)\nputs Set[D.new(1), D.new(2)].size\nputs Q.new(D.new(1), 3) == Q.new(D.new(2), 3)\nputs Set[Q.new(D.new(1), 3), Q.new(D.new(2), 3)].size\nputs P[D].new(D.new(1), 3) == P[D].new(D.new(2), 3)\nputs Set[P[D].new(D.new(1), 3), P[D].new(D.new(2), 3)].size\n",
    );
    let expected = "true\n1\ntrue\n1\ntrue\n1\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
}

#[test]
fn generated_fields_and_abstract_implementations() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"abstract class Model
  @id: Int
  def initialize(@id: Int); end
  def id -> Int = @id
  abstract def label -> String
  abstract def self.describe -> String
  static def self.counted(name: Symbol, start: Int) -> Void
    def_field(name, Int, start, var: true, reader: true, writer: true)
    def_field("#{name}_tag".to_sym, String, "t", reader: true)
    def_field(:seen, Bool, false)
  end
  static def self.labelled(text: String) -> Void
    def_method(:label) { text }
  end
  static def self.touch(target: Type[Model]) -> Void
    puts target.describe
  end
end
"##,
    );
    // `touch Special` reaches `Special.describe` and `Special#more`
    // (checked and lowered at compile time with `@extra` third), then
    // `counted` adds fields to `Post`, which moves `@extra`: what comes
    // after sees the new layout. `Post#initialize` assigns the generated
    // field (a method the runtime names, checked after the statements).
    let app = write(
        &d.0,
        "app.qz",
        r##"require_relative "lib"
class Post < Model
  @title: String
  def initialize(@id: Int, @title: String)
    @hits = 7
  end
  def show -> String = "#{@title}/#{@id}/#{@seen}/#{@hits}"
  def self.describe -> String = "post"
  labelled "post"
  touch Special
  counted :hits, 3
  touch Special
  touch Post
end
class Special < Post
  @extra: Int
  @bonus: Int = 70
  def initialize(@id: Int, @title: String, @extra: Int); end
  def more -> Int = @extra + @bonus
  def self.describe -> String = "special #{Special.new(1, "t", 9).more}"
end
s = Special.new(1, "t", 9)
puts s.show
puts s.more
puts Special.describe
puts s.label
puts s.hits
s.hits = 5
puts s.hits
puts s.hits_tag
puts Post.new(1, "t").hits
"##,
    );
    let expected = "t/1/false/3\n79\nspecial 79\npost\n3\n5\nt\n7\n";
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let cold = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    assert_eq!(cold.1, expected);
    // The compile-time output of the statements, in order.
    assert_eq!(cold.2, "special 79\nspecial 79\npost\n");
    let warm = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    // A class whose ancestor has statements is checked for what it must
    // implement after they ran; one still lacking a method is reported.
    let app2 = write(
        &d.0,
        "app2.qz",
        "require_relative \"lib\"\nclass Bare < Model\n  def self.describe -> String = \"bare\"\n  touch Bare\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app2.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("app2.qz:2:1: error: `Bare` must implement `label` (abstract in `Model`)"),
        "{err}"
    );
}

/// #801: a class including a module whose requirement its own `static`
/// statements generate (its conformance deferred past them, docs/14 §5):
/// the compile-time rounds before the generating statement run, and the
/// program gets the implementation; one that never comes, or comes with
/// another signature, is refused by the deferred check.
#[test]
fn a_deferred_conformance_gets_its_implementation_from_the_statements() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Gen\n  static def self.gen_area -> Void\n    def_method(:area) { 5 }\n  end\n  static def self.gen_other -> Void\n    def_method(:other) { 1 }\n  end\n  static def self.gen_area_arg -> Void\n    def_method(:area, :x) { |x: Int| x }\n  end\nend\n",
    );
    let app = |gen: &str| {
        format!(
            "require_relative \"lib\"\nmodule Sh\n  abstract def area -> Int\nend\nclass K < Gen\n  include Sh\n  {gen}\nend\ndef a(s: Sh) -> Int = s.area\nputs a(K.new)\n"
        )
    };
    let main = write(&d.0, "main.qz", &app("gen_area"));
    let (ok, out, err) = quarz(&d.0, &["run", main.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "5\n");
    // Never generated, or with another signature: the deferred check.
    for (gen, want) in [
        (
            "gen_other",
            "none.qz:5:1: error: `K` must implement `area` (abstract in `Sh`)",
        ),
        (
            "gen_area_arg",
            "none.qz:5:1: error: `K` must implement `area` (abstract in `Sh`)",
        ),
    ] {
        let none = write(&d.0, "none.qz", &app(gen));
        let (ok, _, err) = quarz(&d.0, &["check", none.to_str().unwrap()], &[]);
        assert!(!ok, "{gen}");
        assert!(err.contains(want), "{gen}: {err}");
        assert!(!err.contains("internal error"), "{gen}: {err}");
    }
}

/// #801: compile-time code that reaches a deferred conformance's
/// requirement before a statement generates it fails at its statement,
/// naming the class, the module and the method, whatever `QUARZ_VERIFY`
/// says (a class whose conformance is not deferred keeps the violation,
/// tests/verify.rs); on the instance side and on the class side.
#[test]
fn a_deferred_requirement_reached_before_it_is_generated() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "module Sh\n  abstract def area -> Int\nend\nmodule ShC\n  abstract def self.kind -> Int\nend\nmodule Use\n  def self.area_of(s: Sh) -> Int = s.area\n  def self.kind_of(t: Type[ShC]) -> Int = t.kind\nend\nabstract class Gen\n  include Sh\n  include ShC\n  static def self.use_it -> Void\n    puts Use.area_of(new)\n  end\n  static def self.use_cls -> Void\n    puts Use.kind_of(type)\n  end\n  static def self.gen -> Void\n    def_method(:area) { 5 }\n    def_class_method(:kind) { 7 }\n  end\nend\n",
    );
    for (stmt, method, module) in [("use_it", "area", "Sh"), ("use_cls", "kind", "ShC")] {
        let main = write(
            &d.0,
            "main.qz",
            &format!(
                "require_relative \"lib\"\nclass K < Gen\n  {stmt}\n  gen\nend\nputs K.new.area\n"
            ),
        );
        let want = format!(
            "main.qz:3:3: error: `{stmt}` raised RuntimeError: `{method}` of `K` is not implemented yet: `K`'s conformance to `{module}` waits for its class's `static` statements, and none has generated `{method}` so far (docs/14 §5)"
        );
        for verify in [None, Some("0"), Some("moves")] {
            let mut cmd = Command::new(env!("CARGO_BIN_EXE_quarz"));
            cmd.args(["check", main.to_str().unwrap()])
                .current_dir(&d.0)
                .env("QUARZ_THREADS", "1");
            match verify {
                Some(v) => cmd.env("QUARZ_VERIFY", v),
                None => cmd.env_remove("QUARZ_VERIFY"),
            };
            let out = cmd.output().expect("run quarz");
            let err = String::from_utf8_lossy(&out.stderr);
            assert_eq!(out.status.code(), Some(1), "{stmt} {verify:?}: {err}");
            assert!(err.contains(&want), "{stmt} {verify:?}: {err}");
        }
        // After the generation, the same call runs.
        let after = write(
            &d.0,
            "after.qz",
            &format!(
                "require_relative \"lib\"\nclass K < Gen\n  gen\n  {stmt}\nend\nputs K.new.area\n"
            ),
        );
        let (ok, out, err) = quarz(&d.0, &["run", after.to_str().unwrap()], &[]);
        assert!(ok, "{stmt}: {err}");
        assert_eq!(out, "5\n", "{stmt}");
        // (What the statement printed, at compile time, on stderr.)
        let printed = if stmt == "use_it" { "5" } else { "7" };
        assert!(err.lines().any(|l| l == printed), "{stmt}: {err}");
    }
}

#[test]
fn what_cannot_be_a_field_or_a_callee() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Model
  @id: Int
  def initialize(@id: Int); end
  static def self.generic -> Void
    def_field(:tags, Array, ["t"])
  end
  static def self.again -> Void
    def_field(:id, Int, 0)
  end
  static def self.writer_only -> Void
    def_field(:w, Int, 0, writer: true)
  end
  static def self.clash -> Void
    def_field(:id2, Int, 0, reader: true)
  end
end
data Point = (x: Int, y: Int)
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Model\n  def id2 -> Int = 1\n  generic\n  again\n  writer_only\n  clash\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    for expected in [
        "app.qz:4:3: error: `def_field(:tags)`: `Array` takes type arguments, which a `Type` value does not carry",
        "app.qz:5:3: error: `def_field(:id)`: `A` already has a field `@id`",
        "app.qz:6:3: error: `writer_only` raised ArgumentError: writer: needs var: true, an assignable field",
        "app.qz:7:3: error: `def_field(:id2)`: `A` already has a method `id2`",
    ] {
        assert!(err.contains(expected), "missing {expected:?} in\n{err}");
    }
    // A module's macro is a class method (#494).
    let app = write(
        &d.0,
        "mod.qz",
        "module Macros\n  static def has(x: Int) -> Void; end\nend\nclass B\n  include Macros\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("mod.qz:2:10: error: a module's macro is a class method, run on the class that includes the module: write `static def self.has`"),
        "{err}"
    );
}

#[test]
fn a_constant_made_before_a_generated_field_is_made_again() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "abstract class Model\n  include Shareable\n  @id: Int\n  def initialize(@id: Int); end\n  static def self.show(x: Int) -> Void = puts x\n  static def self.counted(name: Symbol, start: Int) -> Void\n    def_field(name, Int, start, reader: true)\n  end\nend\n",
    );
    // `K` holds a `Special` made with `@extra` second; after `counted`
    // adds `@hits` to `Post`, `@extra` is third.
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nK = Special.new(1, 9)\nclass Post < Model\n  show K.more\n  counted :hits, 3\n  show K.more\n  show K.hits\nend\nclass Special < Post\n  @extra: Int\n  def initialize(@id: Int, @extra: Int); end\n  def more -> Int = @extra\nend\nputs K.more\nputs K.hits\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(err, "9\n9\n3\n");
    assert_eq!(out, "9\n3\n");
}

/// #917 (b): a class's shareability cannot change during a `static`
/// phase, so a conditional extension bounded by `Shareable` applies to it
/// before a statement and after alike: a class that includes `Shareable`
/// gets no `var` field (refused at the statement), and a `data` type,
/// whose shareability is derived from its fields, gets no generated
/// field at all. A class that does not include `Shareable` is not one.
#[test]
fn a_generated_field_cannot_change_whether_a_class_is_shareable() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Box[T]\nend\nmodule Greet\n  def hi -> String = \"hi\"\nend\nextension Box[T <: Shareable]\n  include Greet\nend\nclass Holder\n  static def self.add -> Void\n    def_field(:n, Int, 0, var: true)\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass C < Holder\n  include Shareable\n  def before -> String = Box[C].new.hi\n  add\n  def after -> String = Box[C].new.hi\nend\np C.new.after\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains(
            "`C` must be Shareable, since it includes `Shareable`, but its field `@n` is `var`"
        ),
        "{err}"
    );
    let plain = write(
        &d.0,
        "plain.qz",
        "require_relative \"lib\"\nclass D < Holder\n  def before -> String = Box[D].new.hi\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", plain.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(err.contains("undefined method `hi` for Box[D]"), "{err}");
}

#[test]
fn a_pending_class_is_reached_through_calls_and_later_by_name() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  @id: Int\n  def initialize(@id: Int); end\n  def id -> Int = @id\n  def self.build(id: Int) -> Model = new(id)\n  static def self.showi(x: Int) -> Void = puts x\n  static def self.show(x: Object) -> Void = puts x\n  static def self.stringer(text: String) -> Void\n    def_method(:to_s) { text }\n  end\nend\n",
    );
    // `Post.build(1)`: `new` in an inherited class method reaches
    // `Post#initialize` by construction while Post's statements run;
    // Other's statement prints a Post with the `to_s` Post's statement
    // generated after the name was first reached.
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Post < Model\n  def initialize(@id: Int)\n    @id = @id * 10\n  end\n  showi Post.build(1).id\n  stringer \"a post\"\nend\nclass Other < Model\n  show Post.new(1)\nend\nputs Post.new(2)\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(err, "10\na post\n");
    assert_eq!(out, "a post\n");
    // A dispatch by name to a class whose statements have not run finds
    // no body, and says so.
    let app2 = write(
        &d.0,
        "app2.qz",
        "require_relative \"lib\"\nclass Post < Model\n  def to_s -> String = \"written\"\n  show Post.new(1)\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app2.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`to_s` of `Post` has no body at compile time"),
        "{err}"
    );
}

/// A method the statement running has generated has no body until the
/// class's statements have run, in that statement too (#967): a
/// dispatch it would have answered (by type, by name, the runtime's own
/// `to_s`, `==` and `hash`) is refused with the message a later
/// statement's call gets, not answered by the method it replaces. A
/// generated method that replaces nothing, or a receiver it is not a
/// method of, changes nothing.
#[test]
fn a_method_generated_by_the_running_statement_has_no_body_yet() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Base
  def describe -> String = "base"
  static def self.me -> Meta::ClassDef[Base] = self
  static def self.cls_to_s -> Void
    def_class_method(:to_s) { "generated" }
    k: Type = type
    puts "cls: #{k.to_s}"
  end
  static def self.inst_to_s(x: Object) -> Void
    def_method(:to_s) { "generated" }
    puts "inst: #{x}"
  end
  static def self.inst_eq(x: Object, y: Object) -> Void
    def_method(:==, :o) { |o: Object| true }
    puts "eq: #{[x].include?(y)}"
  end
  static def self.inst_hash(x: Object, y: Object) -> Void
    def_method(:hash) { 1 }
    h = {x => 1, y => 2}
    puts "hash: #{h.size}"
  end
  static def self.ordinary(x: Base) -> Void
    def_method(:describe) { "generated" }
    puts "ordinary: #{x.describe}"
  end
  static def self.fresh(x: Base) -> Void
    def_method(:brand_new) { "generated" }
    puts "fresh: #{x.describe}"
  end
  static def self.into_other(x: Base) -> Void
    Other.me.def_method(:describe) { "generated" }
    puts "other: #{x.describe}"
  end
  def kw(*, a: Int = 0) -> String = "base kw"
  static def self.field_over(x: Base) -> Void
    def_field(:describe, String, "field", reader: true)
    puts "field: #{x.describe}"
  end
  static def self.kw_over(x: Base) -> Void
    ks = [Meta::Keyword.new(:a, Int, false)]
    def_method(:kw, keywords: ks) { |given| "generated kw" }
    puts "kw: #{x.kw(a: 1)}"
  end
  static def self.texted -> Void
    def_method(:to_s) { "texted" }
  end
  static def self.keyed -> Void
    def_method(:==, :o) { |o: Object| true }
    def_method(:hash) { 1 }
  end
  static def self.gen_and_show(x: Object, y: Object) -> Void
    def_method(:to_s) { "mine" }
    puts "shown: #{x} #{{x => 1, y => 2}.size}"
  end
end
class Other < Base
end
"##,
    );
    let refused = |name: &str, class: &str| {
        format!(
            "raised Meta::CompileTimeError: `{name}` of `{class}` has no body at compile time: a method the runtime calls by name is lowered once the class's `static` statements ran, or when a call resolves to it (docs/14)"
        )
    };
    for (statement, after, want) in [
        // A class method over `Type`'s, called through a `Type`.
        ("cls_to_s", "", Err(refused("to_s", "Post"))),
        // The runtime's calls by name: an interpolation's `to_s`,
        // `Array#include?`'s `==`, a `Hash` key's `hash`.
        ("inst_to_s(Post.new)", "", Err(refused("to_s", "Post"))),
        (
            "inst_eq(Post.new, Post.new)",
            "",
            Err(refused("==", "Post")),
        ),
        (
            "inst_hash(Post.new, Post.new)",
            "",
            Err(refused("hash", "Post")),
        ),
        // A superclass's ordinary method, by type.
        ("ordinary(Post.new)", "", Err(refused("describe", "Post"))),
        // A subclass of the class generated into.
        (
            "inst_to_s(Sub.new)",
            "class Sub < Post
end
",
            Err(refused("to_s", "Post")),
        ),
        // Generated into another class, then dispatched on it; on this
        // one, nothing changes.
        (
            "into_other(Other.new)",
            "",
            Err(refused("describe", "Other")),
        ),
        ("into_other(Post.new)", "", Ok("other: base")),
        // A field's reader; a method of the keyword form.
        ("field_over(Post.new)", "", Err(refused("describe", "Post"))),
        ("kw_over(Post.new)", "", Err(refused("kw", "Post"))),
        // A method that replaces nothing; a receiver above the class.
        ("fresh(Post.new)", "", Ok("fresh: base")),
        ("inst_to_s(Base.new)", "", Ok("inst: #<Base>")),
        // Each run starts with an empty record: a later class's statement
        // that generates too gets Post's generated `to_s`, `==` and `hash`
        // (its `==` from the lowering's rows, no entry of an earlier run).
        (
            "texted\n  keyed",
            "class Later < Base\n  gen_and_show(Post.new, Post.new)\nend\n",
            Ok("shown: texted 1"),
        ),
    ] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass Post < Base\n  {statement}\nend\n{after}"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        match want {
            Ok(printed) => {
                assert!(ok, "{statement}: {err}");
                assert!(err.contains(printed), "{statement}: {err}");
            }
            Err(message) => {
                assert!(!ok, "{statement}");
                assert!(err.contains(&message), "{statement}: {err}");
                // (Not answered by the method it replaces first.)
                assert!(
                    !err.contains(": base") && !err.contains("#<"),
                    "{statement}: {err}"
                );
            }
        }
    }
}

const SHOWN_LIB: &str = r##"class Model
  static def self.props(*names: Symbol) -> Void
    names.each do |n|
      doc "Reads #{n}.\nGenerated."
      def_method(n) { n.to_s }
    end
    def_field(:count, Int, 0, var: true, reader: true, writer: true)
    def_field(:label, String, "a\"\#{b}\n", reader: true)
  end

  static def self.finder -> Void
    def_class_method(:find, visibility: :private) { "found" }
  end
end
"##;

const SHOWN_APP: &str = r##"require_relative "lib"

# A post.
class Post < Model
  # Not the generated methods' doc.
  props :title, :body
  finder
end

p Post.new.title
"##;

#[test]
fn expand_and_doc_show_what_was_generated() {
    let d = dir();
    write(&d.0, "lib.qz", SHOWN_LIB);
    write(&d.0, "app.qz", SHOWN_APP);
    let expected = r##"class Post  # app.qz:4
  # generated by `props :title, :body` at app.qz:6
  var @count: Int = 0
  @label: String = "a\"\#{b}\n"
  # Reads title.
  # Generated.
  def title -> String = <block at lib.qz:5>
  # Reads body.
  # Generated.
  def body -> String = <block at lib.qz:5>
  attr_reader :count
  attr_writer :count
  attr_reader :label

  # generated by `finder` at app.qz:7
  private def self.find -> String = <block at lib.qz:12>
end
"##;
    // The same on every check, with the cache and without (docs/14 §14.14:
    // generation follows declaration order).
    for env in [&[][..], &[("QUARZ_NO_CACHE", "1")][..], &[][..]] {
        let (ok, out, err) = quarz(&d.0, &["check", "--expand", "app.qz"], env);
        assert!(ok, "{err}");
        assert_eq!(out, expected);
    }
    // `quarz doc`: the `doc` given, not the statement's comment, and
    // where the member came from.
    let (ok, out, err) = quarz(&d.0, &["doc", "app.qz", "Post#title"], &[]);
    assert!(ok, "{err}");
    assert_eq!(
        out,
        "Post#title  def title -> String\n\n  Reads title.\n  Generated.\n\n  (generated by `props :title, :body` at app.qz:6)\n"
    );
    let (ok, out, err) = quarz(&d.0, &["doc", "app.qz", "Post#count="], &[]);
    assert!(ok, "{err}");
    assert_eq!(
        out,
        "Post#count=  def count=(value: Int) -> Int\n\n  (generated by `props :title, :body` at app.qz:6)\n"
    );
    let (ok, out, err) = quarz(&d.0, &["doc", "app.qz", "Post"], &[]);
    assert!(ok, "{err}");
    assert!(!out.contains("Not the generated"), "{out}");
    let order: Vec<usize> = ["def title", "def body", "def count ", "def count="]
        .iter()
        .map(|s| out.find(s).unwrap_or_else(|| panic!("{s} in {out}")))
        .collect();
    assert!(order.windows(2).all(|w| w[0] < w[1]), "{out}");
    // `:nodoc:` above a statement hides what it generates (docs/13 §5).
    write(
        &d.0,
        "hidden.qz",
        "require_relative \"lib\"\n# A post.\nclass Post < Model\n  # :nodoc:\n  props :secret\nend\n# A page.\nclass Page < Model\n  props :shown\nend\n",
    );
    let (ok, out, err) = quarz(&d.0, &["doc", "hidden.qz", "Post"], &[]);
    assert!(ok, "{err}");
    assert!(
        !out.contains("def secret") && !out.contains("def count"),
        "{out}"
    );
    let (ok, out, err) = quarz(&d.0, &["doc", "hidden.qz", "Page"], &[]);
    assert!(ok, "{err}");
    assert!(
        out.contains("def shown") && out.contains("def count"),
        "{out}"
    );
    let (ok, out, err) = quarz(&d.0, &["doc", "--private", "hidden.qz", "Post"], &[]);
    assert!(ok, "{err}");
    assert!(out.contains("def secret"), "{out}");
    // A program that generates nothing expands to nothing.
    write(&d.0, "plain.qz", "class A\nend\np A.new\n");
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", "plain.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "");
}

const VALUES_LIB: &str = r##"data Pt = (x: Int, y: Int)
data Outer = (s: String, p: Pt, n: Float)
data Cust(x: Int)
  def initialize(y: String)
    @x = y.size
  end
end
data Held(p: Pt, s: String)
  def initialize(n: Int)
    @p = Pt.new(n, n * 2)
    @s = "n#{n}"
  end
end

class Model
  static def self.values -> Void
    def_field(:o, Outer, Outer.new("a", Pt.new(1, 2), 3.0), reader: true)
    def_field(:c, Cust, Cust.new("abc"), reader: true)
    def_field(:r, Regexp, %r{a/b\/c}i, reader: true)
    h = Held.new(4)
    def_method(:h) { h }
  end

  static def self.named(n: Symbol) -> Void
    doc "Names [Post#nope_#{n}]."
    def_method(n) { n.to_s }
  end
end
"##;

const VALUES_APP: &str = r##"require_relative "lib"

class Base < Model
  # The statement's comment, no doc.
  named :title
  named :body
  values
end

class Post < Base
  def title -> String = "t"
end

p Post.new.o
p Post.new.c
p Post.new.r
p Post.new.h
"##;

#[test]
fn generated_values_and_docs_in_detail() {
    let d = dir();
    write(&d.0, "lib.qz", VALUES_LIB);
    write(&d.0, "app.qz", VALUES_APP);
    // A data value whose type has its own `initialize` is baked without
    // running it, its physical fields stored (a nested one held in place).
    let expected = "Outer(s: \"a\", p: Pt(x: 1, y: 2), n: 3.0)\nCust(x: 3)\n/a\\/b\\/c/i\nHeld(p: Pt(x: 4, y: 8), s: \"n4\")\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
    // A data value as `p` shows it, nested ones held in place included;
    // a regexp's `/` escaped.
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert!(
        out.contains("  @o: Outer = Outer(s: \"a\", p: Pt(x: 1, y: 2), n: 3.0)\n"),
        "{out}"
    );
    assert!(out.contains("  @c: Cust = Cust(x: 3)\n"), "{out}");
    assert!(out.contains("  @r: Regexp = /a\\/b\\/c/i\n"), "{out}");
    // An override inherits the generated method's `doc`, not the
    // statement's comment.
    let (ok, out, err) = quarz(&d.0, &["doc", "app.qz", "Post#title"], &[]);
    assert!(ok, "{err}");
    // (A bracket that names nothing shows as written.)
    assert!(out.contains("Names [Post#nope_title]."), "{out}");
    assert!(out.contains("(from Base)"), "{out}");
    assert!(!out.contains("statement's comment"), "{out}");
    // `--check` reads every generated doc, at its statement.
    let (_, out, err) = quarz(&d.0, &["doc", "app.qz", "--check"], &[]);
    let all = format!("{out}{err}");
    assert!(
        all.contains("app.qz:5: warning: `[Post#nope_title]`"),
        "{all}"
    );
    assert!(
        all.contains("app.qz:6: warning: `[Post#nope_body]`"),
        "{all}"
    );
}

#[test]
fn a_block_that_only_raises_gives_nothing() {
    // docs/14 §5: the method's result type is `Nothing`, which implements
    // any method; a result nothing settles is still an error.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "abstract class Model\n  abstract def save -> Bool\n  static def self.stub(n: Symbol) -> Void\n    def_method(n) { raise NotImplementedError, \"#{n} is not implemented\" }\n  end\n  static def self.empty(n: Symbol) -> Void\n    def_method(n) { [] }\n  end\nend\n",
    );
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Post < Model\n  stub :save\nend\nbegin\n  Post.new.save\nrescue => e\n  p e\nend\n",
    );
    let expected = "#<NotImplementedError: save is not implemented>\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert!(
        out.contains("  def save -> Nothing = <block at lib.qz:4>\n"),
        "{out}"
    );
    write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass Q < Model\n  stub :save\n  empty :e\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains(
            "`def_method(:e)`: the block's parameter or result type could not be inferred"
        ),
        "{err}"
    );
    // The result is bound to `Nothing`, not only recorded so: a `next`
    // whose value's type is settled after the block must agree.
    write(
        &d.0,
        "late.qz",
        "class Late\n  static def self.nx(n: Symbol, flag: Bool) -> Void\n    xs = []\n    i = 0\n    while i < 2\n      if i == 1\n        ys = xs.dup\n        def_method(n) do\n          next ys[0] if flag\n          raise \"no\"\n        end\n      end\n      xs = xs.push(5)\n      i += 1\n    end\n  end\nend\n",
    );
    write(
        &d.0,
        "late_app.qz",
        "require_relative \"late\"\nclass Post < Late\n  nx :a, true\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "late_app.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("cannot assign Array[Int] to `xs` of type Array[Nothing]"),
        "{err}"
    );
}

#[test]
fn abstract_methods_implemented_across_statements() {
    // docs/14 §5: a class's conformance is checked after all its file's
    // statements ran, not after each.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "abstract class Shape\n  abstract def area -> Int\n  abstract def side -> Int\n  static def self.a(m: Symbol) -> Void\n    def_method(m) { 1 }\n  end\n  static def self.b(m: Symbol) -> Void\n    def_method(m) { 2 }\n  end\n  static def self.stub(m: Symbol) -> Void\n    def_method(m) { raise NotImplementedError, m.to_s }\n  end\nend\n",
    );
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Two < Shape\n  a :area\n  b :side\nend\nclass Twice < Shape\n  a :area\n  a :side\nend\nclass Stubbed < Shape\n  a :area\n  stub :side\nend\np [Two.new.area, Two.new.side, Twice.new.side]\nbegin\n  Stubbed.new.side\nrescue => e\n  p e\nend\n",
    );
    let expected = "[1, 2, 1]\n#<NotImplementedError: side>\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
    // Still missing after the statements: reported once.
    write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass Half < Shape\n  a :area\n  a :other\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    assert_eq!(
        err.matches("error: `Half` must implement `side` (abstract in `Shape`)")
            .count(),
        1,
        "{err}"
    );
}

const MODULE_LIB: &str = r##"abstract class Model
  def id -> Int = 7
end

class Other < Model
end

module Macros[T <: Model]
  static def self.has(n: Symbol) -> Void
    tn = name
    doc "has #{n}"
    def_method(n) { "#{tn}/#{n}/#{id}" }
    def_class_method(:table) { tn.downcase }
  end

  static def self.label -> String = "#{name}!"
end

module Plain
  def self.tag -> String = "plain"
  static def self.plain(n: Symbol) -> Void
    def_method(n) { 1 }
    def_class_method(:plain_tag) { tag }
  end
end
"##;

#[test]
fn a_generic_modules_macros_through_include() {
    // docs/14 §2: `self` is `Meta::ClassDef[T]`, `T` the class that
    // includes `Macros[T]`; subclasses run them too.
    let d = dir();
    write(&d.0, "lib.qz", MODULE_LIB);
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Post < Model\n  include Macros[Post]\n  has :title\nend\nclass Sub < Post\n  has :more\nend\np Post.new.title\np Post.table\np Sub.new.more\np Sub.label\n",
    );
    let expected = "\"Post/title/7\"\n\"post\"\n\"Sub/more/7\"\n\"Sub!\"\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
    // Included as another class, as a superclass, in a module, `extend`,
    // and a compile-time-only one called at run time.
    write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass A < Model\n  include Macros[Other]\nend\nmodule M2\n  include Macros[Other]\nend\nclass C < Model\nend\nclass D < C\nend\nclass E < C\n  include Macros[D]\nend\nclass X < Model\n  extend Macros[X]\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    for want in [
        "bad.qz:3:11: error: `Macros` has `static def self.` macros, which run on the class including it: include it as `Macros[A]`",
        "bad.qz:6:11: error: `Macros` has `static def self.` macros typed by its first type parameter, which run on the class including it: include it in that class (`include Macros[Post]` in `Post`), not in a module",
        "bad.qz:13:11: error: `Macros` has `static def self.` macros, which run on the class including it: include it as `Macros[E]`",
        "bad.qz:16:3: error: `extend` is not supported: a module's class methods reach a class through `include` (write them as `def self.` methods of the module, and include it)",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
    // A bound naming the module's parameter is met with the arguments
    // substituted.
    write(
        &d.0,
        "fb.qz",
        "require_relative \"fblib\"\nclass K < Cmp[K]\n  include F[K]\nend\np K.nm\n",
    );
    write(
        &d.0,
        "fblib.qz",
        "class Cmp[X]\nend\nmodule F[T <: Cmp[T]]\n  static def self.nm -> String = name\nend\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "fb.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"K\"\n");
    // Not the class's own instance type, outside the bound, through an
    // extension: refused at the declaration.
    write(
        &d.0,
        "lib2.qz",
        "class Base\nend\nmodule Gen[T <: Base]\n  static def self.gen(n: Symbol) -> Void\n    def_method(n) { self }\n  end\nend\nmodule Plain2[T]\nend\nextension Plain2[T]\n  static def me -> Type[Object] = self\nend\n",
    );
    write(
        &d.0,
        "bad2.qz",
        "require_relative \"lib2\"\nclass Box[E] < Base\n  include Gen[Box[Int]]\nend\nclass NotBase\n  include Gen[NotBase]\nend\nclass P < Base\nend\nextension P\n  include Gen[P]\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad2.qz"], &[]);
    assert!(!ok);
    for want in [
        "bad2.qz:3:11: error: `Gen` has `static def self.` macros, which run on the class including it: include it as `Gen[Box[E]]`",
        "bad2.qz:6:11: error: `Gen[NotBase]`: `NotBase` is not a `Base`, which `Gen`'s `static def`s were checked for (`T`)",
        "bad2.qz:10:11: error: `Gen` has `static def`s, which run on a class: an extension cannot include it",
        "lib2.qz:11:10: error: an extension cannot declare a `static def`",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
    // A module without type parameters: `self` is `Meta::ClassDef[Self]`,
    // the class including it.
    write(
        &d.0,
        "plain.qz",
        "require_relative \"lib\"\nclass F < Model\n  include Plain\n  plain :y\nend\np F.new.y, F.plain_tag\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "plain.qz"], &[]);
    assert!(ok, "{err}");
    // (A lifted class-side block finds the module's class methods.)
    assert_eq!(out, "1\n\"plain\"\n");
    write(
        &d.0,
        "late.qz",
        "require_relative \"lib\"\nclass G < Model\n  include Macros[G]\nend\nG.has(:w)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "late.qz"], &[]);
    assert!(!ok);
    assert!(err.contains("`has` runs at compile time only"), "{err}");
}

#[test]
fn a_declared_block_result_is_the_generated_methods() {
    // docs/14 §5: `def_method(n) do -> T ... end` gives the method the
    // result type `T`, checked against the body; an empty array's element
    // type, which nothing settles otherwise, comes from it.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  static def self.labelled(n: Symbol) -> Void\n    def_method(n) do -> String | Int\n      \"label\"\n    end\n  end\n  static def self.none(n: Symbol) -> Void\n    def_method(n) { -> Array[Int] [] }\n  end\n  static def self.never(n: Symbol) -> Void\n    def_method(n) { -> Nothing raise \"never\" }\n  end\nend\n",
    );
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Base\n  labelled :tag\n  none :ids\n  never :boom\nend\nv: String | Int = A.new.tag\np v, A.new.ids.push(1)\nbegin\n  A.new.boom\nrescue => e\n  p e.message\nend\n",
    );
    let expected = "\"label\"\n[1]\n\"never\"\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", "app.qz"], &[]);
    assert!(ok, "{err}");
    for line in [
        "  def tag -> String | Int = <block at lib.qz:3>\n",
        "  def ids -> Array[Int] = <block at lib.qz:8>\n",
        "  def boom -> Nothing = <block at lib.qz:11>\n",
    ] {
        assert!(out.contains(line), "{line:?} in {out}");
    }
    write(
        &d.0,
        "bad.qz",
        "class Bad\n  static def self.wrong(n: Symbol) -> Void\n    def_method(n) do -> Int\n      \"not an int\"\n    end\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("block returns String but is declared `-> Int`"),
        "{err}"
    );
}

const HANDLES_LIB: &str = r##"class Model
  var @post_id: Int = 0
  def post_id=(v: Int) -> Void
    @post_id = v
  end
  static def self.counter(field: Symbol) -> Void
    ref = def_field(field, Int, 0, var: true, reader: true)
    bump = "bump_#{field}".to_sym
    def_method(bump) do -> Void
      ref.set(self, ref.get(self) + 1)
    end
  end
  # `U` names the static def's own type parameter, the call's `Int`.
  static def self.slot[V](n: Symbol, t: Type[V], d: V) -> Void
    ref = def_field(n, t, d, var: true)
    def_method("get_#{n}".to_sym) do -> V
      ref.get(self)
    end
  end
  static def self.belongs(name: Symbol) -> Void
    later = field_ref[Int](:mark)
    flag = def_field(:flag, Int, 0, var: true)
    def_method(:toggle, :on) do |on: Bool| -> Int
      flag.set(self, on ? 1 : 2)
      3.times { flag.set(self, flag.get(self) + 1) }
      flag.get(self)
    end
    fk = field_ref[Int](:post_id)
    def_method("#{name}_key".to_sym) do -> Int
      fk.get(self) * 10 + later.get(self)
    end
    def_field(:mark, Int, 7)
  end
end
"##;

const HANDLES_APP: &str = r##"require_relative "lib"
class Comment < Model
  counter(:views)
  belongs(:post)
  slot :size, Int, 9
end
c = Comment.new
c.bump_views
c.bump_views
p c.views
c.post_id = 4
p c.post_key
p c.toggle(false)
p c.get_size
"##;

#[test]
fn field_handles_read_and_write_generated_and_declared_fields() {
    // docs/14 §5: `def_field` and `field_ref` give handles that the
    // methods a statement generates read and write, interpreted and
    // compiled alike, cold and warm.
    let d = dir();
    write(&d.0, "lib.qz", HANDLES_LIB);
    let app = write(&d.0, "app.qz", HANDLES_APP);
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let cold = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    let warm = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, "2\n47\n5\n9\n");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), "2\n47\n5\n9\n");
    // What a handle cannot name, or be used for, is the statement's
    // error.
    for (body, expected) in [
        (
            "    ref = def_field(:fixed, Int, 0)\n    def_method(:bad) do -> Void\n      ref.set(self, 1)\n    end\n",
            "`@fixed` is not `var`: `set` through a `Meta::FieldRef` needs a `var` field",
        ),
        (
            "    ref = field_ref[Int](:nope)\n    def_method(:bad) do -> Int\n      ref.get(self)\n    end\n",
            "the handle to `@nope` names no field of `Comment`",
        ),
        (
            "    ref = field_ref[Int?](:post_id)\n    def_method(:bad) do -> Int?\n      ref.get(self)\n    end\n",
            "but the field is declared `Int`: a handle's type is the field's exactly",
        ),
        // The object is `self`: another `Model` may lack the field the
        // class generated into has.
        (
            "    ref = def_field(:n, Int, 0)\n    def_method(:peek, :o) do |o: Model| -> Int\n      ref.get(o)\n    end\n",
            "a `Meta::FieldRef`",
        ),
        (
            "    ref = field_ref[Int](:post_id)\n    def_method(:bad) do -> Int\n      ref.get(obj: self)\n    end\n",
            "takes its arguments by position",
        ),
        // `U` a generic helper's type parameter it does not carry (two
        // parameters mention it, #918).
        (
            "    ref = mk(:post_id, Int, 0)\n    def_method(:bad) do -> Int\n      ref.get(self)\n    end\n  end\n  static def self.mk[V](n: Symbol, t: Type[V], d: V) -> Meta::FieldRef[Model, V]\n    field_ref[V](n)\n",
            "a type parameter of another method than the `static def` the statement calls, which does not carry it",
        ),
        // A handle made for another class (here a sibling's).
        (
            "    ref = Other.mk\n    def_method(:bad) do -> Int\n      ref.get(self)\n    end\n  end\n  static def self.mk -> Meta::FieldRef[Model, Int]\n    field_ref[Int](:post_id)\n",
            "which `Comment` does not inherit from",
        ),
    ] {
        write(
            &d.0,
            "lib.qz",
            &format!("class Model\n  var @post_id: Int = 0\n  static def self.gen -> Void\n{body}  end\nend\nclass Other < Model\nend\n"),
        );
        write(&d.0, "bad.qz", "require_relative \"lib\"\nclass Comment < Model\n  gen\nend\n");
        let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
        assert!(!ok, "{body}");
        assert!(err.contains(expected), "{body}: {err}");
    }
}

/// #890: field initializers, a library's base class generating, per
/// statement call, a field of the type it was given with a block that
/// fills it, and the constructors once, in another call.
const FIELD_INIT_LIB: &str = r##"data Settings = (theme: String, per_page: Int = 20)
data Prefs = (lang: String)

abstract class Store
  include Shareable
  # (What the generated `initialize` assigns; a default for the class
  # itself, which has no `initialize` of its own.)
  @raw: Hash[Symbol, String] = {}
  def raw(n: Symbol) -> String? = @raw[n]?

  # A document field of type `T`, decoded once, when the object is made.
  static def self.document[T](name: Symbol, type: Type[T]) -> Void
    n = name
    def_field(name, type, nil, nullable: true, reader: true) do -> T?
      (s = raw(n)) ? JSON.decode[T](s) : nil
    end
  end

  # The same through a helper: its `V` carried into the block.
  static def self.document_via[T](name: Symbol, type: Type[T]) -> Void
    add_document(name, type)
  end

  static def self.add_document[V](name: Symbol, type: Type[V]) -> Void
    n = name
    def_field(name, type, nil, nullable: true, reader: true) do -> V?
      (s = raw(n)) ? JSON.decode[V](s) : nil
    end
  end

  # A field read by a later initializer, and one that raises.
  static def self.themed -> Void
    ref = def_field(:look, Settings, nil, nullable: true) do -> Settings?
      (s = raw(:look)) ? JSON.decode[Settings](s) : nil
    end
    def_field(:theme, String, "none", reader: true) do -> String
      (s = ref.get(self)) ? s.theme : "unset"
    end
    def_field(:checked, Int, 0, reader: true) do -> Int
      raise ArgumentError.new("refused: #{raw(:fail) || ""}") if raw(:fail)
      @raw.size
    end
  end

  # The constructor, generated once, after the fields.
  static def self.table -> Void
    def_initialize(:raw) do |raw: Hash[Symbol, String]|
      @raw = raw
    end
  end
end
"##;

const FIELD_INIT_APP: &str = r##"require_relative "lib"
class Page < Store
  document :settings, Settings
  document_via :prefs, Prefs
  themed
  table
end
class Plain < Page
end
class Sub < Page
  @extra: Int
  def initialize(raw: Hash[Symbol, String], @extra: Int)
    super(raw)
  end
  def extra -> Int = @extra
end
def show(s: Settings?) -> String = (x = s) ? "#{x.theme}/#{x.per_page}" : "nil"
def lang(p: Prefs?) -> String = (x = p) ? x.lang : "nil"
p = Page.new({settings: "{\"theme\":\"dark\"}", prefs: "{\"lang\":\"ja\"}", look: "{\"theme\":\"light\"}"})
puts show(p.settings), lang(p.prefs), p.theme, p.checked
# A second construction decodes again.
q = Page.new({settings: "{\"theme\":\"blue\",\"per_page\":5}"})
puts show(q.settings), lang(q.prefs), q.theme, q.checked
puts lang(Plain.new({prefs: "{\"lang\":\"en\"}"}).prefs)
s = Sub.new({look: "{\"theme\":\"sub\"}"}, 3)
puts s.theme, s.extra
begin
  Page.new({fail: "x"})
rescue ArgumentError => e
  puts e.message
end
"##;

const FIELD_INIT_EXPECTED: &str =
    "dark/20\nja\nlight\n3\nblue/5\nnil\nunset\n1\nen\nsub\n3\nrefused: x\n";

#[test]
fn field_initializers_fill_generated_fields_when_constructed() {
    let d = dir();
    write(&d.0, "lib.qz", FIELD_INIT_LIB);
    let app = write(&d.0, "app.qz", FIELD_INIT_APP);
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let cold = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    let warm = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, FIELD_INIT_EXPECTED);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), FIELD_INIT_EXPECTED);
    // `--expand` shows each field with its initializer, not as a method.
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert!(
        out.contains("@settings: Settings? = nil\n    # then, at the end of each generated `initialize`: <block at lib.qz:14>"),
        "{out}"
    );
    assert!(!out.contains("__init_@"), "{out}");
    // A `next` that ends the `initialize`'s block early runs them too; a
    // subclass's `initialize` that does not call `super` leaves the field
    // at its default (as any field `super` would have assigned).
    write(
        &d.0,
        "early.qz",
        "class Base\n  include Shareable\n  @x: Int = 0\n  static def self.gen -> Void\n    def_field(:twice, Int, 0, reader: true) { @x * 2 }\n    def_initialize(:x) do |x: Int|\n      @x = x\n      next if x > 5\n      @x = x + 1\n    end\n  end\nend\n",
    );
    let early = write(
        &d.0,
        "early_app.qz",
        "require_relative \"early\"\nclass C < Base\n  gen\nend\nclass D < C\n  def initialize(y: Int)\n  end\nend\nputs C.new(2).twice, C.new(7).twice, D.new(4).twice\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", early.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, "6\n14\n0\n");
    // The initializer's name can be written as a quoted symbol, and a
    // handle to it called: it computes the value and stores nothing, so
    // only a generated `initialize` assigns the field.
    write(
        &d.0,
        "handle.qz",
        "class Base\n  var @x: Int = 0\n  def bump -> Void\n    @x += 10\n  end\n  static def self.gen -> Void\n    def_field(:twice, Int, 0, reader: true) { @x * 2 }\n    def_initialize(:x) do |x: Int|\n      @x = x\n    end\n    m = method_ref[() -> Int](:\"__init_@twice\")\n    def_method(:again) do -> Int\n      m.bind(self).call\n    end\n  end\nend\n",
    );
    let handle = write(
        &d.0,
        "handle_app.qz",
        "require_relative \"handle\"\nclass C < Base\n  gen\nend\nc = C.new(3)\nc.bump\nputs c.again, c.twice\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", handle.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, "26\n6\n");
    // What is refused.
    let bad_lib = FIELD_INIT_LIB.replace(
        "  # The constructor, generated once",
        "  static def self.bad -> Void\n    def_field(:n, Int, 0) { \"no\" }\n  end\n\n  # The constructor, generated once",
    );
    for (lib, app, expected) in [
        // The block's result is not the field's type.
        (
            bad_lib.as_str(),
            "require_relative \"lib\"\nclass A < Store\n  bad\n  table\nend\n",
            "`def_field` on Meta::ClassDef[Store] matches (Symbol, Type[Int], Int, { block }):\n    def_field(name: Symbol, type: Type[U], default: U, var: Bool = ..., reader: Bool = ..., writer: Bool = ..., &init: T.() -> U) -> Meta::FieldRef[T, U]: block returns String but Int was expected",
        ),
        // A generated `initialize` before the initializer.
        (
            FIELD_INIT_LIB,
            "require_relative \"lib\"\nclass A < Store\n  table\n  document :settings, Settings\nend\n",
            "`A` already has a generated `initialize`, which would not run the initializer",
        ),
        // A written `initialize`.
        (
            FIELD_INIT_LIB,
            "require_relative \"lib\"\nclass A < Store\n  def initialize\n    @raw = {}\n  end\n  document :settings, Settings\nend\n",
            "`A` has a written `initialize`, which does not run initializers",
        ),
        // No `initialize` of its own.
        (
            FIELD_INIT_LIB,
            "require_relative \"lib\"\nclass A < Store\n  document :settings, Settings\nend\n",
            "`@settings` of `A` has an initializer, which only a generated `initialize` of `A` runs, and `A` has none",
        ),
    ] {
        write(&d.0, "lib.qz", lib);
        let app = write(&d.0, "bad.qz", app);
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{app:?}");
        assert!(err.contains(expected), "{err}");
    }
}

/// #918: a field handle made in a generic helper with the helper's own
/// type parameter, carried as its `def_method` blocks' is (the class its
/// `Type[T]` parameter holds), is typed with the class the generating call
/// passed: rotor's kept document field (`def_field(..., nullable: true)`,
/// a `FieldRef[Self, T?]`, read by a generated method typed `T?`), a
/// `field_ref[T]` read by one typed `T`, the helper called by two
/// statements and twice in one statement with other classes (one site,
/// two handles, each typed by its own), interpreted and compiled, cold and
/// warm.
const CARRIED_HANDLES_LIB: &str = r##"data Settings = (theme: String, per_page: Int = 20)
data Prefs = (lang: String)

abstract class Store
  include Shareable
  @raw: Hash[Symbol, String] = {}
  @count: Int = 7
  def raw(n: Symbol) -> String? = @raw[n]?

  # The helper: a kept document field, decoded when the object is made,
  # and its typed reader, through the handle `def_field` gives.
  static def self.kept[T](field: Symbol, reader: Symbol, type: Type[T]) -> Void
    n = field
    ref = def_field(field, type, nil, nullable: true) do -> T?
      (s = raw(n)) ? JSON.decode[T](s) : nil
    end
    def_method(reader) do -> T?
      ref.get(self)
    end
    shown = ref.inspect
    def_method("#{reader}_handle".to_sym) do -> String
      shown
    end
  end

  # A declared field read through `field_ref[T]` in a helper.
  static def self.reads[T](field: Symbol, reader: Symbol, type: Type[T]) -> Void
    ref = field_ref[T](field)
    def_method(reader) do -> T
      ref.get(self)
    end
  end

  # One statement per class, and one calling the helper twice.
  static def self.doc[T](field: Symbol, reader: Symbol, type: Type[T]) -> Void
    kept(field, reader, type)
  end

  static def self.both -> Void
    kept(:look, :look_doc, Settings)
    kept(:lang, :lang_doc, Prefs)
    reads(:count, :count_now, Int)
  end

  static def self.table -> Void
    def_initialize(:raw) do |raw: Hash[Symbol, String]|
      @raw = raw
    end
  end
end
"##;

const CARRIED_HANDLES_APP: &str = r##"require_relative "lib"
class Page < Store
  doc :settings, :settings_doc, Settings
  doc :prefs, :prefs_doc, Prefs
  both
  table
end
def show(s: Settings?) -> String = (x = s) ? "#{x.theme}/#{x.per_page}" : "nil"
def lang(p: Prefs?) -> String = (x = p) ? x.lang : "nil"
p = Page.new({settings: "{\"theme\":\"dark\"}", prefs: "{\"lang\":\"ja\"}", look: "{\"theme\":\"light\",\"per_page\":5}", lang: "{\"lang\":\"en\"}"})
puts show(p.settings_doc), lang(p.prefs_doc), show(p.look_doc), lang(p.lang_doc), p.count_now
q = Page.new({prefs: "{\"lang\":\"fr\"}"})
puts show(q.settings_doc), lang(q.prefs_doc), show(q.look_doc), lang(q.lang_doc)
puts p.look_doc_handle, p.lang_doc_handle
"##;

const CARRIED_HANDLES_EXPECTED: &str = "dark/20\nja\nlight/5\nen\n7\nnil\nfr\nnil\nnil\n#<Meta::FieldRef Page@look>\n#<Meta::FieldRef Page@lang>\n";

#[test]
fn a_handle_made_in_a_generic_helper_takes_the_carried_class() {
    let d = dir();
    write(&d.0, "lib.qz", CARRIED_HANDLES_LIB);
    let app = write(&d.0, "app.qz", CARRIED_HANDLES_APP);
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let cold = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    let warm = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, CARRIED_HANDLES_EXPECTED);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        CARRIED_HANDLES_EXPECTED
    );
    // What stays refused at the statement: a helper that does not carry
    // its `T` (two parameters mention it), a carried class with type
    // arguments, a carried class whose handle is not the field's type.
    for (helper, call, expected) in [
        (
            "  static def self.two[T](field: Symbol, type: Type[T], d: T) -> Void\n    ref = field_ref[T](field)\n    def_method(:bad) do -> Int\n      ref.get(self)\n      0\n    end\n  end\n",
            "    two(:count, Int, 0)\n",
            "the handle to `@count` is made with `T`, a type parameter of another method than the `static def` the statement calls, which does not carry it",
        ),
        (
            "  static def self.generic[T](field: Symbol, type: Type[T]) -> Void\n    ref = field_ref[T](field)\n    def_method(:bad) do -> Int\n      ref.get(self)\n      0\n    end\n  end\n",
            "    generic(:count, Array)\n",
            "`T` is `Array`, whose type arguments are not known here",
        ),
        (
            "  static def self.other[T](field: Symbol, type: Type[T]) -> Void\n    ref = field_ref[T](field)\n    def_method(:bad) do -> Int\n      ref.get(self)\n      0\n    end\n  end\n",
            "    other(:count, String)\n",
            "the handle to `@count` is a `Meta::FieldRef[Bad, String]`, but the field is declared `Int`: a handle's type is the field's exactly",
        ),
    ] {
        // (The helper called from the `static def` a statement runs.)
        let lib = CARRIED_HANDLES_LIB.replace(
            "  static def self.table -> Void",
            &format!("{helper}  static def self.go -> Void\n{call}  end\n\n  static def self.table -> Void"),
        );
        write(&d.0, "badlib.qz", &lib);
        write(
            &d.0,
            "bad.qz",
            "require_relative \"badlib\"\nclass Bad < Store\n  go\nend\n",
        );
        let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
        assert!(!ok, "{call}");
        assert!(err.contains(expected), "{call}: {err}");
    }
}

/// #950: a class method `def_class_method` generates in the place of
/// `Object#dup` (no parameters, as `dup` has none) is refused as a
/// written one is, at the statement that generates it.
#[test]
fn a_generated_class_method_cannot_take_dups_place() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Gen\n  static def self.gen -> Void\n    def_class_method(:dup) do -> Type[Gen]\n      Gen\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Gen\n  gen\nend\nclass B < A\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains(
            "app.qz:3:3: error: `A.dup` would take the place of `Object#dup` on the class value"
        ),
        "{err}"
    );
}

/// #944: `Type[T]#cast?`, `#cast` in a generated method, with the
/// `Type[T]` a generic helper's `def_method` block captures (baked): the
/// value back as `T` from an untyped store, nil (or `TypeError`) for one
/// of another class, `ArgumentError` for a class with type parameters;
/// interpreted and compiled.
const CAST_LIB: &str = r##"data Settings = (theme: String)
data Box[T] = (v: T)

abstract class Bag
  include Shareable
  @items: Hash[Symbol, Shareable] = {}
  def item(n: Symbol) -> Shareable? = @items[n]?

  static def self.typed[T](name: Symbol, type: Type[T]) -> Void
    n = name
    def_method(name) do -> T?
      (v = item(n)) ? type.cast?(v) : nil
    end
    def_method("#{name}!".to_sym) do -> T
      type.cast(item(n) || raise ArgumentError.new("none"))
    end
  end

  static def self.table -> Void
    def_initialize(:items) do |items: Hash[Symbol, Shareable]|
      @items = items
    end
  end
end
"##;

const CAST_APP: &str = r##"require_relative "lib"
class Things < Bag
  typed :settings, Settings
  typed :count, Int
  typed :box, Box[Int]
  table
end
def show(s: Settings?) -> String = (x = s) ? x.theme : "nil"
t = Things.new({settings: Settings.new("dark"), count: "not an Int", box: Box.new(1)})
puts show(t.settings), t.count.inspect, t.settings!.theme
begin
  t.count!
rescue TypeError => e
  puts e.message
end
begin
  t.box
rescue ArgumentError => e
  puts e.message
end
"##;

const CAST_EXPECTED: &str = "dark\nnil\ndark\ncannot cast String to Int\nBox.cast?: Box has type parameters, and a value's type arguments are not seen at run time\n";

#[test]
fn a_class_value_a_generated_method_captured_casts() {
    let d = dir();
    write(&d.0, "lib.qz", CAST_LIB);
    let app = write(&d.0, "app.qz", CAST_APP);
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, CAST_EXPECTED);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), CAST_EXPECTED);
}

/// #918, the check at a handle's use: a handle a generic helper returns
/// is typed with its caller's view of the helper's type parameter (here
/// `Animal`, for a `Type[Animal]` value holding `Dog`), wider than the
/// field; a generated method that reads or writes it through that type is
/// refused at the statement, whatever carried the handle there. Through
/// the same helper with `Dog` written, it runs, interpreted and compiled.
const USE_CHECK_LIB: &str = r##"class Animal
  def name -> String = "animal"
end
class Dog < Animal
  def name -> String = "dog"
  def bark -> String = "woof"
end
class Cat < Animal
  def name -> String = "cat"
end
class Base
  var @pet: Dog = Dog.new
  def bark -> String = @pet.bark
  static def self.mk[V](n: Symbol, t: Type[V]) -> Meta::FieldRef[Base, V]
    field_ref[V](n)
  end
  static def self.mk_tuple[V](n: Symbol, t: Type[V]) -> [Meta::FieldRef[Base, V], Int]
    [field_ref[V](n), 1]
  end
  static def self.mk_array[V](n: Symbol, t: Type[V]) -> Array[Meta::FieldRef[Base, V]]
    [field_ref[V](n)]
  end
  static def self.mk_lambda[V](n: Symbol, t: Type[V]) -> () -> Meta::FieldRef[Base, V]
    r = field_ref[V](n)
    -> { r }
  end
  static def self.mk_field[V](n: Symbol, t: Type[V]) -> Meta::FieldRef[Base, V?]
    def_field(n, t, nil, nullable: true, var: true)
  end
  static def self.inner[W](r: Meta::FieldRef[Base, W]) -> Void
    def_method(:swap) do -> Void
      r.set(self, r.get(self))
    end
  end
  static def self.outer[V](n: Symbol, t: Type[V]) -> Void
    inner(field_ref[V](n))
  end
#GO#
end
"##;

#[test]
fn a_handle_is_checked_where_it_is_read_or_written() {
    let d = dir();
    let go = |body: &str| {
        USE_CHECK_LIB.replace(
            "#GO#",
            &format!("  static def self.go -> Void\n    kinds: Array[Type[Animal]] = [Dog]\n{body}  end\n"),
        )
    };
    let swap = |ref_expr: &str, write: &str| {
        format!("    ref = {ref_expr}\n    def_method(:swap) do -> Void\n      {write}\n    end\n")
    };
    let app = "require_relative \"lib\"\nclass Home < Base\n  go\nend\nh = Home.new\nh.swap\nputs h.bark\n";
    // Accepted: the helper given `Dog` itself.
    write(
        &d.0,
        "lib.qz",
        &go(&swap("mk(:pet, Dog)", "ref.set(self, Dog.new)")),
    );
    let app_path = write(&d.0, "app.qz", app);
    let (ok, out, err) = quarz(&d.0, &["run", app_path.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "woof\n");
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "woof\n");
    let widened = |u: &str, field: &str| {
        format!("the handle to `@{field}` is used in the generated method as a `Meta::FieldRef[Home, {u}]`, but the field is declared `")
    };
    for (body, expected) in [
        // The helper's result, alone, in a tuple, in an array, through a
        // procedure; read only; written from a block of the method's.
        (swap("mk(:pet, kinds[0])", "ref.set(self, Cat.new)"), widened("Animal", "pet")),
        (swap("mk_tuple(:pet, kinds[0])[0]", "ref.set(self, Cat.new)"), widened("Animal", "pet")),
        (swap("mk_array(:pet, kinds[0])[0]", "ref.set(self, Cat.new)"), widened("Animal", "pet")),
        (swap("mk_lambda(:pet, kinds[0]).call", "ref.set(self, Cat.new)"), widened("Animal", "pet")),
        (swap("mk(:pet, kinds[0])", "puts ref.get(self).name"), widened("Animal", "pet")),
        (swap("mk(:pet, kinds[0])", "[1, 2].each { |_| ref.set(self, Cat.new) }"), widened("Animal", "pet")),
        // `def_field`'s handle alike.
        (swap("mk_field(:pet2, kinds[0])", "ref.set(self, Cat.new)"), widened("Animal?", "pet2")),
        // A handle of one helper's invocation captured in another's
        // block, whose type parameter it does not carry.
        (
            "    outer(:pet, Dog)\n".to_string(),
            "the handle to `@pet` is used in the generated method as a `Meta::FieldRef[Home, W]`, whose `W` has no class here".to_string(),
        ),
    ] {
        write(&d.0, "lib.qz", &go(&body));
        let (ok, _, err) = quarz(&d.0, &["check", "app.qz"], &[]);
        assert!(!ok, "{body}");
        assert!(err.contains(&expected), "{body}: {err}");
    }
}

const METHOD_HANDLES_LIB: &str = r##"class Model
  # Overridden by the generated `fact`, which its handle names.
  def fact(n: Int) -> Int = 0
  static def self.counter(field: Symbol) -> Void
    ref = def_field(field, Int, 0, var: true, reader: true)
    bump = def_method("bump_#{field}".to_sym) do -> Void
      ref.set(self, ref.get(self) + 1)
    end
    def_method("bump_#{field}_twice".to_sym) do -> Void
      bump.bind(self).call
      bump.bind(self).call
    end
  end
  static def self.arith -> Void
    fact = method_ref[(Int) -> Int](:fact)
    def_method(:fact, :n) do |n: Int| -> Int
      n <= 1 ? 1 : n * fact.bind(self).call(n - 1)
    end
    add = def_method(:add, [:a, :b]) do |a: Int, b: Int| -> Int
      a + b
    end
    def_method(:add3, :x) do |x: Int| -> Int
      f = add.bind(self)
      [1, 2].sum { |i| f.call(x, i) }
    end
    hidden = def_method(:secret, visibility: :private) do -> String
      "s"
    end
    def_method(:reveal) do -> String
      hidden.bind(self).call
    end
    mk = def_class_method(:make) do -> Model
      new
    end
    def_class_method(:make2) do -> Model
      mk.bind(self).call
    end
  end
end
"##;

const METHOD_HANDLES_APP: &str = r##"require_relative "lib"
class Post < Model
  counter(:views)
  arith
end
class Sub < Post
  def add(a: Int, b: Int) -> Int = a * b
end
q = Post.new
q.bump_views_twice
p q.views
p q.fact(5)
p q.add3(4)
p Sub.new.add3(4)
p q.reveal
p Post.make2.class
"##;

const METHOD_HANDLES_OUT: &str = "2\n120\n11\n12\n\"s\"\nPost\n";

#[test]
fn method_handles_call_generated_methods() {
    // docs/14 §5: `def_method`'s result and `method_ref` are handles that
    // the methods a statement generates call through `bind(self)`, as a
    // call dispatches (an override is taken), interpreted and compiled,
    // cold and warm.
    let d = dir();
    write(&d.0, "lib.qz", METHOD_HANDLES_LIB);
    let app = write(&d.0, "app.qz", METHOD_HANDLES_APP);
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let cold = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    let warm = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    for _ in 0..2 {
        let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
        assert!(ok, "{err}");
        assert_eq!(out, METHOD_HANDLES_OUT);
    }
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), METHOD_HANDLES_OUT);
    // The cached `lib.qz` in a program whose methods are numbered
    // otherwise (a file declaring methods required first): a handle keeps
    // its method by class and place, not by id.
    write(
        &d.0,
        "extra.qz",
        "class Extra\n  def a(x: Int) -> Int = x\n  def b(x: Int) -> Int = x\nend\n",
    );
    let app2 = write(
        &d.0,
        "app2.qz",
        &format!("require_relative \"extra\"\n{METHOD_HANDLES_APP}"),
    );
    let (ok, out, err) = quarz(&d.0, &["run", app2.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, METHOD_HANDLES_OUT);
    // What a handle cannot name, or be bound to, is the statement's
    // error.
    for (body, expected) in [
        (
            "    m = method_ref[IntFn](:nope)\n    def_method(:bad) do -> Int\n      m.bind(self).call(1)\n    end\n",
            "has no method `nope` of that type",
        ),
        (
            "    m = method_ref[IntFn](:twice)\n    def_method(:bad) do -> Int\n      m.bind(self).call(1)\n    end\n",
            "has no method `twice` of that type",
        ),
        // Checked though nothing captures it.
        (
            "    m = method_ref[IntFn](:nope)\n",
            "has no method `nope` of that type",
        ),
        (
            "    f = field_ref[Int](:nope)\n",
            "names no field of `Comment`",
        ),
        // A handle names a method of positional parameters only.
        (
            "    m = method_ref[(Int, *, k: Int) -> Int](:thrice)\n",
            "which takes keywords: a handle names a method whose parameters are all positional",
        ),
        (
            "    m = def_method(:one) do -> Int\n      1\n    end\n    def_method(:bad, :o) do |o: Model| -> Int\n      m.bind(o).call\n    end\n",
            "takes the generated method's `self`",
        ),
        (
            "    m = Other.mk\n    def_method(:bad) do -> Int\n      m.bind(self).call(1)\n    end\n  end\n  static def self.mk -> Meta::Method[Model, IntFn]\n    method_ref[IntFn](:thrice)\n",
            "which `Comment` does not inherit from",
        ),
    ] {
        write(
            &d.0,
            "lib.qz",
            &format!("type IntFn = (Int) -> Int\nclass Model\n  def twice(s: String) -> Int = 2\n  def thrice(x: Int) -> Int = 3\n  static def self.gen -> Void\n{body}  end\nend\nclass Other < Model\nend\n"),
        );
        write(&d.0, "bad.qz", "require_relative \"lib\"\nclass Comment < Model\n  gen\nend\n");
        let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
        assert!(!ok, "{body}");
        assert!(err.contains(expected), "{body}: {err}");
    }
    // A handle `static(...)` gives is checked as a statement's is.
    write(
        &d.0,
        "lib.qz",
        "class Model\n  def one(x: Int) -> Int = 1\n  static def self.mk(n: Symbol) -> Meta::Method[Model, (Int) -> Int] = method_ref[(Int) -> Int](n)\nend\n",
    );
    write(
        &d.0,
        "ok.qz",
        "require_relative \"lib\"\np static(Model.mk(:one))\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "ok.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "#<Meta::Method Model#one>\n");
    write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\np static(Model.mk(:nope))\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    assert!(err.contains("has no method `nope` of that type"), "{err}");
}

const LIFTED_SELF_LIB: &str = r##"class Model
  @n: Int = 5
  var @m: Int = 0
  def hello -> Int = 1
  # `Self` in the blocks is the class generated into, whether the
  # `static def`'s own signature mentions `Self` or not.
  static def self.gen -> Void
    def_method(:me) do -> Self
      self
    end
    def_method(:same, :o) do |o: Self| -> Bool
      o.hello == hello
    end
    def_class_method(:mk) do -> Self
      new
    end
    # Its fields, as a method reads and writes them.
    def_method(:copy_n) do -> Int
      @m = @n
      @m
    end
  end
  static def self.gen2 -> Self
    def_method(:me2) do -> Self
      self
    end
    new
  end
end
"##;

const LIFTED_SELF_APP: &str = r##"# `Self` in a block given to `def_method` or `def_class_method` is the
# class generated into (docs/14 §5): `Post#me` gives a `Post`, `Post.mk`
# makes one, and `same` takes one.
require_relative "lib"
class Post < Model
  def only -> Int = 42
  gen
  gen2
end
a: Post = Post.new.me
p a.only
b: Post = Post.mk
p b.only
c: Post = Post.new.me2
p c.only
p Post.new.same(Post.new)
p Post.new.copy_n
"##;

#[test]
fn self_in_a_lifted_block_is_the_class_generated_into() {
    // docs/14 §5: `Self` in a block given to `def_method` or
    // `def_class_method` is the class generated into, interpreted and
    // compiled.
    let d = dir();
    write(&d.0, "lib.qz", LIFTED_SELF_LIB);
    let app = write(&d.0, "app.qz", LIFTED_SELF_APP);
    let expected = "42\n42\n42\ntrue\n5\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
}

#[test]
fn new_in_a_generated_class_method_is_checked_against_its_initializes() {
    // `new` in a block given to `def_class_method` builds an instance of
    // the receiver: the class generated into, and its subclasses (which
    // inherit the generated method, not the `static def`), must take
    // what it passes.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  static def self.gen -> Void\n    def_class_method(:mk) do -> Model\n      new\n    end\n  end\nend\n",
    );
    let sub = write(
        &d.0,
        "sub.qz",
        "require_relative \"lib\"\nclass Post < Model\n  gen\nend\nclass Sub < Post\n  @x: Int\n  def initialize(x: Int)\n    @x = x\n  end\n  def self.gen -> Void\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", sub.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`Sub#initialize` does not take the arguments of `new` in `Post.mk`, which `Sub` inherits")
            && err.contains("override `self.mk` in `Sub`"),
        "{err}"
    );
    let own = write(
        &d.0,
        "own.qz",
        "require_relative \"lib\"\nclass Post < Model\n  @x: Int\n  def initialize(x: Int)\n    @x = x\n  end\n  gen\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", own.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains(
            "`Post#initialize` does not take the arguments of `new` in the generated `Post.mk`"
        ),
        "{err}"
    );
    // An `initialize` inherited from between the two classes.
    let mid = write(
        &d.0,
        "mid.qz",
        "require_relative \"lib\"\nclass Mid < Model\n  @x: Int\n  def initialize(x: Int)\n    @x = x\n  end\nend\nclass Post < Mid\n  gen\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", mid.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains(
            "`Mid#initialize`, which `Post` builds with, does not take the arguments of `new` in the generated `Post.mk`"
        ),
        "{err}"
    );
    let good = write(
        &d.0,
        "good.qz",
        "require_relative \"lib\"\nclass Post < Model\n  gen\nend\nclass Sub < Post\n  @y: Int = 3\n  def initialize(y: Int = 3)\n    @y = y\n  end\nend\np Sub.mk.class.name\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", good.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"Sub\"\n");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", good.to_str().unwrap(), "-o", "good.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("good.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), "\"Sub\"\n");
}

#[test]
fn a_modules_static_def_calls_another_of_the_module() {
    // In a module's macro, `self` is the class including the module
    // (docs/14 §2), whose class object has the module's class methods.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "abstract class Model\nend\nmodule Macros[T <: Model]\n  static def self.helper -> Int = 1\n  static def self.go -> Void\n    p name\n    p helper\n    [10].each { |x| p helper + x }\n    p(\"s\".instance_exec { helper + size })\n  end\nend\n",
    );
    // (From blocks too: one with another receiver reaches them through
    // the enclosing `self`.)
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Post < Model\n  include Macros[Post]\n  go\nend\nPost.go\n",
    );
    // At compile time (the statement), then at run time.
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"Post\"\n1\n11\n2\n");
    assert!(err.contains("\"Post\"\n1\n11\n2\n"), "{err}");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(d.0.join("app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), "\"Post\"\n1\n11\n2\n");
}

#[test]
fn it_in_a_static_def() {
    // `it` (docs/01 §9) in a `static def`'s blocks: run at compile time,
    // and in the generated method's body (a block of one parameter).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Base
  static def self.flags(names: Array[Symbol]) -> Void
    names.select { it != :skip }.each do
      def_method("#{it}?".to_sym) { true }
    end
    def_method(:doubled, :x) { |x: Int| [x].map { it * 2 }.first }
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Item < Base\n  flags [:new, :skip, :hot]\nend\nputs Item.new.new?, Item.new.hot?, Item.new.doubled(21)\n",
    );
    let expected = "true\ntrue\n42\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    // `skip?` was not generated.
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Item < Base\n  flags [:new, :skip]\nend\nItem.new.skip?\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok && err.contains("undefined method `skip?`"), "{err}");
}

/// A generated method's body calls the receiver's methods, public and
/// private, without `self.` (docs/14 §5: its `self` is the receiver); an
/// error elsewhere in a body is reported once, not also as calls on the
/// `Meta::ClassDef` of the `static def`.
#[test]
fn generated_bodies_call_the_receivers_methods_implicitly() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Store
  def pub_get(name: Symbol) -> String = "pub #{name}"
  private def priv_get(name: Symbol) -> String = "priv #{name}"
  static def self.both(name: Symbol) -> Void
    def_method(name) do -> String
      pub_get(name) + " " + priv_get(name)
    end
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass S < Store\n  both :x\nend\nputs S.new.x\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "pub x priv x\n");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), "pub x priv x\n");
    write(
        &d.0,
        "lib.qz",
        r##"class Store
  def pub_get(name: Symbol) -> String = "pub #{name}"
  static def self.both(name: Symbol) -> Void
    def_method(name) do -> String
      x: Int = "oops"
      pub_get(name)
    end
  end
end
"##,
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("lib.qz:5:16: error: cannot assign String to `x` of type Int"),
        "{err}"
    );
    assert!(!err.contains("for Meta::ClassDef"), "{err}");
    // The same with a block declaring fewer parameters than its type, and
    // with an argument of the wrong type (no overload reaches the block).
    for args in [", :a", ", 3"] {
        write(
            &d.0,
            "lib.qz",
            &format!(
                r##"class Store
  def pub_get(name: Symbol) -> String = "pub #{{name}}"
  static def self.both(name: Symbol) -> Void
    def_method(name{args}) do -> String
      x: Int = "oops"
      pub_get(name)
    end
  end
end
"##
            ),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok);
        assert!(
            err.contains("lib.qz:5:16: error: cannot assign String"),
            "{args}: {err}"
        );
        assert!(!err.contains("for Meta::ClassDef"), "{args}: {err}");
    }
}

/// `def_method(name, keywords:)` (docs/14 §5): a method of keyword
/// parameters computed at compile time, as rotor's `with` on a model;
/// the body gets the hash of the keywords given. And `def_field(...,
/// nullable: true)`. Interpreted and compiled, cold and warm.
#[test]
fn generated_keyword_methods_and_nullable_fields() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Model
  static def self.columns(cols: Array[Meta::Keyword]) -> Void
    names = cols.map { |c| c.name }
    def_method(:with, keywords: cols) do |given|
      names.filter { |n| given.key?(n) }.map { |n| "#{n}=#{given[n].inspect}" }.join(" ")
    end
    def_class_method(:make, keywords: cols) do |given|
      "#{name} #{given.size}"
    end
    r = def_field(:note, String, nil, nullable: true, var: true, reader: true)
    def_method(:note!, :s) do |s: String?| -> Void
      r.set(self, s)
    end
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class Person < Model
  columns [
    Meta::Keyword.new(:name, String, true),
    Meta::Keyword.new(:age, Int, false),
    Meta::Keyword.new(:email, String, false, nullable: true),
  ]
end
x = Person.new
puts x.with(name: "a", age: 3)
puts x.with(age: 4, name: "b")
puts x.with(name: "c", email: nil)
puts x.with(name: "d", email: "d@e")
p x.note
x.note!("hi")
p x.note
puts Person.make(name: "e", age: 1)
"#,
    );
    let expected = "name=\"a\" age=3\nname=\"b\" age=4\nname=\"c\" email=nil\nname=\"d\" email=\"d@e\"\nnil\n\"hi\"\nPerson 2\n";
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let cold = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    let warm = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    // The signature, as `--expand` shows it.
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert!(
        out.contains("def with(*, name: String, age: Int = …, email: String? = …) -> String"),
        "{out}"
    );
    // A call is checked as any keyword call.
    for (call, expected) in [
        ("x.with(name: 3)", "expects String but found Int"),
        (
            "x.with(name: \"a\", height: 2)",
            "has no parameter `height`",
        ),
        ("x.with(age: 1)", "is missing the argument `name`"),
        ("x.with(name: \"a\", age: nil)", "expects Int but found Nil"),
    ] {
        let bad = write(
            &d.0,
            "bad.qz",
            &format!("require_relative \"lib\"\nclass Person < Model\n  columns [Meta::Keyword.new(:name, String, true), Meta::Keyword.new(:age, Int, false)]\nend\nx = Person.new\n{call}\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
        assert!(!ok, "{call}");
        assert!(err.contains(expected), "{call}: {err}");
    }
    // What the statement refuses.
    for (cols, expected) in [
        (
            "[Meta::Keyword.new(:xs, Array, true)]",
            "the keyword `xs` is typed `Array`, which takes type arguments",
        ),
        (
            "[Meta::Keyword.new(:a, Int, true), Meta::Keyword.new(:a, Int, false)]",
            "the keyword `a` is given twice",
        ),
        ("[]", "keywords: is empty"),
    ] {
        let bad = write(
            &d.0,
            "bad.qz",
            &format!("require_relative \"lib\"\nclass Person < Model\n  columns {cols}\nend\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
        assert!(!ok, "{cols}");
        assert!(err.contains(expected), "{cols}: {err}");
    }
}

/// A field's declared type in full (`Meta::Field#type_ref`, docs/14 §4)
/// and a generated keyword of that type (`Meta::Keyword.typed`, §5,
/// #401): type arguments, `nil` and unions kept, a call checked against
/// them, and the type back through reflection the same `TypeRef` (the two
/// conversions are each other's converse). A type parameter of the class
/// generated into is one of its keywords' types too. Interpreted and
/// compiled, cold and warm.
#[test]
fn generated_keywords_take_a_declared_type_in_full() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Model
  static def self.show(d: Type[Object]) -> Void
    s = d.fields.map { |f| "#{f.name}: #{f.type_ref} (#{f.type.name})" }.join(", ")
    def_class_method(:shown) { s }
  end
  static def self.from_fields(d: Type[Object]) -> Void
    ks = d.fields.map { |f| Meta::Keyword.typed(f.name, f.type_ref, false) }
    def_method(:with, keywords: ks) do |given|
      given.keys.map { |k| "#{k}=#{given[k].inspect}" }.join(" ")
    end
  end
  static def self.round(d: Type[Object]) -> Void
    sig = methods.find { |m| m.name == :with }
    same = !sig.nil? && sig.params.map(&:type_ref) == d.fields.map(&:type_ref)
    def_class_method(:round) { same }
  end
  static def self.own -> Void
    ks = fields.map { |f| Meta::Keyword.typed(f.name, f.type_ref, true) }
    def_method(:set_all, keywords: ks) do |given|
      given.size
    end
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
data P = (ids: Array[Int], name: String?, tags: Hash[String, Array[Int]], v: Int | String)
class K < Model
  show P
  from_fields P
  round P
end
class G[T] < Model
  @v: Array[T]
  def initialize(@v: Array[T]); end
  own
end
class Sub < G[Int]
  own
end
class Sub2[U] < G[U]
  own
end
class ShowSub < Model
  show Sub
end
class ShowSub2 < Model
  show Sub2
end
puts K.shown
p K.round
x = K.new
puts x.with(ids: [1, 2], name: nil, v: "s")
puts x.with(tags: {"a" => [1]}, v: 3)
p G[Int].new([1]).set_all(v: [2, 3])
puts ShowSub.shown, ShowSub2.shown
p Sub.new([1]).set_all(v: [2]), Sub2[String].new(["a"]).set_all(v: ["b"])
"#,
    );
    let expected = "ids: Array[Int] (Array), name: String? (Object), tags: Hash[String, Array[Int]] (Hash), v: Int | String (Object)\ntrue\nids=[1, 2] name=nil v=\"s\"\ntags={\"a\" => [1]} v=3\n1\nv: Array[Int] (Array)\nv: Array[U] (Array)\n1\n1\n";
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let cold = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    let warm = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert!(
        out.contains("def with(*, ids: Array[Int] = …, name: String? = …, tags: Hash[String, Array[Int]] = …, v: Int | String = …) -> String"),
        "{out}"
    );
    assert!(out.contains("def set_all(*, v: Array[T]) -> Int"), "{out}");
    // An inherited field's type as the subclass has it: `G[Int]`'s `T` is
    // `Int` in `Sub`, and `G[U]`'s is `Sub2`'s own `U`.
    assert!(
        out.contains("def set_all(*, v: Array[Int]) -> Int"),
        "{out}"
    );
    assert!(out.contains("def set_all(*, v: Array[U]) -> Int"), "{out}");
    // A call is checked against the types in full.
    for (call, expected) in [
        (
            "K.new.with(ids: [\"x\"])",
            "array elements have type String but Int was expected",
        ),
        ("K.new.with(v: 1.5)", "expects Int | String but found Float"),
        (
            "K.new.with(tags: {\"a\" => [\"b\"]})",
            "array elements have type String but Int was expected",
        ),
        (
            "G[Int].new([1]).set_all(v: [\"s\"])",
            "array elements have type String but Int was expected",
        ),
        (
            "Sub.new([1]).set_all(v: [\"s\"])",
            "array elements have type String but Int was expected",
        ),
        (
            "Sub2[Int].new([1]).set_all(v: [\"s\"])",
            "array elements have type String but Int was expected",
        ),
    ] {
        let bad = write(
            &d.0,
            "bad.qz",
            &format!("require_relative \"lib\"\ndata P = (ids: Array[Int], name: String?, tags: Hash[String, Array[Int]], v: Int | String)\nclass K < Model\n  from_fields P\nend\nclass G[T] < Model\n  @v: Array[T]\n  def initialize(@v: Array[T]); end\n  own\nend\nclass Sub < G[Int]\n  own\nend\nclass Sub2[U] < G[U]\n  own\nend\n{call}\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
        assert!(!ok, "{call}");
        assert!(err.contains(expected), "{call}: {err}");
    }
    // What the statement refuses.
    write(
        &d.0,
        "lib2.qz",
        "class Lim[T <: Int]\nend\nclass Q\n  static def self.gen(ks: Array[Meta::Keyword]) -> Void\n    def_method(:m, keywords: ks) { |given| given.size }\n  end\nend\n",
    );
    for (ks, expected) in [
        (
            "[Meta::Keyword.typed(:t, Meta::TypeRef.of(Array), true)]",
            "the keyword `t`'s `type_ref`: `Array` takes 1 type argument, not 0",
        ),
        (
            "[Meta::Keyword.typed(:t, Meta::TypeRef::Union.new([]), true)]",
            "an empty union is no type",
        ),
        (
            "[Meta::Keyword.typed(:t, Meta::TypeRef::Other.new(\"(Int, Int)\"), true)]",
            "`(Int, Int)` cannot be a generated keyword's type yet",
        ),
        (
            "[Meta::Keyword.typed(:t, Meta::TypeRef::Param.new(Array, :T), true)]",
            "the type parameter `T` of `Array` is not one of `R`, the class generated into",
        ),
        (
            "[Meta::Keyword.new(:t, Int, true, false, Meta::TypeRef.of(String))]",
            "the keyword `t` is typed `Int` with a `type_ref` of `String`, whose class is `String`",
        ),
        (
            "[Meta::Keyword.new(:t, Object, true, true, Meta::TypeRef.of(String))]",
            "the keyword `t` has a `type_ref` and `nullable: true`",
        ),
        (
            "[Meta::Keyword.typed(:t, Meta::TypeRef.of(Lim, [Meta::TypeRef.of(String)]), true)]",
            "type argument String for `T` of `Lim` must be Int",
        ),
    ] {
        let bad = write(
            &d.0,
            "bad.qz",
            &format!("require_relative \"lib2\"\nclass R < Q\n  gen {ks}\nend\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
        assert!(!ok, "{ks}");
        assert!(err.contains(expected), "{ks}: {err}");
    }
}

/// `type` in a `static def` (docs/14 §4): the class the statement runs on
/// as a plain class value, which a generated method captures to call the
/// class's class methods, `Self` there being the class generated into
/// (a subclass that inherits the method gets that class). `self` itself
/// stays uncapturable.
#[test]
fn a_generated_method_builds_its_class_through_type() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  include Shareable\n  @n: Int\n  def initialize; @n = 0; end\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  def self.rebuild(n: Int) -> Self = new(n)\n  static def self.gen -> Void\n    cls = type\n    def_method(:bump) do -> Self\n      cls.rebuild(n + 1)\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass C < Base\n  gen\nend\nclass D < C\nend\nc: C = C.new.bump.bump\np c.n, c.class.name, D.new.bump.class.name\n",
    );
    let expected = "2\n\"C\"\n\"C\"\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    // The inherited method gives the class it was generated into.
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass C < Base\n  gen\nend\nclass D < C\nend\ny: D = D.new.bump\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(err.contains("cannot assign C to `y` of type D"), "{err}");
    // Another class's `Meta::ClassDef` is that class, not `Self`.
    write(
        &d.0,
        "lib3.qz",
        "class Base\n  include Shareable\n  @n: Int\n  def initialize; @n = 0; end\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  def self.rebuild(n: Int) -> Self = new(n)\n  static def self.me -> Meta::ClassDef[Base] = self\n  static def self.gen -> Void\n    c = Other.me.type\n    def_method(:bump) do -> Self\n      c.rebuild(n + 1)\n    end\n  end\nend\nclass Other < Base\nend\n",
    );
    let app3 = write(
        &d.0,
        "app3.qz",
        "require_relative \"lib3\"\nclass C < Base\n  gen\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app3.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("block returns Base but is declared `-> Self`"),
        "{err}"
    );
    // Nor is `type` captured by a method generated into another class.
    write(
        &d.0,
        "lib5.qz",
        "class Base\n  include Shareable\n  @n: Int\n  def initialize; @n = 0; end\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  def self.rebuild(n: Int) -> Self = new(n)\n  static def self.me -> Meta::ClassDef[Base] = self\n  static def self.gen -> Void\n    cls = type\n    Other.me.def_method(:bump) do -> Self\n      cls.rebuild(n + 1)\n    end\n  end\nend\nclass Other < Base\nend\n",
    );
    let app5 = write(
        &d.0,
        "app5.qz",
        "require_relative \"lib5\"\nclass C < Base\n  gen\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app5.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("but the method is generated into another class"),
        "{err}"
    );
    // ... nor through a block run on another class's `Meta::ClassDef`.
    write(
        &d.0,
        "lib6.qz",
        "class Base\n  include Shareable\n  @n: Int\n  def initialize; @n = 0; end\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  def self.rebuild(n: Int) -> Self = new(n)\n  static def self.me -> Meta::ClassDef[Base] = self\n  static def self.gen -> Void\n    t = type\n    Other.me.instance_exec do\n      def_method(:bump) do -> Self\n        t.rebuild(n + 1)\n      end\n    end\n  end\nend\nclass Other < Base\nend\n",
    );
    let app6 = write(
        &d.0,
        "app6.qz",
        "require_relative \"lib6\"\nclass C < Base\n  gen\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app6.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("but the method is generated into another class"),
        "{err}"
    );
    // In the static def itself, `type` is a `Type[Self]` of the class.
    write(
        &d.0,
        "lib4.qz",
        "class Base\n  include Shareable\n  @n: Int\n  def initialize; @n = 0; end\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  def self.rebuild(n: Int) -> Self = new(n)\n  def self.take(t: Type[Base]) -> String = t.name\n  static def self.gen -> Void\n    k: Type[Base] = type\n    v = type.rebuild(3).n + take(type).size\n    def_class_method(:v) { v }\n  end\nend\n",
    );
    let app4 = write(
        &d.0,
        "app4.qz",
        "require_relative \"lib4\"\nclass C < Base\n  gen\nend\np C.v\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app4.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "4\n");
    // `self` is not captured.
    write(
        &d.0,
        "lib2.qz",
        "class Base\n  static def self.gen -> Void\n    me = self\n    def_method(:k) { me.name }\n  end\nend\n",
    );
    let app2 = write(
        &d.0,
        "app2.qz",
        "require_relative \"lib2\"\nclass C < Base\n  gen\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app2.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("cannot be baked into a generated method"),
        "{err}"
    );
}

/// A generated method overriding a method that says `Self` keeps `Self`
/// (docs/01 §3): rotor's `Model#restore -> Self` overridden by a generated
/// `restore` whose block gives the class (`-> C`) is refused at the
/// statement; one declared `-> Self` is accepted.
#[test]
fn a_generated_override_keeps_self() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Model
  @n: Int
  def initialize(@n: Int); end
  def n -> Int = @n
  def self.rebuild(n: Int) -> Self = new(n)
  def restore -> Self = raise "abstract"
  def twice -> Self = restore
  static def self.gen -> Void
    cls = type
    def_method(:restore) do -> Self
      cls.rebuild(n * 2)
    end
  end
  static def self.gen_self -> Void
    def_method(:restore) do -> Self
      self
    end
  end
end
"##,
    );
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass C < Model\n  gen\nend\nclass D < C\n  @tag: String = \"d\"\n  def tag -> String = @tag\nend\ny: D = D.new(1).twice\np y.tag\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`restore` returns C but `Model#restore`, which it overrides, returns Self: write `Self`"),
        "{err}"
    );
    // A generated signature names the class where its block says `Self`
    // (docs/14 §5), so even a block giving `self` is refused there.
    let other = write(
        &d.0,
        "other.qz",
        "require_relative \"lib\"\nclass C < Model\n  gen_self\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", other.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`restore` returns C but `Model#restore`"),
        "{err}"
    );
}

/// `Self.new` in a block given to `def_method` (docs/14 §5): the generated
/// method builds its receiver's class; a subclass inheriting it keeps a
/// compatible `initialize`, as for a written one.
#[test]
fn self_new_in_a_generated_method() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  @n: Int\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  static def self.gen -> Void\n    def_method(:copy) do -> Self\n      Self.new(n + 1)\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass C < Model\n  gen\nend\nclass D < C\nend\nx = D.new(1).copy\np x.class, x.n\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "D\n2\n");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), "D\n2\n");
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass C < Model\n  gen\nend\nclass E < C\n  @s: String\n  def initialize(@s: String)\n    super(1)\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`E#initialize` does not take the arguments of `Self.new` in `C#copy`, which `E` inherits"),
        "{err}"
    );
}

/// `def_initialize` (docs/14 §5): `initialize` overloads generated from
/// blocks, one positional and one of keywords computed at compile time,
/// interpreted and compiled; a `super` in one, past a class that writes
/// no `initialize` (whose field defaults still run first); `Self.new` in
/// an inherited method, and `new` checked as for written overloads.
/// #1002 (c): a method or `initialize` generated with `keywords:` binds
/// any number of keywords: those past the 64th (beyond the activation's
/// 64-bit `provided` mask) are in the hash when given, required or
/// optional, and absent when an optional one is left out; the hash is in
/// the order of the parameters. Interpreted and compiled.
#[test]
fn generated_keywords_past_the_64th_are_bound() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Wide
  @seen: String = ""
  def seen -> String = @seen
  static def self.wide -> Void
    keys = (1..66).map { |i| Meta::Keyword.new(:"k#{i}", Int, i == 1 || i == 65) }
    def_method(:with, keywords: keys) do |given| -> String
      given.keys.map { |k| "#{k}=#{given[k]}" }.join(" ")
    end
    def_initialize(keywords: keys) do |given|
      @seen = given.keys.map { |k| "#{k}=#{given[k]}" }.join(" ")
    end
  end
end
"##,
    );
    let all = |base: i64| -> (String, String) {
        let args: Vec<String> = (1..=66).map(|i| format!("k{i}: {}", base + i)).collect();
        let seen: Vec<String> = (1..=66).map(|i| format!("k{i}={}", base + i)).collect();
        (args.join(", "), seen.join(" "))
    };
    let (new_all, new_all_seen) = all(0);
    let (with_all, with_all_seen) = all(100);
    let app = format!(
        "require_relative \"lib\"\nclass W < Wide\n  wide\nend\nw = W.new({new_all})\nputs w.seen\nputs W.new(k66: 66, k65: 65, k1: 1).seen\nputs W.new(k1: 1, k2: 2, k65: 65).seen\nputs w.with({with_all})\nputs w.with(k66: 166, k65: 165, k1: 101)\nputs w.with(k1: 101, k2: 102, k65: 165)\n"
    );
    write(&d.0, "app.qz", &app);
    let expected = format!(
        "{new_all_seen}\nk1=1 k65=65 k66=66\nk1=1 k2=2 k65=65\n{with_all_seen}\nk1=101 k65=165 k66=166\nk1=101 k2=102 k65=165\n"
    );
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[("QUARZ_VERIFY", "moves")]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

const INIT_LIB: &str = r##"data Point = (x: Int, y: Int)
class Base
  @point: Point
  @name: String
  @n: Int = 0
  def initialize(@point: Point)
    @name = "base"
  end
  def point -> Point = @point
  def name -> String = @name
  def n -> Int = @n
  def moved -> Self = Self.new(Point.new(@point.x + 1, @point.y))
  static def self.ctor(keys: Array[Meta::Keyword]) -> Void
    def_initialize(:point) do |pt: Point|
      super(pt)
      @n = 1
    end
    def_initialize(keywords: keys) do |given|
      @point = Point.new(0, 0)
      @name = given[:name].as(String)
      @n = given.key?(:n) ? given[:n].as(Int) : -1
    end
  end
end
"##;

const INIT_KEYS: &str =
    "[Meta::Keyword.new(:name, String, true), Meta::Keyword.new(:n, Int, false)]";

#[test]
fn generated_initialize_overloads() {
    let d = dir();
    write(&d.0, "lib.qz", INIT_LIB);
    let app = write(
        &d.0,
        "app.qz",
        &format!(
            r#"require_relative "lib"
class Mid < Base
  @tag: String = "mid"
  def tag -> String = @tag
end
class C < Mid
  ctor {INIT_KEYS}
end
a = C.new(Point.new(1, 2))
p a.point, a.name, a.n, a.tag
b = C.new(name: "x", n: 2)
p b.point, b.name, b.n, b.tag
p C.new(name: "y").n
m = a.moved
p m.class, m.point, m.n
"#
        ),
    );
    let expected = "Point(x: 1, y: 2)\n\"base\"\n1\n\"mid\"\nPoint(x: 0, y: 0)\n\"x\"\n2\n\"mid\"\n-1\nC\nPoint(x: 2, y: 2)\n1\n";
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let cold = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(cold.0, "{}", cold.2);
    let warm = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert_eq!(warm, cold);
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &env,
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert!(
        out.contains("def initialize(point: Point) -> Void = <block at lib.qz:14>")
            && out.contains(
                "def initialize(*, name: String, n: Int = …) -> Void = <block at lib.qz:18>"
            ),
        "{out}"
    );
    // Calls, checked as for written overloads.
    for (call, expected) in [
        ("C.new(name: 3)", "expects String but found Int"),
        ("C.new(name: \"a\", h: 2)", "has no parameter `h`"),
        ("C.new(n: 1)", "is missing the argument `name`"),
        ("C.new(5)", "expects Point but found Int"),
    ] {
        let bad = write(
            &d.0,
            "bad.qz",
            &format!("require_relative \"lib\"\nclass C < Base\n  ctor {INIT_KEYS}\nend\n{call}\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
        assert!(!ok, "{call}");
        assert!(err.contains(expected), "{call}: {err}");
    }
    // What the statement or the class refuses.
    for (body, expected) in [
        (
            format!("class C < Base\n  @extra: Int\n  ctor {INIT_KEYS}\nend\n"),
            "bad.qz:4:3: error: `def_initialize`: the `initialize` generated by `ctor` leaves `@extra` of `C` unassigned",
        ),
        (
            format!("class C < Base\n  ctor {INIT_KEYS}\n  ctor {INIT_KEYS}\nend\n"),
            "bad.qz:4:3: error: `def_initialize`: `C` already has an `initialize` with the same parameters (generated by an earlier `def_initialize`)",
        ),
        (
            format!("class C < Base\n  def initialize(point: Point)\n    super(point)\n  end\n  ctor {INIT_KEYS}\nend\n"),
            "bad.qz:6:3: error: `def_initialize`: `C` already has an `initialize` with the same parameters",
        ),
        // The class `super` would reach from `C` is not the one the block
        // was checked for.
        (
            format!("class Mid < Base\n  def initialize(s: String)\n    super(Point.new(s.size, 0))\n  end\nend\nclass C < Mid\n  ctor {INIT_KEYS}\nend\n"),
            "bad.qz:8:3: error: `def_initialize`: `super` in the `initialize` generated by `ctor` calls `Base#initialize`, but `super` in `C` reaches `Mid#initialize`",
        ),
        // `moved`'s `Self.new(point)` (docs/01 §9, #285): a subclass of
        // `C` with an `initialize` of its own that does not take it.
        (
            format!("class C < Base\n  ctor {INIT_KEYS}\nend\nclass D < C\n  def initialize(s: String)\n    super(name: s)\n  end\nend\n"),
            "bad.qz:6:3: error: `D#initialize` does not take the arguments of `Self.new` in `Base#moved`, which `D` inherits",
        ),
    ] {
        let bad = write(&d.0, "bad.qz", &format!("require_relative \"lib\"\n{body}"));
        let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
        assert!(!ok, "{body}");
        assert!(err.contains(expected), "{body}: {err}");
    }
    // A class that both writes and generates `initialize` has both.
    let both = write(
        &d.0,
        "both.qz",
        &format!("require_relative \"lib\"\nclass C < Base\n  def initialize(s: String)\n    super(Point.new(s.size, 9))\n  end\n  ctor {INIT_KEYS}\nend\np C.new(\"abc\").point, C.new(Point.new(5, 5)).n\n"),
    );
    let (ok, out, err) = quarz(&d.0, &["run", both.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "Point(x: 3, y: 9)\n1\n");
}

/// `raise K, msg` and `raise K` run a generated `initialize` taking a
/// String (docs/01 §13), as a written one.
#[test]
fn raise_with_a_generated_initialize() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class AppError < StandardError\n  static def self.coded(code: Int) -> Void\n    def_initialize(:message) do |m: String|\n      super(\"[#{code}] #{m}\")\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass NotFound < AppError\n  coded 404\nend\nbegin\n  raise NotFound, \"gone\"\nrescue NotFound => e\n  puts e.message\nend\nbegin\n  raise NotFound\nrescue NotFound => e\n  puts e.message\nend\n",
    );
    let expected = "[404] gone\n[404] NotFound\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
}

/// A generic module's `static def` generates an `initialize` whose block
/// cannot name the bound's fields (it is not in the class's body): it
/// assigns them through `super`.
#[test]
fn a_modules_def_initialize_calls_super() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  @id: Int\n  def initialize(@id: Int); end\nend\nmodule Gen[T <: Model]\n  static def self.gen(id: Int) -> Void\n    def_initialize { super(id) }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass K < Model\n  include Gen[K]\n  gen 5\nend\np K.new\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "#<K @id=5>\n");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), "#<K @id=5>\n");
}

/// A generated method that builds its class (`Self.new`, or `new` in a
/// class method) is checked again when a later `def_initialize` gives the
/// class overloads of its own, which hide the inherited `initialize` it
/// was checked against.
#[test]
fn a_later_def_initialize_is_checked_against_generated_news() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  @n: Int\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  static def self.dupper -> Void\n    def_method(:dup2) do -> Self\n      Self.new(n + 1)\n    end\n  end\n  static def self.maker -> Void\n    def_class_method(:make) { new(1) }\n  end\n  static def self.ctor(name: Symbol) -> Void\n    def_initialize(name) do |s: String|\n      @n = s.size\n    end\n  end\n  static def self.both -> Void\n    dupper\n    ctor(:s)\n  end\nend\n",
    );
    for (body, expected) in [
        (
            "  dupper\n  ctor :s\n",
            "app.qz:4:3: error: `def_initialize`: `C#initialize` does not take the arguments of `Self.new` in the generated `C#dup2`",
        ),
        (
            "  maker\n  ctor :s\n",
            "app.qz:4:3: error: `def_initialize`: `C#initialize` does not take the arguments of `new` in the generated `C.make`",
        ),
        (
            "  both\n",
            "app.qz:3:3: error: `def_initialize`: `C#initialize` does not take the arguments of `Self.new` in the generated `C#dup2`",
        ),
    ] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass C < Base\n{body}end\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{body}");
        assert!(err.contains(expected), "{body}: {err}");
    }
    // An `initialize` generated into a class between the one that builds
    // itself and the one `new` was checked for (through another class's
    // `Meta::ClassDef`).
    write(
        &d.0,
        "lib2.qz",
        "class Base\n  @n: Int\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  static def self.me -> Meta::ClassDef[Base] = self\n  static def self.dupper -> Void\n    def_method(:dup2) do -> Self\n      Self.new(n + 1)\n    end\n  end\n  static def self.ctor_on_mid -> Void\n    Mid.me.instance_exec do\n      def_initialize(:s) do |s: String|\n        @n = s.size\n      end\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib2\"\nclass Mid < Base\nend\nclass S < Mid\n  dupper\n  ctor_on_mid\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("app.qz:6:3: error: `def_initialize`: `Mid#initialize`, which `S` builds with, does not take the arguments of `Self.new` in the generated `S#dup2`"),
        "{err}"
    );
}

/// `initialize` and `deinitialize` have no method handle (docs/14 §5):
/// bound to a made object, the one would assign its immutable fields
/// again, the other run before the release that runs it.
#[test]
fn initialize_and_deinitialize_have_no_method_handle() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  @n: Int\n  def initialize(@n: Int); end\n  def n -> Int = @n\n  static def self.ctor -> Void\n    r = method_ref[(Int) -> Void](:initialize)\n    def_method(:re) do\n      r.bind(self).call(99)\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass C < Base\n  ctor\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("app.qz:3:3: error: `ctor` raised ArgumentError: `initialize` has no handle: it runs only from `new` and from `super` in an `initialize`"),
        "{err}"
    );
    // Nor has `deinitialize`, run once, when the object is released.
    write(
        &d.0,
        "lib.qz",
        "class Base\n  def deinitialize -> Void = puts \"bye\"\n  static def self.ctor -> Void\n    r = method_ref[() -> Void](:deinitialize)\n    def_method(:bye) { r.bind(self).call }\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("app.qz:3:3: error: `ctor` raised ArgumentError: `deinitialize` has no handle: it runs when the object is released; it cannot be called"),
        "{err}"
    );
}

/// `initialize` and `deinitialize` are no field names (docs/01 §3), for
/// `def_field` too; a generated `initialize` calls `super` once per path.
#[test]
fn reserved_field_names_and_one_super_when_generating() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  @n: Int\n  def initialize(@n: Int); end\n  static def self.field(name: Symbol) -> Void\n    def_field(name, Int, 0, reader: true)\n  end\n  static def self.twice -> Void\n    def_initialize(:x) do |x: Int|\n      super(x)\n      super(x)\n    end\n  end\nend\n",
    );
    let (ok, _, err) = quarz(
        &d.0,
        &[
            "check",
            write(
                &d.0,
                "app.qz",
                "require_relative \"lib\"\nclass C < Base\n  field :deinitialize\nend\nclass D < Base\n  field :initialize\nend\n",
            )
            .to_str()
            .unwrap(),
        ],
        &[],
    );
    assert!(!ok);
    for want in [
        "app.qz:3:3: error: `def_field(:deinitialize)`: `deinitialize` is a reserved name: the runtime runs it when the object is released",
        "app.qz:6:3: error: `def_field(:initialize)`: `initialize` is a reserved name: `new` runs it to make the object",
        "lib.qz:10:7: error: `super` runs the parent's `initialize` once: it is already called on this path",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
}

/// A generic method a `static def` calls carries the type parameters its
/// `Type[T]` parameters give (docs/14 §5): the generated signature says
/// the class the parameter had (`Box[Post]`), interpreted and compiled,
/// and the checker holds callers to it. A class that takes type
/// arguments cannot stand for one.
#[test]
fn a_helper_carries_the_classes_of_its_type_parameters() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Box[T]
  @v: T?
  def initialize(@v: T?); end
  def get -> T? = @v
end
class Base
  static def self.many(ts: Array[Type[Base]]) -> Void
    ts.each { |t| gen(t) }
  end
  private static def self.gen[T <: Base](t: Type[T]) -> Void
    def_method(t.name.downcase.to_sym) { Box[T].new(nil) }
    def_initialize(t.name.downcase.to_sym) { |x: T| }
    nested(t)
  end
  private static def self.nested[U](u: Type[U]) -> Void
    def_class_method("#{u.name.downcase}_class".to_sym) { u }
  end
  static def self.erased(t: Type[Object]) -> Void
    nested(t)
  end
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class Post < Base; end
class Note < Base; end
class User < Base
  many [Post, Note]
end
u = User.new(Post.new)
a: Box[Post] = u.post
b: Box[Note] = User.new(Note.new).note
c: Type[Post] = User.post_class
p a.get, b.class, c, u.class
"#,
    );
    let expected = "nil\nBox\nPost\nUser\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass Post < Base; end\nclass User < Base\n  many [Post]\nend\nx: Box[User] = User.new(Post.new).post\nUser.new(User.new(Post.new))\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    for expected in [
        "bad.qz:6:16: error: cannot assign Box[Post] to `x` of type Box[User]",
        "bad.qz:7:10: error: argument `post` of initialize(post: Post) -> Void expects Post but found User",
    ] {
        assert!(err.contains(expected), "missing {expected:?} in\n{err}");
    }
    let generic = write(
        &d.0,
        "generic.qz",
        "require_relative \"lib\"\nclass User < Base\n  erased Box\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", generic.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("generic.qz:3:3: error: `def_class_method(:box_class)`: `U` is `Box`, whose type arguments are not known here: pass them at the statement's call or use a class without type arguments"),
        "{err}"
    );
}

/// The statement's type arguments hold for a `static def` nothing but
/// statements call (a generic class keeps its arguments there); one that
/// code also calls (recursively, or in a statement's arguments) takes the
/// classes its `Type[T]` parameter holds in every invocation, and so do
/// a module's helpers, whose bounds name the module's `T`. What could let
/// another value of `T` in is not carried: a bound relating `T` to
/// another type parameter, a lower bound, an assignment of the
/// parameter, a call in a parameter's default; nor is a handle made with
/// a `T` there.
#[test]
fn carried_type_params_by_invocation_and_what_is_not_carried() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Box[X]
  def initialize; end
end
class Base
  static def self.rec[T](t: Type[T], n: Int, others: Array[Type[Object]]) -> Void
    def_method("item#{n}".to_sym) do -> Type[T]
      t
    end
    rec(others[0], n - 1, others) if n > 0
  end
  static def self.holder[T](t: Type[T]) -> Void
    def_method(:held, :y) do |y: T| -> String
      y.class.name
    end
  end
  static def self.counted[T](t: Type[T], n: Int = 0) -> Int
    def_method("counted#{n}".to_sym) do -> Type[T]
      t
    end
    n + 1
  end
  static def self.lower(ts: Array[Type[Dog]]) -> Void
    ts.each { |t| via_lower(t) }
  end
  private static def self.via_lower[T >: Dog](t: Type[T]) -> Void
    def_method(:lower_item) do -> T
      Dog.new
    end
  end
  static def self.handle[T](t: Type[T], n: Int) -> Void
    r = field_ref[T](:x)
    def_method("read#{n}".to_sym) do -> T
      r.get(self)
    end
    handle(t, n - 1) if n > 0
  end
  static def self.bounded(t: Type[Object]) -> Void
    via_bound(t, 42)
  end
  private static def self.via_bound[T, U <: T](t: Type[T], u: U) -> Void
    x: T = u
    def_method(:bound_item) do -> T
      x
    end
  end
  static def self.assigned(t: Type[Object]) -> Void
    via_assign(t)
  end
  private static def self.via_assign[T](t: Type[T]) -> Void
    t = t
    def_method(:assigned_item) do -> Type[T]
      t
    end
  end
  static def self.defaulted(t: Type[Object]) -> Void
    via_default(t: t)
  end
  private static def self.via_default[T](x: Int = def_method(:zz, :y) { |y: T| 1 }.name.size, *, t: Type[T]) -> Void
  end
end
module Macros[T]
  static def self.many(us: Array[Type[T]]) -> Void
    us.each { |u| has(u) }
  end
  static def self.has[U <: T](u: Type[U]) -> Void
    def_method(:macro_class) do -> Type[U]
      u
    end
  end
end
class Animal; end
class Dog < Animal; end
class Puppy < Dog; end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class User < Base
  rec String, 1, [Int]
  holder Box[Int]
  counted String, counted(Int, 5)
  # (A handle typed with a carried `T`, in each invocation, #918.)
  @x: String = "s"
  handle String, 1
end
class Post
  include Macros[Post]
  many [Post]
end
a: Type[String] = User.new.item1
b: Type[Int] = User.new.item0
c: Type[Int] = User.new.counted5
e: Type[String] = User.new.counted6
p a, b, User.new.held(Box[Int].new), c, e, Post.new.macro_class, User.new.read1, User.new.read0
"#,
    );
    let expected = "String\nInt\n\"Box\"\nInt\nString\nPost\n\"s\"\n\"s\"\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", "app.bin"],
        &[],
    );
    assert!(ok, "{err}");
    let out = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass User < Base\n  bounded String\n  assigned String\n  defaulted String\n  lower [Puppy]\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    for expected in [
        "bad.qz:3:3: error: `def_method(:bound_item)`: the block's type mentions `T`, a type parameter the generated method cannot carry",
        "bad.qz:4:3: error: `def_method(:assigned_item)`: the block's type mentions `T`, a type parameter the generated method cannot carry",
        "bad.qz:5:3: error: `def_method(:zz)`: the block's type mentions `T`, a type parameter the generated method cannot carry",
        "bad.qz:6:3: error: `def_method(:lower_item)`: the block's type mentions `T`, a type parameter the generated method cannot carry",
    ] {
        assert!(err.contains(expected), "missing {expected:?} in\n{err}");
    }
}

/// What a carried class could otherwise slip past: a `def_method` handle
/// typed by the generic method's `T` as its caller sees it (wider than
/// the method it names), a bound naming `Self` of a generic class, and a
/// `Type[T]` parameter rebound by a bang call.
#[test]
fn carried_classes_refused_where_they_could_mislead() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"extension Object
  def me -> Self = self
end
class Animal; end
class Dog < Animal; end
class Base
  static def self.go(t: Type[Animal]) -> Void
    h = inner(t)
    def_method(:m1, :y) do |y: Animal| -> String
      h.bind(self).call(y)
    end
  end
  private static def self.inner[U](u: Type[U]) -> Meta::Method[Base, (U) -> String]
    def_method(:m0, :y) do |y: U| -> String
      "base"
    end
  end
  static def self.selfish(t: Type[Base]) -> Void
    via_self(t)
  end
  private static def self.via_self[T <: Self](t: Type[T]) -> Void
    def_method(:item, :y) do |y: T| -> Self
      y
    end
  end
  static def self.banged(t: Type[Object]) -> Void
    via_bang(t)
  end
  private static def self.via_bang[T](t: Type[T]) -> Void
    t.me!
    def_method(:bang_item) do -> Type[T]
      t
    end
  end
end
"##,
    );
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass Post < Base; end\nclass User < Base\n  go Dog\n  banged String\nend\nclass Box[E] < Base\n  def initialize; end\n  selfish Post\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    for expected in [
        "bad.qz:4:3: error: `def_method(:m1)`: the handle to `User#m0` is typed with a type parameter its method took a carried class for",
        "bad.qz:5:3: error: `def_method(:bang_item)`: the block's type mentions `T`, a type parameter the generated method cannot carry",
        "bad.qz:9:3: error: `def_method(:item)`: `T` is `Post` here, which is not a `Box[E]`",
    ] {
        assert!(err.contains(expected), "missing {expected:?} in\n{err}");
    }
}

/// Whether a statement's type arguments hold does not depend on the
/// order of the statements: a `static def` the program also calls by its
/// name elsewhere takes only carried classes, whichever statement comes
/// first. A module's `static def` calling itself on its own `self` keeps
/// the module's `T`.
#[test]
fn statement_type_args_whatever_the_order() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"class Box[X]
  def initialize; end
end
class Base
  static def self.useit -> Void
    holder[String](:s) if 1 > 2
  end
  static def self.holder[T](name: Symbol) -> Void
    def_method(name) do -> Box[T]
      Box[T].new
    end
  end
end
module Macros[T]
  static def self.keep(n: Int) -> Void
    def_method("m#{n}".to_sym) do -> T?
      nil
    end
    keep(n - 1) if n > 0
  end
end
"##,
    );
    let mut errs = Vec::new();
    for order in [
        "class Post < Base\n  useit\nend\nclass User < Base\n  holder[Int](:ints)\nend\n",
        "class User < Base\n  holder[Int](:ints)\nend\nclass Post < Base\n  useit\nend\n",
    ] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\n{order}"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{order}");
        assert!(
            err.contains("`def_method(:ints)`: the block's type mentions `T`, a type parameter the generated method cannot carry"),
            "{err}"
        );
        errs.push(err.lines().filter(|l| l.contains("error")).count());
    }
    assert_eq!(errs[0], errs[1]);
    let app = write(
        &d.0,
        "mod.qz",
        "require_relative \"lib\"\nclass Note\n  include Macros[Note]\n  keep 1\nend\nb: Note? = Note.new.m0\np b, Note.new.m1\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "nil\nnil\n");
}

#[test]
fn a_shareable_method_handle_needs_a_shareable_self() {
    // `method_ref[P]` with a `shareable` `P`: `bind` gives a procedure
    // holding `self`, which may cross tasks only when the class promises
    // Shareable (docs/14 §5). A mutable model is refused (it lost updates
    // across tasks).
    let d = dir();
    write(&d.0, "lib.qz", "type SF = shareable () -> Int\nclass Model\n  var @n: Int = 0\n  def bump -> Int\n    @n += 1\n  end\n  def n -> Int = @n\n  static def self.gen -> Void\n    ref = method_ref[SF](:bump)\n    def_method(:bumper) do -> SF\n      ref.bind(self)\n    end\n  end\nend\n");
    let app = write(&d.0, "app.qz", "require_relative \"lib\"\nclass Post < Model\n  gen\nend\npost = Post.new\nf = post.bumper\nTask.scope do |s|\n  20000.times { s.spawn(&f) }\n  nil\nend\np post.n\n");
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("the handle to `Post#bump` is a `shareable () -> Int`, but `Post` is not Shareable: bound to its `self`, it would carry that `self` across tasks"),
        "{err}"
    );
    // A Shareable model's: 20,000 tasks bump it, on several workers.
    let d = dir();
    write(&d.0, "lib.qz", "type SF = shareable () -> Int\nclass Model\n  include Shareable\n  @n: Atom[Int] = Atom.new(0)\n  def bump -> Int = @n.update { |v| v + 1 }\n  def n -> Int = @n.get\n  static def self.gen -> Void\n    ref = method_ref[SF](:bump)\n    def_method(:bumper) do -> SF\n      ref.bind(self)\n    end\n    cref = class_method_ref[SF](:label)\n    def_class_method(:labeler) do -> SF\n      cref.bind(self)\n    end\n  end\n  def self.label -> Int = 7\nend\n");
    let app = write(&d.0, "app.qz", "require_relative \"lib\"\nclass Post < Model\n  gen\nend\npost = Post.new\nf = post.bumper\nTask.scope do |s|\n  20000.times { s.spawn(&f) }\n  nil\nend\np post.n\ng = Post.labeler\np Task.spawn(&g).await\n");
    let (ok, out, err) = quarz(
        &d.0,
        &["run", app.to_str().unwrap()],
        &[("QUARZ_THREADS", "4")],
    );
    assert!(ok, "{err}");
    assert_eq!(out, "20000\n7\n");
    // A class method's `self` is a class value, Shareable whatever the
    // class: `class_method_ref` with a `shareable` type is accepted.
    let d = dir();
    write(&d.0, "lib.qz", "type SF = shareable () -> Int\nclass Model\n  var @n: Int = 0\n  def self.label -> Int = 7\n  static def self.gen -> Void\n    cref = class_method_ref[SF](:label)\n    def_class_method(:labeler) do -> SF\n      cref.bind(self)\n    end\n  end\nend\n");
    let app = write(&d.0, "app.qz", "require_relative \"lib\"\nclass Post < Model\n  gen\nend\ng = Post.labeler\np Task.spawn(&g).await\n");
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "7\n");
}
