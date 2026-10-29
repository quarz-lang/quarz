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
  static def self.helper[U <: Model](name: Symbol, t: Type[U]) -> Void
    def_method(name) { t }
  end
  static def self.free_param(target: Type[Model]) -> Void
    helper(:via_helper, target)
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
end
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Model\n  init\n  ctor\n  untyped :u\n  dup :d\n  big :b\n  eq\n  sealed\nend\nclass B < Model\n  splat :s\nend\n",
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
  static def self.dup -> Void
    def_field(:id, Int, 0)
  end
  static def self.writer_only -> Void
    def_field(:w, Int, 0, writer: true)
  end
  static def self.clash -> Void
    def_field(:id2, Int, 0, reader: true)
  end
end
module Macros
  static def has(x: Int) -> Void; end
end
data Point = (x: Int, y: Int)
"##,
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Model\n  def id2 -> Int = 1\n  generic\n  dup\n  writer_only\n  clash\nend\nclass B\n  extend Macros\n  has 1\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    for expected in [
        "app.qz:4:3: error: `def_field(:tags)`: `Array` takes type arguments, which a `Type` value does not carry",
        "app.qz:5:3: error: `def_field(:id)`: `A` already has a field `@id`",
        "app.qz:6:3: error: `writer_only` raised ArgumentError: writer: needs var: true, an assignable field",
        "app.qz:7:3: error: `def_field(:id2)`: `A` already has a method `id2`",
        "app.qz:11:3: error: `has` is a `static def` of the module `Macros`, reached through `extend`, which a statement cannot call yet: declare it as a class method (`static def self.has`) of a superclass",
    ] {
        assert!(err.contains(expected), "missing {expected:?} in\n{err}");
    }
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
    doc "Names `Post#nope_#{n}`."
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
    let expected = "Outer(s: \"a\", p: Pt(x: 1, y: 2), n: 3.0)\nCust(x: 3)\n/a/b\\/c/i\nHeld(p: Pt(x: 4, y: 8), s: \"n4\")\n";
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
    assert!(out.contains("Names Post#nope_title."), "{out}");
    assert!(out.contains("(from Base)"), "{out}");
    assert!(!out.contains("statement's comment"), "{out}");
    // `--check` reads every generated doc, at its statement.
    let (_, out, err) = quarz(&d.0, &["doc", "app.qz", "--check"], &[]);
    let all = format!("{out}{err}");
    assert!(
        all.contains("app.qz:5: warning: `Post#nope_title`"),
        "{all}"
    );
    assert!(all.contains("app.qz:6: warning: `Post#nope_body`"), "{all}");
}
