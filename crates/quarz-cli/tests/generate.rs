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
