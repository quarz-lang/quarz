//! Class bodies' `static` statements run at compile time (docs/14):
//! through the `quarz` command, which has the interpreter for them.

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
        "quarz-static-{}-{}",
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

const LIB: &str = r##"class Model
  static def self.has_many(target: Type[Model]) -> Void
    puts "#{name} has many #{target.name}: #{fields.map(&:name).inspect}"
    raise ArgumentError, "#{target.name} has no #{name.downcase}_id" unless target.field("#{name.downcase}_id".to_sym)
  end
  static def self.twice(x: Int) -> Int = x * 2
  static def self.count_fields -> Int = fields.size
  static def self.read_schema -> Void
    puts File.read("schema")
  end
  static def self.spin -> Void
    i = 0
    while true
      i += 1
    end
  end
end
"##;

#[test]
fn a_static_statement_runs_at_compile_time() {
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Comment < Model\n  @post_id: Int\n  def initialize(@post_id: Int); end\nend\nclass Post < Model\n  @title: String\n  def initialize(@title: String); end\n  has_many Comment\nend\nputs Model.twice(21)\n",
    );
    // `check` runs the statement (its output goes to standard error) and
    // accepts the program; `run` then runs the program.
    let (ok, out, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "");
    assert_eq!(err, "Post has many Comment: [:title]\n");
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "42\n");
    assert_eq!(err, "Post has many Comment: [:title]\n");
    // Compiled, the program runs the same: the statement ran in the
    // compiler, and the executable has none of the reflection.
    let exe = d.0.join("app-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "42\n");
    let bytes = std::fs::read(&exe).unwrap();
    let needle = b"Type#fields";
    assert!(
        !bytes.windows(needle.len()).any(|w| w == needle),
        "the executable embeds the reflection native"
    );
}

#[test]
fn what_a_static_statement_may_not_do() {
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Post < Model\n  has_many Post\nend\nclass Note < Model\n  read_schema\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    // `raise` is an error at the statement, with the message and where it
    // was raised.
    assert!(
        err.contains("app.qz:3:3: error: `has_many` raised ArgumentError: Post has no post_id"),
        "{err}"
    );
    assert!(err.contains("from lib.qz:4:in Model#has_many"), "{err}");
    // Reaching the outside world is refused before running.
    assert!(
        err.contains("app.qz:6:3: error: `read_schema` reaches `File.read`, which cannot run at compile time"),
        "{err}"
    );
    // The time limit.
    let app = write(
        &d.0,
        "spin.qz",
        "require_relative \"lib\"\nclass Loop < Model\n  spin\nend\n",
    );
    let (ok, _, err) = quarz(
        &d.0,
        &["check", app.to_str().unwrap()],
        &[("QUARZ_STATIC_LIMIT_MS", "200")],
    );
    assert!(!ok);
    assert!(
        err.contains("`spin` raised RuntimeError: compile-time evaluation took too long"),
        "{err}"
    );
    // A `static def` of the same file.
    let app = write(
        &d.0,
        "same.qz",
        "require_relative \"lib\"\nclass Base\n  static def self.own -> Void; end\nend\nclass K < Base\n  own\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("same.qz:6:3: error: `own` is a `static def` of this file"),
        "{err}"
    );
    // A run-time call of a compile-time-only one (decided after lowering,
    // once the program checks otherwise); `check` and `run` agree.
    let app = write(
        &d.0,
        "only.qz",
        "require_relative \"lib\"\nputs Model.twice(1)\nputs Model.count_fields\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("only.qz:3:6: error: `count_fields` runs at compile time only"),
        "{err}"
    );
    let (ok2, _, err2) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(!ok2);
    assert_eq!(err, err2);
}

const LIB2: &str = r##"class Model
  def self.hook -> String = "model"
  def self.helper(x: Int) -> Int = x * LIMIT
  static def self.setup -> Void
    puts "setup: #{hook} / #{helper(2)}"
  end
  static def self.go -> Void
    puts "go: #{hook}"
  end
  static def self.build -> Self = new
  static def self.forever -> Void
    loop { }
  end
end
LIMIT = 10
"##;

#[test]
fn what_a_statement_reaches_is_checked_and_lowered_on_demand() {
    let d = dir();
    write(&d.0, "lib2.qz", LIB2);
    // The helpers and the subclass's override are not checked yet when
    // the statement runs: they are checked and lowered for it, the same
    // whether or not the files' checks were cached.
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib2\"\nclass Post < Model\n  def initialize; end\n  def self.hook -> String = \"post\"\n  setup\nend\nputs Model.helper(1)\n",
    );
    for _ in 0..2 {
        let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
        assert!(ok, "{err}");
        assert_eq!(out, "10\n");
        assert_eq!(err, "setup: post / 20\n");
    }
    // An override reaching the outside world is refused like a direct
    // call, and so is a native that loops over a block.
    let app = write(
        &d.0,
        "over.qz",
        "require_relative \"lib2\"\nclass P < Model\n  def self.hook -> String = File.read(\"/etc/hostname\")\n  go\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("over.qz:4:3: error: `go` reaches `File.read` (via P.hook), which cannot run at compile time"),
        "{err}"
    );
    let app = write(
        &d.0,
        "forever.qz",
        "require_relative \"lib2\"\nclass P < Model\n  forever\nend\n",
    );
    let (ok, _, err) = quarz(
        &d.0,
        &["check", app.to_str().unwrap()],
        &[("QUARZ_STATIC_LIMIT_MS", "200")],
    );
    assert!(!ok);
    assert!(
        err.contains("`forever` raised RuntimeError: compile-time evaluation took too long"),
        "{err}"
    );
    // A statement that is not a call of a `static def` class method.
    let app = write(&d.0, "notcall.qz", "class P\n  raise \"boom\"\nend\n");
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("notcall.qz:2:3: error: a statement in a class body must call a `static def` class method"),
        "{err}"
    );
    // `new` in a `static` class method constructs the class it runs on.
    let app = write(
        &d.0,
        "build.qz",
        "require_relative \"lib2\"\nclass P < Model\n  def initialize; end\nend\np P.build.class.name\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"P\"\n");
}

/// What a construction reaches at compile time: `C.new` runs `C`'s own
/// `initialize` (and those it calls with `super`), not every class's,
/// while `new` on a class method's receiver may build a subclass, whose
/// `initialize` counts (tmp/repro/static-reach-initialize-overapprox.qz).
#[test]
fn a_construction_reaches_its_own_initialize() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Reader\n  @first: Bytes\n  def initialize(io: IO)\n    @first = io.read_bytes(1)\n  end\nend\nclass Box\n  @n: Int\n  def initialize(@n: Int); end\n  def n -> Int = @n\nend\nclass Child < Box\n  def initialize(n: Int)\n    super(n + 1)\n  end\nend\nclass Base\n  static def self.make(n: Int) -> Void\n    k = Box.new(n).n + Child.new(n).n\n    raise ArgumentError, \"negative\" if k < 0\n    def_class_method(:k) { k }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass C < Base\n  make 3\nend\np C.k\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "7\n");
    // `new` in a class method builds the class it is called on, which may
    // be a subclass reaching the outside world.
    write(
        &d.0,
        "lib3.qz",
        "class Base\n  def initialize; end\n  def self.build -> Base = new\n  static def self.make -> Void\n    build\n    def_class_method(:k) { 1 }\n  end\nend\nclass Reader < Base\n  @first: Bytes = b\"\"\n  def initialize\n    @first = STDIN.read_bytes(1)\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "build.qz",
        "require_relative \"lib3\"\nclass C < Base\n  make\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("build.qz:3:3: error: `make` reaches `IO#read_bytes` (via Base.build, Reader#initialize), which cannot run at compile time"),
        "{err}"
    );
    // What building an object also runs: its fields' defaults, and its
    // `deinitialize` when it is released.
    for (body, want) in [
        (
            "@r: Bytes = STDIN.read_bytes(1)",
            "`make` reaches `IO#read_bytes`, which",
        ),
        (
            "def deinitialize\n    STDOUT.puts \"bye\"\n  end",
            "`make` reaches `IO#puts` (via Holder#deinitialize), which",
        ),
    ] {
        write(
            &d.0,
            "lib4.qz",
            &format!("class Holder\n  {body}\n  def n -> Int = 1\nend\nclass Base\n  static def self.make -> Void\n    k = Holder.new.n\n    def_class_method(:k) {{ k }}\n  end\nend\n"),
        );
        let app = write(
            &d.0,
            "held.qz",
            "require_relative \"lib4\"\nclass C < Base\n  make\nend\n",
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{body}");
        assert!(
            err.contains(&format!("held.qz:3:3: error: {want}")),
            "{body}: {err}"
        );
    }
}

/// A symbol is a method's name only where a call says so: a symbol value
/// (`:count` as a hash key) reaches no method of its name, while a call
/// by name (a union's members' methods, `&:name`) reaches them all
/// (tmp/repro/static-reach-symbol-constant.qz).
#[test]
fn a_symbol_value_reaches_no_method() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Counter\n  def count -> Int = STDIN.read_bytes(1).size\nend\nclass A\n  def go -> Int = 1\nend\nclass B\n  def go -> Int = STDIN.read_bytes(1).size\nend\nclass Base\n  static def self.make -> Void\n    h = {count: 1, to_s: 2}\n    k = h[:count]? || 0\n    def_class_method(:k) { k }\n  end\n  static def self.union(flag: Bool) -> Void\n    x: A | B = flag ? A.new : B.new\n    k = x.go\n    def_class_method(:u) { k }\n  end\n  static def self.procs -> Void\n    xs: Array[A | B] = [A.new]\n    k = xs.map(&:go).sum\n    def_class_method(:p) { k }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass C < Base\n  make\nend\np C.k\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "1\n");
    for call in ["union true", "procs"] {
        let app = write(
            &d.0,
            "byname.qz",
            &format!("require_relative \"lib\"\nclass C < Base\n  {call}\nend\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{call}");
        assert!(
            err.contains("reaches `IO#read_bytes` (via B#go), which cannot run at compile time"),
            "{call}: {err}"
        );
    }
}

/// The runtime's own calls by name count as reached for the check that
/// no method with errors runs: an interpolation's `to_s` of a class whose
/// `to_s` failed its check is refused before the statement runs (it ran
/// before). A sort's `<=>`, an interpolation's `to_s` or a key's `==`
/// reaching IO is stopped at the native, as before.
#[test]
fn a_method_with_errors_does_not_run_through_the_runtime() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class B\n  include Comparable[B]\n  def <=>(o: B) -> Int = STDIN.read_bytes(1).size\nend\nclass S\n  def to_s -> String = STDIN.read_bytes(1).to_s\nend\nclass K\n  def ==(o: Object) -> Bool = STDIN.read_bytes(1).size > 0\n  def hash -> Int = 1\nend\nclass Base\n  static def self.sorting -> Void\n    k = [B.new, B.new].sort.size\n    def_class_method(:a) { k }\n  end\n  static def self.interp -> Void\n    k = \"#{S.new}\".size\n    def_class_method(:b) { k }\n  end\n  static def self.hashing -> Void\n    k = {K.new => 1, K.new => 2}.size\n    def_class_method(:c) { k }\n  end\nend\n",
    );
    write(
        &d.0,
        "lib_bad.qz",
        "class Bad\n  def to_s -> String\n    n: Int = \"oops\"\n    \"bad\"\n  end\nend\nclass BadBase\n  static def self.broken -> Void\n    k = \"#{Bad.new}\".size\n    def_class_method(:d) { k }\n  end\nend\n",
    );
    for (call, want) in [
        (
            "sorting",
            "`sorting` raised RuntimeError: `Process.stdin` cannot run at compile time",
        ),
        (
            "interp",
            "`interp` raised RuntimeError: `Process.stdin` cannot run at compile time",
        ),
        (
            "hashing",
            "`hashing` raised RuntimeError: `Process.stdin` cannot run at compile time",
        ),
        (
            "broken",
            "`broken` did not run: it may reach `Bad#to_s` (lib_bad.qz:2), which has errors: ",
        ),
    ] {
        let (lib, base) = if call == "broken" {
            ("lib_bad", "BadBase")
        } else {
            ("lib", "Base")
        };
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"{lib}\"\nclass C < {base}\n  {call}\nend\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{call}");
        assert!(err.contains(want), "{call}: {err}");
    }
    // What reaches nothing of the kind still runs.
    write(&d.0, "lib2.qz", "class Fine\n  def to_s -> String = \"fine\"\nend\nclass Base\n  static def self.fine -> Void\n    k = \"#{Fine.new} #{[3, 1].sort} #{{1 => 2}}\"\n    def_class_method(:e) { k }\n  end\nend\n");
    let app = write(
        &d.0,
        "fine.qz",
        "require_relative \"lib2\"\nclass C < Base\n  fine\nend\np C.e\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"fine [1, 3] {1 => 2}\"\n");
}

#[test]
fn a_statement_reaches_call_targets_and_their_overrides() {
    // The statement's `String.build` reaches `String.build`, not every
    // `build`: a test class's, whose body uses what the statement would
    // generate, does not block it (docs/14 §7).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  static def self.table(name: String) -> Void\n    s = String.build { |b| b << name }\n    def_method(:table_name) { s }\n  end\n  def label -> String = \"m\"\n  static def self.shown(x: Model) -> Void\n    s = x.label\n    def_method(:shown_as) { s }\n  end\nend\n",
    );
    write(
        &d.0,
        "m.qz",
        "require_relative \"lib\"\nclass Post < Model\n  table \"posts\"\nend\n",
    );
    let app = write(
        &d.0,
        "spec.qz",
        "require_relative \"m\"\nclass Spec\n  def build -> String = Post.new.table_name\n  def name -> String = Post.new.table_name\nend\np Spec.new.build\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"posts\"\n");
    // A call resolved to `Model#label` may run any override: one whose
    // body uses what a statement would generate blocks it, named with
    // its first error.
    write(
        &d.0,
        "m2.qz",
        "require_relative \"lib\"\nclass Post < Model\n  table \"posts\"\nend\nclass Note < Model\n  shown Model.new\nend\n",
    );
    let app2 = write(
        &d.0,
        "spec2.qz",
        "require_relative \"m2\"\nclass Spec < Model\n  def label -> String = Note.new.shown_as\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app2.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`shown` did not run: it may reach `Spec#label` (spec2.qz:3), which has errors: undefined method `shown_as` for Note"),
        "{err}"
    );
    // The method's own error is reported, once.
    assert_eq!(
        err.matches("spec2.qz:3:25: error: undefined method `shown_as` for Note")
            .count(),
        1,
        "{err}"
    );
    // A method without errors of its own that uses a constant whose
    // initializer has some: the constant's error is quoted, as what it
    // uses.
    let app3 = write(
        &d.0,
        "spec3.qz",
        "require_relative \"m2\"\nK = nosuch_thing\nclass Spec < Model\n  def label -> String\n    puts K\n    \"x\"\n  end\nend\n",
    );
    let (ok, _, err3) = quarz(
        &d.0,
        &["check", app3.to_str().unwrap()],
        &[("QUARZ_NO_CACHE", "1")],
    );
    assert!(!ok);
    assert!(
        err3.contains("`shown` did not run: it may reach `Spec#label` (spec3.qz:4), which uses what has errors: undefined local variable or method `nosuch_thing` for main (spec3.qz:2)"),
        "{err3}"
    );
}

#[test]
fn a_statement_reaches_what_dispatch_may_find() {
    // A call resolved to a module's method, a class method or one class
    // objects answer reaches every method of the name; another class's
    // instance method, those below it and the modules a class below it
    // includes (docs/14 §7): an implementation inherited from a
    // superclass, a module included in a subclass, a class's own
    // `def self.` over an extended module's or `Type`'s (a
    // `Meta::ClassDef`'s in a static def, whose `self` is the class), an
    // abstract method's implementation above it.
    for (lib, app, want) in [
        ("module Shape\n  abstract def area -> Int\n  def describe -> String = \"area #{area}\"\nend\nclass Base\n  def area -> Int = 7\nend\nclass Sq < Base\n  include Shape\nend\nclass Model\n  static def self.show(s: Shape) -> Void\n    puts s.describe\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show Sq.new\nend\n", "area 7\n"),
        ("module Loud\n  def label -> String = \"loud\"\nend\nclass A\n  def label -> String = \"a\"\nend\nclass B < A\n  include Loud\nend\nclass Model\n  static def self.show(k: A) -> Void\n    puts k.label\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show B.new\nend\n", "loud\n"),
        ("module Named\n  def label -> String = \"base\"\nend\nclass A\n  extend Named\nend\nclass B < A\n  def self.label -> String = \"B\"\nend\nclass Model\n  static def self.show(k: Type[A]) -> Void\n    puts k.label\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show B\nend\n", "B\n"),
        ("class A\n  def self.name -> String = \"customA\"\nend\nclass Model\n  static def self.show(k: Type[Object]) -> Void\n    puts k.name\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show A\nend\n", "customA\n"),
        ("class Model\n  static def self.show -> Void\n    puts type.name\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  def self.type -> Type[Post]\n    puts \"own type\"\n    Post\n  end\n  show\nend\n", "own type\nPost\n"),
        ("module Typed\n  def type -> Type[Object]\n    puts \"typed\"\n    Object\n  end\nend\nclass Model\n  static def self.show -> Void\n    puts type.name\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  extend Typed\n  show\nend\n", "typed\nObject\n"),
        ("class Base\n  def label -> String = \"base\"\nend\nabstract class A < Base\n  abstract def label -> String\nend\nclass B < A\nend\nclass Model\n  static def self.show(k: A) -> Void\n    puts k.label\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show B.new\nend\n", "base\n"),
    ] {
        let d = dir();
        write(&d.0, "lib.qz", lib);
        let app = write(&d.0, "app.qz", app);
        let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
        assert!(ok, "{err}");
        assert_eq!(err, want);
    }
    // So a method with errors found that way blocks the statement, as one
    // found directly does.
    let d = dir();
    write(&d.0, "lib.qz", "module Shape\n  abstract def area -> Int\n  def describe -> String = \"area #{area}\"\nend\nclass Model\n  static def self.show(s: Shape) -> Void\n    puts s.describe\n  end\n  static def self.direct(b: Base) -> Void\n    puts b.area\n  end\nend\n");
    let app = write(&d.0, "app.qz", "require_relative \"lib\"\nclass Base\n  def area -> Int\n    puts \"running broken\"\n    nosuch\n    7\n  end\nend\nclass Sq < Base\n  include Shape\nend\nclass Post < Model\n  direct Base.new\n  show Sq.new\nend\n");
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`show` did not run: it may reach `Base#area` (app.qz:3), which has errors"),
        "{err}"
    );
}

#[test]
fn a_class_typed_receiver_bounds_the_overrides_reached() {
    // A call on a receiver whose static type is a class reaches the
    // overrides an instance of the class or of a subclass may run, and
    // the body of a module's method so reached has that receiver as its
    // `self` (docs/14 §7): `[[1], [2]].flat_map` reaches neither `Rows`'s
    // `flat_map` nor, in `Enumerable#flat_map`, its `each` (#379).
    let rows = "class Rows\n  include Enumerable[Int]\n  def each(&: (Int) -> Void) -> Void\n    File.read(\"/etc/hostname\").size.times { |i| yield i }\n  end\n  def flat_map[U](&: (Int) -> Array[U]) -> Array[U]\n    File.read(\"/etc/hostname\")\n    []\n  end\nend\nclass Base\n  def label -> String = \"base\"\nend\nclass B < Base\n  def label -> String = File.read(\"/etc/hostname\")\nend\n";
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        &format!("{rows}class Model\n  static def self.gen -> Void\n    xs = [[1], [2]].flat_map {{ |a| a }}\n    def_class_method(:total) {{ xs.size }}\n  end\nend\n"),
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass App < Model\n  gen\nend\np App.total\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "2\n");
    let exe = d.0.join("app-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "2\n");
    // A receiver typed by the module (the module's method's `self` calls
    // too), by `Rows` itself, or by a class a subclass of which
    // overrides the method keeps those overrides: refused.
    for (gen, arg, via) in [
        (
            "static def self.gen(e: Enumerable[Int]) -> Void\n    xs = e.flat_map { |a| [a] }\n    def_class_method(:total) { xs.size }\n  end",
            "[1, 2]",
            "Rows#flat_map",
        ),
        (
            "static def self.gen(e: Enumerable[Int]) -> Void\n    xs = e.to_a\n    def_class_method(:total) { xs.size }\n  end",
            "[1, 2]",
            "Rows#each",
        ),
        (
            "static def self.gen(e: Rows) -> Void\n    xs = e.flat_map { |a| [a] }\n    def_class_method(:total) { xs.size }\n  end",
            "Rows.new",
            "Rows#",
        ),
        (
            "static def self.gen(e: Base) -> Void\n    s = e.label\n    def_class_method(:total) { s.size }\n  end",
            "Base.new",
            "B#label",
        ),
        // A lambda with a receiver runs on what it is given, not on the
        // `self` of the method it is written in (whose bound is
        // `Runner`'s here).
        (
            "static def self.gen -> Void\n    s = Runner.new.run(B.new)\n    def_class_method(:total) { s.size }\n  end\nend\nclass Runner\n  def run(b: Base) -> String\n    f: Base.() -> String = -> { label }\n    b.instance_exec(&f)\n  end",
            "",
            "B#label",
        ),
        // A `super` in a block with a receiver runs on the method's
        // `self` (#384): its method is walked with the bound of `P#go`'s
        // `self`, here `P3`, whatever the receiver.
        (
            "static def self.gen -> Void\n    s = P3.new.go(P2.new)\n    def_class_method(:total) { s.size }\n  end\nend\nclass Q\n  def label -> String = \"q\"\n  def go(s: P) -> String = label\nend\nclass H\n  def with(s: P, &b: P.() -> String) -> String = s.instance_exec(&b)\nend\nclass P < Q\n  def go(s: P) -> String = H.new.with(s) { super(s) }\nend\nclass P2 < P\nend\nclass P3 < P\n  def label -> String = File.read(\"/etc/hostname\")",
            "",
            "P3#label",
        ),
        // So does a block given to `instance_exec` with keywords.
        (
            "static def self.gen -> Void\n    s = Runner.new.run(B.new)\n    def_class_method(:total) { s.size }\n  end\nend\nclass Runner\n  def run(b: Base) -> String\n    b.instance_exec(k: 1) { |*, k| label }\n  end",
            "",
            "B#label",
        ),
    ] {
        let d = dir();
        write(
            &d.0,
            "lib.qz",
            &format!("{rows}class Model\n  {gen}\nend\n"),
        );
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass App < Model\n  gen {arg}\nend\np App.total\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
        assert!(!ok);
        let line = err.lines().next().unwrap_or("");
        assert!(
            line.starts_with("app.qz:3:3: error: `gen` reaches `File.read` (via ")
                && line.contains(via),
            "{err}"
        );
    }
}

#[test]
fn an_array_receiver_does_not_reach_another_classs_method_of_the_name() {
    // `names.find { }` on an `Array[Symbol]` reaches `Enumerable#find`
    // and what an `Array` runs, not `C#find`, which has errors until a
    // later statement generates `H.helper` (#386).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Gen\n  def pick(names: Array[Symbol]) -> Symbol? = names.find { |n| n == :b }\n\n  static def self.make -> Void\n    found = new.pick([:a, :b])\n    def_class_method(:found) { found.to_s }\n  end\nend\n\nclass HelperGen\n  static def self.helpers -> Void\n    def_class_method(:helper) { 1 }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "main.qz",
        "require_relative \"lib\"\n\nclass M < Gen\n  make\nend\n\nclass C\n  def find(x: Int) -> Int = H.helper + x\nend\n\nclass H < HelperGen\n  helpers\nend\n\np M.found\np C.new.find(1)\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"b\"\n2\n");
    let exe = d.0.join("main-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "\"b\"\n2\n");
}

#[test]
fn a_round_lowers_and_checks_what_its_statement_reaches() {
    // `touch` reached `Base#dispatch`; `wire` then generated `A#dispatch`,
    // which calls `A#act`, whose `H.helper` a later statement generates.
    // `mark` reaches nothing of `Base`: its round neither lowers nor
    // checks `A#act`, so the check does not run before `helpers` and
    // `mark` is not blamed for it (#387; docs/14 §7).
    let lib = "class Base\n  def dispatch -> Int = 0\n  def self.make -> Base = new\n  static def self.touch -> Void\n    n = Base.make.dispatch\n    def_class_method(:touched) { n }\n  end\n  static def self.wire -> Void\n    h = method_ref[() -> Int](:act)\n    def_method(:dispatch) { h.bind(self).call }\n  end\nend\nclass Plain\n  static def self.mark -> Void\n    def_class_method(:marked) { 1 }\n  end\nend\nclass HelperGen\n  static def self.helpers -> Void\n    def_class_method(:helper) { 1 }\n  end\nend\n";
    let d = dir();
    write(&d.0, "lib.qz", lib);
    let app = write(
        &d.0,
        "main.qz",
        "require_relative \"lib\"\nclass S1 < Base\n  touch\nend\nclass A < Base\n  wire\n  def act -> Int = H.helper\nend\nclass P < Plain\n  mark\nend\nclass H < HelperGen\n  helpers\nend\np A.new.dispatch\np P.marked\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "1\n1\n");
    let exe = d.0.join("main-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "1\n1\n");
    // A statement that does reach it before `helpers` ran (`touch` after
    // `wire`, through `Base#dispatch`'s override) is still refused: the
    // order of the statements (docs/14 §2).
    let d = dir();
    write(&d.0, "lib.qz", lib);
    let app = write(
        &d.0,
        "main.qz",
        "require_relative \"lib\"\nclass A < Base\n  wire\n  def act -> Int = H.helper\nend\nclass S2 < Base\n  touch\nend\nclass H < HelperGen\n  helpers\nend\np A.new.dispatch\n",
    );
    let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("main.qz:7:3: error: `touch` did not run: it may reach `A#act` (main.qz:4), which has errors: undefined method `helper` for Type[H]"),
        "{err}"
    );
}

#[test]
fn a_statement_reaches_dispatch_one_step() {
    // What dispatch may find for a call, not what it may find for those
    // in turn (`Loud#label` reached for `A#label`, not every `label`),
    // and a `super` its method alone: an unrelated `Spec#label` with
    // errors does not block the statement.
    for (lib, app, want) in [
        ("module Loud\n  def label -> String = \"loud\"\nend\nclass A\n  def label -> String = \"a\"\nend\nclass B < A\n  include Loud\nend\nclass Model\n  static def self.show(k: A) -> Void\n    s = k.label\n    def_method(:shown_as) { s }\n  end\nend\n", "require_relative \"lib\"\nclass Note < Model\n  show B.new\nend\nclass Spec\n  def label -> String = Note.new.shown_as\nend\np Spec.new.label\n", "\"loud\"\n"),
        ("class Base\n  def label -> String = \"base\"\nend\nclass B < Base\n  def label -> String = \"b+\" + super\nend\nclass Model\n  static def self.show(k: B) -> Void\n    s = k.label\n    def_method(:shown_as) { s }\n  end\nend\n", "require_relative \"lib\"\nclass Note < Model\n  show B.new\nend\nclass Spec < Base\n  def label -> String = Note.new.shown_as\nend\np Spec.new.label\n", "\"b+base\"\n"),
    ] {
        let d = dir();
        write(&d.0, "lib.qz", lib);
        let app = write(&d.0, "app.qz", app);
        let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
        assert!(ok, "{err}");
        assert_eq!(out, want);
    }
}

#[test]
fn compile_time_only_calls_through_operators_and_symbol_procs() {
    let d = dir();
    let app = write(
        &d.0,
        "ops.qz",
        "class V\n  def initialize; end\n  static def +(o: V) -> V\n    V.fields.size\n    self\n  end\n  static def f -> Int = V.fields.size\nend\na = V.new\na += V.new\np [V.new].map(&:f)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("ops.qz:10:1: error: `+` runs at compile time only"),
        "{err}"
    );
    assert!(
        err.contains("ops.qz:11:16: error: `f` runs at compile time only"),
        "{err}"
    );
    // `quarz test` runs the statements and judges the calls too.
    write(&d.0, "lib2.qz", LIB2);
    let t = write(
        &d.0,
        "boom_test.qz",
        "require \"test\"\nrequire_relative \"lib2\"\nclass Boom < Model\n  static def self.boom -> Void = raise \"boom\"\nend\nclass P < Model\n  go\nend\nclass T < Test::Case\n  def test_x\n    assert(true)\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["test", t.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert!(err.contains("go: model\n"), "{err}");
}

#[test]
fn constants_and_the_cache_in_compile_time_runs() {
    let d = dir();
    // A constant that is not a literal is initialized in the run (it
    // needs a task), and a dependency's change that re-checks the program
    // runs the statements afresh.
    write(&d.0, "dep.qz", "D = 7\n");
    write(
        &d.0,
        "lib.qz",
        "require_relative \"dep\"\nSUM = D + 1\nclass Model\n  def self.h1 -> String = D.to_s + \"!\"\n  static def self.setup -> Void\n    puts \"setup: #{h1} #{SUM} #{\"x\" + \"y\"}\"\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass P < Model\n  setup\nend\n",
    );
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(err, "setup: 7! 8 xy\n");
    write(&d.0, "dep.qz", "D = \"seven\"\n");
    write(
        &d.0,
        "lib.qz",
        "require_relative \"dep\"\nSUM = 8\nclass Model\n  def self.h1 -> String = \"#{D}!\"\n  static def self.setup -> Void\n    puts \"setup: #{h1} #{SUM} #{\"x\" + \"y\"}\"\n  end\nend\n",
    );
    // The constants' change is seen after the first pass: the check
    // starts over, with the statements run again (the first run's output
    // stays).
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert!(
        err.ends_with("setup: seven! 8 xy\n") && !err.contains("7!"),
        "{err}"
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &env);
    assert!(ok, "{err}");
    assert_eq!(err, "setup: seven! 8 xy\n");
}

#[test]
fn overrides_of_object_methods_and_doc_examples() {
    let d = dir();
    // A `to_s` the statement reaches through an `Object` is refused like
    // any other override.
    write(
        &d.0,
        "show.qz",
        "class Model\n  static def self.show(x: Object) -> Void = puts x.to_s\n  static def self.eq(n: Int) -> Void = puts(n == 0)\nend\n",
    );
    let app = write(
        &d.0,
        "tos.qz",
        "require_relative \"show\"\nclass Bad\n  def initialize; end\n  def to_s -> String = File.read(\"/etc/hostname\")\nend\nclass P < Model\n  show Bad.new\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(err.contains("cannot run at compile time"), "{err}");
    // While an `Object` whose `to_s`, `==` and `inspect` are the usual
    // ones is fine: the overrides in classes denied at compile time
    // (`IO#to_s`, `Random#==`) do not count.
    let app = write(
        &d.0,
        "fine.qz",
        "require_relative \"show\"\nclass P < Model\n  show 1\n  show :sym\n  eq 0\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(err, "1\nsym\ntrue\n");
    // A doc example's class body runs its statements under `quarz test`.
    write(&d.0, "lib2.qz", LIB2);
    let t = write(
        &d.0,
        "ex_test.qz",
        "require \"test\"\nrequire_relative \"lib2\"\n# A model.\n#\n# ```\n# class Thing < Model\n#   go\n# end\n# Thing.hook   # => \"model\"\n# ```\nclass Thing2 < Model\nend\nclass T < Test::Case\n  def test_x\n    assert(true)\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["test", t.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert!(err.contains("go: model\n"), "{err}");
    // `&:name` reports a compile-time-only call once.
    let app = write(
        &d.0,
        "once.qz",
        "class V\n  def initialize; end\n  static def f -> Int = V.fields.size\nend\np [V.new].map(&:f)\n",
    );
    let (_, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert_eq!(err.matches("runs at compile time only").count(), 1, "{err}");
}

#[test]
fn a_statement_reaching_code_with_errors_does_not_run() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  static def self.go(x: Object) -> Void = puts x.to_s\nend\nclass Broken\n  def initialize; end\n  def to_s -> String\n    n: Int = \"not an int\"\n    (n + 1).to_s\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass P1 < Model\n  go 1\nend\nclass P2 < Model\n  go Broken.new\nend\nclass P3 < Model\n  go Broken.new\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    // The type error, and every statement reaching the broken body
    // refused (`go` takes an `Object`, so every one of them may reach
    // `Broken#to_s`); none of them ran it.
    assert!(err.contains("lib.qz:7:14: error"), "{err}");
    assert_eq!(
        err.matches("did not run: it may reach `Broken#to_s` (lib.qz:6), which has errors: ")
            .count(),
        3,
        "{err}"
    );
    assert!(!err.contains("raised"), "{err}");
}

#[test]
fn a_discarded_overload_trial_notes_no_compile_time_call() {
    // A block tried with each overload: the `P` trial reaches `P.k`, which
    // is compile-time only, and fails; the `Q` overload is chosen, and
    // nothing of the discarded trial is reported.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class P\n  @n: Int = 0\n  static def self.k -> Int = fields.size\nend\nclass Q\n  def self.k -> Int = 1\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\ndef f(&b: (Type[P]) -> String) -> String = b.call(P)\ndef f(&b: (Type[Q]) -> Int) -> Int = b.call(Q)\np f { |c| c.k }\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "1\n");
    // The call itself is still reported where it is made.
    let bad = write(&d.0, "bad.qz", "require_relative \"lib\"\np P.k\n");
    let (ok, _, err) = quarz(&d.0, &["run", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(err.contains("`k` runs at compile time only"), "{err}");
}

#[test]
fn a_static_defs_self_is_no_instance() {
    // A `static def`'s `self` is a `Meta::ClassDef`: no `Self` (the
    // class's instances), which a method of the class could be called on.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class C\n  @n: Int = 7\n  def hello -> Int = @n + 1\n  static def self.mk -> Self = self\n  static def self.mk2 -> Self\n    k: Self = self\n    k\n  end\nend\n",
    );
    let app = write(&d.0, "app.qz", "require_relative \"lib\"\np 1\n");
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("method `mk` returns Self but its body has type Meta::ClassDef[C]"),
        "{err}"
    );
    assert!(
        err.contains("cannot assign Meta::ClassDef[C] to `k` of type Self"),
        "{err}"
    );
}

#[test]
fn self_in_a_lifted_block_is_the_class_generated_into() {
    // docs/14 §5: a parameter typed `Self` in a block given to
    // `def_method` takes the class generated into, not the `static
    // def`'s class.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  def hello -> Int = 1\n  static def self.gen -> Void\n    def_method(:same, :o) do |o: Self| -> Bool\n      o.hello == hello\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Post < Model\n  gen\nend\np Post.new.same(Model.new)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(err.contains("expects Post but found Model"), "{err}");
}

#[test]
fn a_lifted_block_checked_once_per_type_must_have_one_type() {
    // A block given to `def_method` inside a block checked once per type
    // (here for each array type of a union): the checks found different
    // procedure types, while the generated method has one signature (the
    // last check's was taken, wrong for a run with the other type).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  static def self.gen(flag: Bool) -> Void\n    xs: Array[Int] | Array[String] = flag ? [1] : [\"a\"]\n    xs.each do |v|\n      def_method(:val) do\n        v\n      end\n    end\n  end\nend\n",
    );
    write(
        &d.0,
        "same_lib.qz",
        "class Model\n  static def self.same(flag: Bool) -> Void\n    xs: Array[Int] | Array[String] = flag ? [1] : [\"a\"]\n    xs.each do |v|\n      def_method(:one) do\n        v.to_s.size\n      end\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Post < Model\n  gen true\nend\np Post.new.val.size\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("the block given to `def_method` has a type for each check of the block around it (Model.() -> Int and Model.() -> String)"),
        "{err}"
    );
    // The same type in every check: generated.
    let same = write(
        &d.0,
        "same.qz",
        "require_relative \"same_lib\"\nclass Post < Model\n  same true\nend\np Post.new.one + 1\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", same.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "2\n");
}

const HOOKS: &str = r##"data Plug = (name: String, order: Int)

class Endpoint
  # One line per plug; the class's end makes `self.plugs` of them all.
  static def self.plug(p: Plug) -> Void
    statement_values[Plug](:plugs).add(p)
    at_class_end(:plugs) do |cls|
      ps = cls.statement_values[Plug](:plugs).values
      cls.def_class_method(:plugs) { ps }
    end
  end
  # Another key, of another type: kept apart.
  static def self.tag(t: Symbol) -> Void
    statement_values[Symbol](:tags).add(t)
    at_class_end(:tags) do |cls|
      ts = cls.statement_values[Symbol](:tags).values
      cls.def_method(:tags) { ts }
    end
  end
  # A later statement reads what earlier ones added.
  static def self.count_plugs -> Void
    n = statement_values[Plug](:plugs).size
    puts "plugs so far: #{n}"
    # (It generates in the statement itself too.)
    def_class_method(:counted) { n }
  end
  static def self.misnamed -> Void
    statement_values[String](:plugs)
  end
  static def self.failing -> Void
    at_class_end(:failing) { |cls| raise ArgumentError, "no plugs" }
  end
  static def self.nesting -> Void
    at_class_end(:outer) { |cls| cls.at_class_end(:inner) { |c| nil } }
  end
  static def self.adding -> Void
    at_class_end(:adding) { |cls| cls.statement_values[Plug](:plugs).add(Plug.new("x", 0)) }
  end
end
"##;

#[test]
fn class_end_hooks_combine_a_bodys_statements() {
    // docs/14 §5: `statement_values` and `at_class_end`.
    let d = dir();
    write(&d.0, "lib.qz", HOOKS);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Api < Endpoint\n  plug Plug.new(\"auth\", 1)\n  tag :json\n  plug Plug.new(\"log\", 2)\n  count_plugs\n  plug Plug.new(\"cache\", 3)\n  tag :v1\nend\nclass V2 < Api\nend\np Api.plugs.map(&:name), Api.counted, Api.new.tags\np V2.plugs.size\n",
    );
    let expected = "[\"auth\", \"log\", \"cache\"]\n2\n[:json, :v1]\n3\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    assert_eq!(err, "plugs so far: 2\n");
    // Compiled: the hook's method is an ordinary one.
    let exe = d.0.join("app-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
    // `--tree` lists what a hook generated as generated.
    let (ok, out, err) = quarz(&d.0, &["check", "--tree", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    let tree: serde_json::Value = serde_json::from_str(&out).unwrap();
    let text = tree.to_string();
    assert!(text.contains("\"name\":\"plugs\""), "{text}");
    assert!(text.contains("\"generated\":true"), "{text}");

    // The errors, at the statement (a hook's at the class's last one,
    // naming its key and the `static def` that registered it).
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass A < Endpoint\n  plug Plug.new(\"a\", 1)\n  misnamed\nend\nclass B < Endpoint\n  failing\n  plug Plug.new(\"b\", 1)\nend\nclass C < Endpoint\n  nesting\nend\nclass D < Endpoint\n  adding\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("bad.qz:4:3: error: `misnamed` raised RuntimeError: the statement values `:plugs` were made as `StatementValues[Plug]`, and are named here as `StatementValues[String]`: a key has one type"),
        "{err}"
    );
    assert!(
        err.contains("bad.qz:8:3: error: the class-end hook `:failing` (registered by `failing`) raised ArgumentError: no plugs"),
        "{err}"
    );
    assert!(
        err.contains("bad.qz:11:3: error: the class-end hook `:outer` (registered by `nesting`) raised RuntimeError: a class-end hook cannot register another (`:inner`)"),
        "{err}"
    );
    assert!(
        err.contains("bad.qz:14:3: error: the class-end hook `:adding` (registered by `adding`) raised RuntimeError: a class-end hook cannot add statement values (`:plugs`)"),
        "{err}"
    );
    // A class one of whose statements failed runs no hook.
    assert!(!err.contains("`:plugs` (registered by `plug`)"), "{err}");

    // `U` is a type whose values can be baked, checked where it is written.
    write(
        &d.0,
        "box.qz",
        "class Box\n  @n: Int = 0\nend\nclass Gen\n  static def self.boxes -> Void\n    statement_values[Box](:boxes)\n  end\n  static def self.inferred -> Void\n    statement_values(:any)\n  end\n  static def self.generic[X](v: X) -> Void\n    statement_values[X](:vals).add(v)\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "box.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("box.qz:6:5: error: statement values of type Box cannot be kept: their values must be bakeable"),
        "{err}"
    );
    // Written, and concrete: a generic `static def`'s instantiations would
    // put values of different types under one key.
    assert!(
        err.contains("box.qz:9:5: error: `statement_values` takes the values' type explicitly"),
        "{err}"
    );
    assert!(
        err.contains("box.qz:12:5: error: statement values of type X cannot be kept: their type must be a concrete one, not a type parameter"),
        "{err}"
    );
}

/// `quarz run` and `quarz build` of `app` in `d`: both print `expected`,
/// and the compile-time runs warn of nothing (a `deinitialize` with no
/// body only warns).
fn run_and_build(d: &std::path::Path, app: &std::path::Path, expected: &str) {
    let (ok, out, err) = quarz(d, &["run", app.to_str().unwrap()], &[]);
    assert!(ok && !err.contains("warning"), "{err}");
    assert_eq!(out, expected);
    let exe = d.join("app-bin");
    let (ok, _, err) = quarz(
        d,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

#[test]
fn a_round_reaches_the_names_the_runtime_calls_for_its_reach() {
    // A round reaches the methods the runtime calls by name for what its
    // statement reaches, not every method of those names: `mark` does not
    // reach `App#call`, whose `H.helper` a later statement generates
    // (bezel's router, #387; docs/14 §7). `join_things` reaches `Thing#to_s`
    // through `Array#join`, a native calling `to_s` by name, `Pt#with` the
    // `initialize` taking the fields, and a construction the
    // `deinitialize`s: all lowered for the run.
    let lib = "class Plain\n  static def self.mark -> Void\n    def_class_method(:marked) { 1 }\n  end\nend\nclass HelperGen\n  static def self.helpers -> Void\n    def_class_method(:helper) { 1 }\n  end\nend\nclass Thing\n  def to_s -> String = \"t\"\n  def deinitialize -> Void\n    x = 1\n  end\nend\ndata Pt(x: Int, y: Int)\n  def initialize(x: Int, y: Int)\n    @x = x * 10\n    @y = y\n  end\n  def initialize(s: String)\n    @x = s.size\n    @y = 0\n  end\nend\nclass Joiner\n  static def self.join_things -> Void\n    s = [Thing.new, Thing.new].join(\",\")\n    q = Pt.new(\"abc\").with(y: 2)\n    def_class_method(:joined) { s }\n    def_class_method(:pt) { q.x }\n  end\nend\n";
    let d = dir();
    write(&d.0, "lib.qz", lib);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass App\n  def call(x: Int) -> Int = H.helper + x\nend\nclass P < Plain\n  mark\nend\nclass J < Joiner\n  join_things\nend\nclass H < HelperGen\n  helpers\nend\np App.new.call(1)\np P.marked\np J.joined\np J.pt\n",
    );
    run_and_build(&d.0, &app, "2\n1\n\"t,t\"\n30\n");
    // What a native reached calls by name is still checked: a `to_s`
    // with errors refuses `join_things`.
    let d = dir();
    write(&d.0, "lib.qz", lib);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Bad\n  def to_s -> String = H.helper.to_s\nend\nclass J < Joiner\n  join_things\nend\nclass H < HelperGen\n  helpers\nend\np J.joined\n",
    );
    let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("app.qz:6:3: error: `join_things` did not run: it may reach `Bad#to_s` (app.qz:3), which has errors"),
        "{err}"
    );
}

#[test]
fn data_with_reaches_the_initialize_taking_the_fields() {
    // `with` on a data type builds the copy with the type's `initialize`
    // taking the fields: an impure one refuses the statement before it
    // runs (#389).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "data Pt(x: Int, y: Int)\n  def initialize(x: Int, y: Int)\n    File.read(\"/etc/hostname\")\n    @x = x\n    @y = y\n  end\n\n  def initialize(s: String)\n    @x = s.size\n    @y = 0\n  end\nend\n\nclass Model\n  static def self.gen(s: String) -> Void\n    q = Pt.new(s).with(x: 5)\n    def_class_method(:total) { q.x }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass App < Model\n  gen \"abc\"\nend\np App.total\n",
    );
    let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.starts_with("app.qz:3:3: error: `gen` reaches `File.read` (via Pt#with, Pt#initialize), which cannot run at compile time"),
        "{err}"
    );
}

#[test]
fn a_class_end_hook_reaches_what_the_class_statements_left_out() {
    // `plug`'s round left `C#to_s` out (a name the runtime calls by, of a
    // class whose statements were still to run); the class-end hook's
    // round, after them, reaches it: it does not continue `plug`'s walk,
    // though the statement and the world are the same (#390's review).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Endpoint\n  def self.make -> Endpoint = new\n  static def self.plug(n: Int) -> Void\n    statement_values[Int](:plugs).add(n)\n    at_class_end(:plugs) do |cls|\n      e = cls.type.make\n      s = \"#{e}\"\n      cls.def_class_method(:shown) { s }\n    end\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass C < Endpoint\n  plug 1\n  def to_s -> String = \"C!\"\nend\np C.shown\n",
    );
    run_and_build(&d.0, &app, "\"C!\"\n");
}

#[test]
fn a_super_in_a_block_with_a_receiver_runs_on_the_methods_self() {
    // `super` in a block with a receiver runs on the method's `self`,
    // whether the block is lowered in place (given to `instance_exec`)
    // or as a function of its own (given to `H#with`), and the
    // compile-time reach bounds it by the method's `self` (#384): `P2`'s
    // `go` reaches `Q#label`, not `P3#label`, which the receiver has.
    let classes = "class Q\n  def label -> String = \"q\"\n  def go(s: P) -> String = label\n  def go2(s: P) -> String = label\nend\nclass H\n  def with(s: P, &b: P.() -> String) -> String = s.instance_exec(&b)\nend\nclass P < Q\n  def go(s: P) -> String = s.instance_exec { super(s) }\n  def go2(s: P) -> String = H.new.with(s) { super(s) }\nend\nclass P2 < P\nend\nclass P3 < P\n  def label -> String = File.read(\"/etc/hostname\")\nend\n";
    for (call, ok_expected) in [
        ("P2.new.go(P3.new) + P2.new.go2(P3.new)", true),
        ("P3.new.go(P2.new)", false),
        ("P3.new.go2(P2.new)", false),
    ] {
        let d = dir();
        write(
            &d.0,
            "lib.qz",
            &format!("{classes}class Model\n  static def self.gen -> Void\n    s = {call}\n    def_class_method(:total) {{ s }}\n  end\nend\n"),
        );
        let app = write(
            &d.0,
            "app.qz",
            "require_relative \"lib\"\nclass App < Model\n  gen\nend\np App.total\n",
        );
        if ok_expected {
            run_and_build(&d.0, &app, "\"qq\"\n");
        } else {
            let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
            assert!(!ok);
            assert!(
                err.starts_with("app.qz:3:3: error: `gen` reaches `File.read` (via ")
                    && err.lines().next().unwrap().contains("P3#label"),
                "{call}: {err}"
            );
        }
    }
}

#[test]
fn a_generated_methods_body_is_not_in_its_statements_reach() {
    // A block given to `def_method` and its kin becomes a method's body,
    // which the statement does not run: what it reaches (IO, a task
    // scope, a method doing IO) does not refuse the statement (#397;
    // docs/14 §5). What the statement itself runs still does.
    let lib = "class Base\n  def self.read_it -> String = File.read(\"/etc/hostname\")\n  static def self.gen -> Void\n    def_class_method(:hostname) { File.read(\"/etc/hostname\") }\n  end\n  static def self.gen_kw -> Void\n    def_class_method(:hostname2, keywords: [Meta::Keyword.new(:x, Int, true)]) do |given| -> String\n      Base.read_it\n    end\n  end\n  static def self.gen_task -> Void\n    def_class_method(:t) do -> Int\n      Task.scope { |s| s.spawn { 1 }.await }\n    end\n    def_method(:size_of_host) { File.read(\"/etc/hostname\").size }\n  end\n  static def self.bad -> Void\n    s = File.read(\"/etc/hostname\")\n    def_class_method(:h) { s }\n  end\nend\n";
    let d = dir();
    write(&d.0, "lib.qz", lib);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Base\n  gen\nend\nclass B < Base\n  gen_kw\nend\nclass C < Base\n  gen_task\nend\nputs A.hostname.size > 0\nputs B.hostname2(x: 1).size > 0\np C.t\nputs C.new.size_of_host > 0\n",
    );
    run_and_build(&d.0, &app, "true\ntrue\n1\ntrue\n");
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Base\n  bad\nend\np A.h\n",
    );
    let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.starts_with(
            "app.qz:3:3: error: `bad` reaches `File.read`, which cannot run at compile time"
        ),
        "{err}"
    );
}

#[test]
fn a_block_a_union_receiver_may_call_stays_in_the_reach() {
    // `r.def_method(:x) { ... }` on `Type[Base] | Runner`: the block may
    // be `Runner#def_method`'s, which calls it at compile time, so it is
    // no generated body: walked, lowered and checked (#402's review).
    let lib = |body: &str| {
        format!("class Helper\n  def self.compute -> Int = 41\nend\nclass Runner\n  def def_method[R](name: Symbol, &body: () -> R) -> R = body.call\nend\nclass Base\n  static def self.gen(flag: Bool) -> Void\n    r = flag ? self : Runner.new\n    r.def_method(:hostname) {{ {body} }}\n    def_class_method(:x) {{ 1 }}\n  end\nend\n")
    };
    let d = dir();
    write(&d.0, "lib.qz", &lib("Helper.compute"));
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Base\n  gen(false)\nend\np A.x\n",
    );
    run_and_build(&d.0, &app, "1\n");
    write(&d.0, "lib.qz", &lib("File.read(\"/etc/hostname\")"));
    let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.starts_with(
            "app.qz:3:3: error: `gen` reaches `File.read`, which cannot run at compile time"
        ),
        "{err}"
    );
}
