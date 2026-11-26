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

/// #704: a compile-time run takes a `data` value's field from its only
/// holder as a run does (`FieldTake`), and gets the same value.
#[test]
fn a_compile_time_run_takes_a_field_as_a_run_does() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "data D = (xs: Array[Int])\nmodule Lib\n  def self.build -> Array[Int]\n    d = D.new([])\n    i = 0\n    while i < 5\n      d = D.new(d.xs.push(i))\n      i += 1\n    end\n    d.xs\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nXS = static(Lib.build)\np XS, Lib.build\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "[0, 1, 2, 3, 4]\n[0, 1, 2, 3, 4]\n");
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
        err.contains("`spin` raised Meta::CompileTimeError: compile-time evaluation took too long"),
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
    // A module body takes no statements, even one calling a `static def`
    // of a dependency (docs/14 §2, #718): refused, not run.
    write(
        &d.0,
        "mk.qz",
        "module Mk\n  static def self.mark(tag: String) -> Void\n    puts \"static #{tag}\"\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "in_module.qz",
        "require_relative \"mk\"\nmodule M\n  include Mk\n  mark(\"M\")\nend\nputs \"ok\"\n",
    );
    for cmd in ["check", "run"] {
        let (ok, out, err) = quarz(&d.0, &[cmd, app.to_str().unwrap()], &[]);
        assert!(!ok, "{cmd}: {out}");
        assert!(!out.contains("static M"), "{cmd}: {out}");
        assert!(
            err.contains("in_module.qz:4:3: error: a module body takes no `static` statements: only a class body does"),
            "{cmd}: {err}"
        );
    }
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
        err.contains(
            "`forever` raised Meta::CompileTimeError: compile-time evaluation took too long"
        ),
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

/// An `Int` comparison reaches the `Int` native the checks resolved it
/// to, not every method of the operator's name (docs/14 §8, #1173): a
/// class whose `==`, `<=>` or `>` reaches the outside world, never made,
/// keeps no statement from running. A statement that does call such an
/// `==` is refused as before.
#[test]
fn an_int_comparison_reaches_the_int_native_only() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  static def self.compare -> Void\n    x = [1, 2].size\n    k = x == 2 && x > 1 && x < 3 && (x <=> 2) == 0\n    def_class_method(:k) { k }\n  end\n  static def self.really(v: Object) -> Void\n    k = v == 1\n    def_class_method(:r) { k }\n  end\nend\n",
    );
    let outside = "class Shown\n  include Comparable[Shown]\n  def ==(other: Object) -> Bool = !ENV[\"HOME\"]?.nil?\n  def hash -> Int = 0\n  def <=>(other: Shown) -> Int = (ENV[\"HOME\"]? || \"\").size\nend\n";
    let app = write(
        &d.0,
        "app.qz",
        &format!("require_relative \"lib\"\n{outside}class K < Base\n  compare\nend\np K.k\n"),
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "true\n");
    // CommandLine's `flag` and `program` compare `Int`s (the issue's
    // reproducer).
    let app = write(
        &d.0,
        "cli.qz",
        &format!("require \"command_line\"\n{outside}class Cmd < CommandLine\n  program \"cmd\"\n  flag :v\nend\nputs Cmd.parse([\"--v\"], exit: false).v\n"),
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "true\n");
    // A call of the class's own `==` on a value of it still reaches it.
    let app = write(
        &d.0,
        "really.qz",
        &format!("require_relative \"lib\"\n{outside}class R < Base\n  really(Shown.new)\nend\n"),
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(err.contains("cannot run at compile time"), "{err}");
    // Narrowed so, the static walks drop no method a program calls by
    // name: CommandLine's statements (`Int` comparisons) beside a class's
    // own `==`, `<=>` and `hash`, used through `Comparable`, `include?`,
    // `sort` and a hash's keys, interpreted and compiled.
    let app = write(
        &d.0,
        "both.qz",
        "require \"command_line\"\n\nclass Version\n  include Comparable[Version]\n\n  @n: Int\n\n  def initialize(@n: Int)\n  end\n\n  def n -> Int = @n\n\n  def <=>(other: Version) -> Int = n <=> other.n\n\n  def ==(other: Object) -> Bool\n    case other\n    in Version => v then n == v.n\n    else false\n    end\n  end\n\n  def hash -> Int = n.hash\nend\n\nclass Cmd < CommandLine\n  program \"cmd\"\n  flag :verbose, short: \"v\"\nend\n\nvs = [Version.new(3), Version.new(1), Version.new(2)]\nputs vs.sort.map { |v| v.n }.join(\",\")\nputs vs.include?(Version.new(2))\nputs vs.include?(Version.new(5))\nputs Version.new(2) > Version.new(1)\nputs Version.new(1) == Version.new(1)\nputs({Version.new(1) => \"one\"}[Version.new(1)]? || \"none\")\nx = vs.size\nputs x > 2, x == 3, x <=> 4\nputs Cmd.parse([\"-v\"], exit: false).verbose\n",
    );
    let want = "1,2,3\ntrue\nfalse\ntrue\ntrue\none\ntrue\ntrue\n-1\ntrue\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, want);
    let exe = d.0.join("both-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), want);
}

/// A call on a class value reaches what a class object the receiver's
/// type allows runs: the class methods of `C` and its subclasses (and of
/// modules on their class side), never an instance method of a program
/// class (docs/14 §8, #1173). The matrix: the receiver's type (a class,
/// a generic class, an abstract class, a module, `Type[Int]`,
/// `Type[Object]`, a union with an instance type), where the method
/// reading the environment is (the class's own, its superclass's, a
/// subclass's, a module a subclass includes, an unrelated class's or
/// module's, an instance method), when it exists (declared after the
/// statement, in a file required after it, generated by `def_class_method`
/// before or after it, on a class whose statements are still to run), and
/// the method called (`==`, `Type#name`, a program's class method).
/// Expected from the rule; the cells it leaves are: type arguments (a
/// class value has none: `Type[Box[Int]]` is `Box`'s cell), an
/// extension's class method (bound statically, never dispatched), another
/// cog (the same tables), and the compiled backend (the rule is the
/// compile-time reach; one run and build below shows dispatch unchanged).
#[test]
fn a_call_on_a_class_value_reaches_its_class_side() {
    let impure_eq = "  def self.==(other: Object) -> Bool = !ENV[\"HOME\"]?.nil?\n";
    let lib = "class Base\n  def self.tag -> String = \"base\"\n  static def self.eq_base -> Void\n    t: Type[Base] = Base\n    k = t == Base\n    def_class_method(:k) { k }\n  end\n  static def self.eq_param(t: Type[Base]) -> Void\n    k = t == Base\n    def_class_method(:k) { k }\n  end\n  static def self.eq_int -> Void\n    t = Int\n    k = t == String\n    def_class_method(:k) { k }\n  end\n  static def self.eq_object(t: Type[Object]) -> Void\n    k = t == String\n    def_class_method(:k) { k }\n  end\n  static def self.eq_union(v: Type[Base] | Int) -> Void\n    k = v == 1\n    def_class_method(:k) { k }\n  end\n  static def self.name_base -> Void\n    t: Type[Base] = Base\n    k = t.name\n    def_class_method(:k) { k }\n  end\n  static def self.tag_base -> Void\n    t: Type[Base] = Base\n    k = t.tag\n    def_class_method(:k) { k }\n  end\n  static def self.make_tag -> Void\n    def_class_method(:tag, override: true) { ENV[\"HOME\"]? || \"?\" }\n  end\nend\nclass Box[T]\n  static def self.eq_box(t: Type[Box[Int]]) -> Void\n    k = t == Box\n    def_class_method(:k) { k }\n  end\nend\nabstract class Abs\n  static def self.eq_abs(t: Type[Abs]) -> Void\n    k = t == Abs\n    def_class_method(:k) { k }\n  end\nend\nmodule Mod\nend\nmodule Gm[T]\nend\nclass ModUser\n  static def self.eq_mod(t: Type[Mod]) -> Void\n    k = t == Mod\n    def_class_method(:k) { k }\n  end\n  static def self.eq_gm(t: Type[Gm[Int]]) -> Void\n    k = t == Gm\n    def_class_method(:k) { k }\n  end\nend\n";
    // The class's own and its superclass's, in a file of their own.
    let lib2 = format!("class Top\n{impure_eq}end\nclass Mid < Top\n  static def self.eq_mid -> Void\n    t: Type[Mid] = Mid\n    k = t == Mid\n    def_class_method(:k) {{ k }}\n  end\nend\nclass Own\n{impure_eq}  static def self.eq_own -> Void\n    t: Type[Own] = Own\n    k = t == Own\n    def_class_method(:k) {{ k }}\n  end\nend\n");
    let sub = |name: &str, sup: &str| format!("class {name} < {sup}\n{impure_eq}end\n");
    let other = format!("class Other\n{impure_eq}end\n");
    let instance = "class Inst < Base\n  def ==(other: Object) -> Bool = !ENV[\"HOME\"]?.nil?\nend\nclass Loose\n  def ==(other: Object) -> Bool = !ENV[\"HOME\"]?.nil?\nend\n";
    let d = dir();
    write(&d.0, "lib.qz", lib);
    write(&d.0, "lib2.qz", &lib2);
    write(&d.0, "late.qz", &sub("Late", "Base"));
    // (before, statement class body, after, refused through: None when
    // accepted)
    let cells: Vec<(String, &str, String, Option<&str>)> = vec![
        // `Type[Base]`: where the `def self.==` is.
        (
            sub("Sub", "Base"),
            "class K < Base\n  eq_base\nend\n",
            String::new(),
            Some("Sub.=="),
        ),
        (
            other.clone(),
            "class K < Base\n  eq_base\nend\n",
            String::new(),
            None,
        ),
        (
            instance.to_string(),
            "class K < Base\n  eq_base\nend\n",
            String::new(),
            None,
        ),
        (
            format!("module Mo\n{impure_eq}end\nclass WithMo < Base\n  include Mo\nend\n"),
            "class K < Base\n  eq_base\nend\n",
            String::new(),
            Some("Mo.=="),
        ),
        (
            format!("module Mo\n{impure_eq}end\nclass Apart\n  include Mo\nend\n"),
            "class K < Base\n  eq_base\nend\n",
            String::new(),
            None,
        ),
        // ... when it is declared: after the statement, in a file
        // required after it.
        (
            String::new(),
            "class K < Base\n  eq_base\nend\n",
            sub("After", "Base"),
            Some("After.=="),
        ),
        (
            String::new(),
            "class K < Base\n  eq_base\nend\n",
            "require_relative \"late\"\n".to_string(),
            Some("Late.=="),
        ),
        // ... generated: before the statement, reached; after it, it does
        // not exist yet when the statement runs, which sees `Base.tag`.
        (
            "class Gen < Base\n  make_tag\nend\n".to_string(),
            "class K < Base\n  tag_base\nend\n",
            String::new(),
            Some("Gen.tag"),
        ),
        (
            String::new(),
            "class K < Base\n  tag_base\nend\n",
            "class Gen < Base\n  make_tag\nend\n".to_string(),
            None,
        ),
        // ... on a class whose statements are still to run (docs/14 §8:
        // its methods are not in the reach until they ran); a run that
        // dispatches to it is refused when it runs.
        (
            String::new(),
            "class K < Base\n  eq_base\nend\n",
            format!("class Pending < Base\n  tag_base\n{impure_eq}end\n"),
            None,
        ),
        // `Type#name` and a program's class method.
        (
            "class Named < Base\n  def self.name -> String = ENV[\"HOME\"]? || \"?\"\nend\n"
                .to_string(),
            "class K < Base\n  name_base\nend\n",
            String::new(),
            Some("Named.name"),
        ),
        (
            "class Named\n  def self.name -> String = ENV[\"HOME\"]? || \"?\"\nend\n".to_string(),
            "class K < Base\n  name_base\nend\n",
            String::new(),
            None,
        ),
        (
            "class Tagged < Base\n  def self.tag -> String = ENV[\"HOME\"]? || \"?\"\nend\n"
                .to_string(),
            "class K < Base\n  tag_base\nend\n",
            String::new(),
            Some("Tagged.tag"),
        ),
        (
            "class Tagged\n  def self.tag -> String = ENV[\"HOME\"]? || \"?\"\nend\n".to_string(),
            "class K < Base\n  tag_base\nend\n",
            String::new(),
            None,
        ),
        // `Type[Int]`: nothing of the program's.
        (
            sub("Sub", "Base") + &other + instance,
            "class K < Base\n  eq_int\nend\n",
            String::new(),
            None,
        ),
        // `Type[Object]`: every class object's class side, a module's
        // too, and no instance method.
        (
            other.clone(),
            "class K < Base\n  eq_object(Int)\nend\n",
            String::new(),
            Some("Other.=="),
        ),
        (
            format!("module Mo\n{impure_eq}end\n"),
            "class K < Base\n  eq_object(Int)\nend\n",
            String::new(),
            Some("Mo.=="),
        ),
        (
            instance.to_string(),
            "class K < Base\n  eq_object(Int)\nend\n",
            String::new(),
            None,
        ),
        // A union with an instance type: unbounded, as by name.
        (
            instance.to_string(),
            "class K < Base\n  eq_union(1)\nend\n",
            String::new(),
            Some("#=="),
        ),
        // A generic class, an abstract one, a module.
        (
            sub("IntBox", "Box[Int]"),
            "class K < Box[Int]\n  eq_box(IntBox)\nend\n",
            String::new(),
            Some("IntBox.=="),
        ),
        (
            other.clone(),
            "class K < Box[Int]\n  eq_box(Box)\nend\n",
            String::new(),
            None,
        ),
        (
            sub("Concrete", "Abs"),
            "class K < Abs\n  eq_abs(Concrete)\nend\n",
            String::new(),
            Some("Concrete.=="),
        ),
        (
            other.clone(),
            "class K < Abs\n  eq_abs(Abs)\nend\n",
            String::new(),
            None,
        ),
        (
            format!("class Incl\n  include Mod\n{impure_eq}end\n"),
            "class K < ModUser\n  eq_mod(Incl)\nend\n",
            String::new(),
            Some("Incl.=="),
        ),
        (
            format!("class Incl\n  include Mod\nend\n{other}"),
            "class K < ModUser\n  eq_mod(Incl)\nend\n",
            String::new(),
            None,
        ),
        // What a `Type[Mod]` may hold through an extension's include
        // (unconditional, conditional with its bound met, scoped in a
        // module) or a generic module's: in the cone (the ancestors the
        // runtime ships hold every extension's include).
        (
            format!("class Ext\n{impure_eq}end\nextension Ext\n  include Mod\nend\n"),
            "class K < ModUser\n  eq_mod(Ext)\nend\n",
            String::new(),
            Some("Ext.=="),
        ),
        (
            format!("class CExt[T]\n{impure_eq}end\nextension CExt[T <: Int]\n  include Mod\nend\n"),
            "class K < ModUser\n  eq_mod(CExt[Int])\nend\n",
            String::new(),
            Some("CExt.=="),
        ),
        (
            format!("class SExt\n{impure_eq}end\nmodule Sc\n  extension SExt\n    include Mod\n  end\n  def self.go -> Type[Mod] = SExt\nend\n"),
            "class K < ModUser\n  eq_mod(Sc.go)\nend\n",
            String::new(),
            Some("SExt.=="),
        ),
        (
            format!("class GInc\n  include Gm[Int]\n{impure_eq}end\n"),
            "class K < ModUser\n  eq_gm(GInc)\nend\n",
            String::new(),
            Some("GInc.=="),
        ),
        // The class's own, its superclass's.
        (
            String::new(),
            "class K < Own\n  eq_own\nend\n",
            String::new(),
            Some("Own.=="),
        ),
        (
            String::new(),
            "class K < Mid\n  eq_mid\nend\n",
            String::new(),
            Some("Top.=="),
        ),
    ];
    for (i, (before, stmt, after, refused)) in cells.iter().enumerate() {
        // (`lib2`'s classes' `==`, which a `Type[Object]` reaches, only
        // where its cells are.)
        let lib2_req = if stmt.contains("eq_own") || stmt.contains("eq_mid") {
            "require_relative \"lib2\"\n"
        } else {
            ""
        };
        let app = write(
            &d.0,
            &format!("cell{i}.qz"),
            &format!("require_relative \"lib\"\n{lib2_req}{before}{stmt}{after}puts 1\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        match refused {
            None => assert!(ok, "cell {i}: {before}{stmt}{after}\n{err}"),
            Some(via) => {
                assert!(!ok, "cell {i}: {before}{stmt}{after}: accepted");
                assert!(
                    err.contains("which cannot run at compile time") && err.contains(via),
                    "cell {i}: {before}{stmt}{after}\n{err}"
                );
            }
        }
    }
    // A run that dispatches to a method of a class whose statements are
    // still to run is refused when it runs: the native does not run.
    let app = write(
        &d.0,
        "dispatch.qz",
        &format!("require_relative \"lib\"\nclass K < Base\n  eq_param(Pending)\nend\nclass Pending < Base\n  tag_base\n{impure_eq}end\n"),
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`eq_param` raised Meta::CompileTimeError: `==` of `Pending` has no body at compile time"),
        "{err}"
    );
    // Dispatch itself is unchanged: a class value runs its class's
    // `def self.==`, interpreted and compiled.
    let app = write(
        &d.0,
        "both.qz",
        "class P\n  def self.==(other: Object) -> Bool = true\nend\nclass Q < P\nend\nt: Type[P] = Q\nputs t == 1\nu: Type[Object] = Int\nputs u == String\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "true\nfalse\n");
    let exe = d.0.join("both-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "true\nfalse\n");
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

/// A class method that calls `new`, run at compile time on a subclass
/// whose statements are running, builds it with the `initialize` the
/// checker records for it, as at run time: the first of its overloads
/// that takes what `new` passes (docs/01 §3), here `(n: Object, &blk)`,
/// not the first declared, which takes a `String` (#858).
#[test]
fn an_inherited_new_at_compile_time_builds_with_the_overload_that_fits() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Two\n  @n: Int\n  def initialize(@n: Int); end\n  def self.mk(n: Int) -> Self = new(n)\n  def n -> Int = @n\n  static def self.probe -> Void\n    v = mk(6).n\n    def_class_method(:v) { v }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass TwoSub < Two\n  def initialize(n: String)\n    puts \"str\"\n    @n = n.size\n  end\n  def initialize(n: Object, &blk: (() -> Int)?)\n    puts \"obj\"\n    @n = 9\n  end\n  probe\nend\np TwoSub.v\np TwoSub.mk(6).n\n",
    );
    // (The statement's run, at compile time, prints to stderr.)
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!((out.as_str(), err.as_str()), ("9\nobj\n9\n", "obj\n"));
    let exe = d.0.join("app-bin");
    let (ok, out, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    assert_eq!((out.as_str(), err.as_str()), ("", "obj\n"));
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "9\nobj\n9\n");
}

/// An `initialize` a statement generates into a class between a subclass
/// and the class whose method calls `new` changes what that `new` builds
/// the subclass with, for a run after it as at run time; a generated field
/// (with its default) does not (#536 step 6). `X`'s statement runs `mk`
/// first, so the pass before the runs has recorded `Sub`'s pair before
/// `Mid`'s statement generates the `initialize` it now takes. Derived
/// from the rule (docs/01 §3): `Sub` and `Mid` are built with `Mid`'s
/// generated `initialize(n: Int)` (printing `gen`, `n * 10`), `X` and `F`
/// with `Base`'s.
#[test]
fn a_generated_initialize_changes_what_an_inherited_new_builds() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  @n: Int\n  def initialize(@n: Int); end\n  def self.mk(n: Int) -> Self = new(n)\n  def n -> Int = @n\n  static def self.probe -> Void\n    v = mk(4).n\n    def_class_method(:v) { v }\n  end\n  static def self.gen_init -> Void\n    def_initialize(:n) do |n: Int|\n      puts \"gen\"\n      @n = n * 10\n    end\n  end\n  static def self.gen_field -> Void\n    def_field(:extra, Int, 5, reader: true)\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass X < Base\n  probe\nend\nclass Mid < Base\n  gen_field\n  gen_init\nend\nclass Sub < Mid\n  probe\nend\nclass F < Base\n  gen_field\n  probe\nend\np X.v\np Sub.v\np F.v\np Sub.mk(4).n\np Mid.mk(4).n\np F.mk(4).n\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(
        (out.as_str(), err.as_str()),
        ("4\n40\n4\ngen\n40\ngen\n40\n4\n", "gen\n")
    );
}

/// A compile-time run whose `new` builds a subclass the check refuses (no
/// `initialize` of it takes what `new` passes) stops there: its statement
/// did not run, however the run rescues, and the check reports its own
/// error for the pair where it still holds after the statements (#870).
/// A pair refused before a later statement generates the `initialize`
/// that fits stops only a run that builds that subclass: `X`'s run builds
/// an `X`; one that builds `TwoSub` before then did not run, the only
/// error. Derived from the rule (docs/01 §3): `X` is built with `Two`'s
/// `initialize` (6), `TwoSub` with its generated one (`gen`, 60).
#[test]
fn a_run_that_builds_a_refused_subclass_did_not_run() {
    let d = dir();
    let lib = "class Two\n  @n: Int\n  def initialize(@n: Int); end\n  def self.mk(n: Int) -> Self = new(n)\n  def n -> Int = @n\n  static def self.probe -> Void\n    v = mk(6).n\n    def_class_method(:v) { v }\n  end\n  static def self.rescued -> Void\n    v = begin\n      mk(6).n\n    rescue => e\n      puts \"rescued\"\n      0\n    end\n    def_class_method(:v) { v }\n  end\n  static def self.build(k: Type[Two]) -> Void\n    k.mk(6)\n    def_class_method(:b) { 1 }\n  end\n  static def self.gen_init -> Void\n    def_initialize(:n) do |n: Int|\n      puts \"gen\"\n      @n = n * 10\n    end\n  end\nend\n";
    write(&d.0, "lib.qz", lib);
    let refused = "`TwoSub#initialize` does not take the arguments of `new` in `Two.mk`, which `TwoSub` inherits";
    for (stmt, printed) in [("probe", ""), ("rescued", "rescued\n")] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass TwoSub < Two\n  def initialize(n: String)\n    @n = n.size\n  end\n  {stmt}\nend\np TwoSub.v\n"),
        );
        let (ok, out, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{stmt}");
        assert!(err.starts_with(printed), "{stmt}: {err}");
        assert!(
            err.contains(&format!("app.qz:3:3: error: {refused}")),
            "{stmt}: {err}"
        );
        assert!(
            err.contains(&format!("app.qz:6:3: error: `{stmt}` did not run: it builds `TwoSub` with `new` in `Two.mk`, which no `initialize` of `TwoSub` takes")),
            "{stmt}: {err}"
        );
        assert!(!err.contains("internal error"), "{stmt}: {err}");
        assert_eq!(out, "", "{stmt}");
    }
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass X < Two\n  probe\nend\nclass TwoSub < Two\n  def initialize(n: String)\n    @n = n.size\n  end\n  gen_init\n  probe\nend\np X.v\np TwoSub.v\np TwoSub.mk(6).n\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!((out.as_str(), err.as_str()), ("6\n60\ngen\n60\n", "gen\n"));
    let exe = d.0.join("app-bin");
    let (ok, out, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    assert_eq!((out.as_str(), err.as_str()), ("", "gen\n"));
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "6\n60\ngen\n60\n");
    // A run that builds `TwoSub` before `TwoSub`'s statement generates the
    // `initialize` that fits did not run (it builds a class no overload
    // of which takes what `new` passes then), and that is the only error:
    // the check after the statements finds the generated one.
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass X < Two\n  build TwoSub\nend\nclass TwoSub < Two\n  def initialize(n: String)\n    @n = n.size\n  end\n  gen_init\n  probe\nend\np TwoSub.v\n",
    );
    let (ok, out, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert_eq!(out, "");
    let errors: Vec<&str> = err.lines().filter(|l| l.contains(": error: ")).collect();
    assert_eq!(
        errors,
        ["app.qz:3:3: error: `build` did not run: it builds `TwoSub` with `new` in `Two.mk`, which no `initialize` of `TwoSub` takes"],
        "{err}"
    );
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
            "`sorting` raised Meta::CompileTimeError: `Process.stdin` cannot run at compile time",
        ),
        (
            "interp",
            "`interp` raised Meta::CompileTimeError: `Process.stdin` cannot run at compile time",
        ),
        (
            "hashing",
            "`hashing` raised Meta::CompileTimeError: `Process.stdin` cannot run at compile time",
        ),
        (
            "broken",
            "`broken` did not run: a call of `to_s` the runtime makes by name (for `BadBase#broken`) may reach `Bad#to_s` (lib_bad.qz:2), a method of that name, which has errors: ",
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

/// The refusals of a compile-time run (a native acting on the outside
/// world, reached at run time; a method with no body yet; the time
/// limit) raise `Meta::CompileTimeError`, a direct subclass of
/// `Exception` (#959): no `rescue` short of `rescue Exception` takes it,
/// so the statement fails with the message, and `ensure` runs. Past the
/// time limit every call raises again: neither a handler nor an `ensure`
/// can call anything, and the statement fails.
#[test]
fn a_compile_time_refusal_is_not_rescued_by_standard_error() {
    let d = dir();
    // One `static def` per refusal and per form around it, so that what
    // one refusal's code reaches does not refuse another's statement.
    let kinds = [
        ("native", "[Slow.new, Slow.new].sort.size"),
        ("nobody", "\"#{x}\".size"),
        ("time", "while true\n    end\n    0"),
    ];
    let forms = [
        ("bare", "rescue", "puts \"taken\"\n      0"),
        ("any", "rescue => e", "puts \"taken\"\n      0"),
        (
            "standard",
            "rescue StandardError",
            "puts \"taken\"\n      0",
        ),
        ("runtime", "rescue RuntimeError", "puts \"taken\"\n      0"),
        (
            "exception",
            "rescue Exception => e",
            "puts \"taken: #{e.class.name}: #{e.message}\"\n      1",
        ),
        ("quiet", "rescue Exception", "1"),
        ("cleanup", "ensure", "puts \"ensure ran\""),
    ];
    let mut lib = String::from(
        "class Slow\n  include Comparable[Slow]\n  def <=>(o: Slow) -> Int = STDIN.read_bytes(1).size\nend\nclass Gen\n",
    );
    for (kind, body) in kinds {
        lib += &format!("  static def self.{kind}(x: Object) -> Int\n    {body}\n  end\n");
        for (form, clause, handler) in forms {
            lib += &format!(
                "  static def self.{kind}_{form}(x: Object) -> Int\n    begin\n      {kind}(x)\n    {clause}\n      {handler}\n    end\n  end\n"
            );
        }
        // (A statement goes on past what it rescued: it generates.)
        lib += &format!(
            "  static def self.{kind}_on(x: Object) -> Void\n    k = {kind}_quiet(x)\n    def_class_method(:k) {{ k }}\n  end\n"
        );
    }
    lib += "end\n";
    write(&d.0, "lib.qz", &lib);
    let message = |kind: &str| {
        match kind {
        "native" => "`Process.stdin` cannot run at compile time",
        "nobody" => "`to_s` of `Post` has no body at compile time: a method the runtime calls by name is lowered once the class's `static` statements ran, or when a call resolves to it (docs/14)",
        _ => "compile-time evaluation took too long",
    }
    };
    for (kind, _) in kinds {
        for call in [
            "bare",
            "any",
            "standard",
            "runtime",
            "exception",
            "cleanup",
            "on",
        ] {
            let app = write(
                &d.0,
                "app.qz",
                &format!(
                    "require_relative \"lib\"\nclass Post < Gen\n  def to_s -> String = \"post\"\n  {kind}_{call}(Post.new)\nend\n"
                ),
            );
            let (ok, _, err) = quarz(
                &d.0,
                &["check", app.to_str().unwrap()],
                &[("QUARZ_STATIC_LIMIT_MS", "200")],
            );
            let failed = format!(
                "app.qz:4:3: error: `{kind}_{call}` raised Meta::CompileTimeError: {}",
                message(kind)
            );
            // `rescue Exception` takes it: the statement goes on, but past
            // the time limit, whose next call raises again.
            let rescued = matches!(call, "exception" | "on") && kind != "time";
            assert_eq!(ok, rescued, "{kind}_{call}: {err}");
            if rescued {
                if call == "exception" {
                    assert!(
                        err.contains(&format!("taken: Meta::CompileTimeError: {}", message(kind))),
                        "{kind}_{call}: {err}"
                    );
                }
            } else {
                assert!(err.contains(&failed), "{kind}_{call}: {err}");
                assert!(!err.contains("taken"), "{kind}_{call}: {err}");
            }
            // `ensure` runs; past the time limit, its first call raises.
            if call == "cleanup" {
                assert_eq!(err.contains("ensure ran"), kind != "time", "{kind}: {err}");
            }
        }
    }
    // `static(...)` runs the same way (a value of a `static def` of a
    // required file, docs/14 §8).
    for (call, value) in [
        ("native_bare", None),
        ("native_runtime", None),
        ("native_exception", Some("1")),
    ] {
        let app = write(
            &d.0,
            "value.qz",
            &format!("require_relative \"lib\"\nX = static(Gen.{call}(0))\nputs X\n"),
        );
        let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
        match value {
            Some(v) => {
                assert!(ok, "{call}: {err}");
                assert_eq!(out, format!("{v}\n"), "{call}");
            }
            None => {
                assert!(!ok, "{call}");
                assert!(
                    err.contains(&format!(
                        "value.qz:2:12: error: `{call}` raised Meta::CompileTimeError: `Process.stdin` cannot run at compile time"
                    )),
                    "{call}: {err}"
                );
            }
        }
    }
}

/// A block a native calls repeatedly runs through a kept activation
/// (`BlockCaller`, #987), which checks the compile-time time limit at each
/// call as `call_block` does: a loop through it (`Int#step`'s block, with
/// no back edge of its own; `loop { }`, whose only check it is) and one
/// through `yield` raise
/// `Meta::CompileTimeError` past the limit, and again at each later call
/// after a `rescue Exception` (#969).
#[test]
fn a_kept_block_caller_keeps_the_time_limit() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Gen\n  static def self.kept -> Int\n    s = 0\n    0.step(1_000_000_000_000, 1) { |x| s += x }\n    s\n  end\n  static def self.each_forever(&b: (Int) -> Void) -> Void\n    i = 0\n    while true\n      yield i\n      i += 1\n    end\n  end\n  static def self.yielded -> Int\n    s = 0\n    each_forever { |x| s += x }\n    s\n  end\n  static def self.looped -> Int\n    s = 0\n    loop { s += 1 }\n    s\n  end\n  static def self.again -> Int\n    k = begin\n      kept\n    rescue Exception\n      0\n    end\n    k + kept\n  end\nend\n",
    );
    for call in ["kept", "yielded", "looped", "again"] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass Post < Gen\n  {call}\nend\n"),
        );
        let (ok, _, err) = quarz(
            &d.0,
            &["check", app.to_str().unwrap()],
            &[("QUARZ_STATIC_LIMIT_MS", "200")],
        );
        assert!(!ok, "{call}");
        assert!(
            err.contains("raised Meta::CompileTimeError: compile-time evaluation took too long"),
            "{call}: {err}"
        );
    }
}

/// What the natives that update a collection in place call by name
/// (`shake::native_calls`, which the lowering also reads to update a
/// field in place, #927) is reached: an element's `==` through
/// `Array#delete`, a key's `hash` through `Hash#put` and `#delete`, each
/// with errors, refuses the statement; an `Array#push` of the same
/// elements reaches neither. (`Set#add` and `#delete` are not told apart
/// here: making a set, `Set.new`, reaches every `==` and `hash`. The
/// fixture `owned_update_runs_user_code.qz` fails if their entries, or
/// these, were too small: the field would be updated in place.)
#[test]
fn the_in_place_updates_reach_what_they_compare_by() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class K\n  def ==(o: Object) -> Bool\n    n: Int = \"oops\"\n    true\n  end\n  def hash -> Int = 1\nend\nclass H\n  def ==(o: Object) -> Bool = true\n  def hash -> Int\n    n: Int = \"oops\"\n    1\n  end\nend\nclass Base\n  static def self.adel -> Void\n    [K.new].delete(K.new)\n    def_class_method(:a) { 1 }\n  end\n  static def self.hput -> Void\n    h: Hash[H, Int] = {}\n    h.put(H.new, 1)\n    def_class_method(:b) { 1 }\n  end\n  static def self.hdel -> Void\n    h: Hash[H, Int] = {}\n    h.delete(H.new)\n    def_class_method(:c) { 1 }\n  end\n  static def self.apush -> Void\n    [K.new].push(K.new)\n    def_class_method(:f) { 1 }\n  end\nend\n",
    );
    // (Each brought in by a call by name, which the error names, #1037:
    // the native `Array#delete`'s, or the one an in-place update makes.)
    for (call, reached) in [
        (
            "adel",
            Some("the native `Array#delete`, which is taken to call `==` by name on the values it is given, may reach `K#==` (lib.qz:2)"),
        ),
        (
            "hput",
            Some("a call of `hash` the runtime makes by name (for `Base#hput`) may reach `H#hash` (lib.qz:10)"),
        ),
        (
            "hdel",
            Some("a call of `hash` the runtime makes by name (for `Base#hdel`) may reach `H#hash` (lib.qz:10)"),
        ),
        ("apush", None),
    ] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass C < Base\n  {call}\nend\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        // (The library's own errors fail the check in any case.)
        assert!(!ok, "{call}");
        let refused = format!("`{call}` did not run: ");
        match reached {
            Some(m) => assert!(
                err.contains(&format!("{refused}{m}, a method of that name, which has errors")),
                "{call}: {err}"
            ),
            None => assert!(!err.contains(&refused), "{call}: {err}"),
        }
    }
}

/// A method named like one the runtime calls by name, here `status`, is
/// not in a statement's reach through natives that call nothing of the
/// kind (#394): #1037's reproducer, two unrelated helpers named `status`
/// using a member a later statement generates, compiles and runs.
#[test]
fn an_unrelated_helper_named_like_a_runtime_name_does_not_block_a_statement() {
    let d = dir();
    write(&d.0, "lib.qz", "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    xs: Array[A | B] = [A.new, B.new]\n    s = xs.map { |x| x.status.to_s }.join(\",\")\n    def_class_method(:asked) { s }\n  end\nend\nclass A\n  def status -> String = \"a\"\nend\nclass B\n  def status -> Int = 2\nend\n");
    let app = write(&d.0, "app.qz", "require_relative \"lib\"\nclass First < Model\n  ask\nend\nclass Post < Model\n  gen\nend\nclass Helper\n  def status(h: Int, m: Int) -> String = Post.new.title\nend\nclass Other\n  def status(x: String) -> String = Post.new.title + x\nend\nputs First.asked\n");
    run_and_build(&d.0, &app, "a,2\n");
}

/// A statement blocked by a method that came into its reach by name says
/// which call by name brought it (#1037): here `Array#join`, which calls
/// `to_s` by name on its elements, and the first method of the name with
/// errors in source order, with how many more there are.
#[test]
fn a_method_reached_by_name_is_named_with_the_call() {
    let d = dir();
    write(&d.0, "lib.qz", "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = [1, 2].join(\",\")\n    def_class_method(:asked) { s }\n  end\n  static def self.ask0 -> Void\n    s = C.to_s\n    def_class_method(:asked0) { s }\n  end\nend\n");
    let app = write(&d.0, "app.qz", "require_relative \"lib\"\nclass First < Model\n  ask\nend\nclass Post < Model\n  gen\nend\nclass Helper\n  def to_s -> String = Post.new.title\nend\nclass Other\n  def to_s -> String = Post.new.title + \"!\"\nend\nputs First.asked\n");
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("app.qz:3:3: error: `ask` did not run: the native `Array#join`, which is taken to call `to_s` by name on the values it is given, may reach `Helper#to_s` (app.qz:9), a method of that name, which has errors: undefined method `title` for Post (and 1 more method of that name with errors)"),
        "{err}"
    );
}

/// A method with errors that is not itself of the name, but is reached
/// from a method the call by name took, is named after the chain: the
/// call, the method of the name it pulled in, then the method with errors
/// (#1037: the reported helper's callee).
#[test]
fn a_method_reached_from_one_taken_by_name_names_the_chain() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = [J.new].join(\",\")\n    def_class_method(:asked) { s }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass First < Model\n  ask\nend\nclass Post < Model\n  gen\nend\nclass J\n  def to_s -> String = R.new.text\nend\nclass R\n  def text -> String = Post.new.title\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("app.qz:3:3: error: `ask` did not run: the native `Array#join`, which is taken to call `to_s` by name on the values it is given, may reach `J#to_s` (app.qz:9), a method of that name, which may reach `R#text` (app.qz:12), which has errors: undefined method `title` for Post"),
        "{err}"
    );
}

/// The method a by-name error names, and the count, are among those the
/// call reached by that name: a class method `to_s` with errors, which an
/// earlier statement reached directly, is not one `Array#join`'s
/// instance-side call takes, so it is neither named nor counted (#1037).
#[test]
fn a_by_name_error_counts_only_what_the_call_reached() {
    let d = dir();
    write(&d.0, "lib.qz", "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = [1, 2].join(\",\")\n    def_class_method(:asked) { s }\n  end\n  static def self.ask0 -> Void\n    s = C.to_s\n    def_class_method(:asked0) { s }\n  end\nend\n");
    let app = write(&d.0, "app.qz", "require_relative \"lib\"\nclass Zero < Model\n  ask0\nend\nclass First < Model\n  ask\nend\nclass Post < Model\n  gen\nend\nclass Helper\n  def to_s -> String = Post.new.title\nend\nclass C\n  def self.to_s -> String = Post.new.title\nend\n");
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    let line = err
        .lines()
        .find(|l| l.contains("`ask` did not run"))
        .unwrap_or_else(|| panic!("{err}"));
    assert_eq!(
        line,
        "app.qz:6:3: error: `ask` did not run: the native `Array#join`, which is taken to call `to_s` by name on the values it is given, may reach `Helper#to_s` (app.qz:12), a method of that name, which has errors: undefined method `title` for Post",
        "{err}"
    );
}

/// The natives classified with real names rather than every name (#394)
/// still reach what they call: `Enumerable#min` the elements' `<=>`,
/// `Array#join` their `to_s`, `Enumerator#size` its receiver's `each`.
/// A method of that name using a member a later statement generates
/// blocks the statement, naming it; with that statement first, the
/// program runs. A list too narrow would let the statement run into a
/// method with no body.
#[test]
fn a_native_with_real_names_reaches_them() {
    for (call, lib, classes, want) in [
        (
            "ask_sort",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask_sort -> Void\n    s = D.new.min.nil?\n    def_class_method(:a) { s }\n  end\nend\n",
            "class E\n  include Comparable[E]\n  def <=>(o: E) -> Int = Post.new.title.size\nend\nclass D\n  include Enumerable[E]\n  def each(&: (E) -> Void) -> Void\n    yield E.new\n    yield E.new\n  end\nend\n",
            "app.qz:3:3: error: `ask_sort` did not run: the native `Enumerable#min`, which is taken to call `<=>` by name on the values it is given, may reach `E#<=>` (app.qz:10), a method of that name, which has errors: undefined method `title` for Post",
        ),
        (
            "ask_join",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask_join -> Void\n    s = [J.new].join(\",\")\n    def_class_method(:a) { s }\n  end\nend\n",
            "class J\n  def to_s -> String = Post.new.title\nend\n",
            "app.qz:3:3: error: `ask_join` did not run: the native `Array#join`, which is taken to call `to_s` by name on the values it is given, may reach `J#to_s` (app.qz:9), a method of that name, which has errors: undefined method `title` for Post",
        ),
        (
            "ask_next",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask_next -> Void\n    s = C.new.to_enum.size\n    def_class_method(:a) { s }\n  end\nend\n",
            "class C\n  include Enumerable[Int]\n  def each(&: (Int) -> Void) -> Void\n    yield Post.new.title.size\n  end\nend\n",
            "app.qz:3:3: error: `ask_next` did not run: the native `Enumerator#size`, which is taken to call `each` by name on the values it is given, may reach `C#each` (app.qz:10), a method of that name, which has errors: undefined method `title` for Post",
        ),
    ] {
        let d = dir();
        write(&d.0, "lib.qz", lib);
        let post = "class Post < Model\n  gen\nend\n";
        // The statement first, `Post`'s after: blocked, naming the method.
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass First < Model\n  {call}\nend\n{post}{classes}"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{call}");
        assert!(err.contains(want), "{call}: {err}");
        // `Post`'s first: the method has its member, and the program runs.
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\n{post}class First < Model\n  {call}\nend\n{classes}"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(ok, "{call}: {err}");
    }
}

/// Each name of `shake::NATIVE_NAMES` beyond the common ones is still
/// taken to be sent by the natives that send it (#394, the split by
/// name): `status` by `Process::Output#success?`, `next` and `rewind` by
/// the `Enumerator` natives, `succ` by a range's (of dates), `to_json` by
/// `JSON.generate`, a method an enumerator was made for by the
/// enumerator's. A method of that name using a member a later statement
/// generates blocks the statement, naming the native; with that statement
/// first, the program checks. An attribution too narrow would let the
/// statement run into a method with no body.
#[test]
fn a_rare_name_reaches_its_methods_from_its_senders() {
    for (case, lib, classes, want) in [
        (
            "status",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = Process::Output.new(0, \"\", \"\").success?\n    def_class_method(:a) { s }\n  end\nend\n",
            "class H\n  def status -> Int = Post.new.title.size\nend\n",
            "app.qz:3:3: error: `ask` did not run: the native `Process::Output#success?`, which is taken to call `status` by name on the values it is given, may reach `H#status` (app.qz:9), a method of that name, which has errors: undefined method `title` for Post",
        ),
        (
            "next",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = N.new.each { |x| x }\n    def_class_method(:a) { s }\n  end\nend\n",
            "class N < Enumerator[Int]\n  def next -> Int\n    Post.new.title\n    raise StopIteration.new(\"done\")\n  end\nend\n",
            "app.qz:3:3: error: `ask` did not run: the native `Enumerator#each`, which is taken to call `next` by name on the values it is given, may reach `N#next` (app.qz:9), a method of that name, which has errors: undefined method `title` for Post",
        ),
        (
            "rewind",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = C.new.to_enum.rewind.nil?\n    def_class_method(:a) { s }\n  end\nend\n",
            "class C\n  def rewind -> Void\n    Post.new.title\n  end\n  include Enumerable[Int]\n  def each(&: (Int) -> Void) -> Void\n    yield 1\n  end\nend\n",
            "app.qz:3:3: error: `ask` did not run: the native `Enumerator#rewind`, which is taken to call `rewind` by name on the values it is given, may reach `C#rewind` (app.qz:9), a method of that name, which has errors: undefined method `title` for Post",
        ),
        (
            "succ",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = (Date.new(2026, 1, 1)..Date.new(2026, 1, 3)).to_a.size\n    def_class_method(:a) { s }\n  end\nend\n",
            "class H\n  def succ -> Int = Post.new.title.size\nend\n",
            "app.qz:3:3: error: `ask` did not run: the native `Range#to_a`, which is taken to call `succ` by name on the values it is given, may reach `H#succ` (app.qz:9), a method of that name, which has errors: undefined method `title` for Post",
        ),
        (
            "to_json",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = JSON.generate([1])\n    def_class_method(:a) { s }\n  end\nend\n",
            "class H\n  def to_json -> String = Post.new.title\nend\n",
            "app.qz:3:3: error: `ask` did not run: the native `JSON.generate`, which is taken to call `to_json` by name on the values it is given, may reach `H#to_json` (app.qz:9), a method of that name, which has errors: undefined method `title` for Post",
        ),
        (
            "upto",
            "class Model\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.ask -> Void\n    s = 3.upto(5).size\n    def_class_method(:a) { s }\n  end\nend\n",
            "class H\n  def upto(n: Int) -> Int = Post.new.title.size\nend\n",
            "app.qz:3:3: error: `ask` did not run: the native `Enumerator#size`, which is taken to call `upto` by name on the values it is given, may reach `H#upto` (app.qz:9), a method of that name, which has errors: undefined method `title` for Post",
        ),
    ] {
        let d = dir();
        write(&d.0, "lib.qz", lib);
        let post = "class Post < Model\n  gen\nend\n";
        // The statement first, `Post`'s after: blocked, naming the native.
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass First < Model\n  ask\nend\n{post}{classes}"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{case}");
        assert!(err.contains(want), "{case}: {err}");
        // `Post`'s first: the method has its member, and the program checks.
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\n{post}class First < Model\n  ask\nend\n{classes}"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(ok, "{case}: {err}");
    }
}

/// The `inherited` hook's statement stands at the end of its class's
/// body, in text order among the program's statements (docs/14 §2, §5,
/// #421): `First`'s runs before `Post`'s written statement, and `Post`'s
/// after it. A method with errors reached past a call by name is named
/// after the chain (#1055), the statement named by its hook and class.
#[test]
fn an_inherited_hook_runs_in_text_order_and_names_its_chain() {
    let d = dir();
    write(
        &d.0,
        "base.qz",
        "class Base\n  static def self.mark -> Void\n    puts \"mark #{self.name}\"\n  end\n  static def self.inherited -> Void\n    puts \"hook #{self.name}\"\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "main.qz",
        "require_relative \"base\"\nclass First < Base\nend\nclass Post < Base\n  mark\nend\nputs \"run\"\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(
        err.lines().collect::<Vec<_>>(),
        ["hook First", "mark Post", "hook Post"]
    );
    assert_eq!(out, "run\n");
    let lib = "class Base\n  static def self.gen -> Void\n    def_method(:title) { \"generated\" }\n  end\n  static def self.inherited -> Void\n    s = [J.new].join(\",\")\n    def_class_method(:asked) { s }\n  end\nend\n";
    write(&d.0, "base.qz", lib);
    let classes = "class J\n  def to_s -> String = R.new.text\nend\nclass R\n  def text -> String = Post.new.title\nend\n";
    let app = write(
        &d.0,
        "main.qz",
        &format!("require_relative \"base\"\nclass First < Base\nend\nclass Post < Base\n  gen\nend\n{classes}"),
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("main.qz:2:1: error: `Base.inherited`, run for `First`, did not run: the native `Array#join`, which is taken to call `to_s` by name on the values it is given, may reach `J#to_s` (main.qz:8), a method of that name, which may reach `R#text` (main.qz:11), which has errors: undefined method `title` for Post"),
        "{err}"
    );
    // `Post`'s statement first: its hook, and `First`'s after, find
    // `title` generated.
    let app = write(
        &d.0,
        "main.qz",
        &format!("require_relative \"base\"\nclass Post < Base\n  gen\nend\nclass First < Base\nend\nputs First.asked\n{classes}"),
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "generated\n");
}

/// The `inherited` hook in a script (docs/14 §5, #421): a subclass in a
/// file requiring the file that declares the hook runs it; in the same
/// file, the staging rule refuses it. The checker's cache follows the
/// required file gaining or losing the hook, and the warm run prints what
/// the cold one did.
#[test]
fn an_inherited_hook_runs_in_a_script_and_its_cache() {
    let d = dir();
    let hook = |body: &str| {
        format!("class Base\n  static def self.inherited -> Void\n    def_method(:kind) {{ \"{body}\" }}\n  end\nend\n")
    };
    write(&d.0, "base.qz", &hook("hooked"));
    let app = write(
        &d.0,
        "main.qz",
        "require_relative \"base\"\nclass A < Base\nend\nputs A.new.kind\n",
    );
    let run = || quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    for _ in 0..2 {
        let (ok, out, err) = run();
        assert!(ok, "{err}");
        assert_eq!(out, "hooked\n");
    }
    write(
        &d.0,
        "base.qz",
        "class Base\n  static def self.other -> Void\n  end\nend\n",
    );
    let (ok, _, err) = run();
    assert!(!ok);
    assert!(
        err.contains("main.qz:4:6: error: undefined method `kind` for A"),
        "{err}"
    );
    write(&d.0, "base.qz", &hook("again"));
    for _ in 0..2 {
        let (ok, out, err) = run();
        assert!(ok, "{err}");
        assert_eq!(out, "again\n");
    }
    // `--expand` names the hook and the class it ran for.
    let (ok, out, err) = quarz(&d.0, &["check", "--expand", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert!(
        out.contains("class A  # main.qz:2\n  # generated by `Base.inherited (run for A)` at main.qz:2\n  def kind -> String = <block at base.qz:3>\nend\n"),
        "{out}"
    );
    let same = write(
        &d.0,
        "same.qz",
        "class B2\n  static def self.inherited -> Void\n  end\nend\nclass C2 < B2\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", same.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("same.qz:5:1: error: `C2` is a subclass of `B2`, whose `static def self.inherited` runs for each subclass at compile time (docs/14 §5), and a `static def` of this file cannot run here (the staging rule, §2): declare `C2` in a file that requires `B2`'s (loaded before it)"),
        "{err}"
    );
}

/// `Type#constructors` (docs/14 §4, #1045): the signatures `new` takes,
/// those `World::constructors` gives `new` (docs/01 §3), the expected
/// lines derived from that rule:
/// - none for a class whose `new` takes no arguments (`Plain`);
/// - its own overloads, optional, keyword and private ones included,
///   in order (`Two`); a protected one (`Prot`);
/// - inherited when `new` takes them (`Kid`, `Free`), as the class has
///   them (named after the class); not past a class between with fields
///   to assign (`Below` takes `Between`'s, not `Base0`'s);
/// - a generic class's with its parameter (`Box`), and with its argument
///   applied below it (`IntBox`);
/// - an abstract class's (`Abs`);
/// - a generated one, after the statement that generated it (`Gen`);
/// - a data type's and a variant's constructor (`D`, `E::V`);
/// - each named `initialize`, returning the class, not static.
///
/// Read from `static(...)` while the class's statements are pending, it
/// is refused as the other reflection is (§8).
#[test]
fn constructors_list_what_new_takes() {
    let d = dir();
    write(&d.0, "lib.qz", "class Lib\n  static def self.sig(t: Type[Object]) -> String\n    t.constructors.map { |c| \"(\" + c.params.map { |p| \"#{p.name}: #{p.type_ref} #{p.kind}\" }.join(\", \") + \") -> #{c.result} #{c.name} #{c.static}\" }.join(\" | \")\n  end\n  static def self.show -> Void\n    puts \"#{self.name}: [#{Lib.sig(self.type)}]\"\n  end\n  static def self.show_of(t: Type[Object]) -> Void\n    puts \"#{t.name}: [#{Lib.sig(t)}]\"\n  end\n  static def self.gen_init -> Void\n    def_initialize(:x) { |x: Int| }\n  end\n  static def self.count(t: Type[Object]) -> Int = t.constructors.size\n  static def self.mark(n: Int) -> Void\n  end\nend\n");
    let app = write(&d.0, "main.qz", "require_relative \"lib\"\ndata D = (x: Int, y: String)\nenum E\n  variant V(a: Int)\n  variant W\nend\nclass Plain < Lib\n  show\nend\nclass Two < Lib\n  @n: Int\n  def initialize(@n: Int, label: String = \"x\"); end\n  private def initialize(s: String, *, k: Int); @n = 0; end\n  show\nend\nclass Kid < Two\n  show\nend\nclass Prot < Lib\n  @n: Int\n  protected def initialize(@n: Int); end\n  show\nend\nclass Box[T] < Lib\n  @v: T\n  def initialize(@v: T); end\n  show\nend\nclass IntBox < Box[Int]\n  show\nend\nabstract class Abs < Lib\n  @a: Int\n  def initialize(@a: Int); end\n  show\nend\nclass Gen < Lib\n  show\n  gen_init\n  show\nend\nclass Base0 < Lib\n  def initialize(s: String); end\nend\nclass Between < Base0\n  @f: Int\n  def initialize(@f: Int); super(\"x\"); end\nend\nclass Below < Between\n  show\nend\nclass Free < Base0\n  show\nend\nclass Probe < Lib\n  show_of D\n  show_of E::V\nend\n");
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(
        err.lines().collect::<Vec<_>>(),
        ["Plain: []", "Two: [(n: Int Meta::ParamKind::Required, label: String Meta::ParamKind::Optional) -> Two initialize false | (s: String Meta::ParamKind::Required, k: Int Meta::ParamKind::Keyword) -> Two initialize false]", "Kid: [(n: Int Meta::ParamKind::Required, label: String Meta::ParamKind::Optional) -> Kid initialize false | (s: String Meta::ParamKind::Required, k: Int Meta::ParamKind::Keyword) -> Kid initialize false]", "Prot: [(n: Int Meta::ParamKind::Required) -> Prot initialize false]", "Box: [(v: T Meta::ParamKind::Required) -> Box initialize false]", "IntBox: [(v: Int Meta::ParamKind::Required) -> IntBox initialize false]", "Abs: [(a: Int Meta::ParamKind::Required) -> Abs initialize false]", "Gen: []", "Gen: [(x: Int Meta::ParamKind::Required) -> Gen initialize false]", "Below: [(f: Int Meta::ParamKind::Required) -> Below initialize false]", "Free: [(s: String Meta::ParamKind::Required) -> Free initialize false]", "D: [(x: Int Meta::ParamKind::Required, y: String Meta::ParamKind::Required) -> D initialize false]", "E::V: [(a: Int Meta::ParamKind::Required) -> E::V initialize false]"],
        "{err}"
    );
    let bad = write(&d.0, "bad.qz", "require_relative \"lib\"\nclass Post < Lib\n  mark(static(Lib.count(Post)))\n  gen_init\nend\n");
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("reflects on a class whose `static` statements have not all run (`mark` in `Post`, `gen_init` in `Post`)"),
        "{err}"
    );
}

/// `Meta::Param#default` (docs/14 §4, #1060): whether a call may leave
/// the parameter out, for every kind, in `methods` and in `constructors`.
/// The expected lines are derived from the rule: false for a required
/// positional parameter and for a keyword without a default; true for an
/// optional positional one, a rest, a keyword with a default and a
/// keyword rest. A method's block is not among its parameters
/// (`opt_block` lists none).
#[test]
fn a_param_says_whether_a_call_may_leave_it_out() {
    let d = dir();
    write(&d.0, "lib.qz", "class Lib\n  static def self.show -> Void\n    methods.select { |m| m.name == :all_kinds || m.name == :opt_block }.each do |m|\n      puts \"#{m.name}: \" + m.params.map { |p| \"#{p.name} #{p.kind} #{p.default}\" }.join(\", \")\n    end\n    constructors.each do |c|\n      puts \"initialize: \" + c.params.map { |p| \"#{p.name} #{p.kind} #{p.default}\" }.join(\", \")\n    end\n  end\nend\n");
    let app = write(&d.0, "main.qz", "require_relative \"lib\"\nclass K < Lib\n  @a: Int\n  def initialize(@a: Int, b: Int = 1, *, client: String, retries: Int = 3); end\n  def all_kinds(a: Int, b: Int = 1, *rest: Int, k: Int, j: Int = 2, **kw: Int, &blk: () -> Void) -> Void; end\n  def opt_block(&blk: (() -> Void)?) -> Void; end\n  show\nend\n");
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(err.lines().collect::<Vec<_>>(), ["all_kinds: a Meta::ParamKind::Required false, b Meta::ParamKind::Optional true, rest Meta::ParamKind::Rest true, k Meta::ParamKind::Keyword false, j Meta::ParamKind::Keyword true, kw Meta::ParamKind::Keyword true", "opt_block: ", "initialize: a Meta::ParamKind::Required false, b Meta::ParamKind::Optional true, client Meta::ParamKind::Keyword false, retries Meta::ParamKind::Keyword true"], "{err}");
}

/// The runner keeps `overrides_of`'s answers across rounds (#1057) and
/// drops those a generated method may change: `A`'s statement asks for
/// `Base#greet`'s overrides (none), `Sub`'s generates one, which reads a
/// file, and `C`'s, reaching `Base#greet` again, must see it. Were the
/// answer kept, `C`'s statement would not be refused here (and a debug
/// build's comparison of every kept answer with a fresh one fails).
#[test]
fn a_kept_override_answer_follows_a_generated_override() {
    let d = dir();
    write(&d.0, "lib.qz", "class Base\n  def greet -> String = \"base\"\n  static def self.ask -> Void\n    s = Base.new.greet\n    def_class_method(:asked) { s }\n  end\n  static def self.gen_greet -> Void\n    def_method(:greet, override: true) { File.read(\"/etc/hostname\") }\n  end\nend\n");
    let app = write(
        &d.0,
        "main.qz",
        "require_relative \"lib\"\nclass A < Base\n  ask\nend\nclass Sub < Base\n  gen_greet\nend\nclass C < Base\n  ask\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.starts_with("main.qz:9:3: error: `ask` reaches `File.read` (via Sub#greet), which cannot run at compile time"),
        "{err}"
    );
}

/// The static rounds' world, updated in place from round to round
/// (#1057 PR 4), against the rows that change mid-check, each round
/// compared with a fresh fill in a debug build: a field generated into a
/// class and its subclass after earlier rounds filled them (`B`'s
/// `add_f`, `C` below it), a construction reached by a later round (`D`'s
/// `make_one`, with an inherited default), a constant first initialized
/// by a later round (`E`'s `read_c`). `Late`'s default is lowered only by
/// the final lowering, which fills from scratch: the program run and
/// built shows it (it would not, were the static rounds' world shipped).
#[test]
fn the_static_rounds_world_follows_what_a_round_changes() {
    let d = dir();
    write(&d.0, "lib.qz", "class Model\n  static def self.gen -> Void\n    def_method((\"g_\" + self.name).to_sym) { 1 }\n  end\n  static def self.add_f -> Void\n    def_field(:hits, Int, 0, var: true, reader: true)\n  end\n  static def self.make_one -> Void\n    s = Pt.new.n + Qt.new.n\n    def_class_method(:got) { s }\n  end\n  static def self.read_c -> Void\n    s = LIMIT + 1\n    def_class_method(:limit_seen) { s }\n  end\nend\ndef compute -> Int = 5\nLIMIT = compute + 10\nclass Pt\n  @n: Int = compute\n  def n -> Int = @n\nend\nclass Qt < Pt\nend\nclass Late\n  @v: Int = compute + 2\n  def v -> Int = @v\nend\n");
    let app = write(&d.0, "main.qz", "require_relative \"lib\"\nclass A < Model\n  gen\nend\nclass B < A\n  add_f\nend\nclass C < B\n  gen\nend\nclass D < Model\n  make_one\nend\nclass E < Model\n  read_c\nend\nputs C.new.hits\nputs D.got\nputs E.limit_seen\nputs Late.new.v\n");
    run_and_build(&d.0, &app, "0\n10\n16\n7\n");
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
    // `def self.` over an included module's or `Type`'s (a
    // `Meta::ClassDef`'s in a static def, whose `self` is the class; not
    // `type`, always the reflection's there, #553), an abstract class's
    // requirement implemented below it (the subclass's own method, its
    // include, a top-level extension's module of it: one above it is
    // hidden by the abstract declaration, #687's option 1).
    for (lib, app, want) in [
        ("module Shape\n  abstract def area -> Int\n  def describe -> String = \"area #{area}\"\nend\nclass Base\n  def area -> Int = 7\nend\nclass Sq < Base\n  include Shape\nend\nclass Model\n  static def self.show(s: Shape) -> Void\n    puts s.describe\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show Sq.new\nend\n", "area 7\n"),
        ("module Loud\n  def label -> String = \"loud\"\nend\nclass A\n  def label -> String = \"a\"\nend\nclass B < A\n  include Loud\nend\nclass Model\n  static def self.show(k: A) -> Void\n    puts k.label\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show B.new\nend\n", "loud\n"),
        ("module Named\n  def self.label -> String = \"base\"\nend\nclass A\n  include Named\nend\nclass B < A\n  def self.label -> String = \"B\"\nend\nclass Model\n  static def self.show(k: Type[A]) -> Void\n    puts k.label\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show B\nend\n", "B\n"),
        ("class A\n  def self.name -> String = \"customA\"\nend\nclass Model\n  static def self.show(k: Type[Object]) -> Void\n    puts k.name\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show A\nend\n", "customA\n"),
        ("class Model\n  static def self.show -> Void\n    puts type.name\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  def self.type -> Type[Post]\n    puts \"own type\"\n    Post\n  end\n  show\nend\n", "Post\n"),
        ("module Typed\n  def self.doc(text: String) -> Void\n    puts \"typed #{text}\"\n  end\nend\nclass Model\n  static def self.show -> Void\n    doc(\"x\")\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  include Typed\n  show\nend\n", "typed x\n"),
        ("class Base\n  def label -> String = \"base\"\nend\nabstract class A < Base\n  abstract def label -> String\nend\nclass B < A\n  def label -> String = \"b\"\nend\nclass Model\n  static def self.show(k: A) -> Void\n    puts k.label\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show B.new\nend\n", "b\n"),
        ("module N\n  def label -> String = \"n\"\nend\nclass Base\n  def label -> String = \"base\"\nend\nabstract class A < Base\n  abstract def label -> String\nend\nclass B < A\n  include N\nend\nclass Model\n  static def self.show(k: A) -> Void\n    puts k.label\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show B.new\nend\n", "n\n"),
        ("module N\n  def label -> String = \"top\"\nend\nclass Base\n  def label -> String = \"base\"\nend\nabstract class A < Base\n  abstract def label -> String\nend\nclass B < A\nend\nextension B\n  include N\nend\nclass Model\n  static def self.show(k: A) -> Void\n    puts k.label\n  end\nend\n", "require_relative \"lib\"\nclass Post < Model\n  show B.new\nend\n", "top\n"),
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
  # Several lines, one hook: the first line registers it (#444).
  static def self.check_name(n: String) -> Void
    statement_values[String](:names).add(n)
    at_class_end(:names) do |cls|
      cls.statement_values[String](:names).values.each { |x| raise ArgumentError, "bad name #{x}" if x == "bad" }
    end
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

    // The errors, at the statement (a hook's at the statement that
    // registered it, the first under its key, naming its key and that
    // `static def`, #444).
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass A < Endpoint\n  plug Plug.new(\"a\", 1)\n  misnamed\nend\nclass B < Endpoint\n  failing\n  plug Plug.new(\"b\", 1)\nend\nclass C < Endpoint\n  nesting\nend\nclass D < Endpoint\n  adding\nend\nclass E < Endpoint\n  check_name \"ok\"\n  check_name \"bad\"\n  plug Plug.new(\"e\", 1)\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("bad.qz:4:3: error: `misnamed` raised RuntimeError: the statement values `:plugs` were made as `StatementValues[Plug]`, and are named here as `StatementValues[String]`: a key has one type"),
        "{err}"
    );
    assert!(
        err.contains("bad.qz:7:3: error: the class-end hook `:failing` (registered by `failing`) raised ArgumentError: no plugs"),
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
    // Two lines register `:names`; the hook fails on the second's data,
    // and is located at the first, which registered it (#444).
    assert!(
        err.contains("bad.qz:17:3: error: the class-end hook `:names` (registered by `check_name`) raised ArgumentError: bad name bad"),
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
        err.contains("app.qz:6:3: error: `join_things` did not run: the native `Array#join`, which is taken to call `to_s` by name on the values it is given, may reach `Bad#to_s` (app.qz:3), a method of that name, which has errors"),
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

#[test]
fn json_decode_runs_at_compile_time() {
    // `JSON.decode[T]` is pure: a `static def` decodes its argument into a
    // `data` value it bakes into a generated method (#400).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "require \"json\"\ndata Conf = (name: String, size: Int = 3)\nclass Base\n  static def self.configure(text: String) -> Void\n    c = JSON.decode[Conf](text)\n    def_class_method(:conf) { c }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass App < Base\n  configure '{\"name\": \"x\"}'\nend\np App.conf\n",
    );
    run_and_build(&d.0, &app, "Conf(name: \"x\", size: 3)\n");
}

#[test]
fn json_decode_refuses_a_type_json_does_not_decode_into() {
    // `JSON.decode[T]`: the checker refuses a `T` JSON does not decode
    // into, naming the type at fault, and a call without `T` written
    // (#400).
    let d = dir();
    let app = write(
        &d.0,
        "app.qz",
        r#"require "json"
class Foo
end
enum E
  variant A
end
data W = (f: Foo)
data U = (x: Int | Float)
data R = (id: String)
data S = (n: Int)
u1 = JSON.decode[String | Time]("1")
u2 = JSON.decode[R | S]("1")
u3 = JSON.decode[R | Hash[String, Int]]("1")
u4 = JSON.decode[Array[Int] | Set[Int]]("1")
u5 = JSON.decode[Array[JSON::Value | String]]("1")
u6 = JSON.decode[Int | Integer | String]("1")
u7 = JSON.decode[(Bool | E)?]("1")
x = JSON.decode[Object]("1")
y = JSON.decode[W]("{}")
z = JSON.decode[E]("1")
w = JSON.decode[U]("{}")
sd = JSON.decode[String | Date]("1")
td = JSON.decode[Time | Date]("1")
di = JSON.decode[Decimal | Int]("1")
df = JSON.decode[Decimal | Float]("1")
dsr = JSON.decode[Decimal | String]("1")
dd = JSON.decode[Decimal | Date]("1")
db = JSON.decode[Decimal | Bool | Array[Decimal]]("1")
v = JSON.decode?[Hash[Int, Int]]("{}")
def gen[T](s: String) -> T = JSON.decode[T](s)
r: Int = JSON.decode("1")
f = JSON.:decode
data P[T] = (x: T, nxt: P[Array[T]]? = nil)
q = JSON.decode[P[Int]]("{}")
o = JSON.decode[JSON::Value?]("null")
data Wrap[T] = (x: T)
ok = JSON.decode[Wrap[Wrap[Int]]]('{"x": {"x": 1}}')
"#,
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    for want in [
        "`JSON.decode` cannot decode into Object: `Object` is a class: only `data` types are decoded from objects",
        "`JSON.decode` cannot decode into W: `Foo` is a class",
        "`JSON.decode` cannot decode into E: `E` is an enum",
        "`JSON.decode` cannot decode into U: `Int | Float` is a union JSON cannot tell apart: `Int` and `Float` are both decoded from a number",
        "`JSON.decode` cannot decode into String | Time: `String | Time` is a union JSON cannot tell apart: `String` and `Time` are both decoded from a string",
        "`JSON.decode` cannot decode into String | Date: `String | Date` is a union JSON cannot tell apart: `String` and `Date` are both decoded from a string",
        "`JSON.decode` cannot decode into Time | Date: `Time | Date` is a union JSON cannot tell apart: `Time` and `Date` are both decoded from a string",
        // (A `Decimal` is decoded from a number and from a string, #889.)
        "`JSON.decode` cannot decode into Decimal | Int: `Decimal | Int` is a union JSON cannot tell apart: `Decimal` and `Int` are both decoded from a number",
        "`JSON.decode` cannot decode into Decimal | Float: `Decimal | Float` is a union JSON cannot tell apart: `Decimal` and `Float` are both decoded from a number",
        "`JSON.decode` cannot decode into Decimal | String: `Decimal | String` is a union JSON cannot tell apart: `Decimal` and `String` are both decoded from a string",
        "`JSON.decode` cannot decode into Decimal | Date: `Decimal | Date` is a union JSON cannot tell apart: `Decimal` and `Date` are both decoded from a string",
        "`JSON.decode` cannot decode into R | S: `R | S` is a union JSON cannot tell apart: `R` and `S` are both decoded from an object",
        "is a union JSON cannot tell apart: `R` and `Hash[String, Int]` are both decoded from an object",
        "is a union JSON cannot tell apart: `Array[Int]` and `Set[Int]` are both decoded from an array",
        "is a union JSON cannot tell apart: `JSON::Value` is decoded from any JSON value: write `JSON::Value`",
        "are both decoded from a number",
        "`JSON.decode` cannot decode into Bool | E | Nil: `E` is an enum",
        "`JSON.decode?` cannot decode into Hash[Int, Int]: `Hash[Int, Int]` has keys that are neither `String` nor `Symbol`",
        "`JSON.decode` cannot decode into T: `T` is a type parameter: the type must be written at the call",
        "`JSON.decode` takes the type to decode into explicitly (`JSON.decode[Args](text)`)",
        "`JSON.decode` takes the type to decode into written at the call: call it (`JSON.decode[Args](text)`), there is no reference to it",
        "`JSON.decode` cannot decode into P[Int]: `P` holds itself with other type arguments, without end",
        "`JSON.decode` cannot decode into JSON::Value?: `JSON::Value?` is nullable, but `JSON::Value` holds `null` already",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
    // (A nesting written out is no recursion.)
    assert!(!err.contains("Wrap"), "{err}");
    // (`Decimal` beside a boolean and an array: told apart.)
    assert!(!err.contains("Decimal | Bool"), "{err}");
}

#[test]
fn compile_time_purity_is_an_allow_list() {
    // A native that draws randomness refuses the statement before it runs
    // (#399), as one acting on the world does; a pure use of the same
    // library (verifying a signature) runs at compile time.
    let pem = "-----BEGIN PUBLIC KEY-----\nMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAvXSjzZicRhyOrbfEWfcN\nIUQmSOHU8HBnBzZpXWSSY+02CO+cA8Q1aU8HYw+TBQa5Ni638E3EeAf3DsVA0fJL\nSDU5VL6QIsL+uhjTce7XK4OP/dgzLwRAclPNWo4ASeMkHSrP9+0/LtVxCpIup7zL\n+2lsBdNEirMS7IAbQycONanJ/VRSpgFH3CxkgKiZlb0A+QzXl/0PnLqALCio2iHW\neOLwODywEkvKn7rQ3JEjSmwm7TtQu4cufwDgSc9NeSl9JdetZ3yClZGGOE8Zschf\nxYMsnhwAEoZDGN9lA41J2oTKK81Ni1mf8hBkeEIkRGl+w/p09KxKuFkngqsEGWVM\nUwIDAQAB\n-----END PUBLIC KEY-----\n";
    let lib = format!(
        "require \"crypto\"\nrequire \"base64\"\nclass K\n  PEM = \"{pem}\"\n  static def self.gen -> Void\n    salt = Crypto.random_bytes(4).to_s\n    def_class_method(:salt) {{ salt }}\n  end\n  static def self.hashed -> Void\n    h = Crypto::Argon2.hash(\"pw\")\n    def_class_method(:h) {{ h }}\n  end\n  static def self.shuffled -> Void\n    s = [1, 2, 3].shuffle\n    def_class_method(:sh) {{ s }}\n  end\n  static def self.keyed -> Void\n    k = Crypto::RSA::PrivateKey.generate.bits\n    def_class_method(:k) {{ k }}\n  end\n  static def self.verified -> Void\n    ok = Crypto::RSA::PublicKey.from_pem(PEM).verify(\"hello\", Base64.decode(\"rFXxSLIUWR/cKBx0V2o82USETmjP9Jv6Vvti1LBYWT89NbNu9/gTCNjEjoq5y96Ag6kICcP+GEuc8Lno1wvGRa6hPxKEFCnAjLhoxniPlxhbr0iR8OCczQB1E1m/Xev/U3as86Ab25xJN/sX9QrqN/em40tOjKn639nUhUl2W6BQ+FzSAA5MSj/vX5autUXeiydM199OhtmNfphqW0UVWKXq9TBL2bOxQ4jDgZoYb45xrv91qEOkTBMUX6uylsa1I/EiDKyltkswMYnHaJw7Np/H4YcMBf3j571vbdZoUUjZxxdgDmOv5SsCLMm2xPaVdDIKnuR/Skxl5aLMlpHlUw==\"), :sha256)\n    def_class_method(:ok) {{ ok }}\n  end\nend\n"
    );
    let d = dir();
    write(&d.0, "lib.qz", &lib);
    for (stmt, via) in [
        ("gen", "`gen` reaches `Crypto.random_bytes`, which cannot run at compile time"),
        ("hashed", "`hashed` reaches `Crypto.random_bytes` (via Crypto::Argon2.hash), which cannot run at compile time"),
        (
            "shuffled",
            "`shuffled` reaches `Array#shuffle`, which cannot run at compile time",
        ),
        ("keyed", "`keyed` reaches `Crypto::RSA::PrivateKey.generate_with` (via Crypto::RSA::PrivateKey.generate), which cannot run at compile time"),
    ] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass A < K\n  {stmt}\nend\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok);
        assert!(err.contains(&format!("app.qz:3:3: error: {via}")), "{err}");
    }
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < K\n  verified\nend\np A.ok\n",
    );
    run_and_build(&d.0, &app, "true\n");
}

#[test]
fn compile_time_runs_take_utc_as_the_local_zone() {
    // A compilation does not depend on the machine's time zone: a static
    // statement's (and `static(...)`'s) local times are UTC; the program
    // keeps the real zone (#399).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  static def self.stamp -> Void\n    a = Time.at(0).to_s\n    b = Time.local(2026, 1, 2, 3, 4, 5).to_s\n    c = Time.parse(\"2026-01-02 03:04\").utc_offset\n    d = Time.utc(2026, 1, 2).getlocal.zone\n    def_class_method(:stamped) { \"#{a} | #{b} | #{c} | #{d}\" }\n  end\nend\nclass Clock\n  static def self.epoch -> String = Time.at(0).to_s\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Base\n  stamp\nend\nputs A.stamped\nX = static(Clock.epoch)\nputs X\nputs Time.at(0).to_s\n",
    );
    for (tz, local) in [
        ("UTC", "1970-01-01 00:00:00 +0000"),
        ("Asia/Tokyo", "1970-01-01 09:00:00 +0900"),
    ] {
        let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[("TZ", tz)]);
        assert!(ok, "{err}");
        assert_eq!(
            out,
            format!("1970-01-01 00:00:00 +0000 | 2026-01-02 03:04:05 +0000 | 0 | +00:00\n1970-01-01 00:00:00 +0000\n{local}\n"),
            "TZ={tz}"
        );
    }
}

#[test]
fn json_decode_of_a_type_parameter_a_generated_method_carries() {
    // `JSON.decode[A]` in a `def_method` block whose `A` the generated
    // method carries (docs/14 §5): decided at the statement, with its
    // class; a class that does not decode is refused there; a type
    // parameter elsewhere stays refused (#409).
    let lib = "require \"json\"\nclass Base\n  static def self.args[A](type: Type[A]) -> Void\n    def_method(:decode_args, :text) { |text: String| -> A JSON.decode[A](text) }\n    def_method(:many, :text) { |text: String| -> Array[A]? JSON.decode?[Array[A]?](text) }\n    def_method(:lit) { -> String \"\\u{1}json-type-deferred\" }\n  end\nend\n";
    let d = dir();
    write(&d.0, "lib.qz", lib);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\ndata P = (x: Int, tags: Array[String] = [])\nclass J < Base\n  args P\nend\np J.new.decode_args('{\"x\": 1}')\np J.new.many('[{\"x\": 2}]')\np J.new.many(\"x\")\np J.new.lit\n",
    );
    // (A string the program writes equal to the marker stays as written.)
    run_and_build(
        &d.0,
        &app,
        "P(x: 1, tags: [])\n[P(x: 2, tags: [])]\nnil\n\"\\u0001json-type-deferred\"\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Foo\nend\ndata W = (f: Foo)\nclass K < Base\n  args W\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.starts_with("app.qz:6:3: error: `def_method(:decode_args)`: `JSON.decode` in the block cannot decode into W: `Foo` is a class"),
        "{err}"
    );
    let app = write(
        &d.0,
        "app.qz",
        "require \"json\"\ndef gen[T](s: String) -> T = JSON.decode[T](s)\nclass Base2\n  static def self.direct[A](type: Type[A]) -> Void\n    x = JSON.decode[A](\"1\")\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    for want in [
        "app.qz:2:30: error: `JSON.decode` cannot decode into T: `T` is a type parameter",
        "app.qz:5:9: error: `JSON.decode` cannot decode into A: `A` is a type parameter",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
}

#[test]
fn json_decode_of_a_union_with_a_type_parameter_a_generated_method_carries() {
    // `JSON.decode[A | String]` in a `def_method` block: the union is
    // checked at the statement, with `A` put in (flattened: a union or an
    // optional `A` adds its members), and refused there when two members
    // are decoded from one kind of JSON value (#828). (`A` is inferred
    // from a value: a union is no value to pass as a `Type`.)
    let lib = "require \"json\"\ndata Box[T] = (v: T)\nclass Base\n  static def self.args[A](sample: Box[A]) -> Void\n    def_method(:dec, :text) { |text: String| -> A | String JSON.decode[A | String](text) }\n  end\nend\n";
    let d = dir();
    write(&d.0, "lib.qz", lib);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\ndata P = (x: Int)\nclass J < Base\n  args Box[P].new(v: P.new(x: 0))\nend\nclass K < Base\n  args Box[Int | Array[Int]].new(v: 1)\nend\nclass L < Base\n  args Box[String?].new(v: nil)\nend\np J.new.dec('{\"x\": 1}')\np J.new.dec('\"s\"')\np K.new.dec(\"[1]\")\np K.new.dec(\"2\")\np K.new.dec('\"t\"')\np L.new.dec(\"null\")\np L.new.dec('\"u\"')\n",
    );
    run_and_build(&d.0, &app, "P(x: 1)\n\"s\"\n[1]\n2\n\"t\"\nnil\n\"u\"\n");
    for (arg, want) in [
        ("Box[Time].new(v: Time.at(0))", "`Time | String` is a union JSON cannot tell apart: `Time` and `String` are both decoded from a string"),
        ("Box[JSON::Value].new(v: JSON.parse(\"1\"))", "is a union JSON cannot tell apart: `JSON::Value` is decoded from any JSON value"),
        ("Box[Symbol | Int].new(v: 1)", "are both decoded from a string"),
    ] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass K < Base\n  args {arg}\nend\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{arg}");
        assert!(
            err.starts_with("app.qz:3:3: error: `def_method(:dec)`: `JSON.decode` in the block cannot decode into "),
            "{arg}: {err}"
        );
        assert!(err.contains(want), "{arg}: {want}\n{err}");
    }
}

#[test]
fn json_decode_keeps_a_data_class_named_only_in_a_union() {
    // A `data` type the program names nowhere but in a union `JSON.decode`
    // decodes into: compiled, the tree shake keeps its class and methods,
    // which the descriptor names (#828).
    let d = dir();
    let app = write(
        &d.0,
        "app.qz",
        "require \"json\"\ndata OnlyHere = (k: String)\nv = JSON.decode[Int | OnlyHere]('{\"k\": \"a\"}')\np v\nputs v.to_s\nputs JSON.generate(v)\np JSON.decode[Int | OnlyHere](\"3\")\n",
    );
    run_and_build(
        &d.0,
        &app,
        "OnlyHere(k: \"a\")\nOnlyHere(k: \"a\")\n{\"k\":\"a\"}\n3\n",
    );
}

#[test]
fn a_handle_typed_with_a_static_defs_parameter_called_by_name_elsewhere() {
    // The program calls a method named `args` elsewhere (`e.args`), so the
    // type arguments of statements calling `Base.args` do not hold
    // (docs/14 §5, by name): a handle typed with `A` is refused, the error
    // naming that call and suggesting another name; renamed, it is
    // accepted (#417).
    let lib = |name: &str| {
        format!("class Base\n  static def self.{name}[A](type: Type[A]) -> Void\n    perform = method_ref[(A) -> String](:perform)\n    def_method(:run_with, :a) {{ |a: A| -> String perform.bind(self).call(a) }}\n  end\nend\n")
    };
    let app = |name: &str| {
        format!("require_relative \"lib\"\ndata W = (x: Int)\nclass Entry\n  def args -> String = \"e\"\nend\nclass Use\n  def show(e: Entry) -> String = e.args\nend\nclass J < Base\n  def perform(a: W) -> String = \"#{{a.x}}\"\n  {name} W\nend\np J.new.run_with(W.new(2))\np Use.new.show(Entry.new)\n")
    };
    let d = dir();
    write(&d.0, "lib.qz", &lib("args"));
    let path = write(&d.0, "app.qz", &app("args"));
    let exe = d.0.join("app-bin");
    for args in [
        vec!["run", path.to_str().unwrap()],
        vec!["build", path.to_str().unwrap(), "-o", exe.to_str().unwrap()],
    ] {
        let (ok, _, err) = quarz(&d.0, &args, &[]);
        assert!(!ok);
        assert!(
            err.starts_with("app.qz:11:3: error: `method_ref(:perform)`: the handle to `J#perform` is made with `A`, a type parameter of `args`, which has no class here: the program also calls a method named `args` (at app.qz:7), so the type arguments of the statements calling `args` do not hold (docs/14 §5, by name over the whole program); give the `static def` a less common name"),
            "{args:?}: {err}"
        );
    }
    write(&d.0, "lib.qz", &lib("job_args"));
    let path = write(&d.0, "app.qz", &app("job_args"));
    run_and_build(&d.0, &path, "\"2\"\n\"e\"\n");
}

#[test]
fn override_true_requires_a_generated_method_to_override() {
    // `override: true` (#328): the statement is an error unless the
    // generated method overrides an inherited one of its name.
    let lib = "module Ext\n  def self.made -> String = \"ext\"\nend\nclass Base\n  include Ext\n  def greet(name: String) -> String = \"base #{name}\"\n  def size_of(n: Int) -> String = \"base #{n}\"\n  def with(*, a: Int = 0, b: Int = 0) -> String = \"base #{a} #{b}\"\n  def label(name: String) -> String = \"base\"\n  def self.kind -> String = \"base\"\n  static def self.gen_ok -> Void\n    def_method(:greet, :name, override: true) { |name: String| -> String \"gen #{name}\" }\n    def_class_method(:kind, override: true) { -> String \"gen kind\" }\n    def_class_method(:made, override: true) { -> String \"gen made\" }\n  end\n  static def self.gen_disjoint -> Void\n    def_method(:size_of, :s, override: true) { |s: String| -> String \"gen #{s}\" }\n  end\n  static def self.gen_partial -> Void\n    def_method(:with, keywords: [Meta::Keyword.new(:a, Int, false)], override: true) do |given| -> String\n      \"gen\"\n    end\n  end\n  static def self.gen_superset -> Void\n    def_method(:with, keywords: [Meta::Keyword.new(:a, Int, false), Meta::Keyword.new(:b, Int, false), Meta::Keyword.new(:c, Int, false)], override: true) do |given| -> String\n      \"gen #{given.size}\"\n    end\n  end\n  static def self.gen_result -> Void\n    def_method(:label, :name, override: true) { |name: String| -> Int name.size }\n  end\n  static def self.gen_none -> Void\n    def_method(:nothing_here, override: true) { -> Int 1 }\n  end\nend\n";
    let d = dir();
    write(&d.0, "lib.qz", lib);
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Base\n  gen_ok\nend\nb: Base = A.new\np b.greet(\"x\"), A.kind, A.made\n",
    );
    run_and_build(&d.0, &app, "\"gen x\"\n\"gen kind\"\n\"gen made\"\n");
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Base\n  gen_superset\nend\np A.new.with(a: 1, b: 2, c: 3), A.new.with(a: 1)\nb: Base = Base.new\np b.with(a: 1)\ndef via(b: Base) -> String = b.with(a: 2)\np via(A.new)\n",
    );
    // (A call the inherited one fits too runs the override, #436.)
    run_and_build(
        &d.0,
        &app,
        "\"gen 3\"\n\"gen 1\"\n\"base 1 0\"\n\"gen 1\"\n",
    );
    for (stmt, want) in [
        ("gen_disjoint", "`def_method(:size_of)`: `override: true`, but `A#size_of` overrides no inherited method of its name, which would be overloaded instead: `Base#size_of(n: Int) -> String`: its parameter `s` takes String, not every Int"),
        ("gen_partial", "`def_method(:with)`: `override: true`, but `A#with` overrides no inherited method of its name, which would be overloaded instead: `Base#with(*, a: Int = ..., b: Int = ...) -> String`: it does not take the keyword `b`"),
        ("gen_result", "`def_method(:label)`: `override: true`, but its result Int is not a String, the result of `Base#label(name: String) -> String`"),
        ("gen_none", "`def_method(:nothing_here)`: `override: true`, but `A` inherits no method `nothing_here` to override"),
    ] {
        let app = write(
            &d.0,
            "app.qz",
            &format!("require_relative \"lib\"\nclass A < Base\n  {stmt}\nend\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok);
        assert!(err.starts_with(&format!("app.qz:3:3: error: {want}")), "{stmt}: {err}");
    }
}

#[test]
fn class_def_calls_through_a_union_receiver() {
    // #403: a receiver typed `Meta::ClassDef[Base] | Runner`, the class
    // value at run time, raised "cannot cast Type[A]" for any call: the
    // union's dispatch tested it as an object of `Meta::ClassDef`. Calls
    // reach the class's methods and natives, the generating ones
    // included (into the statement's class), interpreted and compiled.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Runner\n  def def_method[R](name: Symbol, &body: () -> R) -> R = body.call\n  def name -> String = \"runner\"\n  def to_s -> String = \"runner\"\n  def at_class_end(key: Symbol, &hook: () -> Void) -> Void = nil\n  def method_ref[F](name: Symbol) -> String = \"ref\"\nend\nclass Base\n  def go -> Int = 7\n  static def self.gen(flag: Bool) -> Void\n    r = flag ? self : Runner.new\n    puts r.to_s, r.name\n    r.def_method(:hostname) { \"h\" }\n    r.at_class_end(:ended) { nil }\n    h = r.method_ref[() -> Int](:go)\n    puts h.is_a?(String) ? \"string ref\" : \"method ref\"\n    q = flag ? self : Runner.new\n    q.instance_exec { def_method(:c) { 3 } }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "main.qz",
        "require_relative \"lib\"\nclass A < Base\n  gen(true)\nend\nclass B < Base\n  gen(false)\nend\np A.new.hostname, A.new.c, B.new.go\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"h\"\n3\n7\n");
    // (What the statements print at compile time, on standard error.)
    // (And the warning the `instance_exec` block's `def_method` gives.)
    assert!(
        err.starts_with("A\nA\nmethod ref\nrunner\nrunner\nstring ref\n"),
        "{err}"
    );
    let exe = d.0.join("app-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "\"h\"\n3\n7\n");

    // A class-object member is told apart from the `ClassDef` one by its
    // class, and the hidden keywords a native is told stay its own (a
    // `**opts` of the other member's method sees none).
    write(
        &d.0,
        "lib2.qz",
        "class Runner\n  def self.def_method[R](name: Symbol, &body: () -> R) -> R\n    puts \"Runner.def_method\"\n    body.call\n  end\n  def self.method_ref[F](name: Symbol, **opts: Int) -> String = \"ref #{opts.size}\"\nend\nclass Base\n  def go -> Int = 7\n  static def self.gen(flag: Bool) -> Void\n    r = flag ? Runner : self\n    r.def_method(:hostname) { \"h\" }\n    h = r.method_ref[() -> Int](:go)\n    puts h.is_a?(String) ? h : \"method ref\"\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "main2.qz",
        "require_relative \"lib2\"\nclass A < Base\n  gen(true)\nend\nclass B < Base\n  gen(false)\nend\np B.new.hostname\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"h\"\n");
    assert!(
        err.starts_with("Runner.def_method\nref 0\nmethod ref\n"),
        "{err}"
    );
}

#[test]
fn a_union_of_a_class_def_and_a_related_class_object_is_narrowed_first() {
    // #491: `Meta::ClassDef[Base] | Type[Sub]` with `Sub < Base`: the class
    // value `Sub` (or a subclass the statement runs in) is both, so a call
    // the two members answer with different methods is refused; one they
    // answer alike (`name`), `is_a?` to narrow, and an unrelated class
    // object (#490) are accepted.
    let d = dir();
    let lib = "class Sub < Base\n  def self.def_method[R](name: Symbol, &body: () -> R) -> R\n    puts \"Sub.def_method\"\n    body.call\n  end\n  def self.type -> Type[Sub] = Sub\nend\nmodule M\n  def m -> Int = 1\n  def self.def_method[R](name: Symbol, &body: () -> R) -> R = body.call\nend\nclass Runner\n  include M\n  def self.def_method[R](name: Symbol, &body: () -> R) -> R\n    puts \"Runner.def_method\"\n    body.call\n  end\nend\n";
    let refused = [
        (
            "r = flag ? Sub : self\n    r.def_method(:a) { 1 }",
            "`def_method` on Type[Sub] | Meta::ClassDef[Base]: a class value may be both the Meta::ClassDef[Base] and a Type[Sub], which find different `def_method` methods, and no run-time test tells which one the value stands for; narrow the receiver first (`if r.is_a?(Type[Sub])` or a `case`)",
        ),
        (
            // (A module: a subclass of `Base` may include it.)
            "t = Base.pick(Runner)\n    r: Meta::ClassDef[Base] | Type[M] = flag ? t : self\n    r.def_method(:a) { 1 }",
            "`def_method` on Type[M] | Meta::ClassDef[Base]: a class value may be both",
        ),
        (
            // (An implicit call on a block's `self` that is such a union.)
            "r = flag ? Sub : self\n    r.instance_exec { def_method(:a) { 1 } }",
            "error: `def_method` on Type[Sub] | Meta::ClassDef[Base]: a class value may be both",
        ),
        (
            "r = flag ? Sub : self\n    [r].each(&:type)",
            "`&:type` on Type[Sub] | Meta::ClassDef[Base]: a class value may be both",
        ),
    ];
    for (body, want) in refused {
        write(
            &d.0,
            "lib.qz",
            &format!("class Base\n  static def self.gen(flag: Bool) -> Void\n    {body}\n  end\n  def self.pick(t: Type[M]) -> Type[M] = t\nend\n{lib}"),
        );
        let app = write(
            &d.0,
            "main.qz",
            "require_relative \"lib\"\nclass A < Base\n  gen(true)\nend\n",
        );
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{body}");
        assert!(err.contains(want), "{body}: {err}");
    }
    // A class object of `Base` or any class holds the `ClassDef`'s value
    // too: the union is that class object, whose methods are called.
    for member in ["Type[Base]", "Type"] {
        write(
            &d.0,
            "lib.qz",
            &format!("class Base\n  static def self.gen(t: {member}, flag: Bool) -> Void\n    r: Meta::ClassDef[Base] | {member} = flag ? t : self\n    r.def_method(:a) {{ 1 }}\n  end\nend\n{lib}"),
        );
        let app = write(&d.0, "main.qz", "require_relative \"lib\"\n");
        let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
        assert!(!ok, "{member}");
        assert!(
            err.contains("error: undefined method `def_method` for Type["),
            "{member}: {err}"
        );
    }
    write(
        &d.0,
        "lib.qz",
        &format!("class Base\n  static def self.gen(flag: Bool) -> Void\n    r = flag ? Sub : self\n    puts r.name\n    if r.is_a?(Type[Sub])\n      r.def_method(:a) {{ \"sub\" }}\n    else\n      r.def_method(:a) {{ \"gen\" }}\n    end\n    s = flag ? Runner : self\n    s.def_method(:b) {{ \"gen\" }}\n  end\nend\n{lib}"),
    );
    let app = write(
        &d.0,
        "main.qz",
        "require_relative \"lib\"\nclass A < Base\n  gen(true)\n  gen(false)\nend\nclass B < Sub\n  gen(false)\nend\np A.new.a, A.new.b\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "\"gen\"\n\"gen\"\n");
    // (`B`'s value is a `Type[Sub]`: narrowed as one.)
    assert!(
        err.starts_with("Sub\nSub.def_method\nRunner.def_method\nA\nB\nSub.def_method\n"),
        "{err}"
    );
    let exe = d.0.join("app-bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", exe.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "\"gen\"\n\"gen\"\n");
}

/// #553: `Meta::ClassDef#type` is never replaced: in a subclass's static
/// def, `type` is the subclass (the reflection's), not a superclass's
/// `def self.type`, so a generated method builds the subclass; both
/// backends.
#[test]
fn a_class_method_named_type_does_not_replace_the_reflections() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base\n  def initialize; end\n  def self.make -> Self = new\n  static def self.gen -> Void\n    cls = type\n    def_method(:sibling) { cls.make }\n  end\nend\n",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass A < Base\n  def self.type -> Type[A] = A\nend\nclass B < A\n  gen\n  @names: Array[String] = [\"x\", \"y\"]\n  def first -> String = @names[1]\nend\nx: B = B.new.sibling\nputs x.class.name\nputs x.first.upcase\nputs A.type.name\n",
    );
    let want = "B\nY\nA\n";
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, want);
    let bin = d.0.join("app_bin");
    let (ok, _, err) = quarz(
        &d.0,
        &["build", app.to_str().unwrap(), "-o", bin.to_str().unwrap()],
        &[],
    );
    assert!(ok, "{err}");
    let out = std::process::Command::new(&bin).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), want);
}

/// #553: a `def self.type` the static def's own class declares does not
/// shadow the reflection either; using `type` as such a method's result
/// is refused; and a static round does not reach a class method named
/// `type` through it.
#[test]
fn a_static_defs_type_is_the_reflections_beside_an_own_type() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base
  def initialize; end
  def self.type -> Type[Base]
    puts \"own type\"
    Base
  end
  def self.make -> Self = new
  static def self.gen -> Void
    cls = type
    puts cls.name
    def_method(:sibling) { cls.make }
  end
end
",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass B < Base\n  gen\nend\nputs B.new.sibling.class.name\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(err, "B\n");
    assert_eq!(out, "B\n");
    // `type` as an `Int` class method's result, in static code: refused.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Base
  def initialize; end
  def self.type -> Int = 42
  static def self.gen -> Void
    x = type
    puts x + 1
  end
end
",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass B < Base\n  gen\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", app.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(err.contains("undefined method `+` for Type[Self]"), "{err}");
    // An unrelated class's `def self.type` is not reached by a static
    // def's `type`.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Model
  static def self.gen -> Void
    puts type.name
  end
end
",
    );
    let app = write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Other\n  def self.type -> Int\n    File.read(\"/etc/hostname\").size\n  end\nend\nclass B < Model\n  gen\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(err, "B\n");
}

// ----- #717: the tables kept across a static phase's rounds -----
//
// Each program below makes a `static` statement change what the kept
// tables hold (the table on #717, "M2 note, refreshed", §5), and code after
// it observes the change, interpreted and compiled. `cargo test` runs the
// command with `QUARZ_VERIFY_STATIC_TABLES=1` (.cargo/config.toml), so
// every round's kept tables are also compared with the tables built from
// nothing.

/// `quarz run` and the compiled program of `app` both print `expected`.
fn run_both(d: &Path, app: &Path, expected: &str) {
    let (ok, out, err) = quarz(d, &["run", app.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected, "{err}");
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

const KEPT_LIB: &str = r##"class Gen
  static def self.gen_m -> Void
    def_method(:m, override: true) { "B" }
  end
  static def self.gen_area -> Void
    def_method(:area) { 5 }
  end
  static def self.gen_field -> Void
    def_field(:hits, Int, 3, reader: true)
  end
  static def self.gen_name -> Void
    def_class_method(:name) { "custom" }
  end
  static def self.nothing -> Void
  end
end
module GenK
  static def self.gen_k -> Void
    def_method(:k) { 7 }
  end
end
module M
  include GenK
end
class Trigger
  static def self.go -> Void
    M.gen_k
  end
end
"##;

#[test]
fn a_method_generated_between_an_override_and_its_target() {
    // Rows 1–3: `C#m` overrides `A#m`; generating `B#m` between them
    // puts it in `C#m`'s override row, and in the dispatch of `B` and `D`.
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class A < Gen
  def m -> String = "A"
end
class B < A
  gen_m
end
class C < B
  def m -> String = "C" + super
end
class D < B
end
def show(a: A) -> String = a.m
puts show(A.new), show(B.new), show(C.new), show(D.new)
"#,
    );
    run_both(&d.0, &app, "A\nB\nCB\nB\n");
}

#[test]
fn a_method_generated_into_a_module_with_includers() {
    // Rows 4–6: `M#k` generated into a module two classes include and an
    // extension makes a third conform to; `P`'s include now puts `M#k`
    // over its superclass's `k` (an include pair that was not there). A
    // module body takes no statement: `X`'s reaches `M` through the
    // `static def` `M` has from `GenK`.
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class S
  def k -> Int = 1
end
class P < S
  include M
end
class Q
  include M
end
class R
end
extension R
  include M
end
class X < Trigger
  go
end
def kk(m: M) -> Int = m.k
puts kk(P.new), kk(Q.new), kk(R.new), P.new.k
"#,
    );
    run_both(&d.0, &app, "7\n7\n7\n7\n");
}

#[test]
fn key_methods_generated_into_a_module_an_unheld_type_includes() {
    // The class row's `key_methods` (#813) reads the lookup of `Pt`, which
    // meets `Keyed`: `==` and `hash` generated into `Keyed` (a `Method`
    // event, whose D holds `Pt`) make `Pt`'s instances compare by them as
    // keys, at compile time in a later run (`static(Probe.size)`, on the
    // interpreter made from the kept rows) and at run time. `Pt` is a
    // class, which no field holds in place, so the generation is allowed.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r#"module GenEq
  static def self.gen_eq -> Void
    def_method(:==, :other) { |other: Object| true }
    def_method(:hash) { 0 }
  end
end
module Keyed
  include GenEq
end
class Pt
  include Keyed
  var @x: Int
  def initialize(@x: Int) end
end
class Trigger
  static def self.go -> Void
    Keyed.gen_eq
  end
end
class Probe
  static def self.size -> Int = Set[Pt.new(1), Pt.new(2)].size
end
"#,
    );
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class X < Trigger
  go
end
N = static(Probe.size)
puts N, Set[Pt.new(1), Pt.new(2)].size, {Pt.new(1) => "a"}[Pt.new(3)]
"#,
    );
    run_both(&d.0, &app, "1\n1\na\n");
}

#[test]
fn the_implementation_a_deferred_conformance_waits_for() {
    // Rows 5 and 7: `K`'s conformance to `Sh` waits for its statements
    // (`World::conformance_deferred`), which generate `area` (#801); the
    // witness record's entries for `K` and its subclass are made then.
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
module Sh
  abstract def area -> Int
end
class K < Gen
  include Sh
  gen_area
end
class L < K
end
def a(s: Sh) -> Int = s.area
puts a(K.new), a(L.new)
"#,
    );
    run_both(&d.0, &app, "5\n5\n");
}

#[test]
fn a_field_generated_into_a_superclass_with_subclasses() {
    // Rows 1, 2, 8–10: a field into `F` moves the own fields of `G`, its
    // subclass, and is laid out in `F`'s holder `H` (by reference: a
    // class), whose reflection and layout are made again.
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class F < Gen
  gen_field
end
class G < F
  @g: Int
  def initialize(@g: Int)
  end
  def g -> Int = @g
end
class H
  @f: F
  @n: Int
  def initialize(@f: F, @n: Int)
  end
  def f -> F = @f
  def n -> Int = @n
end
x = G.new(4)
h = H.new(x, 6)
puts x.hits, x.g, h.f.hits, h.n
"#,
    );
    run_both(&d.0, &app, "3\n4\n3\n6\n");
}

#[test]
fn a_class_method_that_takes_a_type_method_s_place() {
    // Rows 3 and 7: `N.name` generated over `Type#name` (the override
    // table pairs it with `Type`'s method; the class-side rows of `N` and
    // its subclass take it). An instance method generated into a class of
    // `Type`'s side (`Type`, `Object`, ... #717's T) has no fixture: those
    // are the prelude's, no `static` statement runs in them, and another
    // class's statement reaches a class only through a `static def` the
    // class has, which they have none of.
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class N < Gen
  gen_name
end
class O < N
end
def nm(t: Type[Object]) -> String = t.name
puts N.name, O.name, nm(N), nm(Gen)
"#,
    );
    run_both(&d.0, &app, "custom\ncustom\ncustom\nGen\n");
}

#[test]
fn constructor_choices_made_after_the_statements() {
    // Row 1's `inherited_inits`: the checker records which `initialize`
    // `B.make`'s inherited `new` runs (`check_inherited_constructors`)
    // after the file's statements ran, with no event; the kept class rows
    // follow it (`Kept::inherited`). Before, `B`'s row kept none (the
    // oracle's panic), as no event reached `B`.
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class Z < Gen
  nothing
end
class A
  @x: Int
  def initialize(@x: Int)
  end
  def x -> Int = @x
  def self.make -> Self = new(1)
end
class B < A
  def initialize(x: Int)
    super(x * 10)
  end
end
puts A.make.x, B.make.x
"#,
    );
    run_both(&d.0, &app, "1\n10\n");
}

#[test]
fn a_default_that_builds_a_class_a_field_is_generated_into() {
    // `K`'s field default constructs `F`: a field generated into `F`
    // drops the default's function (`Lowerer::invalidate_layout`), and
    // `K` is neither in D(F) nor a holder of `F`; the next round lowers
    // it again because it waits (`defaults_waiting`). Without that, the
    // oracle's `assert_defaults_lowered` panics at `Q`'s round.
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class P < Gen
  nothing
end
class F < Gen
  gen_field
  def base -> Int = 1
end
class K
  @n: Int = F.new.base
  def n -> Int = @n
end
class Q < Gen
  nothing
end
puts K.new.n, F.new.hits
"#,
    );
    run_both(&d.0, &app, "1\n3\n");
}

#[test]
fn a_field_without_accessors_moves_a_subclass_s_reader() {
    // Rows 1 and 2 through D(F) alone: a field generated into `F`, with no
    // reader (whose `Method` event would rebuild D(F) too), by another
    // class's statement (so `G`, under no class with statements, is not
    // deferred, and no `Conformance` event rebuilds it), moves the index
    // of `@g` that `G`'s `attr_reader` reads. Without the `Field` event's
    // D, `G#g`'s row keeps the old index.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r#"class Gen
  static def self.gen_bare -> Void
    def_field(:bare, Int, 4)
  end
end
class Trig
  static def self.go -> Void
    F.gen_bare
  end
end
"#,
    );
    let app = write(
        &d.0,
        "app.qz",
        r#"require_relative "lib"
class F < Gen
end
class G < F
  @g: Int
  attr_reader :g
  def initialize(@g: Int); end
end
class X < Trig
  go
end
puts G.new(5).g
"#,
    );
    run_both(&d.0, &app, "5\n");
}

#[test]
fn tables_built_again_for_classes_a_later_check_adds() {
    // `quarz test` checks the doc examples after the files' statements
    // ran, with the same runner: their classes make the kept tables be
    // built from nothing. The epochs go on from the earlier tables' (a
    // new start at 1 told the runner's safety net that nothing changed
    // since its last round, and the examples' rows went unchecked: the
    // oracle's panic).
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let t = write(
        &d.0,
        "ex_test.qz",
        r#"require "test"
require_relative "lib"
# One.
#
# ```
# class A1 < Gen
#   gen_area
# end
# A1.new.area   # => 5
# ```
class One < Gen
  gen_area
end
# Two.
#
# ```
# class A2 < Gen
#   gen_field
# end
# A2.new.hits   # => 3
# ```
class Two
end
class T < Test::Case
  def test_x
    assert(One.new.area == 5)
  end
end
"#,
    );
    let (ok, out, err) = quarz(&d.0, &["test", t.to_str().unwrap()], &[]);
    assert!(ok, "{out}{err}");
    assert!(out.contains("3 tests, 3 assertions, 0 failures"), "{out}");
}

#[test]
fn a_statement_that_generates_nothing_rebuilds_nothing() {
    // Row 6 of §5: rounds whose statements generate nothing rebuild no
    // class's rows (each sync's line in `QUARZ_STATIC_TABLES_STATS`).
    let d = dir();
    write(&d.0, "lib.qz", KEPT_LIB);
    let mut src = String::from("require_relative \"lib\"\n");
    for i in 0..20 {
        src.push_str(&format!("class C{i} < Gen\n  nothing\nend\n"));
    }
    src.push_str("puts \"ok\"\n");
    let app = write(&d.0, "app.qz", &src);
    let stats = d.0.join("stats");
    let (ok, out, err) = quarz(
        &d.0,
        &["run", app.to_str().unwrap()],
        &[("QUARZ_STATIC_TABLES_STATS", stats.to_str().unwrap())],
    );
    assert!(ok, "{err}");
    assert_eq!(out, "ok\n");
    let lines = std::fs::read_to_string(&stats).unwrap();
    let incremental: Vec<&str> = lines.lines().filter(|l| l.contains("full=0")).collect();
    assert!(incremental.len() >= 20, "{lines}");
    assert!(
        incremental
            .iter()
            .filter(|l| l.contains("events=0"))
            .all(|l| l.contains("classes=0 methods=0")),
        "{lines}"
    );
}
