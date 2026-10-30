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
        err.matches("did not run: it reaches `Broken#to_s`, which has errors")
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
