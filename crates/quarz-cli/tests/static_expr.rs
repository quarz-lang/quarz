//! `static(call)` (docs/14 §8): a call of a `static def` with constant
//! arguments, run at compile time, its value baked into the program.

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
        "quarz-static-expr-{}-{}",
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

const LIB: &str = r##"data Sql = (text: String, binds: Array[Symbol])

class Q
  static def self.sql(table: String, cols: Array[Symbol]) -> Sql
    Sql.new("SELECT #{cols.join(", ")} FROM #{table}", cols)
  end
  static def self.twice(s: Sql) -> String = s.text + "; " + s.text
  static def self.fields_of(t: Type[Object]) -> Int = t.fields.size
  static def self.count(&f: (Int) -> Bool) -> Int = [1, 2, 3, 4].count { |x| f.call(x) }
  static def self.boom(n: Int) -> Int
    raise ArgumentError, "bad #{n}" if n > 1
    n
  end
  static def self.proc_of -> () -> Int = -> { 1 }
  static def self.obj(n: Int) -> Object = n > 0 ? Q : Object.new
  def self.plain -> Int = 1
end
"##;

const APP: &str = r##"require_relative "lib"
class Post
  @title: String = ""
  @views: Int = 0
end
LIMIT = 2
def query -> Sql = static(Q.sql("posts", [:title, :views]))
p query
p static(Q.twice(static(Q.sql("t", [:a]))))
p static(Q.fields_of(Post))
p static(Q.count { |x| x > LIMIT })
p static(Q.obj(1))
"##;

const OUT: &str = "Sql(text: \"SELECT title, views FROM posts\", binds: [:title, :views])\n\"SELECT a FROM t; SELECT a FROM t\"\n2\n2\nQ\n";

#[test]
fn values_computed_at_compile_time() {
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    write(&d.0, "app.qz", APP);
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, OUT);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), OUT);
}

#[test]
fn what_static_refuses() {
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass Own\n  static def self.mine -> Int = 1\nend\nn = 2\np static(Q.boom(n))\np static(Q.plain)\np static(1 + 2)\np static(Q.proc_of)\np static(Own.mine)\np static(Q.count { |x| x > n })\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    for want in [
        "bad.qz:6:17: error: `static(...)`'s receiver and arguments are constants",
        "bad.qz:7:10: error: `static(...)` takes a call of a `static def`; `plain` is not one",
        "bad.qz:8:10: error: `static(...)` takes a call of a `static def`; `+` is not one",
        "bad.qz:9:3: error: `static(...)` gives a () -> Int, which cannot be baked",
        "bad.qz:10:10: error: `mine` is a `static def` of this file",
        "bad.qz:11:28: error: a block in `static(...)` captures nothing: `n` is not a constant",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
    // At compile time: a raise, a value that cannot be baked.
    write(
        &d.0,
        "run.qz",
        "require_relative \"lib\"\np static(Q.boom(2))\np static(Q.obj(0))\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "run.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("run.qz:2:10: error: `boom` raised ArgumentError: bad 2"),
        "{err}"
    );
    assert!(
        err.contains("run.qz:3:10: error: `static(...)` gives a value that cannot be baked into the program: a value of class `Object`"),
        "{err}"
    );
}

#[test]
fn a_cached_file_sees_its_dependencys_change() {
    // docs/14 §8: the values are computed on every check, a file read
    // back from the cache included.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class K\n  static def self.v -> Int = 1\nend\n",
    );
    write(&d.0, "app.qz", "require_relative \"lib\"\np static(K.v)\n");
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &env);
    assert!(ok, "{err}");
    assert_eq!(out, "1\n");
    write(
        &d.0,
        "lib.qz",
        "class K\n  static def self.v -> Int = 2\nend\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &env);
    assert!(ok, "{err}");
    assert_eq!(out, "2\n");
}

#[test]
fn in_a_quoted_block_a_literal() {
    // docs/14 §6, §8: its value is a `Lit` of the tree.
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass RQ\n  def where(&c: Quoted[(Int) -> Bool]) -> Meta::Expr = c.expr\nend\np RQ.new.where { |x| x > static(Q.sql(\"t\", [:a])).text.size }\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert!(
        out.contains(
            "Meta::Expr::Lit(value: Sql(text: \"SELECT a FROM t\", binds: [:a]), line: 5)"
        ),
        "{out}"
    );
}

#[test]
fn code_run_at_compile_time_still_bakes_the_value() {
    // A `static def` a statement runs is lowered before the `static(...)`
    // values are known: lowered again with them, so the program bakes the
    // value, the same with the cache and without (docs/14 §8).
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Q\n  static def self.say(s: String) -> Int\n    puts s\n    1\n  end\n  static def self.fields_of(t: Type[Object]) -> Int = t.fields.size\nend\n",
    );
    write(
        &d.0,
        "mid.qz",
        "require_relative \"lib\"\nclass Post\n  @a: Int = 1\nend\nclass M3\n  static def self.k -> Int = static(Q.say(\"computed\"))\n  static def self.n -> Int = static(Q.fields_of(Post))\n  static def self.touch -> Nil\n    k\n    n\n    nil\n  end\nend\n",
    );
    write(
        &d.0,
        "app.qz",
        "require_relative \"mid\"\nclass X < M3\n  touch\nend\np M3.k, M3.n\n",
    );
    let cache = d.0.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    for _ in 0..2 {
        let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &env);
        assert!(ok, "{err}");
        assert_eq!(out, "1\n1\n");
    }
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &env);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "1\n1\n");
}

#[test]
fn a_block_in_static_captures_nothing() {
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    for body in [
        "(1..n).include?(x)",
        "{1 => n}.size > x",
        "y = n; x > y",
        "-> { n }.call > x",
        "helper(x)",
    ] {
        write(
            &d.0,
            "bad.qz",
            &format!("require_relative \"lib\"\ndef helper(x: Int) -> Bool = x > 1\ndef f(n: Int) -> Int = static(Q.count {{ |x| {body} }})\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
        assert!(!ok, "{body}");
        assert!(
            err.contains("a block in `static(...)` captures nothing"),
            "{body}: {err}"
        );
    }
}

#[test]
fn a_method_lowered_again_is_judged_again() {
    // Lowered again once its `static(...)` value is known, a `static def`
    // that also reflects at run time is still compile-time only.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "class Q\n  static def self.v(n: Int) -> Int = n\n  static def self.fields_of(t: Type[Object]) -> Int = t.fields.size\nend\n",
    );
    write(
        &d.0,
        "mid.qz",
        "require_relative \"lib\"\nclass P6\n  @a: Int = 1\nend\nclass M6\n  static def self.k -> Int = static(Q.v(1)) + Q.fields_of(P6)\n  static def self.touch -> Nil\n    k\n    nil\n  end\nend\n",
    );
    write(
        &d.0,
        "app.qz",
        "require_relative \"mid\"\nclass X < M6\n  touch\nend\np M6.k\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "app.qz"], &[]);
    assert!(!ok);
    assert!(err.contains("`k` runs at compile time only"), "{err}");
    // `__method__` is not a constant either.
    write(
        &d.0,
        "meth.qz",
        "class C\n  static def self.count(&f: (Int) -> Bool) -> Int = 1\nend\n",
    );
    write(
        &d.0,
        "use.qz",
        "require_relative \"meth\"\ndef f -> Int = static(C.count { |x| __method__.size > x })\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "use.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("`__method__` is the method's name, not a constant"),
        "{err}"
    );
}

#[test]
fn the_value_is_made_once_and_shared() {
    // docs/14 §8: a constant of its own, read by every evaluation.
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\ndef q -> Sql = static(Q.sql(\"t\", [:a]))\np q.equal?(q)\nts = (1..4).map { Task.spawn { q.text.size } }\np ts.map(&:await)\n",
    );
    let expected = "true\n[15, 15, 15, 15]\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

#[test]
fn shared_however_the_site_was_lowered() {
    // `join` is lowered by the run that evaluates the later `static(...)`
    // (`Q.sql` calls a `join`), after its own value is known: lowered
    // again for the program. A quoted block's tree and its closure share
    // the value.
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nclass Repo\n  def self.join -> Sql = static(Q.sql(\"r\", [:b]))\nend\nY = static(Q.sql(\"t\", [:a]))\np Repo.join.equal?(Repo.join)\nclass R\n  def where(&c: Quoted[shareable (Int) -> Sql]) -> Quoted[shareable (Int) -> Sql] = c\nend\ndef at -> Quoted[shareable (Int) -> Sql] = R.new.where { |x| static(Q.sql(\"t\", [:a])) }\ncase at.expr\nin Meta::Expr::Block(body: b)\n  case b[0]\n  in Meta::Expr::Lit(value: v)\n    p v.equal?(at.proc.call(0))\n  else\n    p :no\n  end\nelse\n  p :no\nend\n",
    );
    let expected = "true\ntrue\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}
