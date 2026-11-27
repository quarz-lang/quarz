//! `static(call)` (docs/14 §8): a call of a method or function (a
//! `static def` or not, #981) with constant arguments, run at compile
//! time, its value baked into the program.

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
  static def self.count2(&f: shareable (Int) -> Bool) -> Int = [1, 2, 3, 4].count { |x| f.call(x) }
  static def self.on5(&f: Int.() -> Int) -> Int = 5.instance_exec(&f)
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

/// A `static def` function of a required file is a `static(...)` call,
/// and a block in `static(...)` may call the functions of the files the
/// file depends on, which have no `self` and are compiled before it
/// (docs/14 §8): the same values interpreted and compiled.
#[test]
fn functions_of_a_required_file_at_compile_time() {
    let d = dir();
    write(&d.0, "lib.qz", LIB_FUNCTIONS);
    write(&d.0, "app.qz", APP_FUNCTIONS);
    let expected = OUT_FUNCTIONS;
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

const LIB_FUNCTIONS: &str = r##"# Functions of a required file, compiled before the file that requires it.
static def twice(n: Int) -> Int = n * 2
static def label(n: Int, tag: String = "n") -> String = "#{tag}#{helper(n)}"
def helper(n: Int) -> Int = n + 1

class Runs
  static def self.run(&: () -> Int) -> Int = yield
  static def self.on(x: Int, &f: Int.() -> Int) -> Int = x.instance_exec(&f)
end
"##;

const APP_FUNCTIONS: &str = r##"# A `static def` function of a required file is a `static(...)` call, and
# a block in `static(...)` may call the functions of the files this file
# depends on, which have no `self` and are compiled before it (docs/14 §8).
require_relative "lib"

p static(twice(4)), static(::twice(5)), static(label(1)), static(label(2, "m"))
p static(twice(static(twice(3))))
p static(Runs.run { helper(1) + twice(2) })
p static(Runs.on(3) { helper(self) })
p static(Runs.run { [1, 2].sum { |x| helper(x) } })
# The same functions at run time.
p twice(4), helper(1)
"##;

const OUT_FUNCTIONS: &str = "8\n10\n\"n2\"\n\"m3\"\n12\n6\n4\n5\n8\n2\n";

/// #981: `static(...)` calls any method or function of the cogs (or
/// required files) the file depends on, `static def` or not, natives
/// included; what the call reaches is judged when it runs, at the
/// expression (a native acting on the outside world or nondeterministic),
/// and a `static native def` (reflection) is refused there.
#[test]
fn static_calls_any_method_or_function() {
    let d = dir();
    write(
        &d.0,
        "util.qz",
        "class Util\n  def self.slug(s: String) -> String = s.downcase.gsub(\" \", \"-\")\n  def self.read_it -> String = File.read(\"x\")\n  def self.random_it -> Int = Crypto.random_bytes(4).size\n  def self.now_it -> Int = Time.now.year\n  def self.secret_it -> Int = File.read_secret(\"x\").size\nend\nclass Post\n  def initialize; end\nend\n",
    );
    write(
        &d.0,
        "ok.qz",
        "require_relative \"util\"\nA = static(Util.slug(\"Hello World\"))\nB = static(Digest::SHA256.hexdigest(\"abc\"))\nC = static(Date(\"2026-01-01\"))\nD = static(1 + 2)\np A, B, C, D\np Util.slug(\"Hello World\") == A, Digest::SHA256.hexdigest(\"abc\") == B\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "ok.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(
        out,
        "\"hello-world\"\n\"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad\"\n2026-01-01\n3\ntrue\ntrue\n"
    );
    for (call, want) in [
        (
            "Util.read_it",
            "`File.read`, which cannot run at compile time",
        ),
        (
            "Util.random_it",
            "`Crypto.random_bytes`, which cannot run at compile time",
        ),
        (
            "Util.now_it",
            "`Time.now`, which cannot run at compile time",
        ),
        // quarz#1015: a secret read from a file at compile time, denied
        // as `File` is.
        (
            "Util.secret_it",
            "`File.read_secret`, which cannot run at compile time",
        ),
        (
            "Post.methods",
            "`static(...)` cannot call `methods`, which reflects on a class being defined",
        ),
    ] {
        write(
            &d.0,
            "bad.qz",
            &format!("require_relative \"util\"\nX = static({call})\np X\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
        assert!(!ok, "{call}");
        assert!(err.contains("bad.qz:2:12: error: "), "{call}: {err}");
        assert!(err.contains(want), "{call}: {err}");
    }
}

/// #981: an ordinary generic callee of `static(...)` (a generic function
/// with its arguments inferred, a generic class method with them inferred
/// and written, one using its type parameter as a value through a
/// `Type[T]`) gives the value it has at run time, run and built; and the
/// `Kernel` functions a standard module's extension adds (#936): `URI(...)`
/// is baked, `Decimal(...)` is refused as a value that cannot be baked.
#[test]
fn static_calls_generic_and_std_kernel_functions() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "def pair[A, B](a: A, b: B) -> Array[String] = [a.to_s, b.to_s]\nclass Box\n  def self.wrap[T](x: T) -> Array[T] = [x]\n  def self.named[T](t: Type[T]) -> String = t.name\n  def self.empty_of[T](t: Type[T]) -> Int = Array[T].new.size\nend\n",
    );
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\nrequire \"uri\"\nA = static(pair(1, \"a\"))\nB = static(Box.wrap(3))\nE = static(Box.wrap[Int](4))\nC = static(Box.named(Int))\nD = static(Box.empty_of(String))\nU = static(URI(\"https://example.com/\"))\np A, B, E, C, D, U\np A == pair(1, \"a\"), B == Box.wrap(3), C == Box.named(Int), U == URI(\"https://example.com/\")\n",
    );
    let want = "[\"1\", \"a\"]\n[3]\n[4]\n\"Int\"\n0\n#<URI https://example.com/>\ntrue\ntrue\ntrue\ntrue\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, want);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app"], &[]);
    assert!(ok, "{err}");
    let built = Command::new(d.0.join("app")).output().expect("run app");
    assert_eq!(String::from_utf8_lossy(&built.stdout), want);
    write(
        &d.0,
        "dec.qz",
        "require \"decimal\"\nX = static(Decimal(\"1.10\"))\np X\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "dec.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("dec.qz:2:5: error: `static(...)` gives a Decimal, which cannot be baked into the program"),
        "{err}"
    );
}

#[test]
fn what_static_refuses() {
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass Own\n  static def self.mine -> Int = 1\nend\nn = 2\np static(Q.boom(n))\np static(Q.plain)\np static(1 + 2)\np static(Q.proc_of)\np static(Own.mine)\np static(Q.count { |x| x > n })\nstatic def own_fn(n: Int) -> Int = n\np static(own_fn(1))\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    for want in [
        "bad.qz:6:17: error: `static(...)`'s receiver and arguments are constants",
        "bad.qz:9:3: error: `static(...)` gives a () -> Int, which cannot be baked",
        "bad.qz:10:10: error: `mine` is a method of this file",
        "bad.qz:11:28: error: a block in `static(...)` captures nothing: `n` is not a constant",
        "bad.qz:13:10: error: `own_fn` is a method of this file",
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
    // A `Bytes::Secret` is never baked: written into the executable, it
    // could never be wiped (#963). Refused by its declared type, and,
    // declared as a `Shareable`, by its value.
    write(
        &d.0,
        "key.qz",
        "require \"crypto\"\nmodule KeyLib\n  static def self.key -> Bytes::Secret = Bytes::Secret.of(b\"abc\")\n  static def self.gcm -> Shareable = Crypto::AES::GCM.new(Bytes.from((0...32).to_a))\n  static def self.any -> Shareable = Bytes::Secret.of(b\"abc\")\n  static def self.keys -> Array[Shareable] = [Bytes::Secret.of(b\"abc\")]\nend\n",
    );
    write(
        &d.0,
        "typed.qz",
        "require_relative \"key\"\nK = static(KeyLib.key)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "typed.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("typed.qz:2:5: error: `static(...)` gives a Bytes::Secret, which cannot be baked into the program"),
        "{err}"
    );
    write(
        &d.0,
        "secret.qz",
        "require_relative \"key\"\nA = static(KeyLib.any)\nL = static(KeyLib.keys)\nG = static(KeyLib.gcm)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "secret.qz"], &[]);
    assert!(!ok);
    for line in [2, 3] {
        let want = format!("secret.qz:{line}:12: error: `static(...)` gives a value that cannot be baked into the program: a `Bytes::Secret`: a secret written into the executable could never be wiped");
        assert!(err.contains(&want), "{want}\n{err}");
    }
    // A key held natively is one too (#963).
    assert!(
        err.contains("secret.qz:4:12: error: `static(...)` gives a value that cannot be baked into the program: a `Crypto::AES::GCM`: a secret written into the executable could never be wiped"),
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
fn only_data_of_shareable_fields_is_baked() {
    // docs/14 §5: every bakeable value is Shareable, so a `Lit`'s
    // `Shareable` value answers `is_a?(Shareable)` as its type says.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        r##"data W = (o: Object)
data V = (n: Int, s: Array[String])
enum E
  variant A
  variant B(o: Object)
  variant C(n: Int)
end
class K
  static def self.c -> E::C = E::C.new(1)
  static def self.oc -> Object = E::C.new(2)
  static def self.w -> W = W.new(1)
  static def self.e -> E = E::A
  static def self.o -> Object = W.new(1)
  static def self.v -> V = V.new(1, ["a"])
  static def self.ov -> Object = V.new(2, [])
end
"##,
    );
    write(
        &d.0,
        "ok.qz",
        "require_relative \"lib\"\nclass RQ\n  def where(&c: Quoted[(Int) -> Bool]) -> Meta::Expr = c.expr\nend\np static(K.v), static(K.ov)\np static(K.c), static(K.oc)\np RQ.new.where { |x| static(K.v).n == x }\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "ok.qz"], &[]);
    assert!(ok, "{err}");
    assert!(
        // (A variant by its own fields.)
        out.starts_with("V(n: 1, s: [\"a\"])\nV(n: 2, s: [])\nE::C(n: 1)\nE::C(n: 2)\n"),
        "{out}"
    );
    assert!(
        out.contains("Meta::Expr::Lit(value: V(n: 1, s: [\"a\"])"),
        "{out}"
    );
    write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\np static(K.w)\np static(K.e)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    for expected in [
        "bad.qz:2:3: error: `static(...)` gives a W, which cannot be baked into the program (`W` holds `@o: Object`, which is not Shareable, so its values cannot be baked)",
        "bad.qz:3:3: error: `static(...)` gives a E, which cannot be baked into the program (`E::B` holds `@o: Object`, which is not Shareable, so its values cannot be baked)",
    ] {
        assert!(err.contains(expected), "missing {expected:?} in\n{err}");
    }
    // Captured by a generated method.
    write(
        &d.0,
        "gen.qz",
        "require_relative \"lib\"\nclass Gen\n  static def self.gen(w: W) -> Void\n    def_method(:w) { w.o }\n  end\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "gen.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("gen.qz:4:22: error: `w` has type W, whose values cannot be baked into a generated method (`W` holds `@o: Object`, which is not Shareable, so its values cannot be baked)"),
        "{err}"
    );
    write(&d.0, "run.qz", "require_relative \"lib\"\np static(K.o)\n");
    let (ok, _, err) = quarz(&d.0, &["check", "run.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("run.qz:2:10: error: `static(...)` gives a value that cannot be baked into the program: `W` holds `@o: Object`, which is not Shareable, so its values cannot be baked"),
        "{err}"
    );
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
        "Q.count2 { |y| y > n } > x",
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
fn a_block_in_static_calls_only_functions_compiled_before_it() {
    // A function has no `self`: one of a required file may be called (it
    // is compiled before this one), one of this file may not, nor from a
    // block with a receiver or a shareable one inside the block
    // (tmp/repro/static-block-nested-instance-exec*.qz); `Kernel`'s may.
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        &format!("{LIB}def dep(x: Int) -> Bool = x > 2\n"),
    );
    for body in [
        "helper(x)",
        "5.instance_exec { helper(x) }",
        "Q.count2 { |y| helper(y) } > x",
    ] {
        write(
            &d.0,
            "bad.qz",
            &format!("require_relative \"lib\"\ndef helper(x: Int) -> Bool = x > 1\ndef f(n: Int) -> Int = static(Q.count {{ |x| {body} }})\n"),
        );
        let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
        assert!(!ok, "{body}");
        assert!(
            err.contains("`helper` is a function of this file, not yet compiled when `static(...)` runs: only functions of the cogs (or required files) this file depends on can be called here"),
            "{body}: {err}"
        );
    }
    write(
        &d.0,
        "good.qz",
        "require_relative \"lib\"\np static(Q.count { |x| dep(x) }), static(Q.count { |x| 5.instance_exec { dep(x) } })\np static(Q.count { |x| Q.count2 { |y| dep(y) } > x }), static(Q.count { |x| Kernel.format(\"%d\", x) == \"1\" })\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "good.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "2\n2\n1\n1\n");
}

#[test]
fn a_block_in_static_neither_yields_nor_calls_super() {
    // The method's block and its `self` are outside `static(...)`.
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    for (body, what) in [
        ("def f(&: (Int) -> Bool) -> Int = static(Q.count { |x| yield x })", "`yield`"),
        ("def f(&: (Int) -> Bool) -> Int = static(Q.count { |x| Q.count2 { |y| yield y } > x })", "`yield`"),
        ("class A\n  def g -> Int = 4\nend\nclass B < A\n  def g -> Int = static(Q.count { |x| super > x })\nend", "`super`"),
    ] {
        write(&d.0, "bad.qz", &format!("require_relative \"lib\"\n{body}\n"));
        let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
        assert!(!ok, "{body}");
        assert!(
            err.contains(&format!("a block in `static(...)` captures nothing: {what}")),
            "{body}: {err}"
        );
    }
}

#[test]
fn a_block_with_a_receiver_in_static_uses_its_own_self() {
    // Its receiver is no capture: `self` in it is the value it runs on.
    let d = dir();
    write(&d.0, "lib.qz", LIB);
    write(
        &d.0,
        "good.qz",
        "require_relative \"lib\"\ndef f -> Int = static(Q.count { |x| 2.instance_exec { self > x } })\np f\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "good.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "1\n");
    // So does the block of the call itself when the `static def` gives it
    // a receiver.
    write(
        &d.0,
        "own.qz",
        "require_relative \"lib\"\np static(Q.on5 { self + 1 })\np static(Q.on5 { \"ab\".instance_exec { size + abs } })\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", "own.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "6\n7\n");
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

/// A top-level constant read at compile time, through a function, is
/// initialized with its file's top-level object as `self`, as it is at
/// run time (docs/01 §2, docs/14 §3).
#[test]
fn a_toplevel_constant_reads_main_at_compile_time() {
    let d = dir();
    write(
        &d.0,
        "lib.qz",
        "def zz -> Int = 5\nM = self.class.name\nN = self.nil?\ndef k -> String = \"#{zz} #{M} #{N}\"\nclass Model\n  static def self.v -> String = k\nend\n",
    );
    write(
        &d.0,
        "app.qz",
        "require_relative \"lib\"\np static(Model.v), Model.v\n",
    );
    let expected = "\"5 main false\"\n\"5 main false\"\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

#[test]
fn a_compile_time_static_call_may_not_read_a_pending_class() {
    // docs/14 §8: `static(...)` made in a compile-time run (here a
    // statement's argument) reflecting on a class whose statements have
    // not all run: its value would be the class's as declared so far,
    // the program's when they have run.
    let d = dir();
    write(
        &d.0,
        "base.qz",
        "class Counter\n  static def self.count(c: Type[Object]) -> Int = c.fields.size\n  static def self.one -> Int = 1\n  static def self.plus(k: Int, c: Type[Object]) -> Int = k + c.fields.size\nend\n",
    );
    write(
        &d.0,
        "lib.qz",
        "require_relative \"base\"\nclass Model\n  @m: Int = 0\n  static def self.gen(n: Int) -> Void\n    def_method(:n) do -> Int\n      n\n    end\n  end\n  static def self.add(f: Symbol) -> Void\n    def_field(f, Int, 0)\n  end\nend\n",
    );
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"lib\"\nclass Post < Model\n  @x: Int = 1\n  gen(static(Counter.count(Post)))\n  add :a\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("reflects on a class whose `static` statements have not all run (`gen` in `Post`, `add` in `Post`)"),
        "{err}"
    );
    // Nested in another `static(...)`'s arguments.
    let nested = write(
        &d.0,
        "nested.qz",
        "require_relative \"lib\"\nclass Post < Model\n  @x: Int = 1\n  gen(static(Counter.plus(static(Counter.one), Post)))\n  add :a\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", nested.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("reflects on a class whose `static` statements have not all run"),
        "{err}"
    );
    // Rescued where it is refused, it still fails the statement.
    write(
        &d.0,
        "base.qz",
        "class Counter\n  static def self.count(c: Type[Object]) -> Int = c.fields.size\n  static def self.safe(c: Type[Object]) -> Int\n    begin\n      c.fields.size\n    rescue\n      -1\n    end\n  end\nend\n",
    );
    let rescued = write(
        &d.0,
        "rescued.qz",
        "require_relative \"lib\"\nclass Post < Model\n  @x: Int = 1\n  gen(static(Counter.safe(Post)))\n  add :a\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", rescued.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("reflects on a class whose `static` statements have not all run"),
        "{err}"
    );
    // A class whose statements have run (none here) reads as the program
    // will.
    let good = write(
        &d.0,
        "good.qz",
        "require_relative \"lib\"\nclass Post < Model\n  @x: Int = 1\n  gen(static(Counter.count(Model)))\n  add :a\nend\np Post.new.n\n",
    );
    let (ok, out, err) = quarz(&d.0, &["run", good.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "1\n");
}

#[test]
fn the_block_of_a_static_call_cannot_return() {
    // docs/14 §8: the block runs at compile time, where the code around
    // it is not running; `break` leaves the call with its value.
    let d = dir();
    write(
        &d.0,
        "base.qz",
        "class K\n  static def self.blk(&b: (Int) -> Int) -> Int = b.call(1) + 1\nend\n",
    );
    let bad = write(
        &d.0,
        "bad.qz",
        "require_relative \"base\"\ndef f -> Int\n  static(K.blk { |x| return 5 })\nend\np f\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", bad.to_str().unwrap()], &[]);
    assert!(!ok);
    assert!(
        err.contains("`return` in the block of `static(...)`'s call"),
        "{err}"
    );
    let good = write(
        &d.0,
        "good.qz",
        "require_relative \"base\"\np static(K.blk { |x| x + 4 })\np static(K.blk { |x| break 7 })\np static(K.blk { |x| g = ->(y: Int) -> Int {\n  [1, 2].each { |z| return z + y if z == 2 }\n  0\n}\ng.call(x) })\n",
    );
    // (A `return` in a lambda in the block leaves the lambda.)
    let (ok, out, err) = quarz(&d.0, &["run", good.to_str().unwrap()], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, "6\n7\n4\n");
}
