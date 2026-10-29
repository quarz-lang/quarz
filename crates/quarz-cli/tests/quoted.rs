//! Blocks given as `Quoted` (docs/14 §6): the tree, the captures and the
//! closure, the same interpreted and compiled; what cannot be quoted.

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
        "quarz-quoted-{}-{}",
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

const TREES: &str = r##"data Col = (name: String)

class Cond
  @sql: String
  def initialize(@sql: String); end
  def sql -> String = @sql
  def &&(&other: () -> Cond) -> Cond = Cond.new("(#{@sql} AND #{other.call.sql})")
end

class Row
  def views -> Int = 10
  def tags -> Array[String] = ["a", "b"]
end

LIMIT = 5
TABLE = Col.new("t")

class Rel
  def where(&cond: Quoted[Row.() -> Bool]) -> Quoted[Row.() -> Bool] = cond
  def filter(&cond: Quoted[Row.() -> Bool]) -> Quoted[Row.() -> Bool] = where(&cond)
  def map(&f: Quoted[(Int) -> String]) -> Quoted[(Int) -> String] = f
  def flat_map(&f: Quoted[(Int) -> Array[String]]) -> Quoted[(Int) -> Array[String]] = f
end

def show(e: Meta::Expr) -> String
  case e
  in Meta::Expr::Lit(value: v) then v.inspect
  in Meta::Expr::Capture(name: n) then "$#{n}"
  in Meta::Expr::Arg(name: n, depth: d) then "#{n}@#{d}"
  in Meta::Expr::SelfRef then "self"
  in Meta::Expr::Call(recv: r, method: m, args: a, block: b)
    rs = r ? show(r) + "." : ""
    bs = b ? " " + show(b) : ""
    "#{rs}#{m.name}(#{a.map { |x| show(x) }.join(", ")})#{bs}"
  in Meta::Expr::And(left: l, right: r) then "(#{show(l)} && #{show(r)})"
  in Meta::Expr::Or(left: l, right: r) then "(#{show(l)} || #{show(r)})"
  in Meta::Expr::Not(operand: o) then "!#{show(o)}"
  in Meta::Expr::If(cond: c, then_expr: t, else_expr: f) then "(#{show(c)} ? #{show(t)} : #{f ? show(f) : "nil"})"
  in Meta::Expr::ArrayLit(items: i) then "[#{i.map { |x| show(x) }.join(", ")}]"
  in Meta::Expr::HashLit(pairs: ps) then "{#{ps.map { |kv| show(kv[0]) + "=>" + show(kv[1]) }.join(", ")}}"
  in Meta::Expr::Interp(parts: ps) then "\"#{ps.map { |x| show(x) }.join}\""
  in Meta::Expr::Block(params: ps, body: b) then "{|#{ps.join(",")}| #{b.map { |x| show(x) }.join("; ")}}"
  end
end

r = Rel.new
n = 2
q = r.filter { views > LIMIT && !tags.empty? || views == n }
p show(q.expr)
p q.captures
p Row.new.instance_exec(&q.proc)
q2 = r.map { |x| x > 1 ? "big #{x}" : "small" }
p show(q2.expr), q2.proc.call(3)
q3 = r.flat_map { |x| [x, x + 1].map(&:to_s).select { |s| s != "#{n}" } }
p show(q3.expr), q3.proc.call(2)
q4 = r.map { |x| {x => [TABLE, :sym, 1.5, nil]}.to_s }
p show(q4.expr)
c = Cond.new("a")
q5 = r.map { |x| (c && Cond.new("b")).sql }
p show(q5.expr), q5.proc.call(0)
"##;

const TREES_OUT: &str = r##""{|| ((views().>(5) && !tags().empty?()) || views().==($n))}"
[2]
true
"{|x| (x@0.>(1) ? \"\"big \"x@0\" : \"small\")}"
"big 3"
"{|x| [x@0, x@0.+(1)].map() {|x| x@0.to_s()}.select() {|s| s@0.!=(\"$n\")}}"
["3"]
"{|x| {x@0=>[Col(name: \"t\"), :sym, 1.5, nil]}.to_s()}"
"{|x| $c.&&() {|| Cond.new(\"b\")}.sql()}"
"(a AND b)"
"##;

#[test]
fn trees_and_closures_the_same_interpreted_and_compiled() {
    let d = dir();
    write(&d.0, "app.qz", TREES);
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, TREES_OUT);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), TREES_OUT);
}

#[test]
fn what_cannot_be_quoted() {
    let d = dir();
    write(
        &d.0,
        "bad.qz",
        r##"class R
  def where(&cond: Quoted[(Int) -> Bool]) -> Bool = true
  def each_q(&b: (Int) -> Bool) -> Bool = true
end
r = R.new
pr = ->(x: Int) { x > 1 }
r.where(&pr)
r.where { |x| y = x; y > 1 }
r.where { |x| while x > 1; end; true }
r.where { |x| case x when 1 then true else false end }
r.where { |x| return true }
r.where { |x| (1..x).include?(2) }
r.where { |x| ->(y: Int) { y }.call(x) > 0 }
r.where { |x| x&.even? || false }
r.where { |x| raise "no" }
Quoted.new(1, [], 2, "f")
r.where { |x| x.even? }
"##,
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    let tail = "cannot be quoted: a block given as a `Quoted` holds literals, variables, `self`, calls, `&&`, `||`, `!`, `if` and blocks (docs/14 §6)";
    for (at, what) in [
        ("8:15", "an assignment"),
        ("9:15", "a loop"),
        ("10:15", "`case`"),
        ("11:15", "`return`"),
        ("12:15", "a range"),
        ("13:15", "`call` here"),
        ("14:15", "`&.`"),
        ("15:15", "`raise` here"),
    ] {
        let want = format!("bad.qz:{at}: error: {what} {tail}");
        assert!(
            err.contains(&want),
            "{want}
{err}"
        );
    }
    assert!(
        err.contains("bad.qz:7:10: error: block argument has type (Int) -> Bool but Quoted[(Int) -> Bool] was expected"),
        "{err}"
    );
    assert!(
        err.contains("bad.qz:16:1: error: a `Quoted` is made from a block literal"),
        "{err}"
    );
}

#[test]
fn shareable_quoted_blocks() {
    let d = dir();
    write(
        &d.0,
        "ok.qz",
        r##"class R
  def where(&cond: Quoted[shareable (Int) -> Bool]) -> Quoted[shareable (Int) -> Bool] = cond
  def loose(&cond: Quoted[(Int) -> Bool]) -> Quoted[(Int) -> Bool] = cond
end
PUB = R.new.where { |x| x > 1 }
p PUB.proc.call(3)
t = Task.spawn { PUB.proc.call(0) }
p t.await
"##,
    );
    let (ok, out, err) = quarz(&d.0, &["run", "ok.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(
        out,
        "true
false
"
    );
    write(
        &d.0,
        "bad.qz",
        &format!(
            "{}BAD = R.new.loose {{ |x| x > 1 }}
",
            r##"class R
  def where(&cond: Quoted[shareable (Int) -> Bool]) -> Quoted[shareable (Int) -> Bool] = cond
  def loose(&cond: Quoted[(Int) -> Bool]) -> Quoted[(Int) -> Bool] = cond
end
PUB = R.new.where { |x| x > 1 }
p PUB.proc.call(3)
t = Task.spawn { PUB.proc.call(0) }
p t.await
"##
        ),
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("constant `BAD` has the non-shareable type Quoted[(Int) -> Bool]"),
        "{err}"
    );
}

#[test]
fn for_comprehensions_give_trees() {
    let d = dir();
    write(
        &d.0,
        "app.qz",
        r##"class Rel
  @log: Array[String]
  def initialize(@log: Array[String]); end
  def log -> Array[String] = @log
  def flat_map(&f: Quoted[(Int) -> Rel]) -> Rel = Rel.new(@log + ["flat_map #{f.expr.class}"] + f.proc.call(1).log)
  def filter(&f: Quoted[(Int) -> Bool]) -> Rel = Rel.new(@log + ["filter #{f.expr}"])
  def map(&f: Quoted[(Int) -> Int]) -> Rel = Rel.new(@log + ["map #{f.expr}"])
end
a = Rel.new([])
b = Rel.new([])
r = for x in a, y in b when x > y do x + y end
r.log.each { |l| puts l }
"##,
    );
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines[0], "flat_map Meta::Expr::Block");
    // The inner blocks read the outer one's parameter as a capture.
    assert!(lines[1].starts_with("filter Meta::Expr::Block(params: [:y], body: [Meta::Expr::Call(recv: Meta::Expr::Capture(index: 0, name: :x"), "{out}");
    assert!(
        lines[2].starts_with("map Meta::Expr::Block(params: [:y]"),
        "{out}"
    );
}

#[test]
fn a_quoted_block_is_a_snapshot_at_the_call() {
    // docs/14 §6: the tree's captures and `proc` read the values of the
    // call, a later reassignment seen by neither.
    let d = dir();
    write(
        &d.0,
        "app.qz",
        "class R\n  def where(&cond: Quoted[(Int) -> Bool]) -> Quoted[(Int) -> Bool] = cond\nend\nn = 1\nq = R.new.where { |x| x == n }\nn = 2\np q.captures\np q.proc.call(2)\np q.proc.call(1)\nclass H\n  @lim: Int = 5\n  def lim -> Int = @lim\n  def q -> Quoted[(Int) -> Bool] = R.new.where { |x| x > lim }\nend\nh = H.new.q\np h.captures.size\np h.proc.call(6)\n",
    );
    let expected = "[1]\nfalse\ntrue\n1\ntrue\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

#[test]
fn where_a_quoted_block_and_a_procedure_meet() {
    let d = dir();
    // At the declarations.
    write(
        &d.0,
        "decl.qz",
        "class A\n  def where(&f: Quoted[(Int) -> Bool]) -> Bool = f.proc.call(1)\nend\nclass B < A\n  def where(&f: (Int) -> Bool) -> Bool = f.call(1)\nend\nclass MyQ < Quoted[(Int) -> Bool]\nend\nmodule M\n  abstract def w(&f: Quoted[(Int) -> Bool]) -> Bool\nend\nclass K\nend\nextension K\n  include M\n  def w(&f: (Int) -> Bool) -> Bool = f.call(1)\nend\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "decl.qz"], &[]);
    assert!(!ok);
    for want in [
        "decl.qz:5:3: error: `where` takes its block as a procedure, but `A#where`, which it overrides, takes a `Quoted`",
        "decl.qz:7:1: error: `Quoted` cannot be subclassed",
        "decl.qz:16:3: error: `w` takes its block as a procedure, but `M#w`, which it implements, takes a `Quoted`",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
    // In the bodies.
    write(
        &d.0,
        "body.qz",
        "class A\n  def where(&f: Quoted[(Int) -> Bool]) -> Bool = f.proc.call(1)\n  def y(&f: Quoted[(Int) -> Bool]) -> Bool = yield 1\nend\nclass C\n  def where(&f: (Int) -> Bool) -> Bool = f.call(1)\nend\ndef pick(n: Int) -> A | C = n > 0 ? A.new : C.new\npick(0).where { |x| x > 0 }\nA.new.where(&:even?)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "body.qz"], &[]);
    assert!(!ok);
    for want in [
        "body.qz:3:46: error: `yield` cannot run a `Quoted` block",
        "body.qz:9:1: error: the methods this call may run take its block differently",
        "body.qz:10:14: error: `&:even?` cannot be given for a `Quoted` block parameter",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
}

#[test]
fn overloads_by_block_kind() {
    // The overload chosen decides whether the block is quoted, whatever
    // the order the overloads are tried in.
    let d = dir();
    write(
        &d.0,
        "app.qz",
        "class A\n  def w(&f: Quoted[(Int) -> Bool]) -> String = \"quoted\"\n  def w(&f: (String) -> Bool) -> String = \"proc #{f.call(\"a\")}\"\nend\np A.new.w { |x| x.empty? }\nclass B\n  def w(&f: (String) -> Bool) -> String = \"proc #{f.call(\"a\")}\"\n  def w(&f: Quoted[(Int) -> Bool]) -> String = \"quoted\"\nend\np B.new.w { |x| x > 0 }\np B.new.w { |x| x.empty? }\nclass C\n  def w(x: Int, &f: Quoted[(Int) -> Bool]) -> Int = f.captures.size\n  def w(x: String, &f: (Int) -> Bool) -> Int = 0\nend\nn = 1\np C.new.w(1) { |x| x > n }\nclass R\n  def c(&f: Quoted[(Int) -> Bool]) -> Int = f.captures.size\nend\nclass S < R\n  def c(&f: Quoted[(Int) -> Bool]) -> Int = f.captures.size + super\nend\nr: R = S.new\np r.c { |x| x > n }\n",
    );
    let expected = "\"proc false\"\n\"quoted\"\n\"proc false\"\n1\n2\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

#[test]
fn the_tree_is_built_once_per_call_site() {
    // docs/14 §6: two calls of one site share the tree (a constant),
    // another site has its own; captures stay per call.
    let d = dir();
    write(
        &d.0,
        "app.qz",
        "class R\n  def where(&cond: Quoted[(Int) -> Bool]) -> Quoted[(Int) -> Bool] = cond\nend\ndef q(n: Int) -> Quoted[(Int) -> Bool] = R.new.where { |x| x > n && x.even? }\na = q(1)\nb = q(2)\np a.expr.equal?(b.expr), a.captures, b.captures, a.proc.call(4), b.proc.call(2)\nc = R.new.where { |x| x > 1 && x.even? }\np a.expr.equal?(c.expr), a.expr == c.expr\n",
    );
    let expected = "true\n[1]\n[2]\ntrue\nfalse\nfalse\nfalse\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}
