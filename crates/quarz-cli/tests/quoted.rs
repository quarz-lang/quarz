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
  in Meta::Expr::SelfRef(depth: d) then "self@#{d}"
  in Meta::Expr::Call(recv: r, method: m, args: a, block: b)
    rs = r ? show(r) + "." : ""
    bs = b ? " " + show(b) : ""
    "#{rs}#{m.name}(#{a.map { |x| show(x) }.join(", ")})#{bs}"
  in Meta::Expr::SafeCall(recv: r, method: m, args: a, block: b)
    bs = b ? " " + show(b) : ""
    "#{show(r)}&.#{m.name}(#{a.map { |x| show(x) }.join(", ")})#{bs}"
  in Meta::Expr::And(left: l, right: r) then "(#{show(l)} && #{show(r)})"
  in Meta::Expr::Or(left: l, right: r) then "(#{show(l)} || #{show(r)})"
  in Meta::Expr::Not(operand: o) then "!#{show(o)}"
  in Meta::Expr::If(cond: c, then_expr: t, else_expr: f) then "(#{show(c)} ? #{show(t)} : #{f ? show(f) : "nil"})"
  in Meta::Expr::ArrayLit(items: i) then "[#{i.map { |x| show(x) }.join(", ")}]"
  in Meta::Expr::HashLit(pairs: ps) then "{#{ps.map { |kv| show(kv[0]) + "=>" + show(kv[1]) }.join(", ")}}"
  in Meta::Expr::RangeLit(lo: l, hi: h, exclusive: x) then "(#{l ? show(l) : ""}#{x ? "..." : ".."}#{h ? show(h) : ""})"
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

const TREES_OUT: &str = r##""{|| ((self@0.views().>(5) && !self@0.tags().empty?()) || self@0.views().==($n))}"
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
r.where { |x| :"a#{x}" == :a1 }
r.where { |x| ->(y: Int) { y }.call(x) > 0 }
r.where { |x| x&.even? || false }
r.where { |x| raise "no" }
Quoted.new(1, [], 2, "f")
r.where { |x| x.even? }
"##,
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    let tail = "cannot be quoted: a block given as a `Quoted` holds literals, ranges, variables, `self`, calls (`&.` too), `&&`, `||`, `!`, `if` and blocks (docs/14 §6)";
    for (at, what) in [
        ("8:15", "an assignment"),
        ("9:15", "a loop"),
        ("10:15", "`case`"),
        ("11:15", "`return`"),
        ("12:15", "an interpolated symbol"),
        ("13:15", "`call` here"),
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

/// #901: a block literal that declares no parameters takes the overload
/// whose block has a receiver over one whose block takes an argument, a
/// `Quoted` one as a procedure (the block's arity, `Checker::beats`):
/// `{ |x| }`, `{ it }` take the argument's; a name both readings answer
/// is the receiver's (the tree's `MethodRef`); a `Quoted` passed on with
/// `&b` takes the overload its type fits; across owners the receiver's
/// too, as for procedures (before #901, the subclass's: 2).
#[test]
fn a_block_without_parameters_takes_the_receiver_overload() {
    let d = dir();
    write(&d.0, "app.qz", APP_901);
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, EXPECTED_901);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), EXPECTED_901);
    // `&:name` is no block for a `Quoted` parameter, whichever overload.
    write(
        &d.0,
        "sym.qz",
        "class Q[T]\n  def where(&b: Quoted[T.() -> Bool]) -> Int = 1\n  def where(&b: Quoted[(T) -> Bool]) -> Int = 2\nend\np Q[String].new.where(&:empty?)\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "sym.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("`&:empty?` cannot be given for a `Quoted` block parameter"),
        "{err}"
    );
}

const APP_901: &str = r##"def show(e: Meta::Expr) -> String
  case e
  in Meta::Expr::Block(body: b) then "{ " + b.map { |x| show(x) }.join("; ") + " }"
  in Meta::Expr::SelfRef(depth: d) then "self@#{d}"
  in Meta::Expr::Call(recv: r, method: m, args: a, block: b)
    "#{r ? show(r) + "." : ""}#{m.owner.name}##{m.name}(#{a.map { |x| show(x) }.join(", ")})"
  else e.to_s
  end
end

class Q[T]
  def where(&b: Quoted[T.() -> Bool]) -> Int = 1
  def where(&b: Quoted[(T) -> Bool]) -> Int = 2
end
q = Q[String].new
p q.where { true }
p q.where { |x| true }
p q.where { size > 1 }
p q.where { it.size > 1 }
p q.where { || true }

# A name the receiver and a function both answer: the receiver's reading.
class Row
  def now -> Int = 1
end
module Helpers
  extension Kernel
    private def self.now -> Int = 2
  end
end
using Helpers
class R
  def update(&b: Quoted[Row.() -> Int]) -> String = "receiver " + show(b.expr)
  def update(&b: Quoted[(Row) -> Int]) -> String = "argument " + show(b.expr)
end
puts R.new.update { now }
# rotor's shape: the function alone.
class Plain
end
class U
  def update(&b: Quoted[Plain.() -> Hash[Symbol, Int]]) -> String = "receiver " + show(b.expr)
  def update(&b: Quoted[(Plain) -> Hash[Symbol, Int]]) -> String = "argument " + show(b.expr)
end
puts U.new.update { {at: now} }

# Across owners.
class P1
  def where(&b: Quoted[String.() -> Bool]) -> Int = 1
end
class P2 < P1
  def where(&b: Quoted[(String) -> Bool]) -> Int = 2
end
p P2.new.where { true }

# A `Quoted` passed on with `&b` takes the overload its type fits.
def pass_r(&b: Quoted[String.() -> Bool]) -> Int = Q[String].new.where(&b)
def pass_a(&b: Quoted[(String) -> Bool]) -> Int = Q[String].new.where(&b)
p pass_r { true }
p pass_a { |x| true }
"##;

const EXPECTED_901: &str = "1\n2\n1\n2\n1\nreceiver { self@0.Row#now() }\nreceiver { Meta::Expr::HashLit(pairs: [[Meta::Expr::Lit(value: :at, line: 44), Meta::Expr::Call(recv: nil, method: Meta::MethodRef(owner: Kernel, name: :now, singleton: true, index: 0, extension: Helpers), methods: [Meta::MethodRef(owner: Kernel, name: :now, singleton: true, index: 0, extension: Helpers)], args: [], block: nil, line: 44)]], line: 44) }\n1\n1\n2\n";

/// #886: `recv&.m(...)` in a quoted block is a `Meta::Expr::SafeCall`,
/// a node of its own: on a nilable receiver (typed `Int?` as written),
/// with a block, on a union, chained, on a receiver block's `self`, in an
/// inner block; the closure runs as written; interpreted and compiled.
/// An assignment through `&.` stays refused, and a reader's exhaustive
/// `case` without the node is a compile error saying so.
#[test]
fn a_safe_call_is_a_node_of_its_own() {
    let d = dir();
    write(&d.0, "app.qz", APP_886);
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, EXPECTED_886);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), EXPECTED_886);
    write(&d.0, "assign.qz", "class Box\n  var @n: Int = 0\n  def n -> Int = @n\n  def n=(v: Int) -> Int\n    @n = v\n  end\nend\ndef take(&b: Quoted[(Box?) -> Int?]) -> Int = 0\ntake { |x| x&.n = 1 }\ntake { |x| x&.n += 1 }\n");
    let (ok, _, err) = quarz(&d.0, &["check", "assign.qz"], &[]);
    assert!(!ok);
    assert_eq!(
        err.matches("error: an assignment cannot be quoted").count(),
        2,
        "{err}"
    );
    write(&d.0, "reader.qz", "def name(e: Meta::Expr) -> String\n  case e\n  in Meta::Expr::Lit then \"lit\"\n  in Meta::Expr::Capture then \"capture\"\n  in Meta::Expr::Arg then \"arg\"\n  in Meta::Expr::SelfRef then \"self\"\n  in Meta::Expr::Call then \"call\"\n  in Meta::Expr::And then \"and\"\n  in Meta::Expr::Or then \"or\"\n  in Meta::Expr::Not then \"not\"\n  in Meta::Expr::If then \"if\"\n  in Meta::Expr::ArrayLit then \"array\"\n  in Meta::Expr::HashLit then \"hash\"\n  in Meta::Expr::RangeLit then \"range\"\n  in Meta::Expr::Interp then \"interp\"\n  in Meta::Expr::Block then \"block\"\n  end\nend\nputs name(Meta::Expr::Lit.new(1, 1))\n");
    let (ok, _, err) = quarz(&d.0, &["check", "reader.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains(
            "error: `case` does not cover: Meta::Expr::SafeCall (add an `in` arm or `else`)"
        ),
        "{err}"
    );
}

const APP_886: &str = r##"def show(e: Meta::Expr) -> String
  case e
  in Meta::Expr::Block(body: b) then b.map { |x| show(x) }.join("; ")
  in Meta::Expr::Arg(name: n) then n.to_s
  in Meta::Expr::SelfRef(depth: d) then "self@#{d}"
  in Meta::Expr::Lit(value: v) then v.inspect
  in Meta::Expr::Call(recv: r, method: m, args: a, block: b)
    "#{r ? show(r) + "." : ""}#{m.owner.name}##{m.name}(#{a.map { |x| show(x) }.join(", ")})#{b ? " { " + show(b) + " }" : ""}"
  in Meta::Expr::SafeCall(recv: r, method: m, methods: ms, args: a, block: b)
    "#{show(r)}&.#{m.owner.name}##{m.name}(#{a.map { |x| show(x) }.join(", ")})#{b ? " { " + show(b) + " }" : ""} [#{ms.map { |x| x.owner.name }.join(", ")}]"
  else e.to_s
  end
end

def take(&b: Quoted[(String?) -> Int?]) -> Void
  puts show(b.expr)
  p b.proc.call("abc"), b.proc.call(nil)
end
def take_list(&b: Quoted[(Array[Int]?) -> Array[Int]?]) -> Void
  puts show(b.expr)
  p b.proc.call([1, 2]), b.proc.call(nil)
end
def take_union(&b: Quoted[(String | Array[Int] | Nil) -> Int?]) -> Void
  puts show(b.expr)
  p b.proc.call("ab"), b.proc.call([1]), b.proc.call(nil)
end
def take_chain(&b: Quoted[(String?) -> String?]) -> Void
  puts show(b.expr)
  p b.proc.call(" a "), b.proc.call(nil)
end
class Row
  def name -> String? = "row"
end
def take_row(&b: Quoted[Row.() -> Int?]) -> Void
  puts show(b.expr)
  p Row.new.instance_exec(&b.proc)
end

take { |c| c&.size }
take_list { |xs| xs&.map { |x| x * 2 } }
take_union { |v| v&.size }
take_chain { |s| s&.strip&.upcase }
take_row { name&.size }
take { |c| [1].map { |n| c&.size }.first }
"##;

const EXPECTED_886: &str = "c&.String#size() [String]\n3\nnil\nxs&.Array#map() { x.Int#*(2) } [Array]\n[2, 4]\nnil\nv&.Array#size() [Array, String]\n2\n1\nnil\ns&.String#strip() [String]&.String#upcase() [String]\n\"A\"\nnil\nself@0.Row#name()&.String#size() [String]\n3\nMeta::Expr::ArrayLit(items: [Meta::Expr::Lit(value: 1, line: 44)], line: 44).Array#map() { c&.String#size() [String] }.Array#first()\n3\nnil\n";

/// #653: a range literal in a quoted block is a `Meta::Expr::RangeLit`,
/// its bounds quoted (literals, a capture, an argument, an expression)
/// or nil when left out, `...` marked `exclusive`, always a node; a range
/// in a constant stays the constant's `Lit`. The closure runs as written,
/// interpreted and compiled. `Range`'s `Comparable` bound is checked at the
/// literal as anywhere, and a reader's exhaustive `case` without the node
/// is a compile error saying so.
#[test]
fn a_range_is_a_node_of_its_own() {
    let d = dir();
    write(&d.0, "app.qz", APP_653);
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, EXPECTED_653);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), EXPECTED_653);
    write(&d.0, "bound.qz", "class Box\nend\ndef take(&b: Quoted[(Box) -> Bool]) -> Bool = true\ntake { |x| (x..x).nil? }\n");
    let (ok, _, err) = quarz(&d.0, &["check", "bound.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains(
            "bound.qz:4:12: error: type argument Box for `T` of `Range` must be Comparable[Box]"
        ),
        "{err}"
    );
    write(&d.0, "reader.qz", "def name(e: Meta::Expr) -> String\n  case e\n  in Meta::Expr::Lit then \"lit\"\n  in Meta::Expr::Capture then \"capture\"\n  in Meta::Expr::Arg then \"arg\"\n  in Meta::Expr::SelfRef then \"self\"\n  in Meta::Expr::Call then \"call\"\n  in Meta::Expr::SafeCall then \"safe call\"\n  in Meta::Expr::And then \"and\"\n  in Meta::Expr::Or then \"or\"\n  in Meta::Expr::Not then \"not\"\n  in Meta::Expr::If then \"if\"\n  in Meta::Expr::ArrayLit then \"array\"\n  in Meta::Expr::HashLit then \"hash\"\n  in Meta::Expr::Interp then \"interp\"\n  in Meta::Expr::Block then \"block\"\n  end\nend\nputs name(Meta::Expr::Lit.new(1, 1))\n");
    let (ok, _, err) = quarz(&d.0, &["check", "reader.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains(
            "error: `case` does not cover: Meta::Expr::RangeLit (add an `in` arm or `else`)"
        ),
        "{err}"
    );
}

const APP_653: &str = r##"def show(e: Meta::Expr) -> String
  case e
  in Meta::Expr::Block(body: b) then b.map { |x| show(x) }.join("; ")
  in Meta::Expr::Arg(name: n) then n.to_s
  in Meta::Expr::Capture(name: n) then "$#{n}"
  in Meta::Expr::Lit(value: v) then v.inspect
  in Meta::Expr::Call(recv: r, method: m, args: a)
    "#{r ? show(r) + "." : ""}#{m.name}(#{a.map { |x| show(x) }.join(", ")})"
  in Meta::Expr::RangeLit(lo: l, hi: h, exclusive: x, line: n)
    "(#{l ? show(l) : ""}#{x ? "..." : ".."}#{h ? show(h) : ""})@#{n}"
  else e.to_s
  end
end

def take(&b: Quoted[(Int) -> Bool]) -> Void
  puts show(b.expr)
  p b.proc.call(18), b.proc.call(65), b.proc.call(70)
end
def take_range(a: Int, &b: Quoted[(Int) -> Range[Int]]) -> Void
  puts show(b.expr)
  p b.proc.call(a)
end
ADULT = 18..65

take { |age| (18..65).include?(age) }
take { |age| (18...65).include?(age) }
lo = 20
take { |age| (lo..age + 1).include?(age) }
take_range(3) { |n| n.. }
take_range(3) { |n| ..n }
take { |age| ADULT.include?(age) }
"##;

const EXPECTED_653: &str = "(18..65)@25.include?(age)\ntrue\ntrue\nfalse\n(18...65)@26.include?(age)\ntrue\nfalse\nfalse\n($lo..age.+(1))@28.include?(age)\nfalse\ntrue\ntrue\n(n..)@29\n3..\n(..n)@30\n..3\n18..65.include?(age)\ntrue\ntrue\nfalse\n";

/// #1011: `Meta::MethodRef#result` at run time is `Meta::MethodSig#result`
/// at compile time for the same method (one function, `rtworld::erase`):
/// a `Bool`, a `Bool?` and a type parameter (`Object`), an `Array[Int]`
/// (`Array`), natives and an operator, a generated method; an
/// extension's method (which `Type#methods` does not list) and a
/// construction (`initialize`'s `Void`, `Nil`) by hand; a reference that
/// names no method raises. Interpreted and compiled.
#[test]
fn a_method_reference_tells_its_declared_result() {
    let d = dir();
    write(&d.0, "lib.qz", LIB_1011);
    write(&d.0, "app.qz", APP_1011);
    let expected = "[Bool, Object, Array, Object, Bool, Int, Object, Bool]\n[Bool, Object, Array, Object, Bool, Int, Object, Bool]\n[Bool]\n[Bool]\n[Bool, Nil, Bool, Bool]\nMeta::MethodRef names no method: App#nope (index 0)\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(&d.0, &["build", "app.qz", "-o", "app.bin"], &[]);
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

/// #1011, in a compiled program after `shake`, at -O2: a method named only
/// in a quoted block that never runs (a translator reads `expr` alone)
/// gives its declared result, and of two overloads of one name, the
/// second, named alone, gives its own (the reference's `index` still
/// finds it in the per-name list `shake` keeps).
#[test]
fn a_method_reference_tells_its_result_after_shake() {
    let d = dir();
    write(&d.0, "app.qz", APP_1011_SHAKE);
    let expected = "Bool\nBool\n";
    let (ok, out, err) = quarz(&d.0, &["run", "app.qz"], &[]);
    assert!(ok, "{err}");
    assert_eq!(out, expected);
    let (ok, _, err) = quarz(
        &d.0,
        &["build", "app.qz", "-o", "app.bin"],
        &[("QUARZ_AOT_OPT", "2")],
    );
    assert!(ok, "{err}");
    let run = Command::new(d.0.join("app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

const APP_1011_SHAKE: &str = r##"# Methods named only in quoted blocks that never run.
class Row
  def active? -> Bool = true
  def pick(x: Int) -> Int = x
  def pick(x: String) -> Bool = x.empty?
end

def first_result(&b: Quoted[Row.() -> Bool]) -> Type[Object]
  case b.expr
  in Meta::Expr::Block(body: [Meta::Expr::Call(method: m)]) then m.result
  else Object
  end
end

p first_result { active? }
p first_result { pick("x") }
"##;

const LIB_1011: &str = r##"class Probe
  # The compile-time view: `MethodSig#result` of `name` in `cls`.
  static def self.sig(cls: Type[Object], name: Symbol) -> Type[Object]
    s = cls.methods.find { |m| m.name == name }
    s ? s.result : Nil
  end
  static def self.record -> Void
    found = [
      sig(App, :flag), sig(App, :maybe), sig(App, :list), sig(App, :ident),
      sig(Int, :<), sig(Array, :size), sig(Array, :first), sig(String, :start_with?)
    ]
    def_class_method(:sigs) { found }
    def_method(:generated) do -> Bool
      true
    end
  end
  static def self.record_more -> Void
    more = [sig(App, :generated)]
    def_class_method(:more_sigs) { more }
  end
end
"##;

const APP_1011: &str = r##"require_relative "lib"
module Ext
  extension String
    def shout? -> Bool = true
  end
end
using Ext

class App < Probe
  def flag -> Bool = true
  def maybe -> Bool? = nil
  def list -> Array[Int] = [1]
  def ident[T](x: T) -> T = x
  def initialize; end
  record
  record_more
end

# `MethodRef#result` of each call (or `!`) the block's array holds.
def results(&b: Quoted[(App, Array[Int], String) -> Array[Object?]]) -> Array[Type[Object]]
  out: Array[Type[Object]] = []
  case b.expr
  in Meta::Expr::Block(body: [Meta::Expr::ArrayLit(items: items)])
    items.each do |x|
      case x
      in Meta::Expr::Call(methods: ms) then out = out.push(ms[0].result)
      in Meta::Expr::Not(methods: ms) then out = out.push(ms.empty? ? Bool : ms[0].result)
      else nil
      end
    end
  else nil
  end
  out
end

# At run time, against `MethodSig#result` at compile time (`App.sigs`,
# `App.more_sigs`).
p results { |a, xs, s| [a.flag, a.maybe, a.list, a.ident(1), 1 < 2, xs.size, xs.first, s.start_with?("x")] }
p App.sigs
p results { |a, xs, s| [a.generated] }
p App.more_sigs
# An extension's method (`Type#methods` lists none), a construction
# (`initialize`'s `Void`), `==`, and a user's `!` on `Bool`'s.
p results { |a, xs, s| [s.shout?, App.new, a == a, !a.flag] }
begin
  Meta::MethodRef.new(App, :nope, false, 0, nil).result
rescue ArgumentError => e
  puts e.message
end
"##;

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

#[test]
fn a_call_that_failed_its_check_is_not_also_unquotable() {
    let d = dir();
    write(
        &d.0,
        "bad.qz",
        "def keep(&cond: Quoted[(Int) -> Bool]) -> Bool = cond.proc.call(1)\nkeep { |x| x > \"one\" }\nkeep { |x| x.nope }\n",
    );
    let (ok, _, err) = quarz(&d.0, &["check", "bad.qz"], &[]);
    assert!(!ok);
    assert!(
        err.contains("bad.qz:2:12: error: no overload of `>` on Int matches (String)"),
        "{err}"
    );
    assert!(
        err.contains("bad.qz:3:12: error: undefined method `nope` for Int"),
        "{err}"
    );
    assert!(!err.contains("cannot be quoted"), "{err}");
}
