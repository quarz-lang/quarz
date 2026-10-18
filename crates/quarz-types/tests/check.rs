//! The checker must accept correct programs and reject incorrect ones with
//! the expected message.

use quarz_syntax::{parse, parse_with_bases};
use quarz_types::load::unit_base;
use quarz_types::{check, PRELUDE_SOURCE};

fn diagnostics(src: &str) -> Vec<String> {
    let prelude = parse(PRELUDE_SOURCE);
    assert!(
        prelude.diagnostics.is_empty(),
        "prelude: {:?}",
        prelude.diagnostics
    );
    let base = unit_base(0);
    let parsed = parse_with_bases(src, base, base);
    let errors: Vec<_> = parsed.diagnostics.iter().filter(|d| d.is_error()).collect();
    assert!(errors.is_empty(), "parse errors for {src:?}: {errors:?}");
    let (_, diags) = check(&prelude.program, &parsed.program);
    diags
        .into_iter()
        .filter(|(file, d)| *file == 1 && d.is_error())
        .map(|(_, d)| d.message)
        .collect()
}

fn ok(src: &str) {
    let errs = diagnostics(src);
    assert!(
        errs.is_empty(),
        "unexpected errors for {src:?}:\n{}",
        errs.join("\n")
    );
}

fn err(src: &str, expected: &str) {
    let errs = diagnostics(src);
    assert!(
        errs.iter().any(|e| e.contains(expected)),
        "expected an error containing {expected:?} for {src:?}, got:\n{}",
        errs.join("\n")
    );
}

#[test]
fn prelude_checks_cleanly() {
    let prelude = parse(PRELUDE_SOURCE);
    let empty = parse("");
    let (checked, diags) = check(&prelude.program, &empty.program);
    let errors: Vec<_> = diags.iter().filter(|(_, d)| d.is_error()).collect();
    assert!(errors.is_empty(), "{errors:?}");
    assert!(checked.is_some());
}

#[test]
fn locals_and_literals() {
    ok("x = 1\ny = x + 2\nputs y");
    ok("s = \"a\" + \"b\"\nputs s.size");
    err(
        "x = 1\nx = \"s\"",
        "cannot assign String to `x` of type Int",
    );
    err("\"a\" + 1", "expects String but found Int");
    err("nil.foo", "undefined method `foo` for Nil");
    err(
        "puts undefined_thing",
        "undefined local variable or method `undefined_thing`",
    );
    ok("xs = [1, 2, 3]\nputs xs.map { |x| x * 2 }.sum");
    ok("h = { a: 1, b: 2 }\nputs h[:a] + h.fetch(:c, 0)");
    err(
        "xs = [1, 2]\nxs << 3",
        "undefined method `<<` for Array[Int]",
    );
    err(
        "h = { a: 1 }\nh[:b] = 2",
        "undefined method `[]=` for Hash[Symbol, Int]",
    );
    ok("xs: Array[Int] = []\nxs = xs.push(1)");
    ok("xs = []\nxs = xs.push(1)\nputs xs.size");
    ok("acc = [1, 2].reduce({}) { |h, x| h.put(x, x.to_s) }\nputs acc[1]");
    ok("t = 1.0 + 2\nf: Float = 3\nputs t + f");
}

#[test]
fn nil_safety_and_narrowing() {
    err("x: Int? = nil\nx + 1", "undefined method `+` for Nil");
    ok("x: Int? = nil\nif x\n  puts x + 1\nend");
    ok("x: Int? = nil\nputs x + 1 unless x.nil?");
    ok("def f(x: Int?) -> Int\n  return 0 unless x\n  x + 1\nend");
    ok("def f(x: Int?) -> Int\n  return 0 if x.nil?\n  x * 2\nend");
    ok("def f(x: Int?) -> Int = x || 0");
    ok("def f(x: Int?) -> Int\n  y = x || raise ArgumentError, \"nil\"\n  y + 1\nend");
    ok("def f(x: Int | String) -> String\n  if x.is_a?(Int)\n    (x + 1).to_s\n  else\n    x.upcase\n  end\nend");
    ok("def f(x: Int | String) -> Int\n  case x\n  in Int => n then n\n  in String => s then s.size\n  end\nend");
    err(
        "def f(x: Int | String) -> Int\n  case x\n  in Int => n then n\n  end\nend",
        "does not cover: String",
    );
    ok("x: String? = nil\ny = x&.size\nputs y || 0");
    ok("x: Int? = nil\nputs(x && x + 1)");
    ok("lines = [\"a\", \"bb\"]\ni = 0\nwhile (line = lines[i]?)\n  puts line.size\n  i += 1\nend");
    err("line: String? = \"a\"\nwhile (line = line.size > 3 ? nil : line + \"b\")\n  puts line\nend", "undefined method `size` for Nil");
}

#[test]
fn classes_and_fields() {
    ok("class C\n  @x: Int\n  attr_reader :x\n  def initialize(@x: Int); end\nend\nputs C.new(1).x");
    err(
        "class C\n  @x: Int\n  def initialize\n  end\nend",
        "field `@x` must be assigned in `initialize`",
    );
    err(
        "class C\n  @x: Int\n  def initialize(@x: Int); end\n  def bump -> Nil\n    @x = 2\n  end\nend",
        "field `@x` is immutable",
    );
    ok("class C\n  var @x: Int = 0\n  attr_accessor :x\n  def bump -> Nil\n    @x += 1\n  end\nend\nc = C.new\nc.bump\nc.x = 5");
    err(
        "class C\n  @x: Int = 0\n  attr_accessor :x\nend",
        "is immutable; declare it with `var`",
    );
    err("class C\nend\nclass C\nend", "cannot be reopened");
    err(
        "abstract class A\n  abstract def f -> Int\nend\nA.new",
        "cannot instantiate `A`",
    );
    ok("abstract class A\n  abstract def f -> Int\n  def g -> Int = f + 1\nend\nclass B < A\n  override def f -> Int = 1\nend\nputs B.new.g");
    err(
        "class P\n  private def secret -> Int = 1\nend\nP.new.secret",
        "is private",
    );
    ok("class P\n  def pub -> Int = secret\n  private def secret -> Int = 1\nend\nputs P.new.pub");
    ok("class V\n  @x: Int\n  def initialize(@x: Int); end\n  def +(o: V) -> V = V.new(@x + o.x)\n  def x -> Int = @x\nend\nputs (V.new(1) + V.new(2)).x");
    err(
        "def f -> Int\n  @x\nend",
        "instance variables are not available",
    );
}

#[test]
fn data_and_enum() {
    ok("data P(x: Int, y: Int)\np = P.new(1, 2)\nq = p.with(y: 5)\nputs q.x + q.y\np => P(x:, y:)\nputs x");
    err(
        "data P(x: Int)\nP.new(\"s\")",
        "expects Int but found String",
    );
    ok("data P(x: Int) is\n  def double -> P = P.new(x * 2)\nend\nputs P.new(2).double.x");
    ok("enum E\n  A\n  B(v: Int)\nend\ndef f(e: E) -> Int\n  case e\n  in E::A then 0\n  in E::B(v:) then v\n  end\nend\nputs f(E::A) + f(E::B.new(3))");
    err(
        "enum E\n  A\n  B\nend\ndef f(e: E) -> Int\n  case e\n  in E::A then 1\n  end\nend",
        "does not cover: E::B",
    );
    ok("enum E\n  A\n  B\n  def flip -> E\n    case self\n    in A then B\n    in B then A\n    end\n  end\nend\nputs E::A.flip == E::B");
    ok("enum Shape\n  Circle(r: Float)\n  Rect(w: Float, h: Float)\n  include Comparable[Shape]\n  def area -> Float\n    case self\n    in Circle(r:) then 3.14 * r * r\n    in Rect(w:, h:) then w * h\n    end\n  end\n  def <=>(o: Shape) -> Int = area <=> o.area\nend\nputs [Shape::Circle.new(1.0), Shape::Rect.new(1.0, 2.0)].sort.first");
    ok("r: Result[Int, String] = Result::Ok.new(1)\ncase r\nin Result::Ok(value:) then puts value + 1\nin Result::Err(error:) then puts error.size\nend");
}

#[test]
fn methods_and_calls() {
    err(
        "def f(a: Int)\nend\nf(1, 2)",
        "takes 1 positional argument(s)",
    );
    err(
        "def f(*, k: Int)\nend\nf(1)",
        "takes 0 positional argument(s)",
    );
    ok("def f(a: Int, *, k: Int = 1, v: Bool = false) -> Int = a + k\nputs f(1) + f(2, k: 3) + f(a: 4, v: true)");
    err("def f(a: Int)\nend\nf(b: 1)", "has no parameter `b`");
    err(
        "def f\n  f\nend",
        "recursive method `f` needs an explicit return type",
    );
    ok("def fact(n: Int) -> Int = n <= 1 ? 1 : n * fact(n - 1)\nputs fact(5)");
    err(
        "def f(x: Int) -> String\n  x\nend",
        "returns String but its body has type Int",
    );
    ok("def f(x: Int)\n  x * 2\nend\ny: Int = f(2)");
    err(
        "def f\n  yield\nend",
        "`yield` in a method without a block parameter",
    );
    ok("def twice(&block: (Int) -> Int) -> Int = yield(yield(1))\nputs twice { |x| x + 1 }");
    err(
        "[1].each { |a, b| }",
        "block takes 1 parameter(s) but 2 are declared",
    );
    ok("{ a: 1 }.each { |k, v| puts k.to_s + v.to_s }");
    ok("def apply(f: (Int) -> Int) -> Int = f.call(1)\nputs apply(->(x: Int) { x + 1 })");
    ok("xs = [3, 1, 2]\nputs xs.sort.first\nputs xs.max_by { |x| -x }\nputs xs.map(&:to_s).join(\",\")");
    err("[1, 2].max_by { |x| x }.foo", "undefined method `foo`");
    ok("def g[T](x: T) -> T = x\nputs g(1) + 1\nputs g(\"s\").size");
    ok("def h[T: Comparable[T]](a: T, b: T) -> T = a > b ? a : b\nputs h(1, 2)");
    err("def h[T: Comparable[T]](a: T, b: T) -> T = a > b ? a : b\nh(->(x: Int) { x }, ->(x: Int) { x })", "does not satisfy the bound");
    ok("x = [1, 2].first\nputs x + 1 if x");
    ok("puts [1, 2].first?.to_s");
    ok("class A\n  def f(x: Int) -> Int = x\n  def f(x: String) -> String = x\nend\nputs A.new.f(1) + 1\nputs A.new.f(\"s\").size");
}

#[test]
fn extensions() {
    err(
        "module M\n  extension Int\n    def double -> Int = self * 2\n  end\nend\n1.double",
        "undefined method `double`",
    );
    ok("module M\n  extension Int\n    def double -> Int = self * 2\n  end\nend\nusing M\nputs 1.double");
    ok("module Describable\n  abstract def describe -> String\nend\nmodule M\n  extension Int\n    include Describable\n    def describe -> String = \"int\"\n  end\nend\nusing M\ndef show(d: Describable) -> Nil\n  puts d.describe\nend\nshow(1)");
    err(
        "module Describable\n  abstract def describe -> String\nend\ndef show(d: Describable) -> Nil\n  puts d.describe\nend\nshow(1)",
        "expects Describable but found Int",
    );
    err("using Nope", "unknown constant `Nope`");
}

#[test]
fn concurrency_rules() {
    ok("t = spawn { 1 + 1 }\nputs t.await");
    ok("x = 1\nt = spawn { x + 1 }\nputs t.await");
    err(
        "b = Array::Builder[Int].new\nspawn { b << 1 }",
        "non-shareable type Array::Builder[Int]",
    );
    err(
        "total = 0\nspawn { total += 1 }",
        "cannot assign to `total` from a `spawn` block",
    );
    ok("n = Atom.new(0)\nspawn { n.update { |v| v + 1 } }.await\nputs n.value");
    err("Channel[Array::Builder[Int]].new", "must be Shareable");
    err("B = Array::Builder[Int].new", "non-shareable type");
    ok("ch = Channel[Int].new\nTask.scope do |scope|\n  scope.spawn { ch.send(1) }\n  puts ch.receive\nend");
    ok("class Counter\n  var @n: Int = 0\n  def bump -> Nil\n    @n += 1\n  end\nend\nc = Counter.new\nc.bump");
    err(
        "class Counter\n  var @n: Int = 0\nend\nc = Counter.new\nspawn { c }",
        "non-shareable type Counter",
    );
    ok("data P(x: Int)\np = P.new(1)\nspawn { p.x }.await");
}

#[test]
fn control_flow() {
    ok("x = if true then 1 else 2 end\nputs x + 1");
    ok("def f(b: Bool) -> Int | String\n  if b then 1 else \"s\" end\nend");
    ok("def f(n: Int) -> String\n  case n\n  when 1 then \"one\"\n  when 2, 3 then \"few\"\n  else \"many\"\n  end\nend");
    ok("begin\n  raise ArgumentError, \"x\"\nrescue ArgumentError => e\n  puts e.message\nensure\n  puts \"done\"\nend");
    err("raise 1", "cannot raise Int");
    err("raise String", "`String` is not an exception class");
    ok("i = 0\nwhile i < 3\n  i += 1\n  next if i == 1\n  break if i == 2\nend");
    err("break", "`break` outside of a loop or block");
    ok("loop do\n  break\nend");
    ok("def f -> Nothing\n  loop do\n    puts \"x\"\n  end\nend");
    ok("v = [1, \"a\"]\ncase v\nin [Int => n, String => s] then puts n + s.size\nelse puts \"other\"\nend");
    ok("a, b = 1, 2\nputs a + b");
    ok("def pair -> [Int, String] = [1, \"a\"]\nn, s = pair\nputs n + s.size");
    ok("xs = [1, 2, 3]\nfirst, *rest = xs\nputs first + rest.size");
    ok("x = 5\nputs \"big\" if x > 3");
    ok("s = \"a\"\nmsg = \"value: #{s} #{1 + 2}\"\nputs msg");
}
