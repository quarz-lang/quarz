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

fn warns(src: &str, expected: &str) {
    let prelude = parse(PRELUDE_SOURCE);
    let base = unit_base(0);
    let parsed = parse_with_bases(src, base, base);
    let (_, diags) = check(&prelude.program, &parsed.program);
    let warnings: Vec<String> = diags
        .into_iter()
        .filter(|(file, d)| *file == 1 && !d.is_error())
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        warnings.iter().any(|w| w.contains(expected)),
        "expected a warning containing {expected:?} for {src:?}, got:\n{}",
        warnings.join("\n")
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
fn definite_initialization() {
    // Every path assigns a required field.
    ok("class C\n  var @x: Float\n  def initialize(n: Int)\n    if n > 0\n      @x = 1.0\n    else\n      @x = 2.0\n    end\n  end\nend\nC.new(1)");
    err(
        "class C\n  var @x: Float\n  def initialize(n: Int)\n    if n > 0\n      @x = 1.0\n    end\n  end\nend",
        "field `@x` is not assigned on every path through `initialize`",
    );
    err(
        "class C\n  var @x: Float\n  def initialize(n: Int)\n    while n > 0\n      @x = 1.0\n    end\n  end\nend",
        "field `@x` is not assigned on every path",
    );
    err(
        "class C\n  var @x: Float\n  def initialize(n: Int)\n    return if n > 0\n    @x = 1.0\n  end\nend",
        "field `@x` is not assigned when `initialize` returns",
    );
    // Raising before the assignment is fine: no object comes out.
    ok("class C\n  @x: Int\n  def initialize(n: Int)\n    raise ArgumentError, \"neg\" if n < 0\n    @x = n\n  end\nend\nC.new(1)");
    ok("class C\n  @x: Int\n  def initialize(n: Int)\n    @x = begin\n      n * 2\n    rescue\n      0\n    end\n  end\nend\nC.new(1)");
    // Nilable fields, and fields with defaults, are not required.
    ok("class C\n  var @x: Float?\n  var @y: Int = 0\nend\nC.new");
    // The object is not used before its fields are assigned.
    err(
        "class C\n  var @x: Float\n  def initialize\n    show\n    @x = 1.0\n  end\n  def show -> Nil = p(@x)\nend",
        "the object is used before field `@x` is assigned",
    );
    err(
        "class C\n  var @x: Float\n  def initialize\n    p self\n    @x = 1.0\n  end\nend",
        "the object is used before field `@x` is assigned",
    );
    err(
        "class C\n  var @x: Int\n  var @y: Int\n  def initialize\n    @x = @y\n    @y = 1\n  end\nend",
        "field `@y` is read before it is assigned",
    );
    err(
        "class C\n  var @x: Int\n  def initialize(xs: Array[Int])\n    xs.each { |v| show }\n    @x = 1\n  end\n  def show -> Nil = nil\nend",
        "the object is used before field `@x` is assigned",
    );
    ok("class C\n  var @xs: Array[Int]\n  def initialize(ys: Array[Int])\n    puts \"making\"\n    @xs = ys.map { |y| y * 2 }\n    show\n  end\n  def show -> Nil = p(@xs)\nend\nC.new([1])");
    // A subclass assigns its own fields before `super`.
    ok("class A\n  @a: Int\n  def initialize(@a: Int); end\nend\nclass B < A\n  @b: Int\n  def initialize(@b: Int)\n    super(@b)\n  end\nend\nB.new(1)");
    err(
        "class A\n  @a: Int\n  def initialize(@a: Int); end\nend\nclass B < A\n  @b: Int\n  def initialize(b: Int)\n    super(b)\n    @b = b\n  end\nend",
        "field `@b` must be assigned before `super`",
    );
    err(
        "class A\n  @a: Int\n  def initialize(@a: Int); end\nend\nclass B < A\n  @b: Int\nend",
        "field `@b` has no default and `B` has no `initialize` to assign it",
    );
    // Defaults run before `initialize`.
    ok("class C\n  var @a: Float = 1.0\n  var @b: Float = @a + 1.0\nend\nC.new");
    err(
        "class C\n  var @a: Float = twice\n  var @b: Float\n  def initialize(@b: Float); end\n  def twice -> Float = @b * 2.0\nend",
        "the object is used before field `@a` is assigned",
    );
}

#[test]
fn classes_and_fields() {
    ok("class C\n  @x: Int\n  attr_reader :x\n  def initialize(@x: Int); end\nend\nputs C.new(1).x");
    err(
        "class C\n  @x: Int\n  def initialize\n  end\nend",
        "field `@x` is not assigned on every path through `initialize`",
    );
    err(
        "class C\n  @x: Int?\n  def initialize\n  end\nend",
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
fn protected_methods() {
    // As in Ruby: callable on another receiver only from an instance of
    // the class (or module) that defines it, or of a descendant.
    let account = "class Account\n  @balance: Int\n  def initialize(@balance: Int); end\n  def richer?(o: Account) -> Bool = balance > o.balance\n  protected def balance -> Int = @balance\nend\n";
    ok(&format!(
        "{account}puts Account.new(2).richer?(Account.new(1))"
    ));
    err(
        &format!("{account}puts Account.new(2).balance"),
        "`balance` is protected",
    );
    // `self.` and an implicit receiver are always allowed.
    ok("class A\n  def f -> Int = self.g + g\n  protected def g -> Int = 1\nend\nputs A.new.f");
    // A subclass may call it on an instance of the class, a sibling's
    // instance included; an unrelated class may not.
    ok(&format!("{account}class Savings < Account\n  def more?(o: Account) -> Bool = balance > o.balance\nend\nputs Savings.new(2).more?(Account.new(1))"));
    err(
        &format!("{account}class Bank\n  def peek(a: Account) -> Int = a.balance\nend\nputs Bank.new.peek(Account.new(1))"),
        "`balance` is protected",
    );
    // A class method's `self` is the class, not an instance.
    err(
        &format!("{account}class Audit < Account\n  def self.peek(a: Account) -> Int = a.balance\nend\nputs Audit.peek(Account.new(1))"),
        "`balance` is protected",
    );
    // Declared in a module: any instance of a class including it.
    ok("module Ranked\n  protected def rank -> Int = 1\n  def above?(o: Ranked) -> Bool = rank > o.rank\nend\nclass X\n  include Ranked\nend\nclass Y\n  include Ranked\nend\nputs X.new.above?(Y.new)");
    // The section form and the form naming methods.
    err(
        "class B\n  protected\n  def h -> Int = 1\nend\nputs B.new.h",
        "`h` is protected",
    );
    err(
        "class B\n  def h -> Int = 1\n  protected :h\nend\nputs B.new.h",
        "`h` is protected",
    );
}

#[test]
fn data_and_enum() {
    ok("data P = (x: Int, y: Int)\np = P.new(1, 2)\nq = p.with(y: 5)\nputs q.x + q.y\np => P(x:, y:)\nputs x");
    err(
        "data P = (x: Int)\nP.new(\"s\")",
        "expects Int but found String",
    );
    ok("data P(x: Int)\n  def double -> P = P.new(x * 2)\nend\nputs P.new(2).double.x");
    ok("enum E = A | B(v: Int)\ndef f(e: E) -> Int\n  case e\n  in E::A then 0\n  in E::B(v:) then v\n  end\nend\nputs f(E::A) + f(E::B.new(3))");
    err(
        "enum E = A | B\ndef f(e: E) -> Int\n  case e\n  in E::A then 1\n  end\nend",
        "does not cover: E::B",
    );
    ok("enum E\n  variant A, B\n  def flip -> E\n    case self\n    in A then B\n    in B then A\n    end\n  end\nend\nputs E::A.flip == E::B");
    ok("enum Shape\n  variant Circle(r: Float)\n  variant Rect(w: Float, h: Float)\n  include Comparable[Shape]\n  def area -> Float\n    case self\n    in Circle(r:) then 3.14 * r * r\n    in Rect(w:, h:) then w * h\n    end\n  end\n  def <=>(o: Shape) -> Int = area <=> o.area\nend\nputs [Shape::Circle.new(1.0), Shape::Rect.new(1.0, 2.0)].sort.first");
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
fn captured_self_in_task_blocks() {
    // `self` is captured like a variable: a mutable object cannot be.
    let counter = "class Counter\n  var @n: Int = 0\n  def bump -> Nil\n    @n += 1\n    nil\n  end\n  def run -> Int\n    BODY\n    @n\n  end\nend";
    for (body, msg) in [
        (
            "spawn { bump }.await",
            "calling `bump` uses `self`, which has the non-shareable type Counter",
        ),
        (
            "spawn { @n }.await",
            "`self` (for its instance variables) has the non-shareable type Counter",
        ),
        (
            "spawn { self }.await",
            "`self` has the non-shareable type Counter",
        ),
        (
            "Task.scope { |s| s.spawn { bump } }",
            "calling `bump` uses `self`",
        ),
        ("Task.blocking { @n }", "non-shareable type Counter"),
    ] {
        err(&counter.replace("BODY", body), msg);
    }
    // Immutable objects, `Kernel` methods, top-level methods and a
    // receiver set inside the task are fine.
    ok("class P\n  include Shareable\n  @x: Int\n  def initialize(@x: Int); end\n  def twice -> Int = @x * 2\n  def run -> Int = spawn { twice + @x + self.twice }.await\nend\nputs P.new(2).run");
    ok("class B\n  var @v: Int = 1\n  def run -> Int = spawn { puts \"hi\"; 5 }.await\n  def html -> String\n    spawn do\n      b = String::Builder.new\n      b.instance_exec { self << \"ok\" }\n      b.to_s\n    end.await\n  end\nend\nputs B.new.run");
    ok("def helper(x: Int) -> Int = x + 1\nputs spawn { helper(1) }.await");
    // The same failure through two candidates is reported once.
    let errs = diagnostics(&counter.replace("BODY", "Task.scope { |s| s.spawn { bump } }"));
    assert_eq!(errs[0].matches("calling `bump`").count(), 1, "{errs:?}");
}

#[test]
fn enumerators_stay_in_their_task() {
    // An enumerator has a position, and its receiver may be mutable.
    let counter = "class Counter\n  include Enumerable[Int]\n  var @n: Int = 0\n  def each(&: (Int) -> Nil) -> Nil\n    @n += 1\n    yield @n\n  end\nend\n";
    err(
        &format!("{counter}e = Counter.new.to_enum\nt = spawn {{ e.next }}"),
        "`e` has the non-shareable type Enumerator[Int]",
    );
    err(
        "c = Channel[Enumerator[Int]].new",
        "type argument Enumerator[Int] for `T` of `Channel` must be Shareable",
    );
    err("E = [1, 2].each", "constant `E` has the non-shareable type");
    ok("e = [1, 2].each\np e.next");
}

#[test]
fn shareable_is_promised_and_inherited() {
    let counter = "class Counter\n  var @n: Int = 0\nend\n";
    // A class is Shareable only when it (or an ancestor) includes
    // `Shareable`; then it and its subclasses must be, by their fields.
    err(
        "class Base\n  def name -> String = \"b\"\nend\ndef run(b: Base) -> Task[Base] = spawn { b }",
        "`b` has the non-shareable type Base",
    );
    ok("class Base\n  include Shareable\n  @x: Int = 1\nend\ndef run(b: Base) -> Task[Base] = spawn { b }");
    err(
        "class Base\n  include Shareable\nend\nclass Mut < Base\n  var @n: Int = 0\nend",
        "`Mut` must be Shareable, since `Base` includes `Shareable`, but its field `@n` is `var`",
    );
    err(
        &format!("{counter}class Holder\n  include Shareable\n  @c: Counter\n  def initialize(@c: Counter); end\nend"),
        "its field `@c` has the non-shareable type Counter",
    );
    // Exceptions cross tasks: `Exception` includes `Shareable`.
    err(
        "class Oops < RuntimeError\n  var @count: Int = 0\nend",
        "`Oops` must be Shareable, since `Exception` includes `Shareable`",
    );
    ok("class Oops < RuntimeError\n  @code: Int = 1\nend");
    // So do builtin Shareable classes.
    err(
        "class MyRange < Range[Int]\n  var @n: Int = 0\nend",
        "since `Range` includes `Shareable`",
    );
    // A module that includes `Shareable` holds its includers to it,
    // also through an extension.
    let marked = "module Marked\n  include Shareable\nend\n";
    err(
        &format!("{marked}class Counter\n  include Marked\n  var @n: Int = 0\nend"),
        "`Counter` must be Shareable, since `Marked` includes `Shareable`",
    );
    err(
        &format!(
            "{marked}module M\n  extension Array::Builder[Int]\n    include Marked\n  end\nend"
        ),
        "`Array::Builder` cannot include `Marked`, which is Shareable: it is Unshareable",
    );
    // An enum is Shareable when all its variants are.
    err(
        &format!("{counter}enum Holder\n  variant Some(c: Counter)\n  variant Empty\nend\ndef run(h: Holder) -> Task[Holder] = spawn {{ h }}"),
        "`h` has the non-shareable type Holder",
    );
    // A generic data type is Shareable with Shareable type arguments.
    ok("data Box[T] = (v: T)\nb = Box.new(1)\nt = spawn { b.v }\np t.await");
    ok("r: Result[Int, String] = Result::Ok.new(1)\np spawn { r }.await");
    err(
        &format!("{counter}data Box[T] = (v: T)\nb = Box.new(Counter.new)\nt = spawn {{ b }}"),
        "`b` has the non-shareable type Box[Counter]",
    );
}

#[test]
fn task_results_are_shareable() {
    // A task's result passes to the task that awaits it.
    let counter = "class Counter\n  var @n: Int = 0\nend\n";
    for body in [
        "t = spawn { Counter.new }",
        "Task.scope { |s| s.spawn { Counter.new } }",
        "x = Task.blocking { Counter.new }",
        "t = spawn { [Counter.new] }",
    ] {
        err(
            &format!("{counter}{body}"),
            "a task block returns the non-shareable type",
        );
    }
    ok("t = spawn { [1, 2] }\np t.await");
    ok("t = spawn { puts \"hi\" }\nt.await");
    ok("x = Task.blocking { \"done\" }\nputs x");
}

#[test]
fn nil_results_and_lambda_annotations() {
    // A lambda's declared result is checked like a method's.
    err(
        "l = ->(x: Int) -> String { x }",
        "lambda returns Int but String was expected",
    );
    ok("l = ->(x: Int) -> Int | String { x }\nputs l.call(1)");
    ok("l = ->(x: Int) -> Nil { x }\nl.call(1)");
    // An exception caught as a union can be raised again.
    ok("begin\n  raise IOError, \"x\"\nrescue IOError, SystemCallError => e\n  raise e\nend");
    // `*values: T` is shown with its element type.
    err("xs = [1]\nxs.push(\"a\", \"b\", 3)", "push(*values: T)");
    err(
        "xs = [1]\nxs.push(\"a\", \"b\", 3)",
        "matches (String, String, Int)",
    );
    err("p [3, 1].sort_pairs", "`sort_pairs` is private");
}

#[test]
fn tuple_inference() {
    // Elements of different types make a tuple, with nothing expected.
    ok("pairs = [\"pear\", \"fig\"].map { |w| [w, w.size] }\np pairs.sort_by { |pr| pr[1] }\npairs.each { |w, n| puts w.upcase, n + 1 }");
    ok("t = [1, \"a\"]\nputs t[0] + 1, t[1].upcase");
    // The variable is an array narrowed to the tuple: it can be
    // reassigned an array, and a loop sees the array.
    ok("x = [1, \"a\"]\nx = x.push(2)\np x");
    err(
        "t = [1, \"a\"]\nwhile t.size < 3\n  y: Int = t[0]\n  t = t.push(3)\nend",
        "cannot assign Int | String to `y` of type Int",
    );
    // A common type still makes an array.
    ok("class A\n  def x -> Int = 1\nend\nclass B < A\nend\nitems = [A.new, B.new]\np items.map(&:x)");
    ok("enum S\n  variant C, D\nend\nxs = [S::C, S::D]\np xs.size");
    ok("xs = [1, 2]\nxs = xs.push(3)\np xs");
    // A tuple pattern of the right shape covers the tuple.
    ok("t: [Int, String] = [1, \"a\"]\ncase t\nin [a, b] then p a\nend");
    ok("u: [Int, String, Bool] = [1, \"x\", true]\ncase u\nin [a, *rest] then p rest\nend");
    // Uncovered values of an open element type are a run-time error; a
    // tuple of closed types must be covered.
    warns(
        "t: [Int, String] = [1, \"a\"]\ncase t\nin [Int => a, \"b\"] then p a\nend",
        "a NoMatchingPatternError is raised at run time",
    );
    err(
        "t: [Bool, Bool] = [true, false]\ncase t\nin [true, b] then p b\nend",
        "does not cover",
    );
    // Tuples of comparable elements are comparable, element by element.
    ok("xs = [[2, \"b\"], [1, \"z\"]]\np xs.sort, xs.max\np [[\"x\", 2]].sort_by { |pr| [pr[1], pr[0]] }");
    err(
        "class A\nend\nxs = [[1, A.new], [2, A.new]]\np xs.sort",
        "type bounds not satisfied",
    );
    // ... and with the comparison operators, as are arrays of one
    // comparable element type.
    ok("t = [1, \"b\"]\nu = [1, \"c\"]\np t < u, t <=> u, u >= t\np [1, 2] < [1, 3], [1].between?([0], [2])");
    err(
        "class A\nend\nt = [1, A.new]\np t < [1, A.new]",
        "cannot compare A with A using `<=>`",
    );
    err(
        "p [1, \"a\"] < [1]",
        "cannot compare [Int, String] with Array[Int] using `<`",
    );
}

#[test]
fn self_type_positions() {
    // `Self` where the method hands a value out is fine.
    ok("module M\n  def ok1(&: (Self) -> Nil) -> Self = self\n  def ok2 -> Array[Self] = [self]\n  def ok3(f: (Self) -> Int) -> Int = f.call(self)\n  def ok4 -> Self? = nil\nend");
    // Where the caller hands one in, a subclass would get its parent's.
    for src in [
        "module M\n  abstract def cmp(other: Self) -> Int\nend",
        "module M\n  def a(&: () -> Self) -> Nil = nil\nend",
        "module M\n  def b(x: Array[Self]) -> Nil = nil\nend",
        "class C\n  def c(f: ((Self) -> Int) -> Int) -> Int = 0\nend",
    ] {
        err(
            src,
            "`Self` cannot be the type of a value the caller passes in",
        );
    }
    // The name is reserved.
    err("class Self\nend", "`Self` is reserved");
    err("Self = 1", "`Self` is reserved");
    err("class C\n  data Self = (x: Int)\nend", "`Self` is reserved");
}

#[test]
fn class_methods_and_self() {
    // `Self` in a class method is an instance of the receiving class.
    ok("class S\n  def self.build -> Self = new\nend\nclass C < S\n  def area -> Int = 1\nend\nputs C.build.area");
    // A body can return as `Self` only what is one: `self`, a call on it
    // that returns `Self`, `new` on a class method's receiver.
    ok("class S\n  def me -> Self = self\n  def twin -> Self = dup\n  def t -> Self = tap { |x| x }\n  def self.make -> Self = new\n  def self.again -> Self = make\nend");
    err(
        "class S\n  def copy -> Self = S.new\nend",
        "returns Self but its body has type S",
    );
    err(
        "class S\n  def self.make -> Self = S.new\nend",
        "returns Self but its body has type S",
    );
    // A subclass that inherits a class method calling `new` must take its
    // arguments, or override the method.
    err(
        "class S\n  def self.build -> Self = new\nend\nclass C < S\n  @r: Float\n  def initialize(@r: Float); end\nend",
        "`C#initialize` does not take the arguments of `new` in `S.build`",
    );
    ok("class S\n  def self.build -> Self = new\nend\nclass C < S\n  @r: Float\n  def initialize(@r: Float); end\n  def self.build -> Self = new(1.0)\nend");
    ok("class S\n  @n: Int\n  def initialize(@n: Int); end\n  def self.one -> Self = new(1)\nend\nclass C < S\n  @m: Int = 0\n  def initialize(@n: Int, @m: Int = 2); end\nend");
}

#[test]
fn not_on_unions() {
    let defs = "class Cond\n  def !() -> String = \"c\"\nend\nclass Flag\n  def !() -> String = \"f\"\nend\n";
    ok(&format!(
        "{defs}def f(x: Cond | Flag) -> String = !x\nputs f(Cond.new)"
    ));
    ok(&format!("{defs}def f(x: Int | Nil) -> Bool = !x"));
    ok(&format!(
        "{defs}def f(u: Cond | Nil) -> String = u.nil? ? \"nil\" : !u"
    ));
    // Where only some members define `!`, each value uses its member's.
    ok(&format!("{defs}def f(u: Cond | Nil) -> String | Bool = !u"));
    ok(&format!(
        "{defs}def f(u: Cond | Nil)\n  if !u then 1 else 2 end\nend"
    ));
    err(
        &format!("{defs}def f(u: Cond | Nil) -> String = !u"),
        "returns String but its body has type Bool | String",
    );
}

#[test]
fn logical_operator_methods() {
    let defs = "class Cond\n  def &&(&rhs: () -> Cond) -> String = \"and\"\n  def ||(&rhs: () -> Cond) -> String = \"or\"\nend\n";
    // On a type that defines it, `a && b` is the call `a.&&() { b }`.
    ok(&format!("{defs}def f(c: Cond) -> String = c && Cond.new"));
    ok(&format!("{defs}def f(c: Cond) -> String = c or Cond.new"));
    ok(&format!("{defs}def f(c: Cond) -> String = c.&&() {{ c }}"));
    err(
        &format!("{defs}def f(c: Cond) -> String = c && 1"),
        "block returns Int but Cond was expected",
    );
    // On a union, Bool or Nil it is the built-in operator.
    ok(&format!(
        "{defs}def f(c: Cond?) -> Int? = c && 1
def g(b: Bool) -> Bool = b && !b"
    ));
    // The method takes the right operand as its only, parameterless block.
    for src in [
        "class C\n  def &&(x: Int) -> Int = x\nend",
        "class C\n  def ||(&b: (Int) -> Int) -> Int = 0\nend",
        "class C\n  def &&(x: Int, &b: () -> Int) -> Int = 0\nend",
    ] {
        err(src, "takes only a block with no parameters");
    }
    err(
        "extension Bool\n  def &&(&b: () -> Bool) -> Bool = true\nend",
        "cannot be defined on Bool or Nil",
    );
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
        "cannot assign to `total` from a task block",
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
    ok("data P = (x: Int)\np = P.new(1)\nspawn { p.x }.await");
}

#[test]
fn shareable_procedures() {
    let run = "def run(&h: shareable () -> Nil) -> Nil\n  spawn { h.call }.await\nend\n";
    // A block or lambda where one is expected captures by value, like a
    // `spawn` block: Shareable values, no assignment.
    ok(&format!("{run}x = 1\nrun {{ puts x }}"));
    ok(&format!(
        "{run}f: shareable (Int) -> Int = ->(n: Int) {{ n + 1 }}\nspawn {{ f.call(1) }}"
    ));
    ok(&format!(
        "{run}def opt(f: (shareable () -> Nil)? = nil) = f\nopt(f: ->() {{ puts 1 }})"
    ));
    err(
        &format!("{run}n = 0\nrun {{ n += 1 }}"),
        "cannot assign to `n` from a shareable procedure",
    );
    err(
        &format!("{run}b = Array::Builder[Int].new\nrun {{ b << 1 }}"),
        "cannot be captured by a shareable procedure",
    );
    // A shareable procedure is a procedure, not the reverse; only a
    // shareable one crosses to a task.
    ok("f: shareable () -> Int = ->() { 1 }\ng: () -> Int = f");
    err(
        "g = ->() { 1 }\nf: shareable () -> Int = g",
        "cannot assign () -> Int to `f` of type shareable () -> Int",
    );
    err(
        "g = ->() { 1 }\nspawn { g.call }",
        "non-shareable type () -> Int",
    );
}

#[test]
fn narrowing_after_while() {
    // The loop ends with its condition false: `w` is not nil after it.
    ok("def f -> Int\n  w: Int? = nil\n  i = 0\n  while w.nil?\n    i += 1\n    w = i if i > 2\n  end\n  w\nend");
    // Unless a `break` can leave it first.
    err(
        "def f(n: Int) -> Int\n  w: Int? = nil\n  i = 0\n  while w.nil?\n    i += 1\n    break if i > n\n    w = i if i > 2\n  end\n  w\nend",
        "returns Int but its body has type Int?",
    );
}

#[test]
fn control_flow() {
    ok("x = if true then 1 else 2 end\nputs x + 1");
    ok("def f(b: Bool) -> Int | String\n  if b then 1 else \"s\" end\nend");
    ok("def f(n: Int) -> String\n  case n\n  when 1 then \"one\"\n  when 2, 3 then \"few\"\n  else \"many\"\n  end\nend");
    ok("begin\n  raise ArgumentError, \"x\"\nrescue ArgumentError => e\n  puts e.message\nensure\n  puts \"done\"\nend");
    err("raise 1", "cannot raise Int");
    err("raise String", "`String` is not an exception class");
    ok("begin\n  raise \"x\"\nrescue ArgumentError\n  raise\nend");
    ok("begin\n  raise \"x\"\nrescue => e\n  [1].each { |x| raise }\nend");
    err("raise", "a bare `raise` re-raises only inside `rescue`");
    err(
        "def f\n  raise\nend",
        "a bare `raise` re-raises only inside `rescue`",
    );
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

#[test]
fn module_contracts() {
    // A concrete class must implement the abstract methods it includes.
    err(
        "module M\n  abstract def zero -> Int\nend\nclass A\n  include M\nend",
        "`A` must implement `zero` (abstract in `M`)",
    );
    ok("module M\n  abstract def zero -> Int\nend\nclass A\n  include M\n  def zero -> Int = 0\nend\nputs A.new.zero");
    // ... unless it is abstract itself; its concrete subclasses must.
    ok("module M\n  abstract def zero -> Int\nend\nabstract class A\n  include M\nend\nclass B < A\n  def zero -> Int = 0\nend\nputs B.new.zero");
    err(
        "module M\n  abstract def zero -> Int\nend\nabstract class A\n  include M\nend\nclass B < A\nend",
        "`B` must implement `zero`",
    );
    // Data types and variants too.
    err(
        "module M\n  abstract def zero -> Int\nend\ndata P(x: Int)\n  include M\nend",
        "`P` must implement `zero`",
    );
    // An extension can supply the implementation.
    ok("module M\n  abstract def zero -> Int\nend\nclass A\n  include M\nend\nextension A\n  def zero -> Int = 0\nend\nputs A.new.zero");
    // `extend`: the module's abstract methods are class-side contracts.
    err(
        "module M\n  abstract def zero -> Int\n  def one -> Int = zero + 1\nend\nclass A\n  extend M\nend",
        "`A` must implement `self.zero` (abstract in the extended module `M`)",
    );
    ok("module M\n  abstract def zero -> Int\n  def one -> Int = zero + 1\nend\nclass A\n  extend M\n  def self.zero -> Int = 5\nend\nputs A.one");
    // Including a namespace adds nothing.
    warns(
        "module NS\n  def self.f -> Int = 1\nend\nclass A\n  include NS\nend",
        "`NS` has no instance methods, so including it adds nothing",
    );
    warns(
        "module NS\n  X = 1\nend\nclass A\n  extend NS\nend",
        "extending it adds nothing",
    );
    // Marker modules are fine.
    ok("module Marker\nend\nclass A\n  include Marker\nend\nputs 1");
}

#[test]
fn deinitialize_declarations() {
    ok("class R\n  def deinitialize\n    puts 1\n  end\nend");
    ok("module Cleanup\n  def deinitialize -> Nil = nil\nend\nclass R\n  include Cleanup\nend");
    err(
        "class R\n  def deinitialize(x: Int) = nil\nend",
        "`deinitialize` takes no parameters",
    );
    err(
        "data D(x: Int)\n  def deinitialize = nil\nend",
        "`deinitialize` can only be defined in a class or module",
    );
    err(
        "extension String\n  def deinitialize = nil\nend",
        "`deinitialize` can only be defined in a class or module",
    );
}

/// The top-level variables of `src` whose release may be observed.
fn lexical_vars(src: &str) -> Vec<u32> {
    let prelude = parse(PRELUDE_SOURCE);
    let base = unit_base(0);
    let parsed = parse_with_bases(src, base, base);
    let (checked, diags) = check(&prelude.program, &parsed.program);
    assert!(
        diags.iter().all(|(_, d)| !d.is_error()),
        "errors for {src:?}"
    );
    let out = checked.expect("checked").output;
    let mut slots: Vec<u32> = out
        .lexical_slots
        .iter()
        .filter(|(owner, _)| *owner == quarz_types::SelfOwner::Unit(1))
        .map(|(_, s)| *s)
        .collect();
    slots.sort_unstable();
    slots
}

#[test]
fn lexical_lifetimes_by_type() {
    // Values, collections of values and data of values are released at
    // their last use; objects (any class: a subclass may hold a socket or
    // define `deinitialize`), procedures, and what holds them, at the end
    // of the scope.
    assert_eq!(
        lexical_vars(
            "data P = (x: Int)\ndata Q = (o: Object)\n\
             a = 1\ns = \"x\"\nxs = [1]\np = P.new(1)\n\
             o = Object.new\nf = ->() { 1 }\nos = [Object.new]\nq = Q.new(Object.new)\nh = {a: f}"
        ),
        vec![4, 5, 6, 7, 8]
    );
    // A recursive data type holding nothing observable is not.
    assert_eq!(
        lexical_vars(
            "data Node = (rest: Node?, v: Int)\nn = Node.new(nil, 1)\n\
             enum T = Leaf(v: Int) | Two(l: T, r: T)\nt = T::Leaf.new(1)\n\
             enum U = Hold(o: Object) | Both(l: U, r: U)\nu = U::Hold.new(Object.new)"
        ),
        vec![2]
    );
}
