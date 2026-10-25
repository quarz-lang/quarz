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

fn no_warnings(src: &str) {
    let prelude = parse(PRELUDE_SOURCE);
    let base = unit_base(0);
    let parsed = parse_with_bases(src, base, base);
    let (_, diags) = check(&prelude.program, &parsed.program);
    let diags: Vec<String> = diags
        .into_iter()
        .filter(|(file, _)| *file == 1)
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        diags.is_empty(),
        "unexpected diagnostics for {src:?}:\n{}",
        diags.join("\n")
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

/// An error containing `expected`, reported on line `line` (1-based).
fn err_at(src: &str, expected: &str, line: usize) {
    let prelude = parse(PRELUDE_SOURCE);
    let base = unit_base(0);
    let parsed = parse_with_bases(src, base, base);
    let (_, diags) = check(&prelude.program, &parsed.program);
    let lines: Vec<usize> = diags
        .iter()
        .filter(|(file, d)| *file == 1 && d.is_error() && d.message.contains(expected))
        .map(|(_, d)| src[..(d.span.start - base) as usize].matches('\n').count() + 1)
        .collect();
    assert_eq!(lines, vec![line], "{expected:?} for {src:?}");
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
    ok("abstract class A\n  abstract def f -> Int\n  def g -> Int = f + 1\nend\nclass B < A\n  def f -> Int = 1\nend\nputs B.new.g");
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
            "Task.spawn { bump }.await",
            "calling `bump` uses `self`, which has the non-shareable type Counter",
        ),
        (
            "Task.spawn { @n }.await",
            "`self` (for its instance variables) has the non-shareable type Counter",
        ),
        (
            "Task.spawn { self }.await",
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
    ok("class P\n  include Shareable\n  @x: Int\n  def initialize(@x: Int); end\n  def twice -> Int = @x * 2\n  def run -> Int = Task.spawn { twice + @x + self.twice }.await\nend\nputs P.new(2).run");
    ok("class B\n  var @v: Int = 1\n  def run -> Int = Task.spawn { puts \"hi\"; 5 }.await\n  def html -> String\n    Task.spawn do\n      b = String::Builder.new\n      b.instance_exec { self << \"ok\" }\n      b.to_s\n    end.await\n  end\nend\nputs B.new.run");
    ok("def helper(x: Int) -> Int = x + 1\nputs Task.spawn { helper(1) }.await");
    // The same failure through two candidates is reported once.
    let errs = diagnostics(&counter.replace("BODY", "Task.scope { |s| s.spawn { bump } }"));
    assert_eq!(errs[0].matches("calling `bump`").count(), 1, "{errs:?}");
}

#[test]
fn enumerators_stay_in_their_task() {
    // An enumerator has a position, and its receiver may be mutable.
    let counter = "class Counter\n  include Enumerable[Int]\n  var @n: Int = 0\n  def each(&: (Int) -> Nil) -> Nil\n    @n += 1\n    yield @n\n  end\nend\n";
    err(
        &format!("{counter}e = Counter.new.to_enum\nt = Task.spawn {{ e.next }}"),
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
        "class Base\n  def name -> String = \"b\"\nend\ndef run(b: Base) -> Task[Base] = Task.spawn { b }",
        "`b` has the non-shareable type Base",
    );
    ok("class Base\n  include Shareable\n  @x: Int = 1\nend\ndef run(b: Base) -> Task[Base] = Task.spawn { b }");
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
    // Built-in value classes have no subclasses.
    err(
        "class MyRange < Range[Int]\n  var @n: Int = 0\nend",
        "cannot inherit from the built-in class `Range`",
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
        &format!("{counter}enum Holder\n  variant Some(c: Counter)\n  variant Empty\nend\ndef run(h: Holder) -> Task[Holder] = Task.spawn {{ h }}"),
        "`h` has the non-shareable type Holder",
    );
    // A generic data type is Shareable with Shareable type arguments.
    ok("data Box[T] = (v: T)\nb = Box.new(1)\nt = Task.spawn { b.v }\np t.await");
    ok("r: Result[Int, String] = Result::Ok.new(1)\np Task.spawn { r }.await");
    err(
        &format!("{counter}data Box[T] = (v: T)\nb = Box.new(Counter.new)\nt = Task.spawn {{ b }}"),
        "`b` has the non-shareable type Box[Counter]",
    );
}

#[test]
fn task_results_are_shareable() {
    // A task's result passes to the task that awaits it.
    let counter = "class Counter\n  var @n: Int = 0\nend\n";
    for body in [
        "t = Task.spawn { Counter.new }",
        "Task.scope { |s| s.spawn { Counter.new } }",
        "x = Task.blocking { Counter.new }",
        "t = Task.spawn { [Counter.new] }",
    ] {
        err(
            &format!("{counter}{body}"),
            "a task block returns the non-shareable type",
        );
    }
    ok("t = Task.spawn { [1, 2] }\np t.await");
    ok("t = Task.spawn { puts \"hi\" }\nt.await");
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
    // `*keys: K` is shown with its element type.
    err("h = {1 => 2}\nh.values_at(\"a\", 3)", "values_at(*keys: K)");
    // Pushing other types widens the element type.
    ok("xs = [1]\nys: Array[Int | String] = xs.push(\"a\", \"b\", 3)");
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
    ok("t = Task.spawn { 1 + 1 }\nputs t.await");
    ok("x = 1\nt = Task.spawn { x + 1 }\nputs t.await");
    err(
        "b = Array::Builder[Int].new\nTask.spawn { b << 1 }",
        "non-shareable type Array::Builder[Int]",
    );
    err(
        "total = 0\nTask.spawn { total += 1 }",
        "cannot assign to `total` from a task block",
    );
    ok("n = Atom.new(0)\nTask.spawn { n.update { |v| v + 1 } }.await\nputs n.value");
    err("Channel[Array::Builder[Int]].new", "must be Shareable");
    err("B = Array::Builder[Int].new", "non-shareable type");
    ok("ch = Channel[Int].new\nTask.scope do |scope|\n  scope.spawn { ch.send(1) }\n  puts ch.receive\nend");
    ok("class Counter\n  var @n: Int = 0\n  def bump -> Nil\n    @n += 1\n  end\nend\nc = Counter.new\nc.bump");
    err(
        "class Counter\n  var @n: Int = 0\nend\nc = Counter.new\nTask.spawn { c }",
        "non-shareable type Counter",
    );
    ok("data P = (x: Int)\np = P.new(1)\nTask.spawn { p.x }.await");
}

#[test]
fn shareable_procedures() {
    let run = "def run(&h: shareable () -> Nil) -> Nil\n  Task.spawn { h.call }.await\nend\n";
    // A block or lambda where one is expected captures by value, like a
    // `spawn` block: Shareable values, no assignment.
    ok(&format!("{run}x = 1\nrun {{ puts x }}"));
    ok(&format!(
        "{run}f: shareable (Int) -> Int = ->(n: Int) {{ n + 1 }}\nTask.spawn {{ f.call(1) }}"
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
        "g = ->() { 1 }\nTask.spawn { g.call }",
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

#[test]
fn reraise_block_params_narrowing() {
    ok("begin\n  raise \"x\"\nrescue ArgumentError\n  raise\nend");
    ok("begin\n  raise \"x\"\nrescue => e\n  [1].each { |x| raise }\nend");
    err("raise", "a bare `raise` re-raises only inside `rescue`");
    err(
        "class A\n  private def f -> Int = 1\nend\np [A.new].map(&:f)",
        "`f` is private for A: `&:f` calls only public methods",
    );
    err(
        "class A\n  protected def f -> Int = 1\n  def g(xs: Array[A]) -> Array[Int] = xs.map(&:f)\nend",
        "`f` is protected for A: `&:f` calls only public methods",
    );
    err("[1].each(&:puts)", "`puts` is private");
    err("1.puts", "`puts` is private");
    warns(
        "xs = [1]\nxs.push(2)\np xs",
        "the result of `push` is discarded; Array is immutable",
    );
    warns(
        "xs = [1]\n[2].each { |x| xs.push(x) }",
        "assign it (`xs = xs.push(...)`, or `xs.push!(...)`)",
    );
    warns(
        "s = \"a\"\ns.upcase\np s",
        "assign it (`s = s.upcase`, or `s.upcase!`)",
    );
    no_warnings("xs = [1]\nxs.push!(2)\nys = xs.push(3)\nxs.each { |x| p x }\np ys");
    err(
        "class B[out T]\n  def put(x: T) -> Nil = nil\nend",
        "`T` appears in a parameter position of `put`, against its variance in B",
    );
    err(
        "class B[in T]\n  def get -> T = raise \"x\"\nend",
        "`T` appears in a result position of `get`",
    );
    err(
        "class B[out T]\n  var @x: T\n  def initialize(@x: T)\n  end\nend",
        "`T` appears in the `var` field `@x`",
    );
    ok("class B[out T]\n  def each(&: (T) -> Nil) -> Nil = nil\n  def with[U >: T](x: U) -> Array[U] = [x]\n  private def keep(x: T) -> Nil = nil\nend");
    err(
        "class K[U >: Int]\nend",
        "only a method's type parameters take a lower bound",
    );
    ok("xs = [1]\nys: Array[Int | String] = xs.push(\"a\")\nzs: Array[Int?] = xs + [nil]");
    err(
        "arr = [1]\narr << 2",
        "Array is immutable: write `arr = arr.push(value)`, or build it with `Array::Builder`",
    );
    err("h = {1 => 2}\nh[3] = 4", "write `h = h.put(key, value)`");
    ok("enum C = A | B(x: Int)\ndef f(c: C) -> Int\n  c == C::A ? 0 : c.x\nend");
    ok("enum C = A | B(x: Int)\ndef f(c: C) -> Int\n  return 0 unless c != C::A\n  c.x\nend");
    ok("def f(b: Bool?) -> Bool\n  b == true ? b : false\nend");
    err(
        "def f(b: Bool?) -> Bool\n  b != true ? b : false\nend",
        "Bool?",
    );
    ok("def f(&b: ((Int) -> Nil)?) -> Nil\n  b&.call(1)\nend\nf\nf { |x| p x }");
    err(
        "def f(&b: ((Int) -> Nil)?) -> Nil\n  yield 1\nend",
        "`yield` cannot run an optional block",
    );
    err("def f(&b: ((Int) -> Nil)?) -> Nil\n  b.call(1)\nend", "Nil");
    err(
        "def f(&b: (Int) -> Nil) -> Nil\n  b.call(1)\nend\nf",
        "requires a block",
    );
    err(
        "[1].each { |x: String| puts x }",
        "block parameter `x` is annotated String but receives Int",
    );
    err(
        "def f\n  raise\nend",
        "a bare `raise` re-raises only inside `rescue`",
    );
}

#[test]
fn namespaces_are_added_to_not_reopened() {
    err(
        "module M\nend\nmodule M\nend",
        "`M` is already defined; modules cannot be reopened (to add to it from elsewhere, declare `class M::Name` or `module M::Name`)",
    );
    err(
        "class C\nend\nclass C\nend",
        "classes cannot be reopened (use `extension`)",
    );
    ok("module Geo\n  class Point\n  end\nend\nclass Geo::Line\n  @a: Point\n  def initialize(@a: Point); end\nend\nmodule Geo::Util\n  def self.f -> Point = Point.new\nend\np Geo::Line.new(Geo::Util.f)");
    // Declarations are hoisted: a qualified one may come before its
    // namespace.
    ok("class Geo::Line\n  def f -> Point = Point.new\nend\nmodule Geo\n  class Point\n  end\nend\np Geo::Line.new.f");
    ok("class A::B::C\nend\nmodule A\n  module B\n  end\nend\np A::B::C.new");
    err("class Nope::X\nend", "unknown namespace `Nope`");
    // Deferred ones wait for one another, collected in passes; a second
    // declaration is the one reported.
    ok("class M::A::X::B::C\nend\nclass M::A\nend\nmodule M::A::X::B\nend\nmodule M::A::X\nend\nmodule M\nend\np M::A::X::B::C.new");
    err_at(
        "class Geo::Line\nend\nmodule Geo\nend\nclass Geo::Line\nend",
        "`Geo::Line` is already defined",
        5,
    );
    err_at(
        "class Geo::Inner::Line\nend\nmodule Geo::Inner\nend\nclass Geo::Inner::Line\nend\nmodule Geo\nend",
        "`Geo::Inner::Line` is already defined",
        5,
    );
    // A qualified declaration goes at a file's top level.
    err(
        "module A\nend\nmodule M\n  class A::B\n  end\nend",
        "a qualified name is declared at a file's top level",
    );
    err(
        "module M\n  class ::B\n  end\nend",
        "`::B` is declared inside another declaration: a qualified name is declared at a file's top level",
    );
    ok("module A\nend\nclass ::A::B\nend\np A::B");
    // Only to the program's own modules.
    err(
        "class Kernel::Foo\nend",
        "cannot declare in `Kernel`: it is built in",
    );
    err(
        "module Comparable::Foo\nend",
        "cannot declare in `Comparable`: it is built in",
    );
    // Only the first part is looked up outwards.
    err(
        "module B\nend\nmodule Geo\nend\nclass Geo::B::C\nend",
        "unknown namespace `B`",
    );
    // The hint names the module from a file's top level.
    err(
        "module Outer\n  module Inner\n  end\n  module Inner\n  end\nend",
        "declare `class Outer::Inner::Name` or `module Outer::Inner::Name`",
    );
    // Another kind of declaration under a taken name.
    err("module D\nend\ndata D = (x: Int)", "`D` is already defined");
    err("class C\nend\nmodule C\nend", "`C` is already defined");
    err(
        "module Comparable\nend",
        "`Comparable` is already defined; modules cannot be reopened",
    );
}

#[test]
fn variables_assigned_on_some_paths_may_be_nil() {
    // A variable a branch or a loop body declares is nil where it was not
    // assigned.
    err(
        "n = 3\nif n > 5\n  y = n\nend\nputs y + 1",
        "undefined method `+` for Nil",
    );
    err(
        "n = 3\nif n > 5\n  p 0\nelse\n  y = n\nend\nputs y + 1",
        "undefined method `+` for Nil",
    );
    err(
        "n = 0\nwhile n > 5\n  y = n\n  n += 1\nend\nputs y + 1",
        "undefined method `+` for Nil",
    );
    err(
        "n = 0\nunless n > 5\n  y = n\nend\nputs y.abs",
        "undefined method `abs` for Nil",
    );
    err(
        "def f -> Int\n  begin\n    y = 1\n  rescue\n    p 0\n  end\n  y\nend",
        "returns Int but its body has type Int?",
    );
    err(
        "n = 3\nif n > 5\n  y = 1\nelse\n  y.abs\nend",
        "undefined method `abs` for Nil",
    );
    ok("n = 3\nif n > 5\n  y = n\nelse\n  y = 0\nend\nputs y + 1");
    ok("n = 3\nif n > 5\n  y = n\nend\nputs y.to_s\nputs y + 1 if y");
    ok("n = 3\nif n > 5\n  y = n\nelse\n  raise \"no\"\nend\nputs y + 1");
    ok("def f -> Int\n  begin\n    y = 1\n  rescue\n    raise \"no\"\n  end\n  y\nend");
    ok("def f -> Int\n  begin\n    p 0\n  ensure\n    y = 1\n  end\n  y\nend");
    // A `begin ... end while` body runs once, unless it leaves early.
    ok("n = 0\nbegin\n  y = n\n  n += 1\nend while n < 3\nputs y + 1");
    err(
        "n = 0\nbegin\n  break if n > 1\n  y = n\n  n += 1\nend while n < 3\nputs y + 1",
        "undefined method `+` for Nil",
    );
    err(
        "n = 0\nbegin\n  y = 1 if n > 5\n  n += 1\nend while n < 3\np y + 1",
        "undefined method `+` for Nil",
    );
    // A `while true` is left by its breaks only: as they leave it.
    ok("def f(n: Int) -> Int\n  while true\n    y = n * 2\n    break if y > 0\n    n += 1\n  end\n  y + 1\nend");
    err(
        "def f(n: Int) -> Int\n  while true\n    break if n > 0\n    y = n\n  end\n  y + 1\nend",
        "undefined method `+` for Nil",
    );
    // `ensure` runs also when the body raised part way through, and what
    // it assigns holds after it.
    err("def f(s: String) -> Int\n  begin\n    v = Integer(s)\n  ensure\n    p v + 1\n  end\n  0\nend", "undefined method `+` for Nil");
    err(
        "y: Int? = nil\nbegin\n  y = 1\nensure\n  y = nil\nend\np y + 1",
        "undefined method `+` for Nil",
    );
    ok("y: Int? = nil\nbegin\n  p 0\nensure\n  y = 1\nend\np y + 1");
    // A pattern test binds its variables only when it matches.
    err(
        "def f(v: Int | String)\n  if v in Int => n\n    p 0\n  end\n  p n + 1\nend",
        "undefined method `+` for Nil",
    );
    err(
        "def f(v: Int | String)\n  ok = v in Int => n\n  p n + 1\nend",
        "undefined method `+` for Nil",
    );
    ok("def f(v: Int | String)\n  if v in Int => n\n    p n + 1\n  end\nend");
    // A `break` runs the `ensure` it leaves through.
    err("def f -> Int\n  x: Int? = nil\n  while true\n    begin\n      x = 1\n      break\n    ensure\n      x = nil\n    end\n  end\n  x + 1\nend", "undefined method `+` for Nil");
    // After `ensure`, as on the normal path.
    ok("def f(c: Bool) -> Int\n  begin\n    y = 1\n  ensure\n    y = 2 if c\n  end\n  y + 1\nend");
    ok("def f -> Int\n  x: Int? = nil\n  begin\n    x = 1\n  ensure\n    y = x\n  end\n  y || 0\nend");
    ok("def f -> Int\n  x = 0\n  while true\n    begin\n      x = 1\n      break\n    ensure\n      p 0\n    end\n  end\n  x + 1\nend");
    // Pattern bindings and `when` conditions assign too.
    err("def f(v: Int?) -> Int\n  n: Int? = 1\n  i = 0\n  while i < 2\n    p n + 1\n    v in n\n    i += 1\n  end\n  0\nend", "undefined method `+` for Nil");
    // Assignments inside hashes, ranges and index targets widen a loop's
    // variables too.
    err("def f -> Int\n  x: Int? = 1\n  i = 0\n  while i < 2\n    p x + 1 if i > 0\n    x = 1\n    h = {a: (x = nil)}\n    i += 1\n  end\n  0\nend", "undefined method `+` for Nil");
}

#[test]
fn breaks_inside_expressions_and_blocks() {
    // A `break` in an argument still leaves the loop.
    no_warnings("data V = (x: Int, y: Int)\ndef f(n: Int) -> Int\n  j = 0\n  o = V.new(0, 0)\n  while true\n    j += 1\n    o = V.new(j, j > n ? (break) : 0)\n  end\n  o.x\nend\np f(2)");
    no_warnings(
        "def f(n: Int) -> Int\n  loop do\n    p [n > 1 ? (break) : 0]\n  end\n  n\nend\np f(2)",
    );
    // A `break` in a block leaves the block, not the loop around it.
    warns(
        "def f -> Int\n  while true\n    [1].each { |x| break }\n  end\n  1\nend",
        "unreachable code",
    );
    warns(
        "def f -> Int\n  loop do\n    [1].each { |x| break }\n  end\n  1\nend",
        "unreachable code",
    );
    err(
        "def g(&b: (Int) -> Int) -> Int = b.(1)\ni = 0\nwhile i < 3\n  i += 1\n  g { |x| next \"a\" }\nend",
        "`next` has type String but the block returns Int",
    );
    // A lambda is left by `next`, and `break` does not leave it.
    err(
        "i = 0\nwhile i < 3\n  i += 1\n  f = ->(x: Int) -> Int { next \"a\" }\nend",
        "`next` has type String but the block returns Int",
    );
    err(
        "while true\n  f = ->(x: Int) -> Int { break }\nend",
        "`break` outside of a loop or block",
    );
    // A block's `break` gives the call its value.
    // `loop` also ends, with nil, at a StopIteration.
    err(
        "x = loop do\n  break 5\nend\np x + 1",
        "undefined method `+` for Nil",
    );
    ok("x = loop do\n  break 5\nend\np x + 1 if x");
    // A `break` in the block of a `foo!` call skips the store.
    // A `break` in the block of a `foo!` call gives the value stored.
    err(
        "xs = [1, 2, 3]\nxs.map! { |v| break \"s\" if v > 1; v }",
        "would assign Array[Int] | String",
    );
    // A real `foo!` assigns nothing: a loop keeps the narrowing.
    ok("def g(b: Array::Builder[Int]?)\n  if b\n    i = 0\n    while i < 2\n      b.map! { |v| v + 1 }\n      i += 1\n    end\n    p b.to_a\n  end\nend");
    err(
        "class A\n  def foo! -> Int = 1\nend\ndef f(x: A?)\n  x.foo!\nend",
        "undefined method `foo!` for Nil",
    );
    // On a union, the variable holds any member's result.
    err("class A\n  def foo -> Int = 1\nend\nclass B\n  def foo -> String = \"s\"\nend\ndef f(x: A | B | Int | String)\n  case x\n  when A, B\n    x.foo!.then! { |v| v }\n    p x.size\n  end\nend", "undefined method `size` for Int");
    err("class A\n  def foo -> Int = 1\nend\nclass B\n  def foo! -> String = \"b\"\n  def foo -> Int = 2\nend\ndef f(x: A | B | Int)\n  case x\n  when A, B\n    x.foo!\n  end\nend", "`foo!` is a method of some members of the union and `foo` of others");
    err("class A\n  def foo -> Int = 1\n  def bar -> Int = 2\nend\nclass C\n  @x: A | Int\n  def initialize\n    @x = A.new\n    @x.foo!\n    p @x.bar\n  end\nend", "undefined method `bar` for Int");
    err("class A\n  def foo -> Int = 1\nend\nclass B\n  def foo -> String = \"s\"\nend\ndef f(x: A | B | Int | String)\n  case x\n  when A, B\n    x.foo!\n    p x.size\n  end\nend", "undefined method `size` for Int");
    err(
        "z = [1, 2].map { |v| break \"s\" if v > 0; v }\np z.first",
        "undefined method `first`",
    );
}

#[test]
fn inference_never_binds_a_variable_to_itself() {
    // Found by a generated program: an inference variable bound to a
    // type containing itself made resolving overflow the stack.
    diagnostics("def f(n: Int, x: Array[Int], a: Int?, b: String?) -> Int\n  x.each do |b|\n    unless !c\n      while true\n      end\n      case b\n      in Int => m1\n      end\n      case c\n      in String => s1\n      end\n    end\n    case c\n    in Int => m1\n      begin\n      end\n      case f\n      in String => s1\n        b = b if !c\n      end\n    end\n  end\nend");
    // A type that would contain itself is not a solution.
    err(
        "def h(a: Array[Int]) -> Int\n  a[0] + 1\nend\narr = []\narr = [arr]\np(h(arr))",
        "array elements have type Array[?0] but ?0 was expected",
    );
}

#[test]
fn undecided_types_come_from_uses() {
    // An `if` whose value is unused, and nil joined with an undecided
    // type, do not decide an empty array's element type.
    ok("def f(c: Bool) -> Int\n  arr = []\n  b = arr[0] if c\n  arr = arr.push(5)\n  1\nend");
    ok("def g(c: Bool) -> Int\n  arr = []\n  x = c ? arr[0] : nil\n  arr = arr.push(7)\n  x ? x + 1 : 0\nend");
    err("def g(c: Bool) -> Int\n  arr = []\n  x = c ? arr[0] : nil\n  arr = arr.push(7)\n  x + 1\nend", "undefined method `+` for Nil");
    // A test narrows such a value inside its branch only.
    ok("def f(n: Int) -> Int\n  arr = []\n  r = 0\n  i = 0\n  while i < n\n    case arr[0]\n    in String => s\n      r = r + s.size\n    else\n    end\n    arr = arr.push(\"ab\")\n    i += 1\n  end\n  r\nend");
    ok("def f(c: Bool) -> Int\n  arr = []\n  b = arr[0]\n  if c\n    case b\n    in String => s1\n      p s1.size\n    else\n    end\n  end\n  b = b if c\n  arr = arr.push(5)\n  1\nend");
    // Not by a value or range pattern (`1 === 1.0`), nor to a generic
    // class's unknown arguments (but `Array[Object]`, covariant).
    err("def f -> Int\n  arr = []\n  r = 0\n  case arr[0]\n  in 1..5 => k\n    r = k << 1\n  else\n  end\n  arr = arr.push(2.5)\n  r\nend", "cannot call `<<` on a value whose type is not yet known");
    ok("def f -> Int\n  arr = []\n  r = 0\n  v = arr[0]\n  case v\n  when Array then r += v.size\n  end\n  arr = arr.push([1])\n  r\nend");
    // A narrowing from before `?v` was decided in a later branch does not
    // outlast the branches.
    ok("def takes(v: Int) -> Int = v\ndef f -> Int\n  arr = []\n  r = 0\n  x = arr[0]\n  if x.is_a?(String)\n    r += x.size\n  else\n    arr = arr.push(5)\n  end\n  takes(x)\nend");
    ok("def f(c: Bool, d: Bool) -> Int\n  arr = []\n  if c\n    p 1\n  elsif d\n    arr[0]\n  else\n    \"s\"\n  end\n  arr = arr.push(5)\n  1\nend");
    // A data pattern deconstructs it with unknown (Object) arguments; a
    // method every object has decides nothing.
    ok("data Pair[A, B] = (a: A, b: B)\ndef g -> Int\n  arr = []\n  r = 0\n  case arr[0]?\n  in Pair(a, b)\n    p a\n    r = 1\n  else\n  end\n  arr = arr.push(Pair.new(1, 2))\n  r\nend");
    ok("def f -> Int\n  arr = []\n  x = arr[0]?\n  p x.nil?, x.to_s\n  arr = arr.push(5)\n  1\nend");
    // Not a class whose Object arguments would accept wrong values.
    err("class Cell[T]\n  var @v: T\n  def initialize(v: T)\n    @v = v\n  end\n  def set(v: T) -> Nil\n    @v = v\n    nil\n  end\nend\ndef g -> Int\n  arr = []\n  b = arr[0]?\n  case b\n  in Cell(v:)\n    b.set(\"str\")\n  else\n  end\n  arr = arr.push(Cell.new(5))\n  1\nend", "cannot deconstruct a value whose type is not yet known");
    err("data H[A] = (f: (A) -> Int)\ndef g -> Int\n  arr = []\n  case arr[0]?\n  in H(f)\n    f.call(\"oops\")\n  else\n  end\n  arr = arr.push(H.new(->(x: Int) { x + 1 }))\n  1\nend", "cannot deconstruct a value whose type is not yet known");
    // Nor one with a bounded parameter; a recursive `data` is fine.
    err("module Comb\n  abstract def weight -> Int\nend\ndata Acc[T: Comb](x: T)\n  def plus(y: T) -> Int = x.weight + y.weight\nend\ndata C[A] = (d: Acc[A])\ndef g -> Int\n  arr = []\n  case arr[0]?\n  in C(d)\n    p d.plus(\"str\")\n  else\n  end\n  1\nend", "cannot deconstruct a value whose type is not yet known");
    err("module Comb\n  abstract def weight -> Int\nend\ndata Acc[T: Comb](x: T)\n  def plus(y: T) -> Int = x.weight + y.weight\nend\ndef g -> Int\n  arr = []\n  case arr[0]?\n  in Acc(x) => a\n    p a.plus(\"str\")\n  else\n  end\n  1\nend", "cannot deconstruct a value whose type is not yet known");
    ok("data Node[A] = (value: A, rest: Node[A]?)\ndef g -> Int\n  arr = []\n  case arr[0]?\n  in Node(value, rest)\n    p value, rest\n  else\n  end\n  arr = arr.push(Node.new(1, nil))\n  1\nend");
    // An empty block leaves no unused-statement mark behind.
    err("def f(c: Bool) -> Int\n  [1].each { |i| }\n  y = begin\n    if c then 3.5 else 2.5 end\n  end\n  (y || 7) * 2\nend", "returns Int but its body has type Float");
    // An unused `if` joins nothing; a `?v | Nil` passed as `T?` makes `?v` a `T`.
    ok("def f(c: Bool) -> Int\n  arr = []\n  if c\n    arr[0]\n  else\n    \"x\"\n  end\n  arr = arr.push(5)\n  1\nend");
    ok("def take(v: Int?) -> Int = v || 0\ndef f(c: Bool) -> Int\n  arr = []\n  x = c ? arr[0] : nil\n  take(x)\n  arr = arr.push(5)\n  arr[0] + 1\nend");
    warns(
        "def f(c: Bool) -> Int\n  if c\n    return 1\n  else\n    return 2\n  end\n  p 3\n  4\nend",
        "unreachable code",
    );
    ok("def f(c: Bool) -> Int\n  arr = []\n  b = arr[0]\n  if c\n    case b\n    in String => s1\n      p s1\n    else\n    end\n  end\n  b = b if c\n  arr = arr.push(5)\n  1\nend");
    no_warnings("arr = []\nb = arr[0]\nok = b in String\narr = arr.push(5)\np ok");
}

#[test]
fn tests_narrow_only_to_what_holds() {
    // `||` on an undecided type decides nothing; using the result does.
    ok("def f -> Int\n  arr = []\n  x = arr[0]? || \"s\"\n  arr = arr.push(5)\n  p x\n  (arr[0]? || 0) + 1\nend");
    // A generic class test without known arguments: an invariant one does
    // not narrow an Object (its setters would take anything).
    err("class Box[T]\n  var @v: T\n  def initialize(@v: T); end\n  def set(v: T) -> Nil\n    @v = v\n    nil\n  end\nend\ndef f(o: Object)\n  case o\n  in Box\n    o.set(\"str\")\n  else\n  end\nend", "undefined method `set` for Object");
    ok("def f(o: Object) -> Int\n  case o\n  in Array then o.size\n  else 0\n  end\nend");
    // A union of an undecided type with a decided `Pair` does not take the
    // decided one's arguments.
    err("data Pair[A, B] = (a: A, b: B)\ndef f -> Int\n  arr = []\n  y = [arr[0]?, Pair.new(1, \"s\")]\n  case y[0]\n  in Pair(a, b)\n    a << 1\n  else\n    0\n  end\nend", "undefined method `<<` for Object");
    // A number pattern matches equal numbers of the other classes.
    err(
        "def f(x: Int | Float) -> Int\n  case x\n  in 1 then x << 1\n  else 0\n  end\nend",
        "undefined method `<<` for Float",
    );
    // `== true` does not narrow a value whose `==` a class may define.
    err("class Weird\n  def ==(o: Object) -> Bool = true\nend\ndef f(x: Object) -> Bool\n  if x == true\n    x & true\n  else\n    false\n  end\nend", "undefined method `&` for Object");
    ok("def f(x: Int | Bool) -> Bool\n  if x == true\n    x & true\n  else\n    false\n  end\nend");
    // A field of type `Self` deconstructs to the value's own type.
    ok("data Node[A] = (v: A, nx: Self?)\nn = Node.new(1, Node.new(2, nil))\ncase n\nin Node(v, nx)\n  p nx.v if nx\nend");
    // A type parameter or a supertype the class test cannot narrow stays.
    err("class Box[T]\n  var @v: T\n  def initialize(@v: T); end\n  def set(v: T) -> Nil\n    @v = v\n    nil\n  end\nend\ndef poke[T](x: T) -> Nil\n  case x\n  in Box then x.set(\"str\")\n  else\n  end\n  nil\nend", "undefined method `set` for T");
    ok("def f(o: Object) -> Int\n  case o\n  when Hash then o.size\n  when Range then 1\n  else 0\n  end\nend");
    ok("def b[T](x: T) -> Int\n  case x\n  when Hash then x.size\n  when Set then x.size\n  else 0\n  end\nend");
    // Nor `== nil` a value whose class (or a subclass) defines `==`.
    err("class Weird\n  def ==(o: Object) -> Bool = true\nend\ndef f(x: Weird | Int) -> Int\n  if x == nil\n    n: Nil = x\n    1\n  else\n    0\n  end\nend", "cannot assign Weird | Int to `n` of type Nil");
    ok("class Plain\nend\ndef f(x: Plain?) -> Int\n  if x == nil\n    0\n  else\n    x.hash\n  end\nend");
    err("extension Nil\n  def ==(other: Object) -> Bool = false\nend\ndef g(x: Int?) -> Int\n  if x == nil\n    0\n  else\n    x + 1\n  end\nend", "undefined method `+` for Nil");
    err("class Foo\n  def !=(o: Object) -> Bool = false\nend\ndef takes(n: Nil) -> Int = 0\ndef f(x: Foo?) -> Int\n  if x != nil\n    1\n  else\n    takes(x)\n  end\nend", "expects Nil but found Foo?");
    ok("def tup(t: [Int, String]?) -> Int\n  if t == nil\n    0\n  else\n    t[0]\n  end\nend\ndef pr(f: ((Int) -> Int)?) -> Int\n  if f != nil\n    f.(1)\n  else\n    0\n  end\nend\ndef par[T](x: T?) -> T\n  if x == nil\n    raise \"none\"\n  else\n    x\n  end\nend");
    // `?v | Int` used by an operator or under a bound is an `Int`.
    ok("def g -> Int\n  arr = []\n  y = arr[0]? || 2\n  y += 1\n  xs = [y, 2].sort\n  arr = arr.push(4)\n  xs[0]\nend");
    // A bound may name the class's parameters.
    ok("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Num(n: Int)\n  include Addable[Num]\n  def add(o: Num) -> Num = Num.new(n + o.n)\nend\ndata Acc[T: Addable[T]](x: T)\n  def twice -> T = x.add(x)\nend\np Acc.new(Num.new(2)).twice");
}

#[test]
fn checks_the_types_it_cannot_take_on_trust() {
    // `as`/`is_a?` check the elements of built-in collections at run time,
    // and refuse type arguments they cannot check.
    ok("def obj(v: Object) -> Object = v\nxs = obj([1]).as?(Array[String])\np xs");
    err("class Box[T]\n  def initialize(@v: T); end\n  @v: T\nend\ndef f(o: Object) -> Box[Int] = o.as(Box[Int])", "cannot check at run time that a value of type Object is a Box[Int]");
    ok("class Box[T]\n  def initialize(@v: T); end\n  @v: T\nend\ndef f(o: Box[Int]?) -> Box[Int] = o.as(Box[Int])");
    err("class Box[T]\n  var @v: T\n  def initialize(@v: T); end\nend\ndef obj(v: Object) -> Object = v\nobj(Box.new(\"s\")).as(Box[Object])", "cannot check at run time that a value of type Object is a Box[Object]");
    err(
        "def f[T](y: Object) -> Int\n  y.is_a?(Array[T]) ? 1 : 0\nend",
        "cannot check at run time that a value of type Object is a Array[T]",
    );
    err(
        "def obj(v: Object) -> Object = v\ndef f[T](o: Object, z: T) -> T = o.as(T)",
        "cannot check at run time that a value of type Object is a T",
    );
    err("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Acc[T: Addable[T]] = (x: T)\ndef f[U](u: U) -> U = Acc[U].new(u).x", "type argument U for `T` of `Acc` must be Addable[U]");
    // Bounds are checked in annotations too.
    err("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Acc[T: Addable[T]] = (x: T)\nclass Other\nend\np Acc.new(Other.new)", "type argument Other for `T` of `Acc` must be Addable[Other]");
    err("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Acc[T: Addable[T]] = (x: T)\nclass Other\nend\nx: Acc[Other]? = nil", "type argument Other for `T` of `Acc` must be Addable[Other]");
    err("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Acc[T: Addable[T]] = (x: T)\nclass Other\nend\ndef f(a: Acc[Other]) -> Int = 0", "type argument Other for `T` of `Acc` must be Addable[Other]");
    // A `T` narrowed by a test is still a `T`.
    ok("def keep[T](x: T) -> T\n  if x.is_a?(String)\n    p x.upcase\n    return x\n  end\n  x\nend");
    ok("data Pair[A, B] = (a: A, b: B)\ndef f[T](x: T) -> T\n  case x\n  in Array then p x.size\n  in Pair(a, b) then p a\n  else\n  end\n  x\nend");
    // It does not leave the branch through inferred types.
    err("class Box[T]\n  def initialize(@v: T); end\n  @v: T\n  def s\n    @v.is_a?(String) ? @v : nil\n  end\n  def steal(b: Box[String]) -> T? = b.s\nend", "method `steal` returns T? but its body has type String?");
    ok("def f[T](x: T, z: T) -> Array[T]\n  ys = []\n  if x.is_a?(String)\n    ys = ys.push(x)\n  end\n  ys = ys.push(z)\n  ys\nend");
    ok("def f(t: [Int, String] | Array[Int]) -> Int = 1\np f([1, 2])");
    ok("def f[T](t: [Int, String] | T) -> Int = 1\np f([1, 2])");
    // A value of a module type has Object's methods.
    ok("module Named\n  def name -> String = \"n\"\nend\ndef md(x: Named?) -> String\n  if x == nil\n    \"nil\"\n  else\n    x.name + x.to_s\n  end\nend");
    // A tuple expected among other types.
    ok("def tup(t: [Int, String]?) -> Int = t ? t[0] : 0\np tup([1, \"a\"])");
}

#[test]
fn nil_p_and_is_a_are_sealed() {
    // Types are narrowed by them: a definition of its own would let a
    // value of another type through.
    err(
        "class Null\n  def nil? -> Bool = true\nend",
        "`nil?` cannot be redefined",
    );
    err(
        "class Any\n  def is_a?(c: Class) -> Bool = true\nend",
        "`is_a?` cannot be redefined",
    );
    err(
        "extension String\n  def nil? -> Bool = true\nend",
        "`nil?` cannot be redefined",
    );
    // Nor by an alias, nor as a data field's reader.
    err(
        "class Foo\n  def yes -> Bool = true\n  alias nil? yes\nend",
        "`nil?` cannot be redefined",
    );
    err("data P = (nil?: Bool)", "`nil?` cannot be redefined");
    // `&.nil?` may not call it: no narrowing.
    err(
        "x: Int? = nil\nif x&.nil?\n  p 0\nelse\n  p x + 1\nend",
        "undefined method `+` for Nil",
    );
}

#[test]
fn closures_that_may_run_later_end_narrowings() {
    // A lambda that assigns a local: any call may run it, so the local is
    // not narrowed after it is made.
    err(
        "def f(x: Int | String, z: Int | String) -> Int\n  reset = -> { x = z }\n  if x.is_a?(String)\n    reset.call\n    p x.upcase\n  end\n  0\nend",
        "undefined method `upcase` for Int",
    );
    err(
        "def g[T](x: T, z: T) -> Int\n  reset = -> { x = z }\n  if x.is_a?(Int)\n    reset.call\n    return x + 1\n  end\n  0\nend",
        "undefined method `+` for T",
    );
    // Implicit calls run it too (interpolation calls `to_s`).
    err(
        "class C\n  var @r: (() -> Nil)? = nil\n  def set(r: () -> Nil) -> Nil\n    @r = r\n    nil\n  end\n  def to_s -> String\n    if r = @r\n      r.call\n    end\n    \"c\"\n  end\nend\ndef f(x: Int | String, c: C) -> Int\n  c.set(-> { x = 5; nil })\n  x = \"s\"\n  if x.is_a?(String)\n    s = \"#{c}\"\n    p x.upcase\n  end\n  0\nend",
        "undefined method `upcase` for Int",
    );
    // A lambda made under a narrowing may run after the local changes.
    err(
        "def f(x: Int | String) -> Int\n  r = -> { 0 }\n  if x.is_a?(String)\n    r = -> { p x.upcase; 0 }\n  end\n  x = 5\n  r.call\nend",
        "undefined method `upcase` for Int",
    );
    // A lambda made later in a loop's body may have run by the next turn.
    err(
        "def f(x: Int | String) -> Int\n  r = -> { nil }\n  i = 0\n  while i < 2\n    if x.is_a?(String)\n      r.call\n      p x.upcase\n    end\n    r = -> { x = 5; nil }\n    i += 1\n  end\n  0\nend",
        "undefined method `upcase` for Int",
    );
    // A block given to a method that may keep it (a named `&blk`).
    err(
        "def f(x: Int | String) -> Int\n  if x.is_a?(String)\n    at_exit { p x.upcase; nil }\n  end\n  x = 5\n  0\nend",
        "undefined method `upcase` for Int",
    );
    // A local assigned once keeps its narrowing in a lambda; a block only
    // yielded to does not end narrowings; a block's own locals are new
    // each time it runs.
    ok("def g(s: String?) -> Int\n  x = s\n  if x\n    r = -> { x.size }\n    r.call + x.size\n  else\n    0\n  end\nend\np g(\"abc\")");
    ok("def f(xs: Array[Int]) -> Int\n  found: Int? = nil\n  xs.each { |x| found = x if x > 2 }\n  if found\n    puts found\n    found + 1\n  else\n    0\n  end\nend\np f([1, 5])");
    ok("def f(xs: Array[String?]) -> Int\n  r = -> { 0 }\n  xs.each do |e|\n    y = e\n    if y\n      r = -> { y.size }\n    end\n  end\n  r.call\nend");
    // A local first assigned in a lambda is its own, though the body
    // assigns the name later: narrowed inside and outside.
    ok("def f(c: Channel[Int]) -> Int\n  n = 0\n  l = -> do\n    r = c.try_receive\n    n += r if r\n    nil\n  end\n  l.call\n  r = c.try_receive\n  return 0 unless r\n  n + r\nend");
    // In a loop, before its calls are checked, any block counts as one
    // that may be kept; inside the block an assignment still narrows.
    err(
        "def f(xs: Array[Int]) -> Int\n  i = 0\n  while i < 2\n    last: Int? = nil\n    xs.each { |v| last = v }\n    p last + 1 if last\n    i += 1\n  end\n  0\nend",
        "undefined method `+` for Nil",
    );
    ok("x: String? = nil\n[\"foo\", \"bar\"].each do |i|\n  x = i\n  p x + \"123\"\nend");
    // A block's own locals are new each time it runs: the iterator idiom
    // works inside another block.
    ok("def f(xs: Array[String?]) -> Int\n  t = 0\n  [1].each do |_|\n    found: String? = nil\n    xs.each { |x| found = x if x }\n    if found\n      t += found.size\n    end\n  end\n  t\nend");
    // A closure made later in a block may change the block's own local
    // before a lambda that tested it runs.
    err(
        "def f(s: String) -> Int\n  t = 0\n  [1].each do |i|\n    y: String? = s\n    k = -> { 0 }\n    a = -> do\n      if y\n        k.call\n        y.size\n      else\n        0\n      end\n    end\n    k = -> { y = nil; 0 }\n    t += a.call\n  end\n  t\nend",
        "undefined method `size` for Nil",
    );
    // A block's own `y`, though the loop assigns another `y` after it.
    ok("def f(xs: Array[String?]) -> Int\n  i = 0\n  t = 0\n  while i < 2\n    xs.each do |v|\n      y = v\n      t += y.size if y\n    end\n    y = \"z\"\n    i += 1\n  end\n  t\nend");
}

#[test]
fn an_anonymous_block_is_not_kept() {
    // Only yielded to, or passed on to another anonymous one.
    err(
        "def keep(&blk: () -> Nil) -> Nil = nil\ndef fwd(&: () -> Nil) -> Nil = keep(&)",
        "cannot be passed to `keep`, which may keep it",
    );
    err(
        "def wrap(&: () -> Nil) -> (() -> Nil) = -> { yield }",
        "`yield` in a closure that may run later",
    );
    ok("def anon(&: () -> Nil) -> Nil = yield\ndef fwd(&: () -> Nil) -> Nil = anon(&)");
    // Whether a method keeps its block is part of its signature.
    err(
        "class A\n  def run(&: () -> Nil) -> Nil = yield\nend\nclass B < A\n  def run(&blk: () -> Nil) -> Nil = nil\nend",
        "`run` cannot keep its block",
    );
}

#[test]
fn array_literals_take_the_union_member_they_fit() {
    ok("def f(t: [Int, String] | Array[Int]) -> Int = 1\np f([1, \"a\"]), f([1, 2])");
    ok("def g(t: [Int, String] | [Int, Int]) -> Int = 1\np g([1, 2]), g([1, \"x\"])");
    err(
        "def h(t: [Int, String] | [Int, Int]) -> Int = 1\np h([1, 2.0])",
        "expects [Int, String] | [Int, Int]",
    );
}

#[test]
fn closures_that_may_run_later_in_more_places() {
    // A pattern binds as an assignment does.
    err(
        "def f(s: Int | String) -> Int\n  x = s\n  if x.is_a?(String)\n    r = -> { p x.upcase; 0 }\n    0 => x\n    return r.call\n  end\n  0\nend",
        "undefined method `upcase` for Int",
    );
    // A body a rescue retries runs again.
    err(
        "def f(x: Int | String) -> Int\n  r = -> { nil }\n  n = 0\n  begin\n    if x.is_a?(String)\n      r.call\n      p x.upcase\n    end\n    r = -> { x = 5; nil }\n    n += 1\n    raise \"again\" if n < 2\n  rescue RuntimeError\n    retry\n  end\n  0\nend",
        "undefined method `upcase` for Int",
    );
    // A lambda in a parameter's default value.
    err(
        "def f(x: Int | String, r: () -> Nil = -> { x = 5; nil }) -> Int\n  if x.is_a?(String)\n    r.call\n    p x.upcase\n  end\n  0\nend",
        "undefined method `upcase` for Int",
    );
    // `Channel.select`'s blocks run after its block returns.
    err(
        "def f(x: Int | String) -> Nil\n  Channel.select do |s|\n    if x.is_a?(String)\n      s.default { p x.upcase; nil }\n    end\n    x = 5\n  end\nend",
        "undefined method `upcase` for Int",
    );
    // An immutable field cannot be assigned by a closure that may run
    // after `initialize`.
    err(
        "class C\n  @x: Int\n  @r: () -> Nil\n  def initialize\n    @x = 1\n    @r = -> { @x = 5; nil }\n  end\nend",
        "a closure that may run later, after `initialize`, cannot assign it",
    );
    // The method's block cannot go to a task unchecked.
    err(
        "def later(&: () -> Nil) -> Task[Nil] = Task.spawn(&)",
        "which runs it in a task",
    );
    // A closure that may run later is run after others made later in the
    // body, which may have assigned the local.
    err(
        "def f(x: Int | String) -> Nil\n  g = -> { nil }\n  a = -> { if x.is_a?(String)\n    g.call\n    p x.upcase\n  end\n  nil }\n  g = -> { x = 5; nil }\n  a.call\nend",
        "undefined method `upcase` for Int",
    );
    // In `initialize`, a field's narrowing does not reach a closure that
    // may run after the field is assigned again; nor may one assign it,
    // by any form of assignment.
    err(
        "class C\n  @x: Int | String\n  @r: () -> Nil\n  def initialize\n    @x = \"s\"\n    @r = -> { nil }\n    if @x.is_a?(String)\n      @r = -> { p @x.upcase; nil }\n    end\n    @x = 5\n  end\nend",
        "undefined method `upcase` for Int",
    );
    err(
        "class C\n  @n: Int\n  @r: () -> Nil\n  def initialize\n    @n = 1\n    @r = -> { @n += 1; nil }\n  end\nend",
        "field `@n` is immutable",
    );
    // An overload or a constructor is not an override.
    ok("class P\n  def run(&: () -> Nil) -> Nil = yield\nend\nclass Q < P\n  def run(n: Int, &blk: () -> Nil) -> Nil = nil\nend");
    ok("class C\n  def initialize(&: () -> Nil)\n    yield\n  end\nend\nclass D < C\n  def initialize(&blk: () -> Nil)\n    super(&blk)\n  end\nend");
    // Nor can an extension's method keep a block the one it hides yields.
    err(
        "def keep(b: () -> Nil) -> Nil = nil\nclass A\n  def run(&: () -> Nil) -> Nil = yield\nend\nclass C < A\nend\nextension C\n  def run(&blk: () -> Nil) -> Nil = keep(blk)\nend",
        "`run` cannot keep its block",
    );
}

#[test]
fn inheritance_cycles_are_errors() {
    err(
        "class A < A; end",
        "superclass cycle: `A` would inherit from itself",
    );
    err(
        "class A < B; end\nclass B < A; end",
        "superclass cycle: `B` would inherit from itself",
    );
    err(
        "class G[T] < H[T]; end\nclass H[T] < G[T]; end",
        "superclass cycle",
    );
    err(
        "module M\n  include M\nend",
        "cyclic include: `M` would include itself",
    );
    err(
        "module M\n  include N\nend\nmodule N\n  include M\nend\nclass A\n  include M\nend",
        "cyclic include: `N` would include itself",
    );
    // Through an extension (with growing type arguments, it used to hang).
    err(
        "module N[T]\nend\nmodule M[T]\n  include N[Array[T]]\nend\nextension N[T]\n  include M[T]\nend",
        "cyclic include: `N` would include itself",
    );
    err(
        "module N\nend\nmodule M\n  include N\nend\nextension N\n  include M\nend",
        "cyclic include: `N` would include itself",
    );
}
