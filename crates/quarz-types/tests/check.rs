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
        "class C\n  var @x: Float\n  def initialize\n    show\n    @x = 1.0\n  end\n  def show -> Void = p(@x)\nend",
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
        "class C\n  var @x: Int\n  def initialize(xs: Array[Int])\n    xs.each { |v| show }\n    @x = 1\n  end\n  def show -> Void = nil\nend",
        "the object is used before field `@x` is assigned",
    );
    ok("class C\n  var @xs: Array[Int]\n  def initialize(ys: Array[Int])\n    puts \"making\"\n    @xs = ys.map { |y| y * 2 }\n    show\n  end\n  def show -> Void = p(@xs)\nend\nC.new([1])");
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
    // A `next` in a do-while loop skips the rest of the body; a `when`
    // body runs after whichever of its conditions matched.
    err(
        "class C\n  @a: Int\n  def initialize(c: Bool)\n    begin\n      next if c\n      @a = 1\n    end while false\n  end\nend",
        "field `@a` is not assigned on every path",
    );
    ok("class C\n  @a: Int\n  def initialize(c: Bool)\n    begin\n      @a = 1\n    end while c\n  end\nend\nC.new(false)");
    ok("class C\n  @a: Int\n  def initialize(c: Bool)\n    begin\n      @a = 1\n      break if c\n      [1].each { |x| next if x > 0 }\n    end while false\n  end\nend\nC.new(false)");
    err(
        "class C\n  @a: Int\n  def initialize(x: Int)\n    case x\n    in ^@a then puts \"same\"\n    else\n    end\n    @a = 1\n  end\nend",
        "field `@a` is read before it is assigned",
    );
    err(
        "class C\n  @a: Int\n  def initialize(x: Int)\n    case x\n    when 1, (@a = 2)\n      puts @a\n    else\n      @a = 3\n    end\n  end\nend",
        "field `@a` is read before it is assigned",
    );
    ok("class C\n  @a: Int\n  def initialize(x: Int)\n    case (@a = x)\n    when 1, 2\n      puts @a\n    end\n  end\nend\nC.new(1)");
    // What `||=` and `&.` may not evaluate assigns nothing for sure.
    err(
        "class C\n  @b: Int\n  def initialize(t: Bool)\n    x = t\n    x ||= (@b = 1) == 1\n  end\nend",
        "field `@b` is not assigned on every path",
    );
    err(
        "class D\n  def f(x: Bool) -> Void = nil\nend\nclass C\n  @b: Int\n  def initialize(d: D?)\n    d&.f((@b = 1) == 1)\n  end\nend",
        "field `@b` is not assigned on every path",
    );
    // A parameter's default runs only when the argument is left out; an
    // index target's operands run before the value.
    err(
        "class C\n  @x: String\n  def initialize(a: Int = (@x = \"s\"; 0))\n  end\nend",
        "field `@x` is not assigned on every path",
    );
    err(
        "class C\n  @a: Int\n  def initialize(@a: Int, b: Int = @a)\n  end\nend",
        "field `@a` is read before it is assigned",
    );
    err(
        "class C\n  @x: String\n  def initialize(b: Array::Builder[Int])\n    b[@x.size] = (@x = \"abc\"; 0)\n  end\nend",
        "field `@x` is read before it is assigned",
    );
    // Defaults run before `initialize`.
    ok("class C\n  var @a: Float = 1.0\n  var @b: Float = @a + 1.0\nend\nC.new");
    err(
        "class C\n  var @a: Float = twice\n  var @b: Float\n  def initialize(@b: Float); end\n  def twice -> Float = @b * 2.0\nend",
        "a field's default cannot use the object",
    );
    // Not even once it has assigned every field itself.
    err(
        "class C\n  var @a: Int = (@a = 1; geta)\n  def geta -> Int = @a\nend",
        "a field's default cannot use the object",
    );
    // `raise` ends a path, as does a call of type `Nothing`.
    ok("class C\n  @x: Int\n  def initialize(v: Int)\n    if v > 0\n      @x = v\n    else\n      abort(\"neg\")\n    end\n    show\n  end\n  def show -> Void = p(@x)\nend\nC.new(1)");
    err("raise(\"a\") { puts 1 }", "`raise` takes no block");
    // Not one `&.` may skip.
    err(
        "class D\n  def die -> Nothing = raise \"x\"\nend\nclass C\n  @x: Int\n  def initialize(d: D?)\n    d&.die\n    show\n  end\n  def show -> Void = p(@x)\nend",
        "the object is used before field `@x` is assigned",
    );
    ok("class C\n  @x: Int\n  def initialize(v: Int)\n    if v > 0\n      @x = v\n    else\n      raise \"neg\"\n    end\n    show\n  end\n  def show -> Void = p(@x)\nend\nC.new(1)");
    // A native method on `self` (an accessor, `inspect`) may read the
    // fields too: only `Kernel` functions are fine before they are set.
    err(
        "class C\n  @x: Int\n  @y: Int\n  attr_reader :y\n  def initialize\n    @x = y + 1\n    @y = 2\n  end\nend",
        "the object is used before field `@x` is assigned",
    );
    err(
        "class C\n  @x: Int\n  def initialize\n    puts inspect\n    @x = 1\n  end\nend",
        "the object is used before field `@x` is assigned",
    );
    // A method an extension adds to `Kernel` does take `self`.
    err(
        "extension Kernel\n  def leak -> String = inspect\nend\nclass C\n  @x: Int\n  def initialize\n    puts leak\n    @x = 1\n  end\nend",
        "the object is used before field `@x` is assigned",
    );
}

#[test]
fn initialize_only_from_new() {
    // `initialize` runs only from `new` and from `super` in an
    // `initialize` (docs/01 §3).
    let only = "`initialize` is called only by `new` and by `super` in `initialize`";
    let c = "class C\n  @x: Int\n  def initialize(@x: Int); end\n  def initialize\n    @x = 0\n  end\n  def reset(n: Int) -> Void\n    initialize(n)\n    nil\n  end\nend\n";
    err(&format!("{c}C.new(1).initialize(5)"), only);
    err(&format!("{c}c = C.new\nc.initialize"), only);
    err(&format!("{c}C.new(1).reset(2)"), only);
    err(
        "class C\n  @x: Int\n  def initialize(@x: Int); end\n  def again -> Void\n    self.initialize(7)\n    nil\n  end\nend",
        only,
    );
    err(
        "class C\n  @x: Int\n  def initialize(@x: Int)\n    initialize if @x > 100\n  end\n  def initialize\n    @x = 0\n  end\nend",
        only,
    );
    // A superclass's `initialize` cannot re-enter a subclass's: its
    // implicit call is rejected in its own body.
    err(
        "class A\n  def initialize(n: Int)\n    initialize if n > 0\n  end\n  def initialize; end\nend\nclass B < A\n  @s: String\n  def initialize(@s: String)\n    super(1)\n  end\n  def initialize\n    @s = \"x\"\n  end\nend",
        only,
    );
    err(&format!("{c}[C.new(1)].each(&:initialize)"), only);
    err(&format!("{c}f = C.new(1).:initialize\nf.(5)"), only);
    // Reported after a warning too (a single candidate's failure before
    // its arguments are tried was once reported only with no diagnostic
    // so far).
    err(
        "class C\n  @x: Int\n  def initialize(@x: Int); end\nend\nx = 1\nputs x&.to_s\nC.new(1).initialize(5)",
        only,
    );
    err(
        "class C\n  private def secret -> Int = 1\nend\nx = 1\nputs x&.to_s\nC.new.secret",
        "`secret` is private",
    );
    // `new`, `super` (with arguments and bare) and a module's `initialize`.
    ok("class A\n  @a: Int\n  def initialize(@a: Int); end\n  def initialize(s: String)\n    @a = s.size\n  end\nend\nclass B < A\n  @b: Int\n  def initialize(@b: Int)\n    super(@b)\n  end\nend\nclass D < A\n  def initialize(a: Int)\n    super\n  end\nend\nB.new(1)\nD.new(2)\nA.new(\"ab\")");
    ok("module M\n  def initialize\n    puts \"m\"\n  end\nend\nclass C\n  include M\nend\nC.new");
}

#[test]
fn super_in_initialize_is_direct() {
    // `super` in `initialize` is written in the body, not in a block or
    // lambda that may run again once the object is made (docs/01 §3).
    let direct = "`super` in `initialize` must be called directly, not from a block or lambda";
    let a = "class A\n  @a: Int?\n  def initialize(a: Int?)\n    @a = a\n  end\nend\n";
    err(
        &format!("{a}class B < A\n  var @f: (() -> Void)?\n  def initialize\n    super(1)\n    @f = -> {{ super(nil); nil }}\n  end\nend"),
        direct,
    );
    err(
        &format!("{a}class B < A\n  def initialize\n    super(1)\n    [nil].each {{ |x| super(x) }}\n  end\nend"),
        direct,
    );
    err(
        &format!("{a}class B < A\n  def initialize\n    super(1)\n    [1].each {{ |i| [2].each {{ |j| super(i + j) }} }}\n  end\nend"),
        direct,
    );
    // A bare `super` in a block too; and `super` in another method's block
    // is fine (Ruby).
    err(
        &format!(
            "{a}class B < A\n  def initialize(a: Int?)\n    [1].each {{ |i| super }}\n  end\nend"
        ),
        direct,
    );
    ok("class A\n  def f(x: Int) -> Int = x\nend\nclass B < A\n  def f(x: Int) -> Int = [x].map { |y| super(y) }.first || 0\nend\nputs B.new.f(1)");
    // Directly in the body, in a branch.
    ok(&format!("{a}class B < A\n  def initialize(c: Bool)\n    if c\n      super(1)\n    else\n      super(nil)\n    end\n  end\nend\nB.new(true)"));
}

#[test]
fn super_chooses_among_overloads() {
    // `super` resolves against all the overloads of the first ancestor
    // that has the method, as a call does (docs/01 §9).
    let base = "class Base\n  @a: Int\n  def initialize(x: Int)\n    @a = x\n  end\n  def initialize(s: String)\n    @a = s.size\n  end\n  def f(x: Int) -> String = \"int\"\n  def f(s: String) -> String = \"str\"\n  def f(x: Int, s: String) -> String = \"both\"\nend\n";
    ok(&format!("{base}class Mid < Base\n  def initialize(s: String)\n    super(s)\n  end\n  def initialize(n: Int)\n    super(n)\n  end\n  def f(s: String) -> String = \"Mid \" + super(s)\n  def f(x: Int) -> String = \"Mid \" + super\nend\nMid.new(\"a\")\nMid.new(1)"));
    // A bare `super` forwards the parameters, chosen by their types.
    ok(&format!("{base}class Fwd < Base\n  def initialize(x: Int, s: String)\n    super(s)\n  end\n  def initialize(x: Int)\n    super\n  end\nend\nFwd.new(1, \"a\")"));
    err(
        &format!(
            "{base}class Fwd < Base\n  def initialize(x: Int, s: String)\n    super\n  end\nend"
        ),
        "no overload of `initialize` on Fwd matches",
    );
    // Only the first ancestor with the method: not Base's `f(Int, String)`
    // past Mid's `f(String)`.
    err(
        &format!("{base}class Mid < Base\n  def f(s: String) -> String = super(s)\nend\nclass Leaf < Mid\n  def f(s: String) -> String = super(1, s)\nend"),
        "takes 1 positional argument(s)",
    );
    // A tie is the usual error.
    err(
        "class Base\n  def f(x: Int, y: Int? = nil) -> String = \"a\"\n  def f(x: Int, s: String = \"\") -> String = \"b\"\nend\nclass Mid < Base\n  def f(x: Int) -> String = super(x)\nend",
        "the call of `f` is ambiguous",
    );
}

#[test]
fn narrowing_does_not_survive_assignments() {
    // A narrowing of a field (in `initialize`) or a local ends where the
    // variable may be assigned again: in a loop's body, in a `rescue` or
    // `ensure` the body left part way, and on the right of `&&`/`||`.
    let nil_plus = "undefined method `+` for Nil";
    // The loop's body assigns the field after the test before it.
    err(
        "class C\n  @x: Int?\n  def initialize(n: Int)\n    @x = 1\n    if @x.is_a?(Int)\n      i = 0\n      while i < n\n        @x = nil\n        i += 1\n      end\n      puts @x + 1\n    end\n  end\nend",
        nil_plus,
    );
    ok("class C\n  @x: Int?\n  @y: Int?\n  def initialize(n: Int)\n    @x = 1\n    @y = nil\n    if @x.is_a?(Int)\n      i = 0\n      while i < n\n        @y = nil\n        i += 1\n      end\n      puts @x + 1\n    end\n  end\nend\nC.new(1)");
    // The `rescue` runs when the body raised after assigning the field.
    err(
        "class C\n  @x: Int?\n  def initialize(n: Int)\n    @x = 1\n    begin\n      @x = nil\n      raise \"boom\" if n > 0\n    rescue\n      puts @x + 1\n    end\n  end\nend",
        nil_plus,
    );
    // The `ensure` runs when the body raised before narrowing, and the
    // fields it assigns are not narrowed after it.
    err(
        "def f(x: Int?) -> Void\n  begin\n    raise \"x\" unless x.is_a?(Int)\n  ensure\n    puts x + 1\n  end\nend",
        nil_plus,
    );
    err(
        "class C\n  @x: Int?\n  def initialize(n: Int)\n    @x = 1\n    begin\n      puts @x + 1\n    ensure\n      @x = nil if n > 0\n    end\n    puts @x + 1\n  end\nend",
        nil_plus,
    );
    ok("def f(x: Int?) -> Void\n  return if x.nil?\n  begin\n    puts x + 1\n  ensure\n    puts x + 2\n  end\n  puts x + 3\nend\nf(1)");
    ok("class C\n  @x: Int?\n  def initialize(n: Int)\n    @x = 1\n    begin\n      puts @x + 1\n    ensure\n      puts n\n    end\n    puts @x + 1\n  end\nend\nC.new(1)");
    // A fact of `&&`'s left operand about a variable its right assigns,
    // or about an inherited field once it called `super`, is gone.
    err(
        "x: Int? = 1\nx.is_a?(Int) && (x = nil; true) && puts(x + 1)",
        nil_plus,
    );
    err(
        "class C\n  @x: Int?\n  def initialize\n    @x = 1\n    @x.is_a?(Int) && (@x = nil; true) && puts(@x + 1)\n  end\nend",
        nil_plus,
    );
    err(
        "class P\n  @f: Int?\n  def initialize(v: Int?)\n    @f = v\n  end\nend\nclass C < P\n  def initialize(cond: Bool)\n    @f = 1\n    if @f.is_a?(Int) && (super(nil); true)\n      puts @f + 1\n    end\n  end\nend",
        nil_plus,
    );
    ok("x: Int? = 1\ny: Int? = nil\nx.is_a?(Int) && (y = nil; true) && puts(x + 1)\nif x.is_a?(Int) || (y = 2; false)\n  puts x + 1\nend");
    // A `!` method the type lacks rebinds the variable (docs/01 §9).
    err(
        "class Foo\n  def foo -> Bar = Bar.new\nend\nclass Bar\n  def bar -> Int = 1\nend\ndef f(x: Foo | Bar) -> Void\n  x.is_a?(Foo) && (x.foo!; true) && puts(x.foo.bar)\nend",
        "undefined method `foo` for Bar",
    );
    // In a method other than `initialize`, `super` assigns no field: an
    // inherited field keeps its narrowing past it.
    ok("class P\n  @p: Int?\n  def initialize(@p: Int?); end\n  def go(c: Bool) -> Int = 0\n  def go2(c: Bool) -> Int = 0\nend\nclass C < P\n  def go(c: Bool) -> Int\n    if @p.is_a?(Int)\n      while c\n        super\n        c = false\n      end\n      return @p + 1\n    end\n    0\n  end\n  def go2(c: Bool) -> Int\n    y = @p.is_a?(Int) && (super(c); true) && @p + 1\n    y.is_a?(Int) ? y : 0\n  end\nend\nC.new(1).go(true)\nC.new(1).go2(true)");
}

#[test]
fn patterns_narrow_object_to_classes_admitting_object_arguments() {
    // `in Box`/`when Box` on an `Object` narrows to `Box[Object]` when every
    // parameter is covariant with bounds `Object` meets, as `is_a?` allows
    // (docs/02 §6, §7); not to a class with a bound `Object` does not meet,
    // nor to one with an invariant parameter.
    let shape = "class Shape\n  def area -> Int = 1\nend\n";
    ok(&format!("{shape}class Box[out T <: Object]\n  @v: T\n  def initialize(@v: T); end\n  def get -> T = @v\nend\ndef f(o: Object) -> String\n  case o\n  in Box then o.get.inspect\n  else \"other\"\n  end\nend\ndef g(o: Object) -> String\n  case o\n  when Box then o.get.inspect\n  else \"other\"\n  end\nend\nputs f(Box.new(1))\nputs g(Box.new(1))"));
    err(
        &format!("{shape}class SBox[out T <: Shape]\n  @v: T\n  def initialize(@v: T); end\n  def get -> T = @v\nend\ndef f(o: Object) -> Int\n  case o\n  in SBox then o.get.area\n  else 0\n  end\nend"),
        "undefined method `get` for Object",
    );
    err(
        "class Cell[T]\n  var @v: T\n  def initialize(@v: T); end\n  def set(v: T) -> Void\n    @v = v\n  end\nend\ndef f(o: Object) -> Void\n  case o\n  in Cell then o.set(\"s\")\n  else nil\n  end\nend",
        "undefined method `set` for Object",
    );
}

#[test]
fn super_in_extension_reaches_the_hidden_method() {
    // `super` in an extension's method calls the method it hides: the
    // class's own (among its overloads), else the ancestors' (docs/01 §7).
    let classes = "class Base\n  def greet(n: Int) -> String = \"base\"\n  def greet(s: String) -> String = \"base\"\nend\nclass Mid < Base\n  def greet(n: Int) -> String = \"mid\"\n  def greet(s: String) -> String = \"mid\"\nend\nclass Leaf < Mid\nend\n";
    ok(&format!("{classes}module Loud\n  extension Mid\n    def greet(n: Int) -> String = super(n) + \"!\"\n    def greet(s: String) -> String = super + \"?\"\n  end\n  extension Leaf\n    def greet(n: Int) -> String = \"please, \" + super\n    def greet(s: String) -> String = super(s)\n  end\nend\nusing Loud\nputs Mid.new.greet(1)\nputs Leaf.new.greet(\"a\")"));
    // Also where the extension's module is not `using`-ed (a library's
    // layout: defined in one place, used in others).
    ok(&format!("{classes}module Loud\n  extension Mid\n    def greet(n: Int) -> String = super(n) + \"!\"\n  end\n  extension Leaf\n    def greet(n: Int) -> String = \"please, \" + super\n  end\nend\nclass User\n  using Loud\n  def go -> String = Leaf.new.greet(1)\nend\nputs User.new.go"));
    // The hidden method is the class's own, with its signature.
    err(
        &format!("{classes}module Loud\n  extension Leaf\n    def greet(n: Int) -> String = super(1.5)\n  end\nend\nusing Loud\nputs Leaf.new.greet(1)"),
        "no overload of `greet` on Leaf matches",
    );
    err(
        "class Base\n  def other -> Int = 1\nend\nmodule M\n  extension Base\n    def shout -> String = super\n  end\nend\nusing M\nputs Base.new.shout",
        "no superclass method `shout`",
    );
}

#[test]
fn case_on_self() {
    // `case` on `Self` matches as on the receiver's class.
    no_warnings("enum R[T, E]\n  variant Ok(value: T)\n  variant Err(error: E)\n  def on_ok(&: (T) -> Void) -> Self\n    case self\n    in Ok(value:) then yield(value)\n    in Err then nil\n    end\n    self\n  end\nend");
    // A binding keeps `Self`.
    ok("class S\n  def same -> Self\n    x = self\n    case x\n    in S then x\n    else x\n    end\n  end\n  def bind -> Self\n    case self\n    in s then s\n    end\n  end\nend");
    // In a block with a receiver, `Self` is the method's, not the receiver's.
    err("class B\n  def bonly -> Int = 1\n  def run(&blk: B.() -> Void) -> Void = instance_exec(&blk)\nend\nclass A\n  def go -> Self\n    x: Self = self\n    B.new.run { case x\n    in y then puts(y.bonly)\n    end }\n    self\n  end\nend", "undefined method `bonly` for Self");
    no_warnings("enum R[T, E]\n  variant Ok(value: T)\n  variant Err(error: E)\n  def on_err(&: (E) -> Void) -> Self\n    r: R[T, E] = self\n    case r\n    in Err(error:) then yield(error)\n    in Ok then nil\n    end\n    self\n  end\nend");
}

#[test]
fn overload_resolution() {
    // An integer literal takes its default type first: `x + 1` is
    // `Int#+(Int)`, `1.5 / 2` is `Float#/(Int)`.
    ok("x = 3\ny: Int = x + 1\nputs y");
    ok("z: Float = 1.5 / 2\nputs z");
    // Overloads that fit a call equally make it ambiguous.
    err(
        "def g(*, a: Int, b: Int = 0) -> Int = 1\ndef g(*, b: Int, a: Int = 0) -> Int = 2\ng(a: 1, b: 2)",
        "the call of `g` is ambiguous",
    );
    err(
        "def k(a: Int = 0) -> Int = 1\ndef k(a: Int = 0, b: Int = 0) -> Int = 2\nk",
        "the call of `k` is ambiguous",
    );
    // The more specific wins.
    ok("def h(a: Object) -> Int = 1\ndef h(a: Int) -> String = \"i\"\ns: String = h(1)");
    // Overloads differing only in the block: the one of the block's arity.
    ok("class S\n  def each_m(&: (String) -> Void) -> Int = 1\n  def each_m(&: (String, Int) -> Void) -> String = \"two\"\nend\na: Int = S.new.each_m { |s| }\nb: String = S.new.each_m { |s, i| }");
    // A block with fewer parameters than every overload's takes the
    // fewest.
    ok("class S\n  def each_m(&: (String) -> Void) -> Int = 1\n  def each_m(&: (String, Int) -> Void) -> String = \"two\"\nend\na: Int = S.new.each_m { }");
    ok("puts \"hello world\".gsub(/o/) { \"0\" }");
    // An argument still to be inferred takes the first overload that fits.
    ok("p [].reduce(1) { |a, x| a * x }");
    ok("def f(a: Object) -> String = \"O\"\ndef f(a: Array[Int]) -> String = \"AI\"\nx = []\nputs f(x)\ny: Array[String] = x");
    // An extension's method in scope hides the class's own.
    ok("class C\n  def name -> String = \"own\"\nend\nextension C\n  def name -> String = \"ext\"\nend\nputs C.new.name");
    // Overloads by block type both fitting a block are ambiguous.
    err(
        "class K\n  def run(&blk: (Int) -> Int) -> Int = 1\n  def run(&blk: (Float) -> Float) -> Int = 2\nend\nK.new.run { |x| x }",
        "the call of `run` is ambiguous",
    );
    // A class's own `initialize` hides its ancestors'.
    ok("class A\n  def initialize(s: String = \"a\"); end\nend\nclass B < A\n  def initialize(n: Int = 0, s: String = \"b\"); end\nend\nB.new");
}

#[test]
fn classes_and_fields() {
    // Two definitions of one signature are an error; another signature
    // is an overload.
    err(
        "class C\n  def f -> Int = 1\n  def f -> Int = 2\nend",
        "`f` is already defined with the same parameters",
    );
    err(
        "class C\n  @x: Int\n  attr_reader :x\n  def x -> Int = @x\n  def initialize(@x: Int); end\nend",
        "`x` is already defined with the same parameters",
    );
    ok("class C\n  def g(a: Int) -> Int = a\n  def g(a: String) -> Int = 0\nend\nputs C.new.g(1) + C.new.g(\"s\")");
    err(
        "class C\n  def f[T](x: T) -> T = x\n  def f[U](x: U) -> U = x\nend",
        "`f` is already defined with the same parameters",
    );
    err(
        "class C\nend\nextension C\n  def g -> Int = 2\n  def g -> Int = 3\nend",
        "`g` is already defined with the same parameters",
    );
    ok("class C\n  @x: Int\n  attr_reader :x\n  def initialize(@x: Int); end\nend\nputs C.new(1).x");
    // Keyword-only parameters' names are part of the signature.
    ok("class C\n  def f(*, a: Int) -> Int = 1\n  def f(*, b: Int) -> Int = 2\nend\nputs C.new.f(a: 0) + C.new.f(b: 0)");
    err(
        "class C\n  def f(a: Int) -> Int = 1\n  def f(b: Int) -> Int = 2\nend",
        "`f` is already defined with the same parameters",
    );
    // An override replaces the overload of its keyword names only.
    ok("class C\n  def f(*, a: Int) -> Int = a\n  def f(*, b: Int) -> String = \"b\"\nend\nclass D < C\n  def f(*, b: Int) -> String = \"d\"\nend\nputs D.new.f(a: 1)");
    // A duplicate alias is reported at the alias.
    err_at(
        "class C\n  def f -> Int = 1\n  alias g f\n  alias g f\nend",
        "`g` is already defined with the same parameters",
        4,
    );
    // A data type's generated methods give way to the body's own.
    ok("data P(x: Int)\n  def to_s -> String = \"P\"\n  def with(*, x: Int) -> P = P.new(x + 1)\n  def to_h -> Hash[Symbol, Object] = {}\n  def x -> Int = 0\nend\nputs P.new(1).with(x: 2).to_s");
    err(
        "data Q(a: Int)\n  def initialize(s: String)\n    @a = s.size\n  end\nend\nputs Q.new(1).a",
        "expects String but found Int",
    );
    err(
        "enum Shape\n  variant Circle(radius: Float)\n  def initialize\n  end\nend",
        "an enum cannot define `initialize`",
    );
    // A class with fields of its own to assign is made only by its own
    // `initialize`: not a module's, an extension's or an ancestor's.
    let m = "module M\n  def initialize\n  end\nend\n";
    for (src, missing) in [
        ("enum Shape\n  include M\n  variant Circle(radius: Float)\nend\nputs Shape::Circle.new.radius", "radius"),
        ("enum Shape\n  variant Circle(radius: Float)\nend\nextension Shape\n  include M\nend\nputs Shape::Circle.new.radius", "radius"),
        ("data P(x: Float)\n  include M\nend\nputs P.new.x", "x"),
        ("class C\n  include M\n  @x: Float\n  def initialize(@x: Float)\n  end\nend\nC.new", "x"),
        ("class A\n  def initialize\n  end\nend\nclass B < A\n  @x: Float\n  def initialize(@x: Float)\n  end\nend\nB.new", "x"),
    ] {
        err(&format!("{m}{src}"), &format!("is missing the argument `{missing}`"));
    }
    // Nor past a class below with fields to assign, nor a module's in a
    // class with fields anywhere.
    err(
        "class A\n  @x: Float\n  def initialize(@x: Float); end\nend\nclass B < A\n  @y: String\n  def initialize(@y: String)\n    super(1.0)\n  end\nend\nclass C < B\nend\nC.new(2.0)",
        "expects String but found Float",
    );
    err(
        &format!("{m}class A\n  @x: Float\n  def initialize(@x: Float); end\nend\nclass B < A\n  include M\nend\nB.new"),
        "is missing the argument `x`",
    );
    err(
        &format!("{m}class A\n  include M\n  @x: Float\n  def initialize(@x: Float); end\nend\nclass B < A\nend\nB.new"),
        "is missing the argument `x`",
    );
    // A field of a type parameter counts as one to assign.
    err(
        &format!("{m}class G[T]\n  @v: T\n  def initialize(@v: T); end\nend\nclass H < G[Int]\n  include M\nend\nH.new"),
        "is missing the argument `v`",
    );
    err(
        "class A\n  def initialize(s: String); end\nend\nclass B[T] < A\n  @y: T\n  def initialize(@y: T)\n    super(\"a\")\n  end\nend\nclass C < B[Int]\nend\nC.new(\"x\")",
        "expects Int but found String",
    );
    // A field of a type parameter needs assigning, whatever its bound.
    err(
        "class G[T]\n  @v: T\nend",
        "field `@v` has no default and `G` has no `initialize` to assign it",
    );
    err(
        "class G[T <: Object?]\n  @v: T\nend",
        "field `@v` has no default and `G` has no `initialize` to assign it",
    );
    ok("class G[T]\n  @v: T?\nend\nG[Int].new");
    // An extension cannot define `initialize`.
    err(
        "class C\nend\nextension C\n  def initialize\n  end\nend",
        "an extension cannot define `initialize`",
    );
    // `super` assigns the inherited fields: what was narrowed before it
    // is not after; the class's own fields keep theirs.
    err(
        "class P\n  @x: Int?\n  def initialize\n    @x = nil\n  end\nend\nclass C < P\n  def initialize\n    @x = 1\n    super\n    puts(@x + 1)\n  end\nend",
        "undefined method `+` for Nil",
    );
    ok("class P\n  @x: Int?\n  def initialize\n    @x = nil\n  end\nend\nclass C < P\n  @y: Int?\n  def initialize\n    @y = 1\n    super\n    puts(@y + 1)\n  end\nend\nC.new");
    // A nilable field needs no assignment: the superclass's still makes it.
    ok("class E < StandardError\n  @code: Int?\nend\nraise E.new(\"boom\")");
    // Without fields of its own, a class inherits its superclass's.
    ok("class A\n  @x: Int\n  def initialize(@x: Int); end\nend\nclass B < A\nend\nB.new(1)");
    // `initialize` cannot be aliased, either way.
    err(
        "class C\n  @x: Int\n  def initialize(@x: Int); end\n  def init2 -> Void\n  end\n  alias initialize init2\nend",
        "`initialize` cannot be aliased",
    );
    err(
        "class C\n  @x: Int\n  def initialize(@x: Int); end\n  alias reset initialize\nend",
        "`initialize` cannot be aliased",
    );
    // With an `initialize` of other parameters, there is no `with`.
    err(
        "data Q(a: Int)\n  def initialize(s: String)\n    @a = s.size\n  end\nend\nputs Q.new(\"ab\").with(a: 1)",
        "undefined method `with`",
    );
    err(
        "data P(x: Int)\n  def ==(other: P) -> Bool = true\nend",
        "takes one parameter of type `Object`",
    );
    err(
        "class C\n  @x: Int\n  def initialize\n  end\nend",
        "field `@x` is not assigned on every path through `initialize`",
    );
    err(
        "class C\n  @x: Int?\n  def initialize\n  end\nend",
        "field `@x` must be assigned in `initialize`",
    );
    err(
        "class C\n  @x: Int\n  def initialize(@x: Int); end\n  def bump -> Void\n    @x = 2\n  end\nend",
        "field `@x` is immutable",
    );
    ok("class C\n  var @x: Int = 0\n  attr_accessor :x\n  def bump -> Void\n    @x += 1\n  end\nend\nc = C.new\nc.bump\nc.x = 5");
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
    // Return types are declared, not inferred: without one, a method is
    // `-> Void` (it returns nil), and one defined with `=` must have it.
    ok("def f\n  f\nend");
    err(
        "def g\n  5\nend\nx: Int = g",
        "cannot assign Nil to `x` of type Int",
    );
    err(
        "def h\n  return 5 if true\n  nil\nend",
        "`return` gives a Int but the method is `-> Void`, which returns nil",
    );
    ok("def h\n  return if true\n  return nil\nend");
    // An override returns what the overridden method does.
    err("abstract class Shape\n  abstract def area -> Float\nend\nclass Ci < Shape\n  def area\n    2.0\n  end\nend", "`area` returns Void but `Shape#area`, which it overrides, returns Float (a `-> Void` method, as one without a return type, returns nil)");
    err(
        "class Foo\n  def to_s\n    \"foo\"\n  end\nend",
        "`to_s` returns Void but `Object#to_s`, which it overrides, returns String",
    );
    err(
        "class K\n  include Comparable[K]\n  def <=>(o: K) -> String = \"x\"\nend",
        "`<=>` returns String but `Comparable#<=>`",
    );
    ok("class A\n  def make -> Object = 1\nend\nclass B < A\n  def make -> Int = 2\nend");
    ok("def fact(n: Int) -> Int = n <= 1 ? 1 : n * fact(n - 1)\nputs fact(5)");
    err(
        "def f(x: Int) -> String\n  x\nend",
        "returns String but its body has type Int",
    );
    ok("def f(x: Int) -> Int\n  x * 2\nend\ny: Int = f(2)");
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
    ok("def h[T <: Comparable[T]](a: T, b: T) -> T = a > b ? a : b\nputs h(1, 2)");
    err("def h[T <: Comparable[T]](a: T, b: T) -> T = a > b ? a : b\nh(->(x: Int) { x }, ->(x: Int) { x })", "does not satisfy the bound");
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
    ok("module Describable\n  abstract def describe -> String\nend\nmodule M\n  extension Int\n    include Describable\n    def describe -> String = \"int\"\n  end\nend\nusing M\ndef show(d: Describable) -> Void\n  puts d.describe\nend\nshow(1)");
    err(
        "module Describable\n  abstract def describe -> String\nend\ndef show(d: Describable) -> Void\n  puts d.describe\nend\nshow(1)",
        "expects Describable but found Int",
    );
    err("using Nope", "unknown constant `Nope`");
}

#[test]
fn captured_self_in_task_blocks() {
    // `self` is captured like a variable: a mutable object cannot be.
    let counter = "class Counter\n  var @n: Int = 0\n  def bump -> Void\n    @n += 1\n    nil\n  end\n  def run -> Int\n    BODY\n    @n\n  end\nend";
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
    // A method an extension adds to `Kernel` takes `self`.
    err(
        &format!(
            "extension Kernel\n  def leak -> Int = 1\nend\n{}",
            counter.replace("BODY", "Task.spawn { leak }.await")
        ),
        "calling `leak` uses `self`",
    );
    // The same failure through two candidates is reported once.
    let errs = diagnostics(&counter.replace("BODY", "Task.scope { |s| s.spawn { bump } }"));
    assert_eq!(errs[0].matches("calling `bump`").count(), 1, "{errs:?}");
}

#[test]
fn enumerators_stay_in_their_task() {
    // An enumerator has a position, and its receiver may be mutable.
    let counter = "class Counter\n  include Enumerable[Int]\n  var @n: Int = 0\n  def each(&: (Int) -> Void) -> Void\n    @n += 1\n    yield @n\n  end\nend\n";
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
    // Each kind that cannot be inherited from says so by name.
    err(
        "module N\n  data P = (x: Int)\nend\nclass C < N::P\nend",
        "cannot inherit from data type `N::P`: a data type cannot be subclassed (include a module to share behaviour)",
    );
    err(
        "enum E = A | B(x: Int)\nclass C < E\nend",
        "cannot inherit from enum `E`: its variants are the ones it declares",
    );
    err(
        "enum E = A | B(x: Int)\nclass C < E::B\nend",
        "cannot inherit from enum variant `E::B`",
    );
    err(
        "module M\nend\nclass C < M\nend",
        "cannot inherit from module `M`: include it instead",
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
fn void_and_strict_nil() {
    // `-> Void` discards the body's value; callers see `Nil`.
    ok("def f(x: Int) -> Void\n  x + 1\nend\ny: Nil = f(1)");
    ok("def f(x: Int) -> Void = x + 1\np f(1)");
    err(
        "def f -> Void = 1\nx: Int = f",
        "cannot assign Nil to `x` of type Int",
    );
    // `-> Nil` is strict, as any other type.
    err(
        "def f(x: Int) -> Nil\n  x + 1\nend",
        "method `f` returns Nil but its body has type Int; to discard the body's value, write `-> Void`",
    );
    ok("def f(x: Int) -> Nil\n  p x\n  nil\nend");
    ok("def f -> Nil = nil");
    ok("def g(x: Int?) -> Nil = x.nil? ? nil : nil");
    // Blocks and lambdas alike.
    err(
        "def each(&: (Int) -> Nil) -> Void = yield(1)\neach { |x| x + 1 }",
        "block returns Int but Nil was expected",
    );
    ok("def each(&: (Int) -> Nil) -> Void = yield(1)\neach { |x| nil }");
    ok("def each(&: (Int) -> Void) -> Void = yield(1)\neach { |x| x + 1 }");
    err(
        "l = ->(x: Int) -> Nil { x }",
        "lambda returns Int but Nil was expected",
    );
    ok("l = ->(x: Int) -> Void { x }\ny: Nil = l.call(1)");
    ok("h: (Int) -> Void = ->(x: Int) { x + 1 }\nh.call(1)");
    err(
        "h: (Int) -> Nil = ->(x: Int) { x + 1 }",
        "lambda returns Int but Nil was expected",
    );
    // `yield` and `f.call` of a `Void` procedure give `Nil`.
    err(
        "def run(&: () -> Void) -> Int\n  x: Int = yield\n  x\nend",
        "cannot assign Nil to `x` of type Int",
    );
    // `Void` is only a result.
    for src in [
        "x: Void? = nil",
        "def f(x: Void) -> Int = 1",
        "x: Array[Void] = []",
        "def f -> Int | Void = 1",
        "class C\n  @v: Void\nend",
        "def f(t: Task[Void]) -> Void = nil",
        "def f[T <: Void](x: T) -> Void = nil",
        "type V = Void\nx: V = nil",
    ] {
        err(src, "`Void` is only a result type");
    }
    ok("type Handler = (Int) -> Void\nh: Handler = ->(x: Int) { x }\nh.call(1)");
    ok("f: shareable () -> Void = -> { 1 }\nf.call");
    // `(Int) -> Void` and `(Int) -> Nil` are the same type.
    ok("v: (Int) -> Void = ->(x: Int) -> Nil { nil }\nn: (Int) -> Nil = v\nv = n");
    err(
        "i: (Int) -> Int = ->(x: Int) { x }\nv: (Int) -> Void = i",
        "cannot assign (Int) -> Int to `v` of type (Int) -> Void",
    );
    // A procedure's type argument is never `Void`: callers see `Nil`.
    ok("def f -> Void = 1\ng = ->() -> Void { 1 }\nxs = [1].map { |x| g.call }\nys: Array[Nil] = xs");
    // Overrides: `-> Void` and `-> Nil` replace each other.
    ok("class A\n  def f -> Nil = nil\n  def g -> Void = 1\nend\nclass B < A\n  def f -> Void = 2\n  def g -> Nil = nil\nend");
    ok("abstract class A\n  abstract def f(&: (Int) -> Nil) -> Void\nend\nclass B < A\n  def f(&: (Int) -> Void) -> Void = yield(1)\nend\nB.new.f { |x| nil }");
    // `return` in a `Void` method gives no value.
    ok("def f(x: Int) -> Void\n  return if x > 0\n  x\nend");
    err(
        "def f(x: Int) -> Void\n  return x if x > 0\nend",
        "the method is `-> Void`",
    );
    err(
        "l = ->(x: Int) -> Void { return x }",
        "the lambda is `-> Void`",
    );
    // The top level is `-> Void` too.
    err(
        "[1, 2].each do |x|\n  return 5 if x > 1\nend",
        "the method is `-> Void`",
    );
    // Overloads differing only by `Void`/`Nil` are the same.
    err(
        "def f(x: (Int) -> Void) -> Int = 1\ndef f(x: (Int) -> Nil) -> Int = 2",
        "already defined with the same parameters",
    );
    err(
        "class C\n  def v -> Void = 1\nend\nxs: Array[Int] = [C.new].map(&:v)",
        "`&:v` returns Nil but Int was expected",
    );
}

#[test]
fn void_followups() {
    // `Self`, `Void` and `Nothing` cannot name a declared type.
    for (src, name) in [
        ("class Void\nend", "Void"),
        ("module Nothing\nend", "Nothing"),
        ("data Void = (x: Int)", "Void"),
        ("enum Nothing = A | B", "Nothing"),
        ("type Void = Int", "Void"),
        ("class M\nend\nclass M::Nothing\nend", "Nothing"),
        ("def f[Void](x: Int) -> Int = x", "Void"),
        ("class Box[Nothing]\nend", "Nothing"),
        ("def f[Self](x: Int) -> Int = x", "Self"),
    ] {
        err(src, &format!("`{name}` is reserved"));
    }
    // `&:name` where a `Void` result is expected discards the call's
    // value, as `{ |x| x.name }` does.
    ok("[1, 2].each(&:to_s)");
    ok("def run(&: (Int) -> Void) -> Void\n  x: Nil = yield 1\nend\nrun(&:succ)");
    err(
        "def run(&: (Int) -> Nil) -> Void = yield(1)\nrun(&:succ)",
        "`&:succ` returns Int but Nil was expected",
    );
    // A union's members cannot disagree on discarding it.
    err(
        "class A\n  def run(&: (Int) -> Void) -> Void = yield(5)\nend\nclass B\n  def run(&: (Int) -> Int) -> Int = yield(5)\nend\ndef pick(n: Int) -> A | B = n > 0 ? A.new : B.new\npick(1).run(&:succ)",
        "cannot tell at run time whether `&:succ` gives the value",
    );
    err(
        "class B\n  def run(&: (Int) -> Int) -> Int = yield(5)\nend\nclass A\n  def run(&: (Int) -> Void) -> Void = yield(5)\nend\ndef pick(n: Int) -> B | A = n > 0 ? A.new : B.new\npick(1).run(&:succ)",
        "cannot tell at run time whether `&:succ` gives the value",
    );
    // `next value` in a `Void` block is an error; a bare `next` is not.
    err(
        "[1, 2].each { |x| next x if x > 1 }",
        "`next` gives a Int but the block's result is `Void`",
    );
    ok("[1, 2].each { |x| next if x > 1\n  p x }");
    ok("[1, 2].each { |x| next nil if x > 1\n  p x }");
    ok("p [1, 2].map { |x| next 0 if x > 1\n  x }");
}

#[test]
fn falsy_type_parameters() {
    let bx = |bound: &str, body: &str| {
        format!("class Box[T{bound}]\n  @v: T\n  def initialize(v: T)\n    @v = v\n  end\n  def m -> Int\n    {body}\n  end\nend")
    };
    // `T` may be `Bool` or `Int?`: the falsy side keeps it.
    err(
        &bx("", "if @v then 1 else @v.size end"),
        "undefined method `size` for T",
    );
    err(
        &bx("", "unless @v\n      return @v.size\n    end\n    1"),
        "undefined method `size` for T",
    );
    err(
        &bx("", "!@v ? @v.size : 1"),
        "undefined method `size` for T",
    );
    err(
        &bx("", "x = @v || 3\n    x.size"),
        "undefined method `size` for T",
    );
    ok(&format!(
        "{}\np Box[Int?].new(nil).m, Box[Bool].new(false).m",
        bx("", "if @v then 1 else\n      x: T = @v\n      0\n    end")
    ));
    // The truthy side is as before.
    ok(&bx(
        " <: Comparable[T]",
        "if @v then (@v <=> @v) else 0 end",
    ));
    // A bound that holds neither nil nor false rules them out.
    ok(&bx(" <: Int", "if @v then @v else @v.size end"));
    // One naming the parameter does not.
    err(
        &bx(" <: Comparable[T]", "if @v then 1 else @v.size end"),
        "undefined method `size` for T",
    );
}

#[test]
fn nil_results_and_lambda_annotations() {
    // A lambda's declared result is checked like a method's.
    err(
        "l = ->(x: Int) -> String { x }",
        "lambda returns Int but String was expected",
    );
    ok("l = ->(x: Int) -> Int | String { x }\nputs l.call(1)");
    ok("l = ->(x: Int) -> Void { x }\nl.call(1)");
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
    ok("module M\n  def ok1(&: (Self) -> Void) -> Self = self\n  def ok2 -> Array[Self] = [self]\n  def ok3(f: (Self) -> Int) -> Int = f.call(self)\n  def ok4 -> Self? = nil\nend");
    // Where the caller hands one in, a subclass would get its parent's.
    for src in [
        "module M\n  abstract def cmp(other: Self) -> Int\nend",
        "module M\n  def a(&: () -> Self) -> Void = nil\nend",
        "module M\n  def b(x: Array[Self]) -> Void = nil\nend",
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
    ok("class Counter\n  var @n: Int = 0\n  def bump -> Void\n    @n += 1\n  end\nend\nc = Counter.new\nc.bump");
    err(
        "class Counter\n  var @n: Int = 0\nend\nc = Counter.new\nTask.spawn { c }",
        "non-shareable type Counter",
    );
    ok("data P = (x: Int)\np = P.new(1)\nTask.spawn { p.x }.await");
}

#[test]
fn shareable_procedures() {
    let run = "def run(&h: shareable () -> Void) -> Void\n  Task.spawn { h.call }.await\nend\n";
    // A block or lambda where one is expected captures by value, like a
    // `spawn` block: Shareable values, no assignment.
    ok(&format!("{run}x = 1\nrun {{ puts x }}"));
    ok(&format!(
        "{run}f: shareable (Int) -> Int = ->(n: Int) {{ n + 1 }}\nTask.spawn {{ f.call(1) }}"
    ));
    ok(&format!(
        "{run}def opt(f: (shareable () -> Void)? = nil) -> (shareable () -> Void)? = f\nopt(f: ->() {{ puts 1 }})"
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
    // A type parameter bounded by an exception class can be raised.
    ok("def f[E <: Exception](e: E) -> Nothing = raise e");
    ok("extension Result[T, E <: Exception]\n  def get! -> T\n    case self\n    in Result::Ok(value:) then value\n    in Result::Err(error:) then raise error\n    end\n  end\nend");
    ok("class H[E <: Exception]\n  @e: E\n  def initialize(@e: E)\n  end\n  def go -> Nothing = raise @e\nend");
    ok("def f[T](x: T) -> Void\n  case x\n  in IOError then raise x\n  else nil\n  end\nend");
    ok("def f[E <: Exception](e: E, b: Bool) -> Nothing\n  x = b ? e : IOError.new(\"io\")\n  raise x\nend");
    err(
        "def f[E](e: E, b: Bool) -> Nothing\n  x = b ? e : IOError.new(\"io\")\n  raise x\nend",
        "cannot raise",
    );
    err("def f[E](e: E) -> Nothing = raise e", "cannot raise E");
    err(
        "def f[E <: Comparable[E]](e: E) -> Nothing = raise e",
        "cannot raise E",
    );
    err(
        "def f[E <: Exception](e: E) -> Nothing = raise e, \"m\"",
        "`raise` with an exception object takes no second argument",
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
    ok("module Cleanup\n  def deinitialize -> Void = nil\nend\nclass R\n  include Cleanup\nend");
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
    // `&:name` chooses as a call does: by the bounds of an extension's
    // parameters, and only a method callable with no argument or block.
    ok("p [[1.5]].map(&:sum), [[1]].map(&:sum), [1..3].map(&:size)");
    err(
        "p [\"a\"..\"b\"].map(&:size)",
        "`size` requires T to be Int (found String) (in `&:size`)",
    );
    err(
        "p [(\"a\"..\"b\")].sum(&:size)",
        "`size` requires T to be Int",
    );
    err(
        "p [[\"a\"]].map(&:sum)",
        "`sum` requires T to be Int (found String)",
    );
    err(
        "p(%w[ab].map(&:center))",
        "`center` needs an argument (`&:center` calls it with none)",
    );
    err(
        "p (\"a\"..\"b\").size",
        "`size` requires T to be Int (found String)",
    );
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
        "class B[out T]\n  def put(x: T) -> Void = nil\nend",
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
    // A value is one of its superclass and included modules: an upcast to
    // them must be sound.
    err(
        "class B[T]\n  var @x: T\n  def initialize(@x: T)\n  end\nend\nclass C[out T] < B[T]\n  def initialize(x: T)\n    super(x)\n  end\nend",
        "`T` appears in the type arguments of `B`",
    );
    err(
        "module M[T]\nend\nclass C[out T]\n  include M[T]\nend",
        "`T` appears in the type arguments of `M`",
    );
    // An immutable field is read as a result (its reader returns it).
    err(
        "class B[out T]\n  @f: (T) -> Void\n  attr_reader :f\n  def initialize(@f: (T) -> Void)\n  end\nend",
        "`T` appears in a result position of the field `@f`",
    );
    err(
        "class Cell[T]\n  var @v: T\n  def initialize(@v: T)\n  end\nend\nclass B[out T]\n  @c: Cell[T]\n  def initialize(@c: Cell[T])\n  end\nend",
        "`T` appears in a result position of the field `@c`",
    );
    ok("class B[out T]\n  @x: T\n  @f: () -> T\n  def initialize(@x: T, @f: () -> T)\n  end\nend");
    err(
        "class B[in T]\n  @x: T\n  def initialize(@x: T)\n  end\nend",
        "`T` appears in a result position of the field `@x`",
    );
    ok("class B[out T]\n  def each(&: (T) -> Void) -> Void = nil\n  def with[U >: T](x: U) -> Array[U] = [x]\n  private def keep(x: T) -> Void = nil\nend");
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
    ok("def f(&b: ((Int) -> Void)?) -> Void\n  b&.call(1)\nend\nf\nf { |x| p x }");
    err(
        "def f(&b: ((Int) -> Void)?) -> Void\n  yield 1\nend",
        "`yield` cannot run an optional block",
    );
    err(
        "def f(&b: ((Int) -> Void)?) -> Void\n  b.call(1)\nend",
        "Nil",
    );
    err(
        "def f(&b: (Int) -> Void) -> Void\n  b.call(1)\nend\nf",
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
    err("class Cell[T]\n  var @v: T\n  def initialize(v: T)\n    @v = v\n  end\n  def set(v: T) -> Void\n    @v = v\n    nil\n  end\nend\ndef g -> Int\n  arr = []\n  b = arr[0]?\n  case b\n  in Cell(v:)\n    b.set(\"str\")\n  else\n  end\n  arr = arr.push(Cell.new(5))\n  1\nend", "cannot deconstruct a value whose type is not yet known");
    err("data H[A] = (f: (A) -> Int)\ndef g -> Int\n  arr = []\n  case arr[0]?\n  in H(f)\n    f.call(\"oops\")\n  else\n  end\n  arr = arr.push(H.new(->(x: Int) { x + 1 }))\n  1\nend", "cannot deconstruct a value whose type is not yet known");
    // Nor one with a bounded parameter; a recursive `data` is fine.
    err("module Comb\n  abstract def weight -> Int\nend\ndata Acc[T <: Comb](x: T)\n  def plus(y: T) -> Int = x.weight + y.weight\nend\ndata C[A] = (d: Acc[A])\ndef g -> Int\n  arr = []\n  case arr[0]?\n  in C(d)\n    p d.plus(\"str\")\n  else\n  end\n  1\nend", "cannot deconstruct a value whose type is not yet known");
    err("module Comb\n  abstract def weight -> Int\nend\ndata Acc[T <: Comb](x: T)\n  def plus(y: T) -> Int = x.weight + y.weight\nend\ndef g -> Int\n  arr = []\n  case arr[0]?\n  in Acc(x) => a\n    p a.plus(\"str\")\n  else\n  end\n  1\nend", "cannot deconstruct a value whose type is not yet known");
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
    err("class Box[T]\n  var @v: T\n  def initialize(@v: T); end\n  def set(v: T) -> Void\n    @v = v\n    nil\n  end\nend\ndef f(o: Object)\n  case o\n  in Box\n    o.set(\"str\")\n  else\n  end\nend", "undefined method `set` for Object");
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
    err("class Box[T]\n  var @v: T\n  def initialize(@v: T); end\n  def set(v: T) -> Void\n    @v = v\n    nil\n  end\nend\ndef poke[T](x: T) -> Void\n  case x\n  in Box then x.set(\"str\")\n  else\n  end\n  nil\nend", "undefined method `set` for T");
    ok("def f(o: Object) -> Int\n  case o\n  when Hash then o.size\n  when Range then 1\n  else 0\n  end\nend");
    ok("def b[T](x: T) -> Int\n  case x\n  when Hash then x.size\n  when Set then x.size\n  else 0\n  end\nend");
    // Nor `== nil` a value whose class (or a subclass) defines `==`.
    err("class Weird\n  def ==(o: Object) -> Bool = true\nend\ndef f(x: Weird | Int) -> Int\n  if x == nil\n    n: Nil = x\n    1\n  else\n    0\n  end\nend", "cannot assign Weird | Int to `n` of type Nil");
    ok("class Plain\nend\ndef f(x: Plain?) -> Int\n  if x == nil\n    0\n  else\n    x.hash\n  end\nend");
    err("extension Nil\n  def ==(other: Object) -> Bool = false\nend\ndef g(x: Int?) -> Int\n  if x == nil\n    0\n  else\n    x + 1\n  end\nend", "undefined method `+` for Nil");
    err("class Foo\n  def !=(o: Object) -> Bool = false\nend\ndef takes(n: Nil) -> Int = 0\ndef f(x: Foo?) -> Int\n  if x != nil\n    1\n  else\n    takes(x)\n  end\nend", "expects Nil but found Foo?");
    ok("def tup(t: [Int, String]?) -> Int\n  if t == nil\n    0\n  else\n    t[0]\n  end\nend\ndef pr(f: ((Int) -> Int)?) -> Int\n  if !f.nil?\n    f.(1)\n  else\n    0\n  end\nend\ndef par[T](x: T?) -> T\n  if x.nil?\n    raise \"none\"\n  else\n    x\n  end\nend");
    // Only types that cannot be subclassed narrow by `==` (a subclass,
    // in a file compiled separately, may define it): not a class, a
    // module, a procedure or a type parameter.
    err("class Plain\n  def foo -> Int = 1\nend\ndef f(x: Plain?) -> Int\n  if x == nil\n    0\n  else\n    x.foo\n  end\nend", "undefined method `foo` for Nil");
    err(
        "def par[T](x: T?) -> T\n  if x == nil\n    raise \"none\"\n  else\n    x\n  end\nend",
        "returns T but its body has type T?",
    );
    ok("data P = (x: Int)\nenum E = A | B(n: Int)\ndef f(p: P?, e: E?) -> Int\n  if p == nil || e == nil\n    0\n  else\n    p.x + (e == E::A ? 1 : 2)\n  end\nend");
    // `?v | Int` used by an operator or under a bound is an `Int`.
    ok("def g -> Int\n  arr = []\n  y = arr[0]? || 2\n  y += 1\n  xs = [y, 2].sort\n  arr = arr.push(4)\n  xs[0]\nend");
    // A bound may name the class's parameters.
    ok("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Num(n: Int)\n  include Addable[Num]\n  def add(o: Num) -> Num = Num.new(n + o.n)\nend\ndata Acc[T <: Addable[T]](x: T)\n  def twice -> T = x.add(x)\nend\np Acc.new(Num.new(2)).twice");
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
    err("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Acc[T <: Addable[T]] = (x: T)\ndef f[U](u: U) -> U = Acc[U].new(u).x", "type argument U for `T` of `Acc` must be Addable[U]");
    // Bounds are checked in annotations too.
    err("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Acc[T <: Addable[T]] = (x: T)\nclass Other\nend\np Acc.new(Other.new)", "type argument Other for `T` of `Acc` must be Addable[Other]");
    err("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Acc[T <: Addable[T]] = (x: T)\nclass Other\nend\nx: Acc[Other]? = nil", "type argument Other for `T` of `Acc` must be Addable[Other]");
    err("module Addable[T]\n  abstract def add(o: T) -> T\nend\ndata Acc[T <: Addable[T]] = (x: T)\nclass Other\nend\ndef f(a: Acc[Other]) -> Int = 0", "type argument Other for `T` of `Acc` must be Addable[Other]");
    // And in a superclass and the modules included and extended, whose
    // arguments may be the class's parameters, meeting a bound their
    // own bounds imply.
    let shape = "abstract class Shape\n  def name -> String = \"s\"\nend\nclass Sq < Shape\nend\nclass H[T <: Shape]\n  def k(x: T) -> String = x.name\nend\n";
    err(
        &format!("{shape}class G[U] < H[U]\nend"),
        "type argument U for `T` of `H` must be Shape",
    );
    err(
        &format!("{shape}class J < H[Int]\nend"),
        "type argument Int for `T` of `H` must be Shape",
    );
    ok(&format!(
        "{shape}class G[U <: Shape] < H[U]\nend\nclass S2 < H[Sq]\nend\np G[Sq].new.k(Sq.new)"
    ));
    err("class Model\n  def id -> Int = 1\nend\nmodule Gen[T <: Model]\n  def run(x: T) -> Int = x.id\nend\nclass NotModel\n  extend Gen[NotModel]\nend", "type argument NotModel for `T` of `Gen` must be Model");
    err(
        "class Model\nend\nmodule Gen[T <: Model]\nend\nclass M2\n  include Gen[String]\nend",
        "type argument String for `T` of `Gen` must be Model",
    );
    // An extension's included modules, and the bounds written on type
    // parameters, meet theirs too.
    err("class Model\nend\nmodule Gen[T <: Model]\nend\nclass NotModel\nend\nextension NotModel\n  include Gen[NotModel]\nend", "type argument NotModel for `T` of `Gen` must be Model");
    err(
        &format!("{shape}class G[U <: H[Int]]\nend"),
        "type argument Int for `T` of `H` must be Shape",
    );
    err(
        &format!("{shape}def f[V <: H[Int]](x: V) -> Int = 0"),
        "type argument Int for `T` of `H` must be Shape",
    );
    // A parameter is Shareable when a bound makes every type it admits
    // Shareable: one that promises it (`Int`, a module including
    // `Shareable`), a Shareable `data` type or enum, a parameter that is.
    let boxed = "class Box[T <: Shareable]\nend\n";
    ok(&format!("{boxed}module Sendable\n  include Shareable\nend\nclass B3[U <: Sendable] < Box[U]\nend\nclass B4[U <: Int] < Box[U]\nend\ndata D = (x: Int)\nclass B9[U <: D] < Box[U]\nend\nenum E = A | B\nclass B10[U <: E] < Box[U]\nend\nclass B11[V <: Shareable, U <: V] < Box[U]\nend\ndef g[U <: Int](x: U) -> Int\n  c = Channel[U].new\n  0\nend"));
    err(
        &format!("{boxed}class M\n  var @x: Int = 0\nend\nclass B7[U <: M] < Box[U]\nend"),
        "type argument U for `T` of `Box` must be Shareable",
    );
    // A class Shareable without promising it may have a subclass that is not.
    err(
        &format!("{boxed}class P\n  @x: Int = 1\nend\nclass B8[U <: P] < Box[U]\nend"),
        "type argument U for `T` of `Box` must be Shareable",
    );
    ok("class Cmp[X <: Cmp[X]]\nend\nclass K < Cmp[K]\nend\nmodule Ord[T <: Comparable[T]]\nend\nclass V\n  include Comparable[V]\n  include Ord[V]\n  def <=>(o: V) -> Int = 0\nend");
    // A `T` narrowed by a test is still a `T`.
    ok("def keep[T](x: T) -> T\n  if x.is_a?(String)\n    p x.upcase\n    return x\n  end\n  x\nend");
    ok("data Pair[A, B] = (a: A, b: B)\ndef f[T](x: T) -> T\n  case x\n  in Array then p x.size\n  in Pair(a, b) then p a\n  else\n  end\n  x\nend");
    // It does not leave the branch through inferred types.
    err("class Box[T]\n  def initialize(@v: T); end\n  @v: T\n  def s -> String?\n    @v.is_a?(String) ? @v : nil\n  end\n  def steal(b: Box[String]) -> T? = b.s\nend", "method `steal` returns T? but its body has type String?");
    ok("def f[T](x: T, z: T) -> Array[T]\n  ys = []\n  if x.is_a?(String)\n    ys = ys.push(x)\n  end\n  ys = ys.push(z)\n  ys\nend");
    ok("def f(t: [Int, String] | Array[Int]) -> Int = 1\np f([1, 2])");
    ok("def f[T](t: [Int, String] | T) -> Int = 1\np f([1, 2])");
    // A value of a module type has Object's methods.
    ok("module Named\n  def name -> String = \"n\"\nend\ndef md(x: Named?) -> String\n  if x.nil?\n    \"nil\"\n  else\n    x.name + x.to_s\n  end\nend");
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
    // `equal?` is identity.
    err(
        "class P\n  def equal?(o: Object) -> Bool = true\nend",
        "`equal?` cannot be redefined: it is identity",
    );
    err(
        "extension String\n  def equal?(o: Object) -> Bool = true\nend",
        "`equal?` cannot be redefined",
    );
    err("data Q = (equal?: Bool)", "`equal?` cannot be redefined");
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
        "class C\n  var @r: (() -> Void)? = nil\n  def set(r: () -> Void) -> Void\n    @r = r\n    nil\n  end\n  def to_s -> String\n    if r = @r\n      r.call\n    end\n    \"c\"\n  end\nend\ndef f(x: Int | String, c: C) -> Int\n  c.set(-> { x = 5; nil })\n  x = \"s\"\n  if x.is_a?(String)\n    s = \"#{c}\"\n    p x.upcase\n  end\n  0\nend",
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
        "def keep(&blk: () -> Void) -> Void = nil\ndef fwd(&: () -> Void) -> Void = keep(&)",
        "cannot be passed to `keep`, which may keep it",
    );
    err(
        "def wrap(&: () -> Void) -> (() -> Void) = -> { yield }",
        "`yield` in a closure that may run later",
    );
    ok("def anon(&: () -> Void) -> Void = yield\ndef fwd(&: () -> Void) -> Void = anon(&)");
    // Whether a method keeps its block is part of its signature.
    err(
        "class A\n  def run(&: () -> Void) -> Void = yield\nend\nclass B < A\n  def run(&blk: () -> Void) -> Void = nil\nend",
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
        "def f(x: Int | String, r: () -> Void = -> { x = 5; nil }) -> Int\n  if x.is_a?(String)\n    r.call\n    p x.upcase\n  end\n  0\nend",
        "undefined method `upcase` for Int",
    );
    // `Channel.select`'s blocks run after its block returns.
    err(
        "def f(x: Int | String) -> Void\n  Channel.select do |s|\n    if x.is_a?(String)\n      s.default { p x.upcase; nil }\n    end\n    x = 5\n  end\nend",
        "undefined method `upcase` for Int",
    );
    // An immutable field cannot be assigned by a closure that may run
    // after `initialize`.
    err(
        "class C\n  @x: Int\n  @r: () -> Void\n  def initialize\n    @x = 1\n    @r = -> { @x = 5; nil }\n  end\nend",
        "a closure that may run later, after `initialize`, cannot assign it",
    );
    // The method's block cannot go to a task unchecked.
    err(
        "def later(&: () -> Void) -> Task[Nil] = Task.spawn(&)",
        "which runs it in a task",
    );
    // A closure that may run later is run after others made later in the
    // body, which may have assigned the local.
    err(
        "def f(x: Int | String) -> Void\n  g = -> { nil }\n  a = -> { if x.is_a?(String)\n    g.call\n    p x.upcase\n  end\n  nil }\n  g = -> { x = 5; nil }\n  a.call\nend",
        "undefined method `upcase` for Int",
    );
    // In `initialize`, a field's narrowing does not reach a closure that
    // may run after the field is assigned again; nor may one assign it,
    // by any form of assignment.
    err(
        "class C\n  @x: Int | String\n  @r: () -> Void\n  def initialize\n    @x = \"s\"\n    @r = -> { nil }\n    if @x.is_a?(String)\n      @r = -> { p @x.upcase; nil }\n    end\n    @x = 5\n  end\nend",
        "undefined method `upcase` for Int",
    );
    err(
        "class C\n  @n: Int\n  @r: () -> Void\n  def initialize\n    @n = 1\n    @r = -> { @n += 1; nil }\n  end\nend",
        "field `@n` is immutable",
    );
    // An overload or a constructor is not an override.
    ok("class P\n  def run(&: () -> Void) -> Void = yield\nend\nclass Q < P\n  def run(n: Int, &blk: () -> Void) -> Void = nil\nend");
    ok("class C\n  def initialize(&: () -> Void)\n    yield\n  end\nend\nclass D < C\n  def initialize(&blk: () -> Void)\n    super(&blk)\n  end\nend");
    // Nor can an extension's method keep a block the one it hides yields.
    err(
        "def keep(b: () -> Void) -> Void = nil\nclass A\n  def run(&: () -> Void) -> Void = yield\nend\nclass C < A\nend\nextension C\n  def run(&blk: () -> Void) -> Void = keep(blk)\nend",
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

#[test]
fn calls_a_class_test_cannot_choose_are_errors() {
    // Members of one class differing only in type arguments.
    err(
        "extension Array[T <: Int]\n  def desc -> String = \"ints\"\nend\nextension Array[T <: String]\n  def desc -> String = \"strs\"\nend\ndef pk(i: Int) -> Array[Int] | Array[String] = i > 0 ? [1] : [\"a\"]\nputs pk(1).desc",
        "cannot tell at run time which `desc` to call for Array[Int] and Array[String]: extension Array[T <: Int]#desc or extension Array[T <: String]#desc",
    );
    // Overloads chosen by an argument's type, in a block checked per type.
    err(
        "class Foo\n  def sub(o: Int) -> Int = 1\n  def sub(o: String) -> Int = 2\nend\ndef pk(i: Int) -> Array[Int] | Array[String] = i > 0 ? [1] : [\"a\"]\nf = Foo.new\npk(1).each { |x| p f.sub(x) }",
        "cannot tell at run time which `sub` to call on Foo: Foo#sub(Int) or Foo#sub(String)",
    );
    // A module and an unrelated member: a value may be both.
    err(
        "module M\nend\nclass A\nend\nextension A\n  def ext -> String = \"A\"\nend\nextension M\n  def ext -> String = \"M\"\nend\ndef pk(i: Int) -> A | M = A.new\nputs pk(1).ext",
        "cannot tell at run time which `ext` to call for A and M",
    );
    err(
        "extension Array[T <: Int]\n  def to_s -> String = \"ints\"\nend\ndef pk(i: Int) -> Array[Int] | Array[String] = i > 0 ? [1] : [\"a\"]\nputs \"#{pk(1)}\"",
        "cannot tell at run time which `to_s` the interpolation calls for Array",
    );
    // A class and its subclass, or unrelated classes: tested in order.
    ok("class Foo\nend\nclass Sub < Foo\nend\nextension Foo\n  def ext -> String = \"F\"\nend\nextension Sub\n  def ext -> String = \"S\"\nend\ndef pk(i: Int) -> Array[Foo] | Array[Sub] = [Sub.new]\nclass Box[T]\n  @v: T\n  def initialize(@v: T); end\n  def each(&blk: (T) -> Void) -> Void\n    blk.call(@v)\n    nil\n  end\nend\ndef pb(i: Int) -> Array[Foo] | Box[Sub] = Box.new(Sub.new)\npb(1).each { |x| puts x.ext }");
    // Called by name, natives' overloads and the value's own methods are
    // found; a check thrown away (an overload that does not match)
    // leaves nothing behind.
    ok("def pk(i: Int) -> Array[Int] | Array[Float] = i > 0 ? [1, 2] : [1.5]\np pk(1).map { |x| x + 1 }\npk(0).each { |x| p(1 + x) }");
    ok("module Shape\n  abstract def area -> Float\nend\nclass Sq\n  def area -> Float = 4.0\nend\nclass C\n  include Shape\n  def area -> Float = 3.0\nend\ndef pk(i: Int) -> Sq | Shape = i > 0 ? Sq.new : C.new\np pk(1).area");
    ok("class Foo\n  def sub(o: Int) -> Int = 1\n  def sub(o: String) -> Int = 2\nend\nclass R\n  def run(&blk: (String) -> String) -> String = blk.call(\"s\")\n  def run(&blk: (Int) -> Int) -> Int = blk.call(3)\nend\nf = Foo.new\np R.new.run { |x| f.sub(x); 5 }");
    // Overloads split between a class and its superclass: by name, the
    // subclass's is found for every argument.
    err(
        "class A\n  def foo(o: Int) -> String = \"i\"\nend\nclass B < A\n  def foo(o: String) -> String = o\nend\ndef pk(i: Int) -> Array[Int] | Array[String] = i > 0 ? [1] : [\"a\"]\nb = B.new\npk(1).each { |x| puts b.foo(x) }",
        "cannot tell at run time which `foo` to call on B: A#foo(Int) or B#foo(String)",
    );
    // A compound assignment's reader from two extensions.
    err(
        "class A\nend\nclass B\nend\nextension A\n  def w -> Int = 1\n  def w=(x: Int) -> Int = x\nend\nextension B\n  def w -> Int = 2\n  def w=(x: Int) -> Int = x\nend\ndef pk(i: Int) -> Array[A] | Array[B] = i > 0 ? [A.new] : [B.new]\npk(1).each { |o| o.w += 1 }",
        "cannot tell at run time which `w` to call: extension A#w or extension B#w",
    );
    // A method body first checked within a check thrown away keeps what
    // it found (its errors too).
    err(
        "class R\n  def run(&blk: (String) -> String) -> String = blk.call(\"s\")\n  def run(&blk: (Int) -> Int) -> Int = blk.call(3)\nend\ndef caller -> Int\n  R.new.run { |x| helper; x + 1 }\nend\ndef helper\n  y: Int = \"oops\"\n  1\nend\np caller",
        "cannot assign String to `y` of type Int",
    );
    // A module and an unrelated class with their own methods: tested in
    // order, each value finds its own (overloads included).
    ok("module M\n  abstract def foo(o: Int) -> String\nend\nclass A\n  def foo(o: String) -> String = \"A-str\"\n  def foo(o: Int) -> String = \"A-int\"\nend\nclass C\n  include M\n  def foo(o: Int) -> String = \"C-int\"\nend\ndef pk(i: Int) -> A | M = i > 0 ? A.new : C.new\nputs pk(1).foo(1)");
    // User operator overloads in a compound assignment to an attribute.
    err(
        "class V\n  def +(o: Int) -> V = self\n  def +(o: String) -> V = self\nend\nclass H\n  var @v: V = V.new\n  attr_accessor :v\nend\ndef pk(i: Int) -> Array[Int] | Array[String] = i > 0 ? [1] : [\"a\"]\nh = H.new\npk(1).each { |x| h.v += x }",
        "cannot tell at run time which `+` to call",
    );
    // Overloaded `initialize` chosen by an argument's type.
    err(
        "class Foo\n  @s: String\n  def initialize(o: Int)\n    @s = \"int\"\n  end\n  def initialize(o: String)\n    @s = \"str\"\n  end\nend\ndef pk(i: Int) -> Array[Int] | Array[String] = i > 0 ? [1] : [\"a\"]\npk(1).each { |x| Foo.new(x) }",
        "cannot tell at run time which `initialize` to call",
    );
    // A type's own `&&` for one check of a block, the built-in for another.
    err(
        "class Ma\n  def &&(&blk: () -> Bool) -> String = \"Ma&&\"\nend\nclass Mb\nend\ndef u(i: Int) -> Array[Ma] | Array[Mb] = [Ma.new]\nu(0).each { |x| p(x && true) }",
        "cannot tell at run time whether `&&` is a method of",
    );
    // `&:name` resolved to two extensions' methods.
    err(
        "class Ma\nend\nclass Mb\nend\nextension Ma\n  def hi -> String = \"ma\"\nend\nextension Mb\n  def hi -> String = \"mb\"\nend\ndef u(i: Int) -> Array[Ma] | Array[Mb] = [Ma.new]\np u(0).map(&:hi)",
        "cannot tell at run time which `hi` `&:hi` calls",
    );
    // A module and a class that includes it.
    ok("module M\nend\nclass A\n  include M\nend\nextension A\n  def ext -> String = \"A\"\nend\nextension M\n  def ext -> String = \"M\"\nend\ndef pk(i: Int) -> A | M = A.new\nputs pk(1).ext");
}

#[test]
fn std_exports_are_the_top_level_declarations() {
    let scanned: Vec<(&str, Vec<String>)> = quarz_types::load::std_exports().to_vec();
    assert_eq!(scanned, quarz_types::load::std_exports_parsed());
}

#[test]
fn equality_takes_an_object() {
    // The runtime calls a class's own `==` by name with any value, so a
    // narrower parameter would receive a value not of its type.
    err(
        "class P\n  def ==(o: P) -> Bool = true\nend",
        "`==` takes one parameter of type `Object`",
    );
    err(
        "class P\n  def !=(o: P) -> Bool = true\nend",
        "`!=` takes one parameter of type `Object`",
    );
    err(
        "class P\n  def ==(o: Object, strict: Bool = false) -> Bool = true\nend",
        "`==` takes one parameter of type `Object`",
    );
    err(
        "extension String\n  def ==(o: String) -> Bool = true\nend",
        "`==` takes one parameter of type `Object`",
    );
    err(
        "class P\n  def same(o: P) -> Bool = true\n  alias == same\nend",
        "`==` takes one parameter of type `Object`",
    );
    ok("class P\n  def ==(o: Object) -> Bool = o.is_a?(P)\n  def !=(o: Object) -> Bool = !(self == o)\nend");
    // A class method or another name is free.
    ok("class P\n  def self.==(o: P) -> Bool = true\n  def eq(o: P) -> Bool = true\nend");
}

#[test]
fn what_runs_deinitialize_is_not_copied() {
    // An exception is copied when raised while referred to.
    err(
        "class E < StandardError\n  def deinitialize -> Void\n  end\nend",
        "an exception class cannot define `deinitialize`",
    );
    err(
        "module M\n  def deinitialize -> Void\n  end\nend\nclass E < StandardError\n  include M\nend",
        "`E` cannot include `M`, which defines `deinitialize`",
    );
    // A subclass reports nothing of its own.
    let src = "module M\n  def deinitialize -> Void\n  end\nend\nclass E < StandardError\n  include M\nend\nclass F < E\nend";
    assert!(!diagnostics(src)
        .iter()
        .any(|e| e.contains("`F` cannot include")));
    // Data types, enums and built-in value classes are copied too.
    err(
        "module M\n  def deinitialize -> Void\n  end\nend\ndata D(v: Int)\n  include M\nend",
        "`D` cannot include `M`",
    );
    err(
        "module M\n  def deinitialize -> Void\n  end\nend\nenum Light = Red | Green\nextension Light\n  include M\nend",
        "`Light` cannot include `M`",
    );
    err(
        "module M\n  def deinitialize -> Void\n  end\nend\nextension String\n  include M\nend",
        "`String` cannot include `M`",
    );
    // Through a module the prelude's copied classes include (`Exception`
    // includes `Shareable`).
    err(
        "module M\n  def deinitialize -> Void\n  end\nend\nextension Shareable\n  include M\nend",
        "`Shareable` cannot include `M`",
    );
    // A copy would release what the original owns again.
    err(
        "class R\n  def deinitialize -> Void\n  end\nend\nR.new.dup",
        "cannot dup R",
    );
    err(
        "class R\n  def deinitialize -> Void\n  end\nend\nclass S < R\nend\nS.new.dup",
        "cannot dup S",
    );
    err(
        "class R\n  def deinitialize -> Void\n  end\n  def again -> R = dup\nend",
        "cannot dup R",
    );
    ok("class P\nend\nP.new.dup\nclass E < StandardError\nend\nE.new(\"e\").dup");
}

#[test]
fn eq_comes_with_hash() {
    // Hash keys and Set members are compared by both.
    warns(
        "class P\n  def ==(o: Object) -> Bool = true\nend",
        "`P` defines `==` but not `hash`",
    );
    warns(
        "class P\n  def hash -> Int = 0\nend",
        "`P` defines `hash` but not `==`",
    );
    no_warnings("class P\n  def ==(o: Object) -> Bool = true\n  def hash -> Int = 0\nend");
}

#[test]
fn type_of_classes() {
    // A class written in an expression is a `Type[C]`; `Type[T]` takes a
    // class argument and binds `T` to the class.
    ok("def name_of[T](t: Type[T]) -> String = t.name\np name_of(Int), name_of(Array[Int])");
    ok("t: Type[Int] = Int\np t.name, t <= Comparable, t == Int");
    // Covariant: `Type[Sub]` is a `Type[Base]`, and `Class` is `Type[Object]`.
    ok("class A; end\nclass B < A; end\nt: Type[A] = B\nc: Class = B\nts: Array[Type[A]] = [A, B]\np ts.map(&:name)");
    err(
        "t: Type[String] = Int",
        "cannot assign Type[Int] to `t` of type Type[String]",
    );
    // The arguments count: `Type[Array[Int]]` is not a `Type[Array[String]]`.
    err(
        "t: Type[Array[String]] = Array[Int]",
        "cannot assign Type[Array[Int]] to `t` of type Type[Array[String]]",
    );
    ok("t: Type[Array[Object]] = Array[Int]");
    // Only a class or a type parameter.
    err(
        "t: Type[Int | String] = Int",
        "`Type[Int | String]`: the argument must be a class or a type parameter",
    );
    // `Type` alone is `Type[Object]`.
    ok("t: Type = Int\np t.name");
    err(
        "t: Type[Int, String] = Int",
        "`Type` takes at most 1 type argument",
    );
    // The class methods of the bound, with `Self` the parameter.
    ok("class M\n  def initialize; end\n  def self.label -> String = \"m\"\n  def self.make -> Self = new\nend\nclass N < M; end\ndef label_of[T <: M](t: Type[T]) -> String = t.label\ndef make[T <: M](t: Type[T]) -> T = t.make\nn: N = make(N)\np label_of(N)");
    err(
        "def label_of[T](t: Type[T]) -> String = t.label",
        "undefined method `label`",
    );
}

#[test]
fn new_only_where_the_class_is_written() {
    ok("class P\n  def initialize(x: Int); end\nend\nP.new(1)\nArray[Int].new");
    ok("class P\n  def initialize(x: Int); end\n  def self.make -> Self = new(1)\n  def self.make2 -> Self = self.new(1)\nend");
    // A `Type[P]` value may be a subclass with another `initialize`.
    err(
        "class P\n  def initialize(x: Int); end\nend\nk = P\nk.new(1)",
        "cannot call `new` on a `Type[P]` value",
    );
    err(
        "class P\n  def initialize(x: Int); end\n  def copy -> P = self.class.new(1)\nend",
        "cannot call `new` on a `Type[Object]` value",
    );
    err(
        "def make[T](t: Type[T]) -> T = t.new",
        "cannot construct a `Type[T]`",
    );
}

#[test]
fn class_values_in_tests_and_patterns() {
    // Only "a class" is testable at run time: not the class's arguments.
    err(
        "def g(y: Object) -> Bool = y.is_a?(Type[Int])",
        "cannot check at run time that a value of type Object is a Type[Int]",
    );
    ok("def g(y: Object) -> Bool = y.is_a?(Class)\ndef g2(y: Object) -> Bool = y.is_a?(Type)\ndef g3(y: Object) -> Class? = y.as?(Type)\ndef h(y: Object) -> String = case y\n  in Type then y.name\n  else \"no\"\nend");
    // The bound's class methods come before `Type`'s own, as a class
    // object's do (and as the run time dispatches).
    ok("class P\n  def self.name -> String = \"p\"\nend\ndef f[T <: P](t: Type[T]) -> String = t.name");
    // `Class` is a type alias, so a pattern or `when` names `Type`.
    err(
        "k = 1.class\ncase k\nin Class then 1\nend",
        "`Class` is a type alias of `Type[Object]`, not a class: write `Type`",
    );
    err(
        "k = 1.class\ncase k\nwhen Class then 1\nend",
        "`Class` is a type alias, not a value; the class of class values is `Type` (`when Type`, `in Type`)",
    );
    // `raise` takes a `Type[E]` value, as it took a `Class`.
    // A class value may be a subclass whose `initialize` takes other
    // arguments: raise the class by name (docs/01 §12).
    err(
        "def fail(k: Type[StandardError], m: String) -> Nothing\n  raise k, m\nend",
        "cannot raise a class value",
    );
    err(
        "def fail[E <: Exception](k: Type[E]) -> Nothing\n  raise k\nend",
        "cannot raise",
    );
}

/// `static def` and class bodies' `static` statements (docs/14): what
/// the checker accepts and rejects; running them is quarz-cli's.
#[test]
fn static_declarations() {
    // A `static` class method's `self` is the class's `Meta::ClassDef`,
    // a `Type[Self]` with reflection; the body may call the class's own
    // class methods and `Type`'s.
    ok("class Model\n  def self.table -> String = \"t\"\n  static def self.describe -> String = name + table + fields.size.to_s + method?(:x).to_s\nend");
    // A statement in a class body calls a `static def` class method of a
    // file loaded earlier; here there is none, so of this file: an error
    // that names the rule, not \"only declarations\".
    err(
        "class Model\n  static def self.has_many(t: Type[Object]) -> Void; end\nend\nclass Post < Model\n  has_many Post\nend",
        "`has_many` is a `static def` of this file",
    );
    err(
        "class Model\n  def self.plain -> Void; end\nend\nclass Post < Model\n  plain\nend",
        "a statement in a class body must call a `static def` class method; `plain` is not one",
    );
    err(
        "class P\n  1 + 1\nend",
        "only declarations are allowed in a class body",
    );
    // Reflection is compile-time only: not from ordinary code.
    err("p Int.fields", "`fields` runs at compile time only");
    err(
        "def f[T](t: Type[T]) -> Bool = t.method?(:x)",
        "`method?` runs at compile time only",
    );
    // A `static def` that does not reach `Meta` is also an ordinary
    // method, callable at run time.
    ok("class M\n  static def self.twice(x: Int) -> Int = x * 2\nend\np M.twice(2)");
    // `static(...)` takes a call of a `static def` (docs/14 §8).
    err(
        "x = static(1)",
        "`static(...)` takes a call of a `static def`",
    );
    let parsed = quarz_syntax::parse("class A\n  static abstract def x -> Int\nend");
    assert!(
        parsed
            .diagnostics
            .iter()
            .any(|d| d.message.contains("a `static def` cannot be abstract")),
        "{:?}",
        parsed.diagnostics
    );
    // `Meta::ClassDef[X]` is a `Type[X]`.
    ok("class Model\n  static def self.me -> Type[Model] = self\n  static def self.named -> String = self.name\nend");
    // `Type` is not for subclassing outside the prelude.
    err("class K < Type[Int]; end", "cannot inherit from `Type`");
}

#[test]
fn narrowing_holds_only_where_the_test_succeeded() {
    // A `Box[T]` tested with a subclass that fixes its argument
    // (`IntBox < Box[Int]`): `T` may be `Int`, so the branch is a live
    // `IntBox`, checked.
    let boxes = "class Box[T]\n  @v: T\n  def initialize(@v: T)\n  end\nend\nclass IntBox < Box[Int]\nend\n";
    err(
        &format!("{boxes}class W[T]\n  def f(b: Box[T]) -> Int\n    if b.is_a?(IntBox)\n      s: String = b\n      return 1\n    end\n    0\n  end\nend"),
        "cannot assign IntBox to `s` of type String",
    );
    ok(&format!("{boxes}class W[T]\n  def f(b: Box[T]) -> Int\n    if b.is_a?(IntBox)\n      i: IntBox = b\n      return 1\n    end\n    0\n  end\nend"));
    // An existing local an `in` test binds holds the binding's type only
    // where it matched: elsewhere it keeps its old one (a failed match puts
    // it back, docs/01 §11).
    let p = "data P = (a: Int, b: Int)\n";
    err(
        &format!("{p}def h(p: P | Int, y: Int | String) -> Int\n  return 0 unless y.is_a?(String)\n  if p in P(y, 9)\n    return 1\n  end\n  y + 1\nend"),
        "expects String but found Int",
    );
    ok(&format!("{p}def h(p: P | Int, y: Int | String) -> Int\n  return 0 unless y.is_a?(String)\n  if p in P(y, 9)\n    return y + 1\n  end\n  0\nend"));
    // A pattern that rebinds its subject leaves it the binding's type.
    let l = "enum L\n  variant Cons(h: Int, tail: L)\n  variant E\nend\n";
    err(
        &format!("{l}def f(l: L) -> Int\n  case l\n  in L::Cons(_, l) then l.h\n  in L::E then 0\n  end\nend"),
        "undefined method `h` for L",
    );
    err(
        &format!("{l}def f(l: L) -> Int\n  if l in L::Cons(_, l)\n    return l.h\n  end\n  0\nend"),
        "undefined method `h` for L",
    );
    ok(&format!("{l}def f(l: L) -> Int\n  case l\n  in L::Cons(_, L::Cons => l) then l.h\n  in L::Cons(h, _) then h\n  in L::E then 0\n  end\nend"));
    // Without a rebinding arm before, the subject narrows as usual.
    ok(&format!("{l}def f(l: L) -> Int\n  case l\n  in L::Cons(h, _) then h + l.h\n  in L::E then 0\n  end\nend"));
    // In `case ... in`, the names an arm's pattern binds are its own: a
    // failed arm leaves the outer `y` as it was (docs/01 §11).
    let ys =
        "def h(p: P | Int, y: Int | String) -> Int\n  return 0 unless y.is_a?(String)\n  case p\n";
    for rest in [
        "  in P(y, 9) then 1\n  in _ then y.size\n  end\nend",
        "  in P(y, 9) then 1\n  else y.size\n  end\nend",
        "  in P(y, _) if y > 100 then 1\n  in _ then y.size\n  end\nend",
        "  in P(y, 9) then return 1\n  in _ then 0\n  end\n  y.size\nend",
    ] {
        ok(&format!("{p}{ys}{rest}"));
    }
    // A guard that assigns an outer local does change it.
    err(
        &format!("{p}{ys}  in P(_, _) if (y = 5) == 0 then 1\n  in _ then y.size\n  end\nend"),
        "undefined method `size` for Int",
    );
    // A guard that only tests a field keeps what it was narrowed to.
    ok(&format!("{p}class C\n  @x: Int | String | Nil\n  def initialize\n    @x = 1\n  end\n  def takes(v: Int | String) -> Int = 1\n  def k(p: P | Int) -> Int\n    return 0 if @x.nil?\n    case p\n    in P(_, _) if @x.is_a?(String) then 1\n    in _ then takes(@x)\n    end\n  end\nend"));
    // A field a failing guard assigned.
    err(
        &format!("{p}class C\n  @x: Int?\n  def initialize(p: P | Int)\n    @x = 1\n    case p\n    in P(_, _) if (@x = nil).nil? && false then puts 1\n    in _ then puts @x + 1\n    end\n  end\nend"),
        "undefined method `+` for Nil",
    );
    // An arm's own `x` or `l` is not the subject: later arms narrow it.
    ok("def h(x: Int | Array[Int]) -> Int\n  case x\n  in [x, 1] then 1\n  in Array then x.size\n  in Int then 0\n  end\nend");
    ok(&format!("{l}def f(l: L) -> Int\n  case l\n  in L::Cons(_, l) if false then 0\n  in L::Cons then l.h\n  in L::E then 0\n  end\nend"));
}

#[test]
fn rescue_and_raise_build_what_they_say() {
    // `retry` belongs directly in the clause.
    err(
        "class Box\n  def once(&: () -> Void) -> Nil\n    yield\n    nil\n  end\nend\ndef f -> Int\n  begin\n    raise ArgumentError, \"x\"\n  rescue ArgumentError\n    Box.new.once do\n      retry\n    end\n  end\n  0\nend",
        "`retry` outside of a rescue clause",
    );
    err(
        "def f -> Int\n  begin\n    raise ArgumentError, \"x\"\n  rescue ArgumentError\n    -> { retry }.call\n  end\n  0\nend",
        "`retry` outside of a rescue clause",
    );
    // `raise K, m` builds `K.new(m)`: its `initialize` takes one String.
    err(
        "class E < StandardError\n  @code: Int\n  def initialize(@code: Int)\n    super(\"e\")\n  end\nend\ndef f -> Nothing = raise E, \"m\"",
        "`E#initialize` does not take one String",
    );
    err(
        "def f(k: Type[StandardError]) -> Nothing = raise k, \"m\"",
        "cannot raise a class value",
    );
    ok("class E < StandardError\n  @code: Int = 7\nend\ndef f -> Nothing = raise E, \"m\"\ndef g -> Nothing = raise E");
    err(
        "abstract class AE < StandardError\n  abstract def code -> Int\nend\ndef f -> Nothing = raise AE, \"x\"",
        "cannot instantiate `AE`",
    );
    err(
        "class Sn < StandardError\n  def self.new(message: String, n: Int) -> Sn = Sn.allocate_with(message)\nend\ndef f -> Nothing = raise Sn, \"r\"",
        "defines or inherits `self.new`",
    );
    ok("class Sp < StandardError\n  def initialize(message: String, *rest: Int)\n    super(message)\n  end\nend\ndef f -> Nothing = raise Sp, \"x\"");
}

#[test]
fn a_kept_closure_reads_fields_as_declared() {
    // `initialize` may assign a field after a method it calls made the
    // closure (docs/02 §6).
    let c = "class C\n  @a: Int?\n  var @f: (() -> Int)?\n  def initialize\n    @a = 1\n    @f = nil\n    make\n    @a = nil\n  end\n";
    err(
        &format!("{c}  def make -> Nil\n    if @a\n      @f = ->() -> Int {{ @a + 1 }}\n    end\n    nil\n  end\nend"),
        "undefined method `+` for Nil",
    );
    err(
        &format!("{c}  def make -> Nil\n    if @a\n      Task.spawn {{ @a + 1 }}\n    end\n    nil\n  end\nend"),
        "undefined method `+` for Nil",
    );
    // A local copy keeps it; so does a block only yielded to.
    ok(&format!("{c}  def make -> Nil\n    a = @a\n    if a\n      @f = ->() -> Int {{ a + 1 }}\n    end\n    nil\n  end\nend"));
    ok(&format!("{c}  def make -> Nil\n    if @a\n      [1].each {{ |x| p @a + x }}\n    end\n    nil\n  end\nend"));
}

#[test]
fn a_data_types_fields_keep_their_narrowing_in_closures() {
    // Only a generated constructor assigns them, before any code of the
    // type runs: a kept closure keeps their narrowing (docs/02 §6).
    ok("data D(n: Int?)\n  def later -> Int\n    if @n\n      Task.spawn { @n + 1 }.await\n    else\n      0\n    end\n  end\n  def f -> (() -> Int)?\n    if @n\n      -> { @n + 1 }\n    end\n  end\nend");
    // Not where the type has an `initialize` of its own.
    err(
        "data D2(n: Int?)\n  def initialize(n: Int?)\n    @n = n\n  end\n  def f -> (() -> Int)?\n    if @n\n      -> { @n + 1 }\n    end\n  end\nend",
        "undefined method `+` for Nil",
    );
}

#[test]
fn a_shareable_promise_holds_for_every_instance() {
    // A class that promises Shareable bounds the parameters its fields
    // use, so that every instance keeps the promise (docs/03).
    err("class Counter\n  var @n: Int = 0\n  def bump -> Int\n    @n += 1\n    @n\n  end\n  def n -> Int = @n\nend\nmodule Sendable\n  include Shareable\n  def run -> Int = 0\nend\nclass Holder[S <: Counter]\n  include Sendable\n  @y: S\n  def initialize(@y: S)\n  end\n  def run -> Int = @y.bump\nend\ndef spread(x: Sendable) -> Int\n  ts = (1..4).map { Task.spawn { s = 0; 100000.times { s = x.run }; s } }\n  ts.map(&:await).sum\nend\nk = Counter.new\nspread(Holder[Counter].new(k))\np k.n\n", "its parameter `S` may be a non-Shareable type");
    err("# A Shareable-promised class whose subclass hides a mutable object behind\n# a type parameter of its own (erased when the promise is checked).\nclass Counter\n  var @n: Int = 0\n  def bump -> Int\n    @n += 1\n    @n\n  end\n  def n -> Int = @n\nend\nclass Cell[T]\n  include Shareable\n  @x: T\n  def initialize(@x: T)\n  end\n  def run -> Int = 0\nend\nclass Sub[S <: Counter] < Cell[Int]\n  @y: S\n  def initialize(@y: S)\n    super(1)\n  end\n  def run -> Int = @y.bump\nend\ndef spread(x: Cell[Int]) -> Int\n  ts = (1..4).map do\n    Task.spawn do\n      s = 0\n      100000.times { s = x.run }\n      s\n    end\n  end\n  ts.map(&:await).sum\nend\nk = Counter.new\nspread(Sub[Counter].new(k))\np k.n\n", "its parameter `T` may be a non-Shareable type");
    ok("module Sendable\n  include Shareable\nend\nclass Holder[S <: Shareable]\n  include Sendable\n  @y: S\n  def initialize(@y: S)\n  end\nend");
    // A collection is a `Shareable` only when its elements are.
    err("n = 0\nx: Shareable = [-> { n += 1; n }]\nch = Channel[Shareable].new(1)\nch.send(x)\np 0\n", "array elements have type () -> Int but Shareable was expected");
    ok("x: Shareable = [1, 2]\ny: Shareable = {a: [\"s\"]}\np x, y");
}

#[test]
fn shareable_by_arguments_is_not_laundered() {
    // A `data` type or enum taking the promise from a module follows the
    // class rule: the module's `self` carries no arguments (docs/03).
    err("class Counter\n  var @n: Int = 0\n  def bump -> Int\n    @n += 1\n    @n\n  end\n  def n -> Int = @n\nend\nmodule Sendable\n  include Shareable\n  abstract def run -> Int\n  def me -> Sendable = self\nend\ndata D[T <: Counter](x: T)\n  include Sendable\n  def run -> Int = x.bump\nend\nk = Counter.new\ns = D[Counter].new(k).me\nts = (1..4).map do\n  Task.spawn do\n    100000.times { s.run }\n    0\n  end\nend\nts.each(&:await)\np k.n\n", "its parameter `T` may be a non-Shareable type");
    err("class Counter\n  var @n: Int = 0\n  def bump -> Int\n    @n += 1\n    @n\n  end\n  def n -> Int = @n\nend\nmodule Sendable\n  include Shareable\n  def me -> Sendable = self\nend\nenum E[T]\n  include Sendable\n  variant A(x: T)\nend\nv = E::A.new(Counter.new)\ns: Sendable = v\nt = v.me\np 1\n", "its parameter `T` may be a non-Shareable type");
    // A tuple is a `Shareable` only with Shareable elements.
    err("class Counter\n  var @n: Int = 0\n  def bump -> Int\n    @n += 1\n    @n\n  end\n  def n -> Int = @n\nend\ndef id(x: Shareable) -> Shareable = x\nk = Counter.new\nt = [k, 1]\ns = id(t)\nts = (1..4).map do\n  Task.spawn do\n    a = s.as(Array[Counter | Int])\n    c = a[0]\n    100000.times { c.bump } if c.is_a?(Counter)\n    0\n  end\nend\nts.each(&:await)\np k.n\n", "expects Shareable but found [Counter, Int]");
    // A run-time test against `Shareable` sees the class only.
    err("class Counter\n  var @n: Int = 0\n  def bump -> Int\n    @n += 1\n    @n\n  end\n  def n -> Int = @n\nend\nk = Counter.new\no: Object = [k]\nif o.is_a?(Shareable)\n  s = o\n  ts = (1..4).map do\n    Task.spawn do\n      a = s.as(Array[Counter])\n      100000.times { a[0].bump }\n      0\n    end\n  end\n  ts.each(&:await)\nend\np k.n\n", "`is_a?` cannot be checked at run time against Shareable");
    err(
        "def launder(o: Object) -> Shareable?\n  case o\n  when Shareable then o\n  else nil\n  end\nend",
        "`when` cannot be checked at run time against Shareable",
    );
    // A generic `data` type or enum including `Shareable` itself is
    // Shareable by its arguments, as a collection.
    ok("data D[T](x: T)\n  include Shareable\nend\nenum E[T]\n  include Shareable\n  variant A(x: T)\nend");
    // Parameters that cannot make a field non-Shareable, and an F-bound.
    ok("class H2[T]\n  include Shareable\n  @t: Type[T]\n  @f: shareable (Int) -> Int\n  def initialize(@t: Type[T], @f: shareable (Int) -> Int)\n  end\nend");
    ok("class Counter\n  var @n: Int = 0\n  def bump -> Int\n    @n += 1\n    @n\n  end\n  def n -> Int = @n\nend\nclass Node[T <: Comparable[T] & Shareable]\n  include Shareable\n  @v: T\n  def initialize(@v: T)\n  end\nend\nclass B[U <: B[U]]\n  include Shareable\n  @x: U?\n  def initialize(@x: U?)\n  end\nend\ndata P = (x: Int)\nclass Bx[T <: P]\n  include Shareable\n  @x: T\n  def initialize(@x: T)\n  end\nend\np 1\n");
}

#[test]
fn a_rescue_clauses_variable_is_its_own() {
    // As a block's parameter (docs/01 §12): separate `begin`s may bind it
    // to other classes, an outer local of the name is unchanged, and the
    // code after the clause does not see it.
    ok("begin\n  raise ArgumentError, \"a\"\nrescue ArgumentError => e\n  p e.message\nend\nbegin\n  raise KeyError, \"b\"\nrescue KeyError => e\n  p e.message\nend");
    ok("def f(n: Int) -> Int\n  e = 5\n  begin\n    raise ArgumentError, \"x\" if n > 0\n  rescue ArgumentError => e\n    p e.message\n  end\n  e\nend");
    err(
        "begin\n  raise ArgumentError, \"a\"\nrescue ArgumentError => e\n  p 1\nend\np e",
        "undefined local variable or method `e`",
    );
    err(
        "begin\n  raise ArgumentError, \"a\"\nrescue ArgumentError => e\n  p 1\nensure\n  p e\nend",
        "undefined local variable or method `e`",
    ); // In a large frame (the index of its names) too.
    let many: String = (0..35).map(|i| format!("v{i} = {i}\n")).collect();
    err(
        &format!(
            "{many}begin\n  raise ArgumentError, \"a\"\nrescue ArgumentError => e\n  p 1\nend\np e"
        ),
        "undefined local variable or method `e`",
    );
    // The outer local keeps its narrowing: the clause assigns its own.
    ok("def r(n: Int | Nil) -> Int\n  e = n\n  return 0 unless e\n  i = 0\n  while i < 2\n    begin\n      raise ArgumentError, \"a\"\n    rescue ArgumentError => e\n      e = ArgumentError.new(\"b\")\n    ensure\n      p e + 1\n    end\n    i += 1\n  end\n  e + 1\nend");
}

#[test]
fn a_class_method_has_no_fields() {
    // `self` is the class there: reading `@a` checked, then failed at run
    // time ("instance variable access outside of an object").
    err(
        "class C\n  @a: Int?\n  def initialize\n    @a = 1\n  end\n  def self.f -> Int? = @a\nend\np C.f",
        "instance variables are not available here: `self` is a class",
    );
    err(
        "data D(n: Int)\n  def self.g -> Int = @n\nend",
        "instance variables are not available here: `self` is a class",
    );
    // A field parameter of a class method, and a constant's initializer.
    err(
        "class C\n  var @a: Int? = nil\n  def initialize\n  end\n  def self.f(@a: Int) -> Nil = nil\nend\nC.f(1)",
        "instance variables are not available here: `self` is a class",
    );
    err(
        "class C\n  @a: Int = 1\n  X = @a\nend",
        "instance variables are not available here: `self` is a class",
    );
}

#[test]
fn expansive_inheritance_is_refused_at_the_class() {
    // Kennedy and Pierce: a cycle through an expansive edge would make
    // subtyping run forever (found by the Lean model).
    for parent in [
        "N[N[C[C[X]]]]",
        "N[N[C[C[X]]] | N[C[X]]]",
        "N[N[C[Hash[X, X]]]]",
    ] {
        err(
            &format!(
                "class N[in Z]\nend\nclass C[X] < {parent}\nend\ndef f(x: C[Int]) -> N[C[Int]] = x"
            ),
            "expansive inheritance, `X` grows through",
        );
    }
    // Through an extension's include, and through a module.
    err(
        "module N[in Z]\nend\nclass C[X]\nend\nextension C[X]\n  include N[N[C[C[X]] | Int] | N[C[X]]]\nend\ndef f(x: C[Int]) -> N[C[Int]] = x",
        "`extension C[X] includes N[N[C[C[X]] | Int] | N[C[X]]]`: expansive inheritance",
    );
    err(
        "module N[in Z]\nend\nmodule M[Y]\n  include N[N[C[C[Y]]]]\nend\nclass C[X]\n  include M[X]\nend\ndef f(x: C[Int]) -> N[C[Int]] = x",
        "`M[Y] includes N[N[C[C[Y]]]]`: expansive inheritance",
    );
    // Without expansion the questions are finitely many, and one met again
    // while being answered is answered no: this ends (it hung).
    err(
        "class N[in Z]\nend\nclass C[X] < N[N[C[X]] | N[N[N[C[X]]]]]\nend\ndef f(x: C[Int]) -> N[C[Int]] = x",
        "method `f` returns N[C[Int]] but its body has type C[Int]",
    );
    // A union with the parameter as a member does not grow.
    ok("class Base[out T]\nend\nclass Opt[out T] < Base[Opt[T?]]\nend");
    // Recursion without growth, and F-bounds, are fine.
    ok("class L[T]\n  include Comparable[L[T]]\n  def <=>(o: L[T]) -> Int = 0\nend\nclass Tree[T]\n  @kids: Array[Tree[T]]\n  def initialize(@kids: Array[Tree[T]])\n  end\nend");
    // A deep but finite coercion is checked as before (63 deep in the
    // CLI's tests, where the stack is the main thread's).
    let (mut t, mut u, mut v) = ("Int".to_string(), "Int?".to_string(), "1".to_string());
    for _ in 0..30 {
        t = format!("Array[{t}]");
        u = format!("Array[{u}]");
        v = format!("[{v}]");
    }
    ok(&format!("def g(x: {t}) -> {u} = x\np g({v})"));
}

#[test]
fn a_data_type_shareable_by_its_fields_is_a_shareable() {
    // docs/03: the derivation decides, without `include Shareable`.
    ok("data Point = (x: Int, y: Int)\nenum Col = Red | Green\nx: Shareable = Point.new(1, 2)\ny: Shareable = [Point.new(1, 2)]\nz: Shareable = {\"a\" => [Col::Red]}\nw: Shareable = [Point.new(1, 2), 1]");
    err(
        "class Counter\n  var @n: Int = 0\nend\ndata Holds = (c: Counter)\nx: Shareable = Holds.new(Counter.new)",
        "cannot assign Holds to `x` of type Shareable",
    );
    err(
        "class Counter\n  var @n: Int = 0\nend\ndata Box[T] = (v: T)\nx: Shareable = Box.new(Counter.new)",
        "of type Shareable",
    ); // A recursive type's answer leans on its own: kept only once the
       // outermost is decided (`B` holds an `A` holding a `Counter`).
    for b in [
        "data A = (b: B?, c: Counter)\ndata B = (a: A?)\nx: Shareable = B.new(A.new(nil, Counter.new))",
        "enum E = One(b: B?) | Two(c: Counter)\ndata B = (e: E)\nx: Shareable = B.new(E::Two.new(Counter.new))",
    ] {
        err(
            &format!("class Counter\n  var @n: Int = 0\nend\n{b}"),
            "to `x` of type Shareable",
        );
    }
    // A negative answer a caller drops (a parameter's other bound) still
    // undoes what leaned on it: `X` holds a `Y` that holds a `Counter`.
    err(
        "data O = (p: P[Nothing]?)\nclass Counter\n  var @n: Int = 0\nend\nclass P[T <: Y & Shareable]\n  include Shareable\n  @t: T\n  def initialize(@t: T)\n  end\nend\ndata Y = (x: X?, k: Counter)\ndata X = (y: Y?)\nx: Shareable = X.new(Y.new(nil, Counter.new))\np x\n",
        "cannot assign X to `x` of type Shareable",
    );
    // Mutually recursive types are decided in polynomial time (each once
    // per outermost decision; 12 such types took minutes).
    let n = 12;
    let mut src = String::new();
    for i in 0..n {
        let fields: Vec<String> = (0..n)
            .filter(|j| *j != i)
            .map(|j| format!("f{j}: K{j}?"))
            .collect();
        src.push_str(&format!("data K{i} = ({})\n", fields.join(", ")));
    }
    src.push_str("x: Shareable = K0.new(nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil)\n");
    ok(&src);
    // Known to the declaration's own checks (an override's result).
    ok("data Point = (x: Int, y: Int)\nclass Base\n  def get -> Shareable = 1\nend\nclass Sub < Base\n  def get -> Point = Point.new(1, 2)\nend");
}

#[test]
fn what_may_be_nil_or_false_is_decided_by_subtyping() {
    // A module `Nil` and `Bool` include holds them (tmp/repro/lean-falsy-module.qz).
    err(
        "def f(x: Shareable) -> Int\n  x && 1\nend",
        "returns Int but its body has type Nil | Bool | Int",
    );
    err(
        "def g(x: Shareable) -> Int\n  if x\n    1\n  else\n    x.foo\n  end\nend",
        "undefined method `foo` for Nil",
    );
    // A class does not.
    ok("class K\nend\ndef h(x: K) -> Int\n  x && 1\nend");
    // A type not decided yet may become `Bool` (an element pushed later).
    err(
        "xs = []\ni = 0\ntotal = 0\nwhile i < 2\n  if xs.size > 0\n    total = total + (xs[0] && 1)\n  end\n  xs = xs.push(false)\n  i += 1\nend",
        "cannot assign Array[Int | Bool] to `xs` of type Array[Int]",
    );
    // A field `&&=` or a multiple assignment sets in `initialize`
    // (tmp/repro/lean-opassign-init-field.qz).
    err(
        "class C\n  @x: Int?\n  def initialize\n    @x = 1\n    @x &&= nil\n    p(@x + 1)\n  end\nend",
        "undefined method `+` for Nil",
    );
    err(
        "class C\n  @x: Int?\n  @y: Int?\n  def initialize\n    @x = 1\n    @x, @y = nil, 2\n    p(@x + 1)\n  end\nend",
        "undefined method `+` for Nil",
    );
}

/// A block's declared result type (`do |x| -> T ... end`) is its result,
/// as a `def`'s return type is: the body and `next` are checked against
/// it, it binds the callee's result type, and the callee must take it.
#[test]
fn block_result_type() {
    ok("names: Array[String] = [1, 2].map { |x| -> String x.to_s }");
    ok("u: Array[Int | String] = [1, 2].map { |x| -> Int | String x > 1 ? x : \"one\" }");
    ok("[1].each { |x| -> Void x + 1 }");
    ok("def keep(&blk: (Int) -> Bool) -> Bool = blk.call(1)\nkeep { |x| -> Bool x > 0 }");
    // Declared `-> Int` where the callee expects `Void`: Void takes any.
    ok("def run(&blk: (Int) -> Void) -> Void = blk.call(1)\nrun { |x| -> Int x }");
    ok("def try_it(&blk: () -> Int) -> Int = blk.call\ntry_it { -> Nothing raise \"no\" }");
    ok("p([1, 2].map { |x| -> Int\n  next 0 if x == 2\n  x\n})");
    err(
        "a = [1, 2].map { |x| -> String\n  x\n}",
        "block returns Int but is declared `-> String`",
    );
    err(
        "a = [1, 2].map { |x| -> String\n  next 1 if x == 2\n  \"s\"\n}",
        "`next` has type Int but the block returns String",
    );
    // Without overloads to try, at the expression.
    err_at(
        "def one(&blk: (Int) -> String) -> String = blk.call(1)\none { |x| -> String\n  x\n}",
        "block returns Int but is declared `-> String`",
        3,
    );
    err(
        "[1].each { |x| -> Void next x }",
        "`next` gives a Int but the block's result is `Void`",
    );
    err(
        "def try_it(&blk: () -> Int) -> Int = blk.call\ntry_it { -> Nothing 1 }",
        "block returns Int but is declared `-> Nothing`",
    );
    err(
        "def keep(&blk: (Int) -> Bool) -> Bool = blk.call(1)\nkeep { |x| -> String \"s\" }",
        "the block is declared `-> String` but `keep` expects (Int) -> Bool",
    );
    // A task's declared result reaches the awaiting task.
    err(
        "class Box\n  @v: Int\n  def initialize(@v: Int); end\nend\nc = true\nt = Task.spawn { -> Int | Box\n  next Box.new(1) if c\n  1\n}\np t.await",
        "a task block returns the non-shareable type",
    );
    // The declared type, not the body's, is the block's result.
    err(
        "a: Array[Int] = [1, 2].map { |x| -> Int | String x }",
        "the block is declared `-> Int | String` but `map` expects (Int) -> Int",
    );
}

#[test]
fn a_case_arms_names_are_its_own() {
    // docs/01 §11: as a block's parameters; not seen after the `case`.
    err(
        "def h(v: Int) -> Int\n  case v\n  in Int => n then 1\n  end\n  n\nend",
        "undefined local variable or method `n`",
    );
    // Two arms may bind one name to different types; an outer local of
    // the name is shadowed, unchanged.
    ok("def g(v: Int | String) -> Int\n  x = \"outer\"\n  r = case v\n      in Int => x then x + 1\n      in String => x then x.size\n      end\n  r + x.size\nend");
}

#[test]
fn alternatives_bind_no_names_and_objects_have_no_rest() {
    // docs/01 §11 (tmp/repro/pattern-alt-binding*.qz).
    for src in [
        "# Hole on main (found in the pattern-binding review, 2026-10-31): a name bound in only some alternatives of `|` is typed as bound whichever matched; here `a` is still a String at run time (VM: QIR fact violated). Ruby refuses names in alternatives.\ndata P = (a: Int, b: Int)\ndef ob(p: P, a: Int | String) -> Int\n  return 0 unless a.is_a?(String)\n  if p in P(b: 7, a:) | P(b: 1)\n    return a + 1\n  end\n  -1\nend\np ob(P.new(5, 1), \"str\")\ndef oc(p: P, a: Int | String) -> Int\n  case p\n  in P(b: 7, a:) | P(b: 1) then a + 1\n  else -1\n  end\nend\np oc(P.new(5, 1), \"str\")\n",
        "# Same as pattern-alt-binding.qz in a case/in arm: the arm's own `a` is nil when the other alternative matched.\ndata P = (a: Int, b: Int)\ndef oc(p: P, a: Int | String) -> Int\n  case p\n  in P(b: 7, a:) | P(b: 1) then a + 1\n  else -1\n  end\nend\np oc(P.new(5, 1), \"str\")\n",
        "# A failed alternative's partial bindings are seen by a later alternative's pin (`^a` reads the 1 the failed one bound).\ndata P = (a: Int, b: Int)\ndef ob(p: P | Int) -> String\n  a = -1\n  r = p in P(a:, b: 7) | P[_, ^a]\n  \"#{r} #{a}\"\nend\nputs ob(P.new(1, 1))\nputs ob(P.new(5, -1))\ndef oc(p: P | Int) -> String\n  a = -1\n  r = case p\n      in P(a:, b: 7) | P[_, ^a] then \"arm #{a}\"\n      else \"else\"\n      end\n  \"#{r} #{a}\"\nend\nputs oc(P.new(1, 1))\nputs oc(P.new(5, -1))\n",
    ] {
        err(src, "is bound in an alternative pattern");
    }
    ok("def f(v: Array[Int]) -> Bool = v in [_, 7] | [_, 6]");
    // tmp/repro/pattern-object-rest.qz; a hash pattern keeps `**rest`.
    err("# Hole on main (2026-10-31): `**rest` in a class's hash pattern type-checks as a Hash but is never bound (object_hash_pattern stores no rest): nil at run time.\ndata P = (a: Int, b: Int)\ndef oh(p: P | Int) -> Int\n  if p in P(a: 1, **rest)\n    return rest.size\n  end\n  -1\nend\np oh(P.new(1, 2))\n", "in a class pattern: an object has no rest of keys");
    ok("def g(h: Hash[Symbol, Int]) -> Int\n  case h\n  in {a: 1, **rest} then rest.size\n  else 0\n  end\nend");
    // Nor a hash pattern on a `data` value.
    err(
        "data P = (a: Int, b: Int)\ndef g5(p: P) -> Int\n  case p\n  in {a: 1, **r} then r.size\n  else -1\n  end\nend",
        "on a `data` value: an object has no rest of keys",
    );
    // Nor is a range's bound.
    ok("def k(v: String, w: Array[Int]) -> Bool\n  v in \"a\" | \"a\"..\"#{w.map { |e| (e in Int => z) ? z : 0 }.sum}\"\nend");
    // An expression in a pin is no part of the alternative.
    ok("def f(v: Int, w: Array[Int]) -> Bool\n  v in 0 | ^(case w\n             in [y] then y\n             else 1\n             end)\nend");
}

/// `y := e` and `y: T = e` declare in the innermost scope (docs/01 §10):
/// an outer `y` is hidden, not changed; one in the same scope is an error.
#[test]
fn local_declarations() {
    // The hidden variable and its type are unchanged after the block.
    ok("y = \"s\"\n[1].each { |x| y := x }\np y.size");
    ok("y = \"s\"\n[1].each { |x| y: Int? = x }\np y.size");
    // The value reads the outer one.
    ok("y = 1\n[1].each { |x| y := \"#{y}\" }\np y + 1");
    ok("def f(y: Int) -> String\n  [1].map { |x| y := y.to_s\n    y }[0]\nend");
    // The outer's narrowing is not affected by the inner's assignments.
    ok("def f(s: String?) -> Int\n  return 0 unless s\n  [1].each { |x| s: Int? = x\n    s = nil }\n  s.size\nend");
    ok("def f(s: String?) -> Int\n  return 0 unless s\n  [1].each { |x| s := x\n    s = 2 }\n  s.size\nend");
    // A case arm and a rescue clause are scopes.
    ok("z = 5\ncase 3\nin Int => n\n  z := \"arm\"\n  p z.size\nend\np z + 1");
    ok("z = 5\nbegin\n  p 1\nrescue => e\n  z := e.message\nend\np z + 1");
    // `y := e` types `y` as `e`; `nil` is Nil.
    err("y := nil\ny = 1", "cannot assign Int to `y` of type Nil");
    err("y := [1, \"a\"]\ny = y.push(:s)", "cannot assign");
    // The same scope: an error, wherever the first one came from.
    let again = "`y` is already declared in this scope; a local variable's type is fixed at its declaration";
    err("y = 1\ny := 2", again);
    err("y := 1\ny: Int = 2", again);
    err(
        "def f -> Void\n  y = 1\n  if true\n    y := 2\n  end\nend",
        again,
    );
    err("def f(y: Int) -> Void\n  y := 2\nend", again);
    err("[1].each { |y| y := 2 }", again);
    err("case 1\nin Int => y\n  y := 2\nend", again);
    err("begin\n  p 1\nrescue => y\n  y := 2\nend", again);
    // Out of scope after the arm.
    err(
        "case 1\nin Int\n  k := 2\nend\np k",
        "undefined local variable or method `k`",
    );
    // A closure keeps the variable it saw.
    ok("fs = []\n[1, 2].each { |j| m := j\n  fs = fs.push(-> { m }) }\np fs");
    // What is learned of a declared variable after its declaration is
    // its own: a late closure's read is not narrowed when it is assigned
    // later, also where the declaration is in an `if`'s body (the scope
    // is the enclosing one) or the late closure is made in a loop.
    for decl in ["y: Int? = 5", "y := maybe(5)"] {
        err(
            &format!("def maybe(n: Int) -> Int? = n > 100 ? nil : n\nif true\n  {decl}\n  f = -> {{ y + 1 }}\n  y = nil\n  p f.call\nend"),
            "undefined method `+` for Nil",
        );
        err(
            &format!("def maybe(n: Int) -> Int? = n > 100 ? nil : n\ng = -> {{ nil }}\ni = 0\nwhile i < 2\n  if true\n    {decl}\n  end\n  if y\n    g.call\n    p y + 1\n  end\n  g = -> {{ y = nil\n    nil }}\n  i += 1\nend"),
            "undefined method `+` for Nil",
        );
    }
    // ... and where the declaration is directly in a block, an arm or a
    // rescue clause, seen from the method's own scan.
    for (open, close) in [
        ("[1].each do |_|", "end"),
        ("case 1\nin Int", "end"),
        ("begin\n  raise \"x\"\nrescue", "end"),
    ] {
        err(
            &format!("{open}\n  y: Int? = 5\n  f = -> {{ y + 1 }}\n  y = nil\n  p f.call\n{close}"),
            "undefined method `+` for Nil",
        );
    }
    // An arm's guard is in its scope.
    err(
        "case 3\nin Int => n if (q := n; true)\n  p q\nend\np q",
        "undefined local variable or method `q`",
    );
}

#[test]
fn a_type_not_yet_known_cannot_cross_tasks() {
    // docs/03: what decides it later might not be Shareable.
    let c = "class Counter\n  var @n: Int = 0\nend\nk = Counter.new\n";
    for (src, msg) in [
        ("ch = Channel[Shareable].new(4)\na = []\nch.send(a)\na = a.push(k)", "the type is not yet known here, and it must be Shareable"),
        ("data Box[T] = (v: T)\nch = Channel[Shareable].new(4)\na = []\nch.send(Box.new(a))\na = a.push(k)", "the type is not yet known here, and it must be Shareable"),
        ("ch = Channel.new(4)\na = []\nch.send(a)\na = a.push(k)", "the type argument for `T` of `Channel` is not yet known here"),
        ("a = []\nt = Task.spawn { a }\na = a.push(k)\np t.await", "the type of `a` is not yet known here"),
        ("t = Task.spawn { a = []; a }\np t.await", "the type of a task block's result is not yet known here"),
    ] {
        err(&format!("{c}{src}"), msg);
    }
    // Annotated, it is checked as any type.
    ok("a: Array[Int] = []\nch = Channel[Shareable].new(4)\nch.send(a)\nch2 = Channel[Int].new(4)\nch2.send(1)");
}

/// `using` is in effect from its statement to the end of the statement
/// list it appears in (docs/01 §7): at a file's top level and in a class
/// body as in a method body, what is above it does not see it.
#[test]
fn using_is_positional() {
    let m = "module M\n  extension String\n    def shout -> String = upcase + \"!\"\n  end\nend\n";
    for above in [
        "puts \"a\".shout",
        "def early -> String = \"a\".shout",
        "X = \"a\".shout",
        "class Before\n  def f -> String = \"a\".shout\nend",
        "class Before\n  @g: String = \"a\".shout\nend",
    ] {
        err(
            &format!("{m}{above}\nusing M\n"),
            "undefined method `shout` for String",
        );
    }
    ok(&format!(
        "{m}using M\nputs \"a\".shout\ndef late -> String = \"a\".shout\nY = \"a\".shout\nclass After\n  @g: String = \"a\".shout\n  def f -> String = \"a\".shout\nend"
    ));
    err(
        &format!("{m}class C\n  def a -> String = \"a\".shout\n  using M\nend"),
        "undefined method `shout` for String",
    );
    ok(&format!(
        "{m}class C\n  using M\n  def b -> String = \"b\".shout\nend"
    ));
    err(
        &format!("{m}def f -> String\n  x = \"a\".shout\n  using M\n  x\nend"),
        "undefined method `shout` for String",
    );
    // A module's own extensions are in effect in its body, without `using`.
    ok("module M\n  extension String\n    def shout -> String = upcase + \"!\"\n    def twice -> String = shout + shout\n  end\n  X = \"k\".shout\n  def self.m -> String = \"m\".shout\nend\nputs M.m, M::X");
    err(
        &format!("{m}puts \"a\".shout"),
        "undefined method `shout` for String",
    );
    // In a class or module body, to its end: constants, field defaults
    // of nested classes, `static` statements.
    ok(&format!("{m}class C\n  using M\n  X = \"a\".shout\nend"));
    ok(&format!(
        "{m}module N\n  using M\n  class C\n    @g: String = \"a\".shout\n  end\nend"
    ));
    // An extension's method is written in the extension's module: its
    // `using`s, not the extended class's.
    ok(&format!(
        "{m}module N\n  using M\n  extension Int\n    def g -> String = \"g\".shout\n  end\nend"
    ));
    err(
        &format!("{m}class C\n  using M\nend\nmodule N\n  extension C\n    def g -> String = \"g\".shout\n  end\nend"),
        "undefined method `shout` for String",
    );
    // Lexical: `class M::D` written at the top level is not in M's body,
    // nor in N's: neither M's own extensions nor N's `using` reach it,
    // though M's names do.
    for d in [
        "class M::D\n  def f -> String = \"a\".shout\nend",
        "class M::D\n  @g: String = \"a\".shout\nend",
        "class M::D\n  X = \"a\".shout\nend",
        "module N\n  using M\nend\nclass N::Inner\n  def f -> String = \"a\".shout\nend",
    ] {
        err(&format!("{m}{d}"), "undefined method `shout` for String");
    }
    ok("module M\n  extension String\n    def shout -> String = upcase + \"!\"\n  end\n  K = 7\nend\nclass M::D\n  using M\n  def f -> String = \"a\".shout + K.to_s\nend");
}

#[test]
fn a_literal_no_variable_holds_is_decided() {
    // An empty literal sent, or a join's empty branch, has no holder that
    // could decide it later (the user's refinement of docs/03's rule).
    ok("ch = Channel[Shareable].new(4)\nch.send([])\nch.send([[], 1])\nx: Shareable = {}\ny = true ? [1] : []\nch.send(y)\nt = Task.spawn { [] }\np t.await\nt2 = Task.spawn { if true then [1] else [] end }\np t2.await");
    // Only literals: an empty array a variable holds is still undecided
    // (it may be pushed to later), whatever it is joined with.
    ok("c = true\nx = []\ny = c ? [1] : x\nx = x.push(\"s\")");
    err(
        "c = true\nch = Channel[Shareable].new(4)\ny = if c then [] else [] end\nch.send(y)",
        "not yet known",
    );
    ok("c = true\nch = Channel[Shareable].new(4)\nch.send(c ? [] : [])\nz = c ? [[1]] : [[]]\nch.send(z)\nw: Shareable? = []");
    // A non-Shareable element is still refused.
    err(
        "class Counter\n  var @n: Int = 0\nend\nch = Channel[Shareable].new(4)\nch.send([Counter.new])",
        "array elements have type Counter but Shareable was expected",
    );
}

#[test]
fn an_overload_is_not_dropped_for_a_type_not_yet_known() {
    // `f(a)` would take the Shareable overload once `a` is known: rather
    // than silently taking the other one, an error asks to annotate.
    let defs = "def f(x: Shareable) -> Int\n  1\nend\ndef f(x: Object) -> Int\n  2\nend\n";
    err(
        &format!("{defs}a = []\np f(a)"),
        "which overload this call takes depends on a type not yet known here, which must be Shareable for f(x: Shareable) -> Int",
    );
    ok(&format!(
        "{defs}a: Array[Int] = []\np f(a)\np f([1])\np f(1)"
    ));
    // A block's result, too.
    err(
        "def m(x: Int, &blk: () -> Shareable) -> Int\n  1\nend\ndef m(x: Object, &blk: () -> Object) -> Int\n  2\nend\na = []\np m(1) { a }",
        "depends on a type not yet known here",
    );
    // Not when the candidate fails for another reason as well.
    ok("def h(x: Shareable, &blk: () -> Int) -> Int\n  1\nend\ndef h(x: Object, &blk: () -> String) -> Int\n  2\nend\na = []\np h(a) { \"s\" }");
    // An overload that does not fit for another reason is dropped as before.
    ok("def g(x: Int) -> Int\n  1\nend\ndef g(x: Object) -> Int\n  2\nend\na = []\np g(a)");
}

#[test]
fn clamp_gives_the_receiver_or_a_bound() {
    // `clamp` returns `min` or `max`, a `T`, which need not be `Self`.
    let include = "class B\n  def b -> String = \"B\"\nend\nclass A\n  include Comparable[B]\n  def <=>(other: B) -> Int = -1\n  def a -> String = \"A\"\nend\n";
    err(
        &format!("{include}r = A.new.clamp(B.new, B.new)\nputs r.a"),
        "undefined method `a`",
    );
    ok(&format!(
        "{include}r = A.new.clamp(B.new, B.new)\nputs r.class"
    ));
    let sub = "class P\n  @v: Int\n  include Comparable[P]\n  def initialize(@v: Int)\n  end\n  def <=>(other: P) -> Int = @v <=> other.v\n  def v -> Int = @v\nend\nclass Q < P\n  def name -> String = \"Q\"\nend\n";
    err(
        &format!("{sub}r = Q.new(5).clamp(P.new(0), P.new(3))\nputs r.name"),
        "undefined method `name`",
    );
    ok(&format!(
        "{sub}r = Q.new(5).clamp(P.new(0), P.new(3))\nputs r.v"
    ));
    // When `T` is the class itself, it is that class.
    ok("x: Int = 5.clamp(1, 3)\ny: Int = 5.clamp(1..3)");
}

#[test]
fn an_override_with_wider_parameters_keeps_the_result_and_block_types() {
    // The runtime takes a method with wider parameters to override
    // (`rtworld::overridden_methods`): its result and block type are
    // checked as a same-parameter override's.
    err(
        "class A\n  def f(x: Int) -> Int = x + 1\nend\nclass B < A\n  def f(x: Object) -> String = \"str\"\nend",
        "`f` returns String but `A#f`, which it overrides, returns Int",
    );
    err(
        "class A\n  def f(x: Int, &blk: (Int) -> Int) -> Int = yield x\nend\nclass B < A\n  def f(x: Int, &blk: (String) -> Int) -> Int = yield \"s\"\nend",
        "`f` takes a block of type (String) -> Int but `A#f`, which it overrides, is given one of type (Int) -> Int",
    );
    // The interpreter also overrides where a parameter is a type
    // parameter (`same_signature`): the parameters must then take what
    // the overridden method's callers pass.
    err(
        "class A[T]\n  def f(x: T) -> T = x\nend\nclass B < A[Int]\n  def f(x: String) -> String = x\nend",
        "`f` takes String for `x` but `A#f`, which it overrides, is given Int",
    );
    err(
        "class A\n  def f[U](x: U) -> U = x\nend\nclass B < A\n  def f(x: Int) -> String = \"s\"\nend",
        "`f` takes Int for `x` but `A#f`, which it overrides, is given U",
    );
    err(
        "class A\n  def f(x: Int) -> Int = x\nend\nclass B < A\n  def f[V](x: Int) -> String = \"s\"\nend",
        "`f` returns String but `A#f`, which it overrides, returns Int",
    );
    // Class methods, a module's method over the superclass's, `Self`.
    err(
        "class A\n  def self.make -> Int = 1\nend\nclass B < A\n  def self.make -> String = \"s\"\nend",
        "`make` returns String but `A#make`, which it overrides, returns Int",
    );
    err(
        "class A\n  def f -> Int = 1\nend\nmodule M\n  def f -> String = \"s\"\nend\nclass B < A\n  include M\nend",
        "`f` returns String but `A#f`, which it overrides in `B`, which includes `M`, returns Int",
    );
    err(
        "class A\n  def me -> Self = self\nend\nclass B < A\n  def me -> Int = 5\nend",
        "`me` returns Int but `A#me`, which it overrides, returns B",
    );
    // A block the overridden method may go without, the override must too.
    err(
        "class A\n  def each(&b: ((Int) -> Void)?) -> Void\n    b.call(1) if b\n  end\nend\nclass B < A\n  def each(&b: (Int) -> Void) -> Void\n    yield 2\n  end\nend",
        "`each` requires a block but `A#each`, which it overrides, may be called without one",
    );
    // A block whose result is dropped takes one of any result.
    ok("class A\n  def each(&blk: (Int) -> Int) -> Void\n    puts yield 1\n  end\nend\nclass B < A\n  def each(&blk: (Int) -> Void) -> Void\n    yield 2\n  end\nend");
    // A narrower result, and a block of a wider type (one giving any
    // Object takes one giving an Int), are fine.
    ok("class A\n  def f(x: Int, &blk: (Int) -> Int) -> Object = yield x\nend\nclass B < A\n  def f(x: Object, &blk: (Int) -> Object) -> Int = 1\nend");
}

#[test]
fn a_task_blocks_next_value_must_be_shareable() {
    // tmp/repro/task-next-shareable.qz: the body ends in `raise`, so a
    // `next` value is all that passes to the awaiting task.
    err("# A task block's `next` value reaches the task that awaits it, so it must\n# be Shareable, as the body's last value must be. When the body ends in\n# `raise`, only the last value is checked (it is Nothing): this program is\n# accepted, and a mutable Box crosses tasks. Expected: an error at `next`,\n# \"a task block returns the non-shareable type Box\".\nclass Box\n  var @v: Int\n  def initialize(@v: Int); end\nend\nc = true\nt = Task.spawn do\n  next Box.new(1) if c\n  raise \"unreachable\"\nend\np t.await\n", "a task block returns the non-shareable type Box");
    ok("c = true\nt = Task.spawn do\n  next 1 if c\n  raise \"x\"\nend\np t.await");
}

/// A top-level `def` runs with its file's top-level object, not the
/// caller's `self` (docs/01 §1): calling it does not use the object, so
/// it is allowed before `initialize` has assigned the fields, in a
/// field's default, and in a task's block in a mutable class.
#[test]
fn toplevel_defs_take_no_self() {
    ok("def label -> String = \"x\"\nclass D\n  @a: String = label\n  @b: String\n  def initialize\n    @b = label\n  end\nend");
    ok("def work -> Int = 1\nclass Counter\n  var @n: Int = 0\n  def go -> Int = Task.spawn { work }.await\nend");
    // A method of the class still uses it.
    err(
        "class Counter\n  var @n: Int = 0\n  def work -> Int = @n\n  def go -> Int = Task.spawn { work }.await\nend",
        "calling `work` uses `self`",
    );
}

#[test]
fn an_extension_or_class_method_in_place_of_a_modules_keeps_its_types() {
    // An extension's method the runtime dispatches to in place of a
    // module's (abstract or not), and a class method implementing an
    // extended module's abstract one, take and return what it declares.
    let sized = |body: &str| {
        format!("module Sized\n  {body}\n  def plus -> Int = size2 + 1\nend\nclass Box\nend\nextension Box\n  include Sized\n  def size2 -> String = \"s\"\nend")
    };
    err(
        &sized("abstract def size2 -> Int"),
        "`size2` returns String but `Sized#size2`, which it overrides, returns Int",
    );
    err(
        &sized("def size2 -> Int = 3"),
        "`size2` returns String but `Sized#size2`, which it overrides, returns Int",
    );
    err(
        "module Named\n  abstract def label -> Int\n  def twice -> Int = label + 1\nend\nclass Thing\n  extend Named\n  def self.label -> String = \"s\"\nend",
        "`label` returns String but `Named#label`, which it overrides, returns Int",
    );
    // Another extended module's method found first runs in its place.
    err(
        "module Named\n  abstract def label -> Int\n  def twice -> Int = label + 1\nend\nmodule Other\n  def label -> String = \"o\"\nend\nclass A\n  extend Named\n  extend Other\nend",
        "`label` returns String but `Named#label`, which it overrides, returns Int",
    );
    // Generic extensions and extended modules are seen with their own
    // type arguments.
    ok("class Bag[T]\n  @items: Array[T]\n  def initialize(@items: Array[T])\n  end\n  def items -> Array[T] = @items\nend\nextension Bag[T]\n  include Enumerable[T]\n  def each(&: (T) -> Void) -> Void\n    items.each { |x| yield x }\n  end\nend\np Bag.new([1, 2]).map { |x| x * 2 }");
    ok("module Factory[T]\n  abstract def make -> T\nend\nclass Foo\n  extend Factory[Foo]\n  def self.make -> Foo = Foo.new\nend");
    // A superclass's class method is not found before a module the class
    // extends, nor is a wider parameter the same signature there.
    ok("module Named\n  def label -> Int = 1\nend\nclass A\n  def self.label -> String = \"a\"\nend\nclass B < A\n  extend Named\nend");
    ok("module Named\n  def f(x: Int) -> Int = x\nend\nclass A\n  extend Named\n  def self.f(x: Object) -> String = \"a\"\nend");
    // A class method overrides an extended module's concrete method too.
    err(
        "module Named\n  def label -> Int = 1\nend\nclass Thing\n  extend Named\n  def self.label -> String = \"s\"\nend",
        "`label` returns String but `Named#label`, which it overrides, returns Int",
    );
}

#[test]
fn an_extension_implementing_an_abstract_method_keeps_its_types_anywhere() {
    // What `ext_impl` runs for an abstract method is checked for a prelude
    // class's extension and for one in a module, active through `using`.
    let describable = "module Describable\n  abstract def describe -> String\n  def shout -> String = describe.upcase\nend\n";
    err(
        &format!(
            "{describable}extension Int\n  include Describable\n  def describe -> Int = 3\nend"
        ),
        "`describe` returns Int but `Describable#describe`, which it overrides, returns String",
    );
    err(
        &format!("{describable}class Pt\nend\nmodule Describing\n  extension Pt\n    include Describable\n    def describe -> Int = 3\n  end\nend\nusing Describing"),
        "`describe` returns Int but `Describable#describe`, which it overrides, returns String",
    );
    // A target with a method of the name (`Int#abs()`) still runs the
    // extension's in its place (`find_override`).
    err(
        "module Absy\n  abstract def abs(x: Int) -> String\n  def shout -> String = abs(1).upcase\nend\nextension Int\n  include Absy\n  def abs(x: Int) -> Int = x + 41\nend",
        "`abs` returns Int but `Absy#abs`, which it overrides, returns String",
    );
    // tmp/repro/extension-implements-abstract.qz: an extension's method
    // implementing a superclass's abstract one.
    err("abstract class Base\n  abstract def describe -> String\nend\nextension Shape\n  def describe -> Int = 3\nend\nclass Shape < Base\nend\ndef f(b: Base) -> String = b.describe\nputs f(Shape.new).size", "`describe` returns Int but `Base#describe`, which it overrides, returns String");
    // Of overloads, the one of the same signature implements it.
    ok("module Sized\n  abstract def f(x: Int) -> Int\n  def g -> Int = f(1) + 1\nend\nclass Box\nend\nextension Box\n  include Sized\n  def f(x: String) -> String = x\n  def f(x: Int) -> Int = x\nend");
}

#[test]
fn keywords_are_part_of_an_overrides_signature() {
    // tmp/repro/kw-*.qz: a method requiring a keyword the abstract one does
    // not take, or not taking one it does, does not implement it.
    let kw = "module Kw\n  abstract def kw(x: Int) -> String\n  def go -> String = kw(1)\nend\n";
    err(
        &format!(
            "{kw}class Pt\n  include Kw\n  def kw(x: Int, *, y: Int) -> String = \"kw#{{y}}\"\nend"
        ),
        "`Pt` must implement `kw` (abstract in `Kw`)",
    );
    err(
        &format!("{kw}class Pt\nend\nextension Pt\n  include Kw\n  def kw(x: Int, *, y: Int) -> String = \"kw#{{y}}\"\nend"),
        "`Pt` must implement `kw` (abstract in `Kw`)",
    );
    err(
        &format!("{kw}extension Int\n  include Kw\n  def kw(x: Int, *, y: Int) -> String = \"kw#{{y}}\"\nend"),
        "`Int` must implement `kw` (abstract in `Kw`)",
    );
    err(
        "module Kw\n  abstract def kw(x: Int, *, y: Int) -> String\nend\nclass Pt\n  include Kw\n  def kw(x: Int) -> String = \"nokw\"\nend",
        "`Pt` must implement `kw` (abstract in `Kw`)",
    );
    // A `**rest` stands in for no keyword, and a parent's `**rest` takes
    // an override's `**rest` of a type at least as wide.
    err(
        "module M\n  abstract def f(x: Int, *, y: Int) -> String\nend\nclass C\n  include M\n  def f(x: Int, **opts: String) -> String = \"c\"\nend",
        "`C` must implement `f` (abstract in `M`)",
    );
    err(
        "module M\n  abstract def f(x: Int, **opts: Int) -> String\nend\nclass C\n  include M\n  def f(x: Int, *, k: String = \"d\", **opts: Int) -> String = k\nend",
        "`C` must implement `f` (abstract in `M`)",
    );
    // A concrete method of a module the included one includes implements it.
    ok("module M1\n  abstract def f -> String\nend\nmodule M2\n  include M1\n  def f -> String = \"M2#f\"\nend\nextension Int\n  include M2\nend\nputs 1.f");
    // An extra keyword with a default implements it; a keyword's type is
    // compared as a parameter's (one typed by a type parameter matches
    // any at run time, so it must take what callers pass).
    ok(&format!(
        "{kw}class Pt\n  include Kw\n  def kw(x: Int, *, y: Int = 1) -> String = \"kw\"\nend"
    ));
    err(
        "class A[T]\n  def g(x: Int, *, y: T) -> Int = x\nend\nclass B < A[Int]\n  def g(x: Int, *, y: String) -> Int = 1\nend",
        "`g` takes String for `y` but `A#g`, which it overrides, is given Int",
    );
}

/// `::name(...)` calls a function: the file's top-level `def`s of the
/// name, then the built-in `Kernel` functions (docs/01 §1); never a
/// method of `self`, an `Object` method or one an `extension Kernel` adds.
#[test]
fn function_calls() {
    ok("def f -> Int = 1\nclass C\n  def f -> String = \"m\"\n  def g -> Int = ::f\nend");
    ok("class C\n  def puts(*values: Object) -> Void = nil\n  def g -> Void = ::puts(\"x\")\nend");
    let none =
        "calls a built-in function or a top-level `def` of this cog, and there is none named";
    err("::inspect", none);
    err("::nosuch(1)", none);
    err(
        "class C\n  def m -> Int = 1\n  def g -> Int = ::m\nend",
        none,
    );
    err(
        "extension Kernel\n  def shout -> String = \"S\"\nend\n::shout",
        none,
    );
    // A top-level `def` comes before the built-in for `::` as for an
    // implicit call at the top level, whose other overloads stay.
    ok("def puts(s: String) -> Void = nil\nclass D\n  def g -> Void = ::puts(\"b\")\nend");
    ok("def puts(s: String) -> Void = nil\nclass D\n  def g -> Void = ::puts(2)\nend");
    ok("class D\n  def Integer(s: String) -> Int = 99\n  def g -> Int = ::Integer(\"3\")\nend");
    // It takes no `self`: allowed before the fields are assigned.
    ok("class D\n  @a: Int\n  def initialize\n    ::puts(\"early\")\n    @a = 1\n  end\nend");
}

/// `Kernel.name(...)` is the built-in function, wherever it is written
/// (docs/01 §1); another name is a method of the module object.
#[test]
fn kernel_functions_by_name() {
    ok("def puts(s: String) -> Void = Kernel.puts(\"[mine] \" + s)\nputs \"a\"");
    ok("class W\n  def self.run -> Void\n    Kernel.sleep(1.ms)\n    Kernel.exit(3)\n  end\nend");
    ok("x: String = Kernel.inspect");
    err("Kernel.nosuch(1)", "undefined method `nosuch`");
    // So no module method may take a built-in's name, overloads included;
    // other names and the instance side are as before.
    err(
        "extension Kernel\n  def self.puts(n: Int) -> Void = nil\nend",
        "`puts` is a built-in function: `Kernel.puts` always calls it; name the method otherwise",
    );
    ok("extension Kernel\n  def self.shout -> String = \"S\"\nend\nx: String = Kernel.shout");
}

#[test]
fn an_override_keeps_the_names_callers_may_pass_by_keyword() {
    // tmp/repro/override-renames-positional.qz (docs/01 §3): a parameter
    // before `*` may be passed by keyword through the overridden method.
    err("class A\n  def f(x: Int, *, k: Int = 0) -> String = \"A#f #{x}\"\nend\nclass B < A\n  def f(y: Int, *, k: Int = 0) -> String = \"B#f #{y}\"\nend\ndef call(a: A) -> String = a.f(x: 3)\nputs call(B.new)", "`f` renames parameter `x` to `y`; callers of `A#f` may pass it as `x:`");
    // An implementation too.
    err(
        "module M\n  abstract def size_of(item: Int) -> Int\nend\nclass C\n  include M\n  def size_of(x: Int) -> Int = x\nend",
        "`size_of` renames parameter `item` to `x`",
    );
    // An operator takes no keyword argument (docs/01 §9), so its
    // parameters may be named anything.
    ok("class P\n  @v: Int\n  def initialize(@v: Int)\n  end\n  def v -> Int = @v\n  def ==(o: Object) -> Bool = o.is_a?(P) && o.v == @v\n  def hash -> Int = @v\nend\np P.new(1) == P.new(1)");
    err("p 1.==(other: 1)", "`==` takes no keyword arguments");
    // A setter is called by assignment, and a `Kernel` function is bound
    // where it is called: neither's parameters are passed by name.
    ok("class A\n  var @x: Int = 0\n  def x=(value: Int) -> Void\n    @x = value\n  end\nend\nclass B < A\n  def x=(v: Int) -> Void\n    @x = v\n  end\nend");
    ok("class Logger\n  def rand(n: Int) -> Int = 4\n  def p(v: Int) -> Int = v\nend\nputs Logger.new.rand(3)");
    // A class method is named as one.
    err(
        "class A\n  def self.f(x: Int) -> Int = x\nend\nclass B < A\n  def self.f(y: Int) -> Int = y\nend",
        "callers of `A.f` may pass it as `x:`",
    );
}

#[test]
fn a_splat_may_fill_a_position_named_by_keyword() {
    // tmp/repro/splat-then-keyword.qz (docs/01 §9): what a splat holds is
    // bound by position first, wherever it is in the call.
    let h =
        "def h(a: String, *rest: Object) -> String = \"#{a} #{rest}\"\nxs: Array[Object] = [1]\n";
    err(
        &format!("{h}puts h(*xs, a: \"x\")"),
        "`a:` names a positional parameter, but `*xs` in the call may fill that position; pass it positionally",
    );
    err(
        &format!("{h}puts h(a: \"x\", *xs)"),
        "`a:` names a positional parameter",
    );
    err(
        "xs: Array[Object] = [1]\nputs format(*xs, format: \"%d\")",
        "`format:` names a positional parameter",
    );
    // An operator takes no keyword argument in `super` either.
    err(
        "class Foo\n  def ==(other: Object) -> Bool = super(other: other)\n  def hash -> Int = 1\nend",
        "`==` takes no keyword arguments",
    );
    ok("class Foo\n  def ==(other: Object) -> Bool = super(other)\n  def hash -> Int = 1\nend");
    // A splatted tuple has a known length: it cannot reach `b`.
    ok("def g(a: Int, b: Int = 0, *r: Int) -> Int = a + b\nt: [Int] = [1]\nputs g(*t, b: 2)");
    // Positionally, or a keyword-only parameter, it is fine.
    ok(&format!("{h}puts h(\"y\", *xs)"));
    ok("def k(*rest: Int, by: Int = 1) -> Int = rest.size * by\nys = [1, 2]\nputs k(*ys, by: 3)");
}
