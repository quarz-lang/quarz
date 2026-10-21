# Differences from Crystal: Quick Reference

日本語版: [08-crystal-diff.ja.md](08-crystal-diff.ja.md)

Crystal is the closest relative of Quarz: a statically typed, compiled language with Ruby's syntax. This page lists what someone who knows Crystal will notice first. The two share most of their surface; they differ in where types must be written, in mutability, in how memory and concurrency work, and in what can be changed at compile time.

## What works the same

`def ... end`, `class`/`module`, `include`/`extend`, `abstract class`/`abstract def`, single inheritance, `super`, blocks and `yield`, `->(x) { }` procedures, `case/when` and `case/in`, `begin/rescue/ensure`, `raise`, string interpolation and heredocs, `require`, `private`/`protected`, operator methods, union types and `T?` (`T | Nil`), narrowing with `if x`, `x.nil?`, `is_a?` and `case/in`, `as`/`as?` (checked casts), generics with type parameters, positional arguments that can also be passed by name and keyword-only parameters after `*`, `def initialize(@x: T)` assigning the field, and the rule that the object cannot be used in `initialize` before its fields are assigned (Crystal reports `self` used before initialization; Quarz's definite initialization is described in [01-syntax.md](01-syntax.md) §3). Strings are immutable in both, and both build them with `String.build { |b| b << ... }` (a `String::Builder` in both; Crystal's is also an `IO`, so `print`-style methods and `to_s(io)` write into it).

## What changes

| Item | Crystal | Quarz |
|---|---|---|
| Type annotation syntax | `x : Int32`, `def f(a : Int32) : Bool` | `x: Int`, `def f(a: Int) -> Bool` (no space before the colon; `->` for the return type) |
| Method parameter types | Optional: an untyped method is instantiated for each combination of argument types (whole-program inference) | Required (except when a default value gives the type). Return types and locals are inferred. This keeps separate compilation and fast checking ([02-types.md](02-types.md) §10) |
| Generic type syntax | `Array(Int32)`, `Hash(String, Int32)`, `Proc(Int32, Bool)` | `Array[Int]`, `Hash[String, Int]`, `(Int) -> Bool` |
| Empty literals | `[] of Int32`, `{} of String => Int32` | Typed from the context: `xs: Array[Int] = []`, `h: Hash[String, Int] = {}` |
| Integers | `Int32` by default (`1_i64` for `Int64`); overflow raises `OverflowError` | `Int` is arbitrary precision (promoted to a big integer on overflow, as in Ruby). Fixed-width types are planned for FFI |
| Floating point | `Float64` (`Float32`) | `Float` (`Float32` planned) |
| Instance variables | Declared or inferred from assignments; mutable | Declared in the class body (`@x: Int`); immutable by default, mutable with `var @x: Int` |
| Accessors | `getter`, `setter`, `property` | `attr_reader`, `attr_writer`, `attr_accessor` (writers only on `var` fields) |
| `Array`, `Hash`, `Set` | Mutable (`<<`, `[]=`, `delete`) | Immutable and persistent: `push`/`put`/`delete` return new values, updated in place when unshared (`xs = xs.push(x)`). Mutable `Array::Builder` and friends for task-local building |
| `arr[i]`, `h[k]` | Raise when out of range / missing; `[]?` returns `nil` | Same |
| Records | `record Point, x : Int32, y : Int32`, or a `struct` | `data Point(x: Int, y: Int)`: immutable, structural `==`/`hash`, `with`, patterns; small ones are stored in place in the objects that hold them |
| `struct` | Mutable value type, copied on assignment | No user value types: `data` is immutable, so copying and sharing cannot be told apart |
| `enum` | Named integer constants (with flags) | Algebraic data types: `enum Shape = Circle(r: Float) \| Rect(w: Float, h: Float)`, matched exhaustively with `case/in` |
| `&.method` shorthand | `xs.map(&.upcase)` | `xs.map(&:upcase)` (Ruby's spelling) |
| Block parameter types | `&block : Int32 -> Int32` | `&block: (Int) -> Int`; a method that yields declares its block (`&: (Int) -> Nil`) |
| Reopening classes | Allowed anywhere (monkey patching) | Not allowed. Methods are added to existing types with `extension`, active where `using` is in effect |
| Interfaces | Modules with abstract methods; duck typing through untyped parameters | Modules with abstract methods, checked when a class includes them; a type you did not write is made to conform with `extension T; include M; end` |
| Macros | `macro`, `{{ }}`, `@type`, annotations | None. Code generation by the compiler only for `data`, `attr_*` and friends |
| Narrowing fields | Instance variables are not narrowed (assign to a local first) | Immutable fields and `data` fields are narrowed; `var` fields are not |
| `to_s` | Overridden as `to_s(io : IO)` | `def to_s -> String` |
| Tuples | `Tuple`, `NamedTuple` (`{1, "a"}`, `{x: 1}`) | Tuple types `[Int, String]` written as array literals; named fields use `data` |
| Concurrency | Fibers sharing memory (`spawn`, `Channel(T)`, `Mutex`); nothing stops a mutable object from being shared | Tasks (`spawn`, `Task.scope` with cancellation, `Channel[T]`, `select`, `Atom[T]`); only `Shareable` values (immutable ones) cross task boundaries, checked by the compiler; no locks; blocking work in `Task.blocking { }` |
| Memory | Tracing GC (Boehm) | Reference counting with in-place updates of uniquely referenced values; no pauses |
| C interop | `lib LibC; fun strlen(s : UInt8*) : SizeT; end` | `extern "C"; def strlen(s: CString) -> SizeT; end` |
| Running a program | Compiled (`crystal run` compiles first) | `quarz run` interprets (fast start for development); `quarz build` compiles with LLVM or Cranelift |

## What is added

- `data`, algebraic `enum`, `var`, `override`, `extension`/`using`, `type` aliases
- Immutable collections, with mutable Builders to assemble them (`Array::Builder`, `Hash::Builder`, `Set::Builder`; `Array.build { |b| b << x }` gives an immutable array). Crystal's `Array.build(capacity) { |buffer| ... }` is a different, low-level API: it writes into a raw pointer buffer and returns the number of elements written
- `Task.scope` (structured concurrency with cancellation), `Atom`, the compiler-derived `Shareable` marker
- Blocks with a receiver (`Html.() -> Nil` with `instance_exec`) for DSLs
- `for` comprehensions
- `obj.:method` (method reference) and `Result[T, E]`
- An interpreter (`quarz run`, a REPL) alongside the compiler

## Rewriting example

```crystal
# Crystal
struct Vec2
  getter x : Float64, y : Float64
  def initialize(@x, @y); end
  def +(o : Vec2)
    Vec2.new(x + o.x, y + o.y)
  end
end

class Particle
  property pos : Vec2
  def initialize(@pos : Vec2, @vel : Vec2); end
  def step(dt : Float64)
    @pos = Vec2.new(@pos.x + @vel.x * dt, @pos.y + @vel.y * dt)
  end
end

ps = [] of Particle
3.times { |i| ps << Particle.new(Vec2.new(i.to_f, 0.0), Vec2.new(1.0, 0.5)) }
ps.each &.step(0.1)
puts ps.map(&.pos.x).sum
```

```ruby
# Quarz
data Vec2(x: Float, y: Float) is
  def +(o: Vec2) -> Vec2 = Vec2.new(x + o.x, y + o.y)
end

class Particle
  var @pos: Vec2
  @vel: Vec2
  attr_reader :pos
  def initialize(@pos: Vec2, @vel: Vec2); end
  def step(dt: Float) -> Nil
    @pos = Vec2.new(@pos.x + @vel.x * dt, @pos.y + @vel.y * dt)
  end
end

ps: Array[Particle] = []
3.times { |i| ps = ps.push(Particle.new(Vec2.new(i.to_f, 0.0), Vec2.new(1.0, 0.5))) }
ps.each { |p| p.step(0.1) }
puts ps.map { |p| p.pos.x }.sum
```

The particles are still mutable objects (`var @pos`), so they stay in the task that made them; the array holding them is immutable and grows with `ps = ps.push(...)`, in place since nothing else refers to it.
