# Differences from Crystal: Quick Reference

日本語版: [08-crystal-diff.ja.md](08-crystal-diff.ja.md)

Crystal is the closest relative of Quarz: a statically typed, compiled language with Ruby's syntax. This page lists what someone who knows Crystal will notice first. The two share most of their surface; they differ in where types must be written, in mutability, in how memory and concurrency work, and in what can be changed at compile time.

## What works the same

`def ... end`, `class`/`module`, `include`/`extend`, `abstract class`/`abstract def` (a class must implement the abstract methods it inherits or includes, checked in both), single inheritance, `super`, blocks and `yield`, `->(x) { }` procedures, `case/when` and `case/in`, `begin/rescue/ensure`, `raise`, string interpolation and heredocs, `require`, `private`/`protected`, operator methods, union types and `T?` (`T | Nil`), narrowing with `if x`, `x.nil?`, `is_a?` and `case/in`, `as`/`as?` (checked casts), generics with type parameters, positional arguments that can also be passed by name and keyword-only parameters after `*`, `def initialize(@x: T)` assigning the field, and an error for a field of a non-nilable type that `initialize` does not assign on every path. Strings are immutable in both, and both build them with `String.build { |b| b << ... }` (a `String::Builder` in both; Crystal's is also an `IO`, so `print`-style methods and `to_s(io)` write into it).

## What changes

| Item | Crystal | Quarz |
|---|---|---|
| Type annotation syntax | `x : Int32`, `def f(a : Int32) : Bool` | `x: Int`, `def f(a: Int) -> Bool` (no space before the colon; `->` for the return type) |
| Method parameter types | Optional: an untyped method is instantiated for each combination of argument types, which needs the whole program to be type-checked together | Required (except when a default value gives the type); return types and locals are inferred. More to write, and each file can be checked on its own ([02-types.md](02-types.md) §10) |
| Generic type syntax | `Array(Int32)`, `Hash(String, Int32)`, `Proc(Int32, Bool)` | `Array[Int]`, `Hash[String, Int]`, `(Int) -> Bool` |
| Empty literals | `[] of Int32`, `{} of String => Int32` | Typed from the context: `xs: Array[Int] = []`, `h: Hash[String, Int] = {}` |
| Integers | `Int32` by default (`1_i64` for `Int64`); overflow raises `OverflowError` | `Int` is 64-bit and overflow raises `OverflowError`, as in Crystal; `Integer` is arbitrary precision (Crystal's `BigInt`), and mixing it with an `Int` gives an `Integer`. Other fixed-width types are planned for FFI |
| Floating point | `Float64` (`Float32`) | `Float` (`Float32` planned) |
| Instance variables | Declared or inferred from assignments; mutable | Declared in the class body (`@x: Int`); immutable by default, mutable with `var @x: Int` |
| Using the object in `initialize` before its fields are assigned | An error when `self` is used or passed on, or when a method it calls reads a field not assigned yet; a call to a method that does not touch such a field is allowed | An error on any use of `self` and any call to a method of the class until every such field is assigned (the methods called are not looked into); see [01-syntax.md](01-syntax.md) §3 |
| Accessors | `getter`, `setter`, `property` | `attr_reader`, `attr_writer`, `attr_accessor` (writers only on `var` fields) |
| `Array`, `Hash`, `Set` | Mutable (`<<`, `[]=`, `delete`) | Immutable: `push`/`put`/`delete` return new values, updated in place when unshared (`xs = xs.push(x)`) and copied otherwise. Mutable `Array::Builder` and friends for task-local building |
| `arr[i]`, `h[k]` | Raise when out of range / missing; `[]?` returns `nil` | Same |
| Records | `record Point, x : Int32, y : Int32`: a struct with getters, field-wise `==`/`hash` and `copy_with` | `data Point = (x: Int, y: Int)`: immutable, with structural `==`/`hash`, `with` and patterns; small ones are stored in place in the objects that hold them |
| `struct` | Mutable value type, copied on assignment | No user value types: `data` is immutable, so copying and sharing cannot be told apart |
| `enum` | Named integer constants (with flags); sum types are written as unions of types or an abstract struct hierarchy | Algebraic data types: `enum Shape = Circle(r: Float) \| Rect(w: Float, h: Float)`, matched exhaustively with `case/in` |
| `&.method` shorthand | `xs.map(&.upcase)` | `xs.map(&:upcase)` (Ruby's spelling) |
| Block parameter types | `&block : Int32 -> Int32` | `&block: (Int) -> Int`; a method that yields declares its block (`&: (Int) -> Nil`) |
| Reopening classes | Allowed anywhere, for the whole program | Not allowed. Methods are added to existing types with `extension`, active where `using` is in effect |
| Making an existing type conform to a module | Reopen it and include the module (`struct Int32; include M; ...; end`), everywhere; untyped parameters also accept anything with the right methods (duck typing) | `extension Int; include M; ...; end`: active everywhere when written at the top level, or where `using` brings in the module that declares it; parameters are typed, so a value must conform |
| Type aliases | `alias UserId = Int32` | `type UserId = Int` |
| Method references | `->obj.method` | `obj.:method` |
| Blocks with a receiver (DSLs) | `with obj yield`: the block's implicit receiver is `obj`, whatever the block | The receiver is part of the block's type (`Html.() -> Nil`), and the block is run with `obj.instance_exec(&block)` |
| Macros | `macro`, `{{ }}`, `@type`, annotations | None. Code generation by the compiler only for `data`, `attr_*` and friends |
| Narrowing fields | Instance variables are not narrowed (assign to a local first) | Immutable fields and `data` fields are narrowed; `var` fields are not |
| `to_s` | Overridden as `to_s(io : IO)` | `def to_s -> String` |
| Tuples | `Tuple`, `NamedTuple` (`{1, "a"}`, `{x: 1}`) | Tuple types `[Int, String]` written as array literals; named fields use `data` |
| Concurrency | Fibers that share memory (`spawn`, `Channel(T)`, `Mutex`, `Atomic(T)`): any object can be passed between fibers, and execution contexts run fibers on several threads | Tasks (`spawn`, `Task.scope` with cancellation, `Channel[T]`, `select`, `Atom[T]`): only `Shareable` (immutable) values cross task boundaries, which the compiler checks, and there are no locks. The current scheduler runs tasks on one thread; `Task.blocking { }` runs a block on a helper thread |
| Memory | Tracing GC (Boehm) | Reference counting with in-place updates of uniquely referenced values |
| C interop | `lib LibC; fun strlen(s : UInt8*) : SizeT; end` | `extern "C"; def strlen(s: CString) -> SizeT; end` |
| Running a program | Compiled (`crystal run` compiles first); `crystal i` is an experimental interpreter, available in builds that include it | `quarz run` interprets; `quarz build` compiles with LLVM |

## What is added

- `data`, algebraic `enum`, `var`, `extension`/`using`
- Immutable collections, with mutable Builders to assemble them (`Array::Builder`, `Hash::Builder`, `Set::Builder`; `Array.build { |b| b << x }` gives an immutable array). Crystal's `Array.build(capacity) { |buffer| ... }` is a different, low-level API: it writes into a raw pointer buffer and returns the number of elements written
- `Task.scope` (structured concurrency with cancellation), the compiler-derived `Shareable` marker, and `Atom[T]` for `Shareable` values, updated with `update { |old| ... }` (a CAS loop)
- `for` comprehensions
- `Result[T, E]`
- An interpreter as the everyday way of running programs (`quarz run`, a REPL), sharing the runtime with the compiler

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
data Vec2(x: Float, y: Float)
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
