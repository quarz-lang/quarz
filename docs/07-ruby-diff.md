# Changes from Ruby: Quick Reference

A summary of the things someone who knows Ruby will first stumble on when starting to write Quarz.

## What works as is

`def ... end`, `class`/`module`, `include`/`extend`, `attr_reader` and friends, blocks (`do ... end`/`{ }`), `yield`, `&block`, `&:sym`, `if`/`unless`/`while`/`until` and their modifier forms, `case/when`, `case/in` (pattern matching), `begin/rescue/ensure/retry`, `raise`, string interpolation, heredocs, `%w[]`/`%i[]`, symbols, ranges, regexp literals, `&.`, `||=`, multiple assignment, `*splat`, keyword argument call syntax, `private`/`protected`, `self.` methods, operator definitions, `<=>` and `Comparable`, `Enumerable`, `super`, `alias`, `__FILE__`/`__LINE__`, `ARGV`, `ENV`, `puts`/`p`/`pp`.

## What changes

| Item | Ruby | Quarz |
|---|---|---|
| Method parameters | `def f(a, b = 1, k:)` | `def f(a: Int, b: Int = 1, *, k: Bool)` — parameter types are required |
| Return type | Not part of the language (signatures can be written in RBS files beside the code, or with Sorbet's `sig`) | `def f(...) -> Int`; a method without one is `-> Void`: its body's value is discarded and it returns nil (`-> Nil` is strict, as any type) |
| Declaring keyword parameters | `k:` label | Written after `*`. Parameters before `*` can be passed positionally or by keyword |
| Instance variables | Created on assignment | Declared in the class body with `@x: Int`. Immutable by default; mutable with `var @x: Int` |
| Uninitialized instance variables | `nil` | Never seen: a field whose type does not admit `nil` and that has no initializer is assigned on every path through `initialize`, before the object is used (a compile error otherwise) |
| Reopening classes | Allowed | Not allowed. Add within a lexical scope with `extension` + `using` |
| `define_method`, `method_missing`, `send`, `eval`, `instance_eval`, `instance_variable_get` | Exist | Do not exist (`instance_exec` does, for blocks typed with a receiver) |
| `Struct`/`Data` | `Data.define(:x, :y)` | `data Point = (x: Int, y: Int)` |
| Sum types | No dedicated construct; written as a class hierarchy or several `Data` types | `enum` |
| Interfaces | Duck typing | A `module` with `abstract def`. Retroactive conformance with `extension T; include M; end` |
| `nil` | Fits in any variable | Only fits in types written as `T?`. Narrow with `if x` etc. |
| Arrays, hashes, strings | Mutable | Immutable. `push`/`put` return new values. Use `Array::Builder` etc. when mutation is needed |
| `arr << x`, `h[k] = v`, `str << "a"`, `sort!` | Destructive update | Not available on immutable types. `arr = arr.push(x)`, `h = h.put(k, v)`, Builders |
| `arr[i]`, `h[k]` | `nil` when out of range / missing | Raise. Use `arr[i]?`, `h[k]?` if you want `nil` |
| `gets`, `IO#read` | `nil` at EOF | `gets?` returns `nil`; `gets` raises `EOFError` |
| `Integer` | Arbitrary precision; literals are `Integer`s | `Int` is 64-bit and integer literals are `Int`s: `2 ** 70` raises `OverflowError`. `Integer` is arbitrary precision (`2.to_integer ** 70`), with no implicit conversion from `Int`. Fixed-width `Int32` etc. are planned |
| String encodings | Multiple | UTF-8 only. Binary is `Bytes` |
| `freeze`, `frozen?`, `dup` | Exist | `frozen?` is false only for Builders. `dup` returns a built-in immutable value (an array, a string, ...) as it is and copies Builders and objects. A Builder's `freeze` hands its contents over as an immutable value |
| `eql?` | Separate from `==` | Dropped. Only `==`/`hash` |
| Global variables `$x`, class variables `@@x` | Exist | Do not exist. Constants + `Atom` |
| Constants | Reassignment is a warning | Cannot be reassigned; must be Shareable |
| `Proc.new`, `proc` | Exist | Only `->` and blocks. Procedures always have lambda semantics |
| `it`, numbered parameters | `it` (3.4) in any parameterless block or lambda; `_1`, `_2` | `it` in a parameterless block whose type takes one argument (`xs.map { it * 2 }`); an error in a lambda, a block with parameters, or a block type taking none or two or more; a nested block's `it` hiding an enclosing one warns. No numbered parameters (01-syntax.md §9) |
| Block and lambda parameter defaults | `{ \|x, y = 1\| }`, `->(x, y = 1) { }` | None: the procedure type decides how many arguments a block gets and their types |
| `for x in xs` | A loop; the variable stays visible after it | A comprehension returning the body's values (`map`, `flat_map` for several iterators, `filter` for `when` guards); the variables stay inside. For a loop, use `each` |
| `Thread`, `Mutex`, `Queue`, `Fiber` | Exist | `Task.spawn`, `Task.scope`, `Channel`, `Atom` |
| `Thread#join`, `Thread#value` | Wait for a thread (and take its value) | `Task#await` |
| `require` | Loads at runtime | Resolved at compile time (same syntax) |
| RubyGems, Bundler (`Gemfile`) | Packages installed from rubygems.org, then `require`d | Cogs: git repositories pinned to a commit in `Cog.lock`, each under its own module, visible without `require` ([10-cogs.md](10-cogs.md)) |
| `puts`, `p` and the other `Kernel` functions | Private methods of every object: a subclass's `def puts` takes over its superclass's calls of `puts` | Functions: a call is resolved where it is written, and a subclass's `def puts` does not take it over. `::puts` calls the function where a method `puts` of `self` hides it, and `Kernel.puts` (private in Ruby) always the built-in |
| Top-level `def` | Private method of `Object`: `self` in it is the caller's | A function of its cog (in a script, of the file and those that require it), run with its own file's top-level object (`main`) as `self` wherever it is called from |
| Arbitrary expressions in a class body | Executed | Declarations only (constant initializers are allowed) |
| `respond_to?` | Runtime | Compile-time constant |
| `obj.method(:foo)` | `Method` | `obj.:foo` (a procedure) |
| `Comparable`, `Enumerable` | Modules | Same, but generic (`Comparable[T]`, `Enumerable[T]`) |
| `<` between classes | `A < B` is strict: `Object < Object` is false | In a type parameter's bound, `T <: X` is reflexive: `T` may be `X` itself (02-types.md §3) |
| `Array[1, 2]` | Creates an array | `Array[Int]` is a type. Arrays are `[1, 2]` |
| Redefining a method with the same name | Overwrites | Overloading by parameter types. Redefining the same signature is an error |
| `nil?`, `is_a?`, `equal?`, `==` | Any class may redefine them (`equal?` should not be, by its documentation) | `nil?` and `is_a?` (the checker narrows types by them) and `equal?` (identity) cannot be defined; a class's own `==`/`!=` takes an `Object` (01-syntax.md §3) |
| Exceptions `rescue => e` | `StandardError` | Same. `Task::Cancelled` is directly under `Exception`, so it is not caught |
| Pattern variables | Bound as the match reaches them: a pattern that fails partway leaves those bound before; a `case/in` arm's names are locals of the method, seen after the `case` | Bound only once the whole pattern matched; a `case/in` arm's names are the arm's own (shadowing, not seen after it); `in`/`=>` bind into the enclosing scope |
| Block-local variables `\|x; y\|` | `y` is the block's own, hiding an outer `y` | Not available: declare in the block, `y := nil` or `y: T = ...`, which hides an outer `y` in any scope (01-syntax.md §10) |
| The variable of `rescue E => e` | A local of the method: it stays after the `begin` (and `ensure`/`else` see it) | The clause's own, as a block's parameter: it shadows an outer local of the name, which is unchanged after; `ensure`, `else` and the code after the `begin` do not see it |
| `raise e` with `e` kept | Sets `e`'s backtrace and cause | When `e` lacks them, raises a copy given them (exceptions are immutable): `e` keeps none, and the exception rescued is not `equal?` to `e` (06-stdlib.md) |

## What is added

- Type annotations: `x: Int`, `-> Int`, `T?`, `A | B`, `Array[T]`, `(A) -> B`, `[A, B]`
- `data`, `enum`, `var`, `abstract`, `extension`, `using` (now a keyword), `type`, `extern`
- `as`/`as?`
- Builder types such as `Array::Builder`, and `Array.build { }`
- `Task.spawn`, `Task`, `Task.scope`, `Task.blocking`, `Channel`, `Channel.select`, `Atom` (`Supervisor` is planned)
- `Result[T, E]`
- `Shareable` (an automatically derived marker)
- `obj.:method` (method reference)
- Blocks with a receiver (`Html.() -> Void`, run with `instance_exec`) for DSLs, and `using M do ... end`
- Nil-returning variants such as `[]?` and `gets?`

## Rewriting example

```rb
# Ruby
class Inventory
  def initialize
    @items = Hash.new(0)
  end

  def add(name, qty = 1)
    @items[name] += qty
  end

  def report
    @items.map { |name, qty| "#{name}: #{qty}" }.join("\n")
  end
end
```

```ruby
# Quarz (immutable style)
class Inventory
  @items: Hash[String, Int]

  def initialize(@items: Hash[String, Int] = {}); end

  def add(name: String, qty: Int = 1) -> Inventory
    Inventory.new(@items.update(name) { |q| (q || 0) + qty })
  end

  def report -> String
    @items.map { |name, qty| "#{name}: #{qty}" }.join("\n")
  end
end

puts Inventory.new.add("apple").add("pear", 2).report
```

```ruby
# Quarz (mutable style, for task-local use)
class Inventory
  var @items: Hash[String, Int] = {}

  def add(name: String, qty: Int = 1) -> Void
    @items = @items.update(name) { |q| (q || 0) + qty }
  end

  def report -> String
    @items.map { |name, qty| "#{name}: #{qty}" }.join("\n")
  end
end
```
