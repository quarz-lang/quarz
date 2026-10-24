# Changes from Ruby: Quick Reference

日本語版: [07-ruby-diff.ja.md](07-ruby-diff.ja.md)

A summary of the things someone who knows Ruby will first stumble on when starting to write Quarz.

## What works as is

`def ... end`, `class`/`module`, `include`/`extend`, `attr_reader` and friends, blocks (`do ... end`/`{ }`), `yield`, `&block`, `&:sym`, `if`/`unless`/`while`/`until` and their modifier forms, `case/when`, `case/in` (pattern matching), `begin/rescue/ensure/retry`, `raise`, string interpolation, heredocs, `%w[]`/`%i[]`, symbols, ranges, regexp literals, `&.`, `||=`, multiple assignment, `*splat`, keyword argument call syntax, `private`/`protected`, `self.` methods, operator definitions, `<=>` and `Comparable`, `Enumerable`, `super`, `alias`, `__FILE__`/`__LINE__`, `ARGV`, `ENV`, `puts`/`p`/`pp`.

## What changes

| Item | Ruby | Quarz |
|---|---|---|
| Method parameters | `def f(a, b = 1, k:)` | `def f(a: Int, b: Int = 1, *, k: Bool)` — parameter types are required |
| Return type | Not part of the language (signatures can be written in RBS files beside the code, or with Sorbet's `sig`) | `def f(...) -> Int` (inferred if omitted) |
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
| `for x in xs` | A loop; the variable stays visible after it | A comprehension returning the body's values (`map`, `flat_map` for several iterators, `filter` for `when` guards); the variables stay inside. For a loop, use `each` |
| `Thread`, `Mutex`, `Queue`, `Fiber` | Exist | `spawn`, `Task.scope`, `Channel`, `Atom` |
| `Thread#join`, `Thread#value` | Wait for a thread (and take its value) | `Task#await` |
| `require` | Loads at runtime | Resolved at compile time (same syntax) |
| RubyGems, Bundler (`Gemfile`) | Packages installed from rubygems.org, then `require`d | Cogs: git repositories pinned to a commit in `Cog.lock`, each under its own module, visible without `require` ([10-cogs.md](10-cogs.md)) |
| Top-level `def` | Private method of `Object` | A function within that file |
| Arbitrary expressions in a class body | Executed | Declarations only (constant initializers are allowed) |
| `respond_to?` | Runtime | Compile-time constant |
| `obj.method(:foo)` | `Method` | `obj.:foo` (a procedure) |
| `Comparable`, `Enumerable` | Modules | Same, but generic (`Comparable[T]`, `Enumerable[T]`) |
| `Array[1, 2]` | Creates an array | `Array[Int]` is a type. Arrays are `[1, 2]` |
| Redefining a method with the same name | Overwrites | Overloading by parameter types. Redefining the same signature is an error |
| Exceptions `rescue => e` | `StandardError` | Same. `Task::Cancelled` is directly under `Exception`, so it is not caught |

## What is added

- Type annotations: `x: Int`, `-> Int`, `T?`, `A | B`, `Array[T]`, `(A) -> B`, `[A, B]`
- `data`, `enum`, `var`, `abstract`, `extension`, `using` (now a keyword), `type`, `extern`
- `as`/`as?`
- Builder types such as `Array::Builder`, and `Array.build { }`
- `spawn`, `Task`, `Task.scope`, `Task.blocking`, `Channel`, `select`, `Atom` (`Supervisor` is planned)
- `Result[T, E]`
- `Shareable` (an automatically derived marker)
- `obj.:method` (method reference)
- Blocks with a receiver (`Html.() -> Nil`, run with `instance_exec`) for DSLs, and `using M do ... end`
- Nil-returning variants such as `[]?` and `gets?`

## Rewriting example

```ruby
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

  def add(name: String, qty: Int = 1) -> Nil
    @items = @items.update(name) { |q| (q || 0) + qty }
  end

  def report -> String
    @items.map { |name, qty| "#{name}: #{qty}" }.join("\n")
  end
end
```
