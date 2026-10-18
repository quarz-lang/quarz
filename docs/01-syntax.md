# Syntax

日本語版: [01-syntax.ja.md](01-syntax.ja.md)

The syntax of Quarz is based on Ruby, with only the minimal changes needed to "define statically" and "default to immutable". This document focuses on the differences from Ruby. Everything that is the same as Ruby (operator precedence, string literals, heredocs, `%w[]`, the `if` modifier, `unless`/`until`, `begin/rescue/ensure`, the ternary operator, `&.`, and so on) follows the Ruby 3.x specification in principle.

## 1. Lexical structure

- Source files are UTF-8. The extension is `.qz`.
- Comments are `#` only (`=begin`/`=end` are dropped).
- Global variables starting with `$` and class variables starting with `@@` **do not exist** (to remove shared mutable state from the language; the replacement is `Atom` in [04-concurrency.md](04-concurrency.md)).
- Numeric literals: `42`, `1_000_000`, `0xff`, `0b1010`, `0o755`, `3.14`, `1e-9`. The `r`/`i` suffixes are dropped.
- Symbols `:foo`, `:"with space"`, `%i[a b]` are interned at compile time.
- Regexp literals `/.../` and `%r{...}` are compiled at compile time and become `Regexp` constants.
- String-like literals are `"..."`, `'...'`, `%q()`, `%Q()`, `%()`, `%w[]`, `%i[]` and heredocs (`<<~EOS`, `<<-EOS`, `<<EOS`, `<<~'EOS'`). Ruby's `?a` character literal, `%W`/`%I` (interpolating arrays), `%s`, `%x` and backquotes are dropped.
- Lexing stops at a line consisting only of `__END__`; the rest can be read as `DATA` (an `IO`).

### Contextual keywords

The following words are treated as keywords **only in declaration positions**; elsewhere they are ordinary identifiers (`type = "json"` and `data = fetch` are valid).

| Word | Context in which it is recognized |
|---|---|
| `data` | At the start of a line, followed by `data ConstantName(` |
| `enum` | At the start of a line, followed by `enum ConstantName` |
| `var` | Followed by `var @name` / `var @name:` |
| `abstract` | `abstract class` / `abstract def` |
| `override` | `override def` |
| `extension` | At the start of a line, followed by `extension Type` |
| `using` | At the start of a line, followed by `using Constant` |
| `type` | At the start of a line, followed by `type Constant =` |
| `extern` | At the start of a line, followed by `extern def` / `extern "C"` |

Of Ruby's reserved words, `defined?`, `undef`, `redo`, `BEGIN`, `END`, `__ENCODING__` and `for` are dropped. The others (`alias`, `retry`, `yield`, `super`, `self`, `and`/`or`/`not`, etc.) are kept.

## 2. Program structure

- One file = one compilation unit (module). `require "path"` and `require_relative "path"` are resolved **at compile time**, and the dependency graph is determined statically.
- Statements may appear at the top level. `quarz run hello.qz` runs a one-line script `puts "Hello"`. Top-level statements of a library file are executed once, at `require` time.
- A top-level `def` becomes a function visible only within that file (it does not become a private method of `Object` as in Ruby).
- Declarations (`class`/`module`/`data`/`enum`/`def`/`type`/constants) are **hoisted**. They can be referenced from lines before their definition within the file, and mutual recursion can be written.
- Program arguments are `ARGV`, environment variables are `ENV`, and the standard streams are the constants `STDIN`/`STDOUT`/`STDERR`.

```ruby
# hello.qz
require "json"

def greet(name: String) -> String
  "Hello, #{name}!"
end

puts greet(ARGV.first? || "world")
```

## 3. Classes

```ruby
class Account
  @id: Int                 # immutable field; can only be assigned in initialize
  @owner: String
  var @balance: Int = 0    # mutable field; this class is no longer Shareable

  attr_reader :id, :owner, :balance

  def initialize(id: Int, owner: String)
    @id = id
    @owner = owner
  end

  def deposit(amount: Int) -> Nil
    raise ArgumentError, "amount must be positive" unless amount > 0
    @balance += amount
  end

  def to_s -> String = "#{owner}: #{balance}"
end

acct = Account.new(1, "alice")
acct.deposit(100)
puts acct          # => alice: 100
```

Differences from Ruby:

- **Fields must be declared.** They are declared with `@name: Type`, and the object layout is fixed at compile time. Assigning to an undeclared instance variable is a compile error.
- **Fields are immutable by default.** They must be assigned exactly once inside `initialize` (definite assignment analysis). With an initializer (`@tags: Array[String] = []`) the assignment can be omitted.
- **Mutable fields are declared with `var`.** A class with a `var` field, or with a field of a non-Shareable type, is not Shareable ([03-data-model.md](03-data-model.md)).
- **Classes cannot be reopened.** Defining a class with the same name twice is an error. Adding methods to an existing class is done with `extension` (§7).
- **Class bodies contain only declarations.** Field declarations, method definitions, `include`/`extend`, `attr_*`, constants, nested types and visibility specifiers (`private`/`protected`/`public`) are allowed. Arbitrary expressions are not.
- `attr_reader`/`attr_writer`/`attr_accessor` are built-in declarations that generate accessor methods for declared fields (`attr_writer`/`attr_accessor` can only be used on `var` fields).
- Prefixing an `initialize` parameter with `@` also assigns the field (same as Crystal):

```ruby
class Account
  @id: Int
  @owner: String
  var @balance: Int = 0

  def initialize(@id: Int, @owner: String); end
end
```

### Inheritance and abstract classes

```ruby
abstract class Shape
  abstract def area -> Float

  def describe -> String = "#{self.class.name} with area #{area}"
end

class Circle < Shape
  @radius: Float
  def initialize(@radius: Float); end

  override def area -> Float = Math::PI * @radius ** 2
end
```

- Single inheritance. An `abstract class` cannot be instantiated and an `abstract def` has no body.
- `override` is optional, but a method marked with it that does not exist in the parent is an error, and overriding a parent method without it is a warning.
- Since the class hierarchy is fixed at compile time for the whole program, the compiler automatically turns calls to methods that are never overridden into static calls (no `final` needed).
- `super` works as in Ruby. A bare `super` passes the same arguments.

## 4. Data types (`data`)

Immutable record types, corresponding to Ruby 3.2's `Data`.

```ruby
data Point(x: Int, y: Int)

data Line(from: Point, to: Point) do
  def length -> Float
    Math.sqrt((to.x - from.x) ** 2 + (to.y - from.y) ** 2)
  end
end

p1 = Point.new(1, 2)
p2 = Point.new(x: 3, y: 4)         # keywords also work
p3 = p1.with(y: 10)                # a copy with some fields changed
p1 == Point.new(1, 2)              # => true (structural equality)
case p3
in Point(x:, y:) then puts "#{x}, #{y}"
end
```

`data` generates the following automatically: fields (immutable), reader methods, `initialize`, `==`/`hash`, `to_s`/`inspect`, `with`, `deconstruct`/`deconstruct_keys`, `to_h`. To add methods, write them in a `do ... end` body. `data` types cannot be inherited (they can `include`).

## 5. Enumerations (`enum`)

Sum types (algebraic data types). Each variant can carry data.

```ruby
enum Shape
  Circle(radius: Float)
  Rect(width: Float, height: Float)
  Point

  def area -> Float
    case self
    in Circle(radius:) then Math::PI * radius ** 2
    in Rect(width:, height:) then width * height
    in Point then 0.0
    end
  end
end

s = Shape::Circle.new(2.0)
s.area
```

- Variants can be referenced as nested types like `Shape::Circle`, and each is a subtype of `Shape`.
- A variant without data (`Point`) is a singleton; writing `Shape::Point` yields the value.
- `case/in` checks exhaustiveness. Missing a variant is a compile error.
- The standard library's `Result[T, E]` is `enum Result[T, E]; Ok(value: T); Err(error: E); end`.

## 6. Modules

As in Ruby, modules serve both as namespaces and as mixins. A module with abstract methods is the static replacement for Ruby's "interface expected through duck typing".

```ruby
module Comparable[T]
  abstract def <=>(other: T) -> Int

  def <(other: T) -> Bool = (self <=> other) < 0
  def between?(min: T, max: T) -> Bool = self >= min && self <= max
  # ...
end

data Version(major: Int, minor: Int) do
  include Comparable[Version]
  def <=>(other: Version) -> Int
    [major, minor] <=> [other.major, other.minor]
  end
end
```

- `include` mixes into the instance side, `extend` into the class side (`self.` methods).
- There are no dynamic mechanisms such as `prepend`, `module_function` or the `included` hook.
- Modules can be used as types (`def sort[T: Comparable[T]](xs: Array[T])`).

## 7. Extensions (`extension`) and `using`

A mechanism for adding methods to existing types after the fact. It is the static version of Ruby's refinements and is confined to a **lexical scope**.

```ruby
module StringShout
  extension String
    def shout -> String = upcase + "!"
  end

  extension Int
    include Describable           # make an existing type conform to a module after the fact
    def describe -> String = "the number #{self}"
  end
end

using StringShout
"hi".shout          # => "HI!"
```

- `using` can be written in a file or inside a `class`/`module` body, and is in effect until the end of that lexical scope.
- Resolution of extension methods is **entirely at compile time**. It is determined only by the static type of the receiver and the `using`s in effect at that position; there is no runtime table rewriting.
- If an extension defines a method with the same name as an existing one, the extension's method is statically chosen within that scope (the same "override only where visible" as Ruby's refinements). To prevent unintended overrides, a warning is issued unless `override` is present.
- `include` inside an extension makes an existing type conform to a module after the fact (equivalent to Swift's `extension Int: Describable`). This is the only way to "make a class you did not write satisfy an interface".
- Generic types can be extended too, with constraints on the type arguments: `extension Array[T: Describable]; def describe_all -> String = map(&:describe).join(", "); end`.

## 8. Type aliases and constants

```ruby
type UserId = Int
type Handler = (Request) -> Response

MAX_RETRY = 3
DEFAULT_HEADERS = { "Content-Type" => "application/json" }
```

- Constants are bound once, and their values must be Shareable (constants are visible from all tasks).
- Constant initializers are evaluated once, in dependency order, when the module is loaded.

## 9. Method definitions

```ruby
def name(a: Int, b: String = "x", *rest: Int, *, flag: Bool, limit: Int? = nil, **opts: String, &block: (Int) -> Nil) -> Ret
```

| Syntax | Meaning |
|---|---|
| `a: Int` | Required parameter. Can be passed positionally or by keyword (`name(a: 1)`) |
| `b: String = "x"` / `b = "x"` | Optional parameter. The type may be omitted if it can be inferred from the default value |
| `*rest: Int` | Variadic parameter. The type of `rest` is `Array[Int]` |
| `*` | Everything after this is keyword-only |
| `flag: Bool` (after `*`) | Required keyword parameter |
| `**opts: String` | Remaining keywords. The type is `Hash[Symbol, String]` |
| `&block: (Int) -> Nil` | Block parameter. The type is a procedure type |
| `-> Ret` | Return type. If omitted it is inferred from the body (required for recursive methods) |

- **Parameter types are required** (except where they can be inferred from a default value). Because types are fixed at method boundaries, per-file separate compilation and fast type checking are possible.
- Ruby 3's "separation of positional and keyword arguments" is unnecessary in Quarz because an argument list never implicitly becomes a `Hash`. Parameters before `*` can be passed either positionally or by keyword (same as Python/Crystal).
- A method whose return type is `Nil` discards the value of the last expression in its body (equivalent to `void`).
- Methods of the same name can be **overloaded** by parameter count and types. Resolution is at compile time.
- One-line definitions (endless def) such as `def x -> Int = @x` are allowed.
- Operator methods (`+`, `[]`, `<=>`, `-@`, `==`, `call`, etc.) are defined with the same names as in Ruby. `[]=` can only be defined on mutable types.
- `def self.create(...)` defines a class method. `private`/`protected`/`public` are written as in Ruby and checked at compile time.
- `alias new_name old_name` creates an alias statically.

### Blocks, `yield` and procedures

```ruby
def each_pair(&block: (Int, Int) -> Nil) -> Nil
  yield 1, 2
  yield 3, 4
end

def map[U](&block: (T) -> U) -> Array[U]
  Array.build do |out|
    each { |x| out << yield(x) }
  end
end

each_pair { |a, b| puts a + b }
each_pair do |a, b|
  puts a * b
end

double = ->(x: Int) { x * 2 }          # a procedure (equivalent to a Ruby lambda)
[1, 2, 3].map(&double)
[1, 2, 3].map(&:to_s)
```

- Block parameter types are inferred from the type of the callee's `&block`. To be explicit, write `{ |x: Int| ... }`.
- A block that is only invoked with `yield` (a non-escaping block) is expanded by the compiler without allocating a closure. Only when `&block` **escapes**, by being stored in a variable or returned, does it become a heap-allocated closure.
- `break`/`next`/`return` inside a block mean the same as in Ruby. `next` returns the block's value, `break` exits the call the block was passed to, and `return` returns from the enclosing method.
- `->(x) { }` is the same as a Ruby lambda (strict arity, `return` returns from the procedure). `Proc.new` and `proc` are dropped; procedures are created with `->` or from blocks.
- `&:name` is a compile-time transformation to `{ |x| x.name }`.
- Procedure types are written like `(Int, String) -> Bool`. Passing a block to a method that does not take one is a compile error.

## 10. Variables and assignment

```ruby
x = 1                  # inferred as Int
x = "one"              # error: a local variable's type is fixed at declaration (reassignment must have the same type)
y: Int? = nil          # with a type annotation
y = 10                 # OK
a, b = 1, 2            # multiple assignment (tuple)
first, *rest = [1, 2, 3]
count += 1
name ||= "anon"        # when name is T?
```

- The type of a local variable is determined by its first assignment. To widen the type, add an annotation (`y: Int? = nil`).
- After an assignment the type is narrowed by **flow typing** (after `y = 10`, `y` can be treated as `Int`).
- The rules for variable declaration and scope (a variable assigned inside an `if` is visible afterwards, block parameters are visible only within the block, etc.) are the same as in Ruby.
- Assignment to an `@ivar` is only possible inside `initialize` if the field is immutable.

## 11. Expressions and control structures

Same as Ruby: `if`/`unless`/`elsif`/`else`, `while`/`until`, modifier forms, `case/when`, `case/in`, `begin/rescue/else/ensure`, `loop`, `break`/`next`/`retry`/`return`, `and`/`or`/`not`, `&&`/`||`/`!`, `..`/`...` (including endless ranges), `&.`, `=>` (rightward assignment / pattern), `in` (pattern test), string interpolation `#{}`, `__FILE__`/`__LINE__`/`__method__`.

Different from Ruby:

- There is no `for` (use `each`).
- All control structures are expressions (as in Ruby), but if the branches of an `if` have different types, the result is a union type. An `if` without `else` has type `T?`.
- Truthiness is as in Ruby: only `nil` and `false` are falsy. However, a condition that is known from its type to be always true / always false (`if 3`, `if some_int`) produces a warning.
- Variable types are narrowed by `while` and `if` conditions ([02-types.md](02-types.md) §6).

### Pattern matching

Ruby 3's `case/in` is adopted as is, with static checks added.

```ruby
case event
in Click(x:, y:) if x > 100 then handle_right(x, y)
in Key(code: :escape | :q) then quit
in Key(code:) then type(code)
in [first, *rest] then ...
in { name: String => name, age: Int => age } then ...
in ^expected then ...
in Int | Float => n then ...
in nil then ...
end
```

- Available patterns: value patterns, pin `^x`, alternatives `|`, array patterns (`*rest`, find pattern), hash patterns, `Const(...)`/`Const[...]` (`deconstruct`/`deconstruct_keys`), binding `=> name`, guards `if`/`unless`, `nil`.
- `case/in` on `data`/`enum`/union types checks exhaustiveness. If the patterns are not exhaustive, an `else` is required; without either exhaustiveness or `else` it is a compile error. `case/in` on a class hierarchy is open, so without an `else` it raises `NoMatchingPatternError` at runtime (with a warning).
- The variables bound by a pattern and the narrowed type of the receiver are statically known within that branch.
- `expr => Point(x:, y:)` raises on failure; `expr in Point` returns a `Bool` and narrows.

## 12. Exceptions

```ruby
class ParseError < StandardError
  @line: Int
  attr_reader :line
  def initialize(message: String, @line: Int)
    super(message)
  end
end

begin
  parse(src)
rescue ParseError => e
  warn "line #{e.line}: #{e.message}"
  retry if (tries += 1) < 3
rescue IOError, SystemCallError
  raise
else
  puts "ok"
ensure
  cleanup
end

value = risky rescue default   # the modifier form is also allowed
```

- The exception hierarchy follows Ruby (`Exception` > `StandardError` > ...). The argument of `raise` is an exception class, an exception object, or a string (`RuntimeError`).
- Exceptions are handled within the task that raised them. The handling of exceptions that escape a task is described in [04-concurrency.md](04-concurrency.md).
- Exception objects must be Shareable (because they propagate to other tasks).
- The type of `raise` is `Nothing` (the bottom type), so narrowing such as `x = arg || raise ArgumentError` is possible.

## 13. String, array and hash literals

```ruby
s  = "name: #{name}\n"     # String
s2 = 'raw \n'
s3 = <<~EOS
  heredoc
EOS
a  = [1, 2, 3]             # Array[Int]
t  = [1, "a"]              # [Int, String] if the context requires a tuple type, otherwise Array[Int | String]
h  = { name: "alice", age: 30 }     # Hash[Symbol, String | Int]
h2 = { "a" => 1, "b" => 2 }         # Hash[String, Int]
r  = 1..10                 # Range[Int]
set = Set[1, 2, 3]         # Set[Int]
bytes = b"\x00\xff"        # Bytes (binary)
```

- Strings are always UTF-8 and immutable. Binary data is a separate type, `Bytes`.
- `Array`/`Hash`/`Set` created from literals are immutable persistent data structures. The empty literals `[]` and `{}` take their element types from the context ([02-types.md](02-types.md) §5).
- The keys of `{ a: 1 }` are `Symbol`s; the keys of `{ "a" => 1 }` are `String`s. Mixing them gives `Hash[Symbol | String, Int]`.

## 14. FFI

```ruby
extern "C"
  def strlen(s: CString) -> SizeT
  def getpid -> Int32
end

puts strlen("hello")
```

C functions can be declared and called directly. There are FFI types such as `CString`, `Pointer[T]` and the fixed-width integers. C functions that may block are called inside `Task.blocking { }`.
