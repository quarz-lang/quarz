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
- Lexing stops at a line consisting only of `__END__`; the rest is ignored (reading it as `DATA`, an `IO`, is planned).

### Contextual keywords

The following words are treated as keywords **only in declaration positions**; elsewhere they are ordinary identifiers (`type = "json"` and `data = fetch` are valid).

| Word | Context in which it is recognized |
|---|---|
| `data` | At the start of a line, followed by `data ConstantName =` or `data ConstantName(` |
| `enum` | At the start of a line, followed by `enum ConstantName` |
| `variant` | In the body of an `enum`, followed by `variant ConstantName` |
| `var` | Followed by `var @name` / `var @name:` |
| `abstract` | `abstract class` / `abstract def` |
| `extension` | At the start of a line, followed by `extension Type` |
| `using` | At the start of a line, followed by `using Constant` |
| `type` | At the start of a line, followed by `type Constant =` |
| `extern` | At the start of a line, followed by `extern def` / `extern "C"` (FFI is planned, §14) |
| `for` | `for variable in` (a comprehension, §11) |

Of Ruby's reserved words, `defined?`, `undef`, `redo`, `BEGIN`, `END`, and `__ENCODING__` are dropped (`for` returns as a contextual keyword with a different meaning, §11). The others (`alias`, `retry`, `yield`, `super`, `self`, `and`/`or`/`not`, etc.) are kept.

## 2. Program structure

- One file = one compilation unit (module). `require "name"` loads a standard library module (`std/name.qz`, embedded in the interpreter) and `require_relative "path"` loads a file relative to the requiring one (`.qz` is appended when there is no extension). Both are resolved **at compile time**: the dependency graph is determined statically, each file is loaded once, and a circular `require` is an error. A standard library module that the program names (`JSON`, `TCPSocket`) is loaded without `require` too, unless the program declares one of its names itself. A **cog**, a package fetched from a git repository, is loaded whole from the manifest that names it, without `require`, and its declarations appear under its own module ([10-cogs.md](10-cogs.md)).
- Statements may appear at the top level. `quarz run hello.qz` runs a one-line script `puts "Hello"`. The top-level statements of a required file run once, before those of the file that requires it (dependencies first, in depth-first order).
- Classes, modules, data types, enums, constants and type aliases declared in a required file are visible everywhere; top-level `def`s and `using`s stay private to their file.
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
- **Fields are immutable by default.** They must be assigned inside `initialize` (definite assignment analysis), where they may be reassigned. With an initializer (`@tags: Array[String] = []`) the assignment can be omitted.
- **A field is never seen before it is assigned.** A field whose type does not admit `nil` and that has no initializer (`var` or not) must be assigned on every path through `initialize`, and the object may not be used until all such fields are: no `self`, no call on the implicit receiver to a method of the class (or of a module it includes), no read of a field not yet assigned, and no block that does one of these. `raise` and functions such as `puts` are fine; a `return` must come after the assignments. A subclass assigns its own such fields *before* calling `super` (so a method the superclass's `initialize` calls, and the subclass overrides, sees them), and `super` assigns the inherited ones. A class with such a field of its own must define `initialize`. Field initializers run first, in declaration order, and may read the fields declared before them but not use the object otherwise. Hence a field always holds a value of its declared type (`@x: Float` is a `Float`, never `nil`), which compiled code relies on.
- **Mutable fields are declared with `var`.** A class with a `var` field, or with a field of a non-Shareable type, is not Shareable ([03-data-model.md](03-data-model.md)).
- **Classes cannot be reopened.** Defining a class with the same name twice is an error. Adding methods to an existing class is done with `extension` (§7).
- **Class bodies contain only declarations.** Field declarations, method definitions, `include`/`extend`, `attr_*`, constants, nested types and visibility specifiers (`private`/`protected`/`public`) are allowed. Arbitrary expressions are not.
- **Visibility is checked statically, as in Ruby.** A `private` method is called only on `self` (implicitly or as `self.`); a `protected` one also on another receiver, but only from code whose `self` is an instance of the class or module that defines it, or of a descendant (`def richer?(o: Account) = balance > o.balance`). A class method's `self` is a class, so it cannot call an instance's protected method. `private`/`protected`/`public` apply to the methods after them, to the one they prefix (`private def f`), or to the ones they name (`protected :f`).
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

  def area -> Float = Math::PI * @radius ** 2
end
```

- Single inheritance. An `abstract class` cannot be instantiated and an `abstract def` has no body.
- A method with the name of a parent's method overrides it; as in Ruby and Crystal, nothing marks it (no `override`).
- Since the class hierarchy is fixed at compile time for the whole program, the compiler automatically turns calls to methods that are never overridden into static calls (no `final` needed).
- `super` works as in Ruby. A bare `super` passes the same arguments.

## 4. Data types (`data`)

Immutable record types, corresponding to Ruby 3.2's `Data`.

```ruby
data Point = (x: Int, y: Int)

data Line(from: Point, to: Point)
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

`data` generates the following automatically: fields (immutable), reader methods, `initialize`, `==`/`hash`, `to_s`/`inspect`, `with`, `to_h`. (`deconstruct`/`deconstruct_keys` methods are not generated: patterns read the declared fields directly, §11.) A `data` type without methods is written on one line with `=` (`data Point = (x: Int, y: Int)`), like the one-line `enum`; without `=`, a body with methods follows and `end` closes it. `data` types cannot be inherited (they can `include`).


### Data values stored in place

A field (of a class or of another data type) whose declared type is a small immutable data type is stored *by value* inside the object: a data type whose fields are all `Int`, `Float`, `Bool` or such data types, with no type parameters and no `==`, `hash` or `equal?` of its own. `var @pos: Vec2` keeps `x` and `y` in the particle itself, so `@pos = @pos + @vel.scale(dt)` allocates nothing. Reading such a field gives a value equal to the one stored, but not the same object: `p.pos.equal?(p.pos)` is false, as it is for two `Vec2.new(1.0, 2.0)`. Everything else (`==`, `hash`, `inspect`, `with`, `to_h`, patterns, JSON) sees the declared fields. A nilable field (`Vec2?`), a union or a data type with its own equality keeps its reference.

## 5. Enumerations (`enum`)

Sum types (algebraic data types). Each variant can carry data. A body declares them with `variant`; the one-line form separates them by `|`, as in a union type.

```ruby
enum Color = Red | Green | Blue              # no body: one line, no `end`

enum Shape
  variant Circle(radius: Float)
  variant Rect(width: Float, height: Float)
  variant Point

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
- In the block form, `variant` declares variants, one or several per line (`variant Hearts, Spades`), alongside the methods, as `def` declares methods. The one-line form `enum Name = A | B` declares an enum without a body and needs no `end` (like `data Name = (...)`); a line that ends with `|` continues on the next.
- The standard library's `Result[T, E]` is `enum Result[T, E] = Ok(value: T) | Err(error: E)` plus its methods.

## 6. Modules

As in Ruby, modules serve both as namespaces and as mixins. A module with abstract methods is the static replacement for Ruby's "interface expected through duck typing".

```ruby
module Comparable[T]
  abstract def <=>(other: T) -> Int

  def <(other: T) -> Bool = (self <=> other) < 0
  def between?(min: T, max: T) -> Bool = self >= min && self <= max
  # ...
end

data Version(major: Int, minor: Int)
  include Comparable[Version]
  def <=>(other: Version) -> Int
    [major, minor] <=> [other.major, other.minor]
  end
end
```

- `include` mixes into the instance side, `extend` into the class side (`self.` methods).
- **Contracts are checked.** A concrete class (a `class` that is not `abstract`, a `data`, an enum variant) must implement every abstract method it inherits or includes; a missing one is a compile error (`` `Version` must implement `<=>` (abstract in `Comparable`) ``). A class that `extend`s `M` implements `M`'s abstract methods as `def self.name`. The module's default methods work on the class side too (`extend Named` makes `Thing.greeting` call `Thing.label`).
- A module plays one of three roles with one keyword: a namespace (`Math`, `JSON`), a contract with default methods (`Comparable`, `Enumerable`) or a marker (`Shareable`). Name contracts with adjectives or `-able`, namespaces with nouns. Including or extending a namespace module (one with no instance methods) adds nothing, so it is a warning.
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

- `using` can be written in a file, inside a `class`/`module` body, or inside a method or block body, and is in effect until the end of that lexical scope (the statement list it appears in). `using M do ... end` / `using M { ... }` is an expression: the extensions are active in its body only and its value is the body's.
- A block parameter can carry a `using`: `def where(&: () -> Cond using SqlDSL)`. A block literal written at a call site is then checked as if it began with `using SqlDSL` (nested blocks included), so a DSL applies its own extensions to the caller's block without the caller naming them; this is the static form of Ruby's `Proc#refined`. The `using` is not part of the procedure type: an existing procedure value passed with `&proc` is unaffected.
- Resolution of extension methods is **entirely at compile time**. It is determined only by the static type of the receiver and the `using`s in effect at that position; there is no runtime table rewriting. In particular a module's extension does not take part in dynamic dispatch: a call through a supertype (`s.name` with `s: Shape` holding a `Circle`) runs the class's method even inside `using`, and outside `using` the extension is unreachable. The exception is conformance: the methods of a module the extension `include`s dispatch to the extension's implementations wherever the value goes, since a value typed as that module may have been made where the extension was visible. `&:name` uses the method resolved for the block's parameter type where it is written. An extension declared outside any module is active everywhere, in dynamic dispatch too.
- If an extension defines a method with the same name as an existing one, the extension's method is statically chosen within that scope (the same "override only where visible" as Ruby's refinements).
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
- Constant initializers are evaluated once, in dependency order, when the module is loaded. (Currently each is evaluated at the constant's first use: a task that uses a constant whose initializer another task is running waits for it, a constant used by its own initializer raises `RuntimeError`, and one whose initializer raised is evaluated again at its next use.)
- A constant whose initializer is a constant path naming a class or module is also an alias of it: after `P = Geometry::Point`, `P` serves in constant paths (`G::Point` after `G = Geometry`), types (`p: P`), patterns (`in P`) and `is_a?`, as well as a value (`P.new`). The class keeps its name (`P.name` is `"Geometry::Point"`).

## 9. Method definitions

```ruby
def name(a: Int, b: String = "x", *rest: Int, *, flag: Bool, limit: Int? = nil, **opts: String, &block: (Int) -> Nil) -> Ret
```

| Syntax | Meaning |
|---|---|
| `a: Int` | Required parameter. Can be passed positionally or by keyword (`name(a: 1)`) |
| `b: String = "x"` / `b = "x"` | Optional parameter. The type may be omitted if it can be inferred from the default value |
| `*rest: Int` | Variadic parameter. The type of `rest` is `Array[Int]` |
| `*` | Everything after this is keyword-only (the same holds after `*rest`) |
| `flag: Bool` (after `*`) | Required keyword parameter |
| `**opts: String` | Remaining keywords. The type is `Hash[Symbol, String]` |
| `&block: (Int) -> Nil` | Block parameter. The type is a procedure type; `block` is a procedure value (`block.call`, `block.()`, `block[]`) |
| `&: (Int) -> Nil` | Anonymous block parameter: only `yield` and forwarding with `f(&)` can use it |
| `-> Ret` | Return type. If omitted it is inferred from the body (required for recursive methods) |

- **Parameter types are required** (except where they can be inferred from a default value). Because types are fixed at method boundaries, compile times stay short and error messages clear.
- Ruby 3's "separation of positional and keyword arguments" is unnecessary in Quarz because an argument list never implicitly becomes a `Hash`. Parameters before `*` can be passed either positionally or by keyword (same as Python/Crystal).
- A method whose return type is `Nil` discards the value of the last expression in its body (equivalent to `void`).
- Methods of the same name can be **overloaded** by parameter count and types. Resolution is at compile time.
- One-line definitions (endless def) such as `def x -> Int = @x` are allowed.
- Operator methods (`+`, `[]`, `<=>`, `-@`, `==`, `call`, etc.) are defined with the same names as in Ruby. `[]=` can only be defined on mutable types (not checked yet). The unary operators are `-@`, `+@`, `~` and `!` (`!` and `~` may also be written `!@`/`~@`); `!x` calls the type's own `!` when it defines one and is the built-in negation (`true` for `nil` and `false`) otherwise. The static type decides, so an operand typed `Object` is negated even if its class defines `!`, and the built-in negation costs no check at run time. On a union, each value uses its member's `!` when that member defines one and the built-in negation otherwise (`!u` with `u: Cond | Nil` asks a `Cond`, negates `nil`), so a value answers the same through `Cond` and `Cond | Nil`; the type test this takes is paid only where such a union is the static type.
- `&&` and `||` can be defined too, taking the right operand as a block with no parameters: `def &&(&rhs: () -> Cond) -> Cond`. `a && b` (and `a and b`, `a || b`, `a or b`) is then the call `a.&&() { b }`, and the method decides whether `b` is evaluated, by calling the block; it may return any type (a query DSL builds an expression). `x &&= v` is `x = x.&&() { v }`, stored whatever it returns. As for `!`, the static type of the left operand decides, with no check at run time; unlike `!`, a union (`Cond?`) keeps the built-in short circuit, so `c && c.name` still narrows `c`. They cannot be defined on `Bool` or `Nil`.
- `def self.create(...)` defines a class method. As in Ruby, a class method runs on the class it is called on: in `Circle.describe`, inherited from `Shape`, an implicit call (`label`) goes to `Circle.label`, and `new` builds a `Circle` (`def self.build -> Self = new` gives a `Circle`). A subclass that inherits a class method calling `new` must take the same arguments in its `initialize` (it may add optional ones), or override the class method. `private`/`protected`/`public` are written as in Ruby and checked at compile time.
- `alias new_name old_name` creates an alias statically.

### Blocks, `yield` and procedures

```ruby
def each_pair(&: (Int, Int) -> Nil) -> Nil     # anonymous block: used with yield
  yield 1, 2
  yield 3, 4
end

def map[U](&: (T) -> U) -> Array[U]
  Array.build do |out|
    each { |x| out << yield(x) }
  end
end

def twice(&block: (Int) -> Int) -> Int          # named: a procedure value
  block.call(1) + block.(2) + block[3]
end

def forward(&: (Int) -> Int) -> Int = twice(&)  # `&` forwards the anonymous block

each_pair { |a, b| puts a + b }
each_pair do |a, b|
  puts a * b
end

double = ->(x: Int) { x * 2 }          # a procedure (equivalent to a Ruby lambda)
[1, 2, 3].map(&double)
[1, 2, 3].map(&:to_s)
```

- Block parameter types are inferred from the type of the callee's block parameter. To be explicit, write `{ |x: Int| ... }`; a union there goes in parentheses, `|x: (Int | String)|`, since `|` closes the parameters. Destructuring parameters (`|(a, b), c|`) are not supported; match in the body (`pair => [a, b]`).
- `yield` requires a block parameter (named or anonymous), since the block's type comes from its declaration; calling such a method without a block is a compile error, so an optional block is written `&block: ((Int) -> Nil)?`: the parameter is then `nil` when the caller gives no block, so the body calls it with `block.call` where it is not `nil` (`yield` cannot run it), and `&block` passes it on to another optional block.
- A block that is only invoked with `yield` (a non-escaping block) is expanded by the compiler without allocating a closure. Only when `&block` **escapes**, by being stored in a variable or returned, does it become a heap-allocated closure.
- `break`/`next`/`return` inside a block mean the same as in Ruby. `next` returns the block's value, `break` exits the call the block was passed to, and `return` returns from the enclosing method.
- `->(x) { }` is the same as a Ruby lambda (strict arity, `return` returns from the procedure). `Proc.new` and `proc` are dropped; procedures are created with `->` or from blocks.
- `&:name` is a compile-time transformation to `{ |x| x.name }`. As with Ruby's `Symbol#to_proc`, the method must be public: a private or protected one is an error, even where `x.name` could call it (`[1].each(&:puts)` is an error, `puts` being a private method of `Kernel`).
- Procedure types are written like `(Int, String) -> Bool`. Passing a block to a method that does not take one is a compile error.

### Blocks with a receiver

A procedure type can name a receiver: `Html.() -> Nil` is a block that runs with `self` = an `Html` (Kotlin's `Html.() -> Unit`). Such a block is declared as a named block parameter and run with `instance_exec`, which replaces its `self`; it is how DSLs are built.

```ruby
class Html
  var @parts: Array[String] = []
  def title(s: String) -> Nil = (@parts = @parts.push("<title>#{s}</title>"))
  def body(&b: Body.() -> Nil) -> Nil
    node = Body.new
    node.instance_exec(&b)              # the block's self is `node`
    @parts = @parts.push(node.render)
  end
end

def html(&build: Html.() -> Nil) -> Html
  h = Html.new
  h.instance_exec(&build)
  h
end

page = html do
  title "Hello"                         # Html#title
  body do
    p "world"                           # Body#p
  end
end
```

- Inside the block, `self` is the receiver and an implicit-self call is looked up on the receiver first. A method the receiver does not have is looked up on the enclosing receivers and finally on the lexical `self` (so `html { title(page_title) }` reaches the enclosing class's `page_title`); when both have it, the receiver's is called and the compiler warns.
- `@x` refers to the receiver's fields but is only allowed when the block is lexically inside that class's body, like any other field access.
- `return` returns from the enclosing method, `break` from the `instance_exec` call, `next` from the block, and `yield` goes to the enclosing method's block, as in any block.
- `instance_exec` is `Object#instance_exec[R](&: Self.() -> R) -> R` (with one- and two-argument overloads), so `5.instance_exec { self * 2 }` is `10`. `yield` cannot run a block with a receiver: name the parameter and call `recv.instance_exec(&name)`. A `->` lambda takes its receiver from the type it is assigned to (`f: String.() -> String = -> { upcase }`).
- The receiver position is contravariant: an `Object.() -> R` block can be passed where `Html.() -> R` is expected; a block with a receiver is not interchangeable with one without.
- A class that includes the marker module `DslScope` keeps nested builders apart: inside a block whose receiver is marked, the receivers of enclosing blocks that are marked too are not implicit (name them), while the enclosing method's `self` stays reachable. This is Kotlin's `@DslMarker`.
- A literal block given directly to `instance_exec` (`h.instance_exec { ... }`) is compiled in place, with `self` replaced by the receiver and no closure created, unless its body creates a closure of its own; a block passed on by name (`&build`) is a real closure.

## 10. Variables and assignment

```ruby
x = 1                  # inferred as Int
x = "one"              # error: a local variable's type is fixed at declaration (reassignment must have the same type)
y: Int? = nil          # with a type annotation
y = 10                 # OK
a, b = 1, "x"          # multiple assignment (the right-hand side is a tuple [Int, String])
first, *rest = [1, 2, 3]
count += 1
name ||= "anon"        # when name is T?
xs.push!(4)            # xs = xs.push(4): a method call with `!` rebinds its receiver
```

- The type of a local variable is determined by its first assignment. To widen the type, add an annotation (`y: Int? = nil`).
- After an assignment the type is narrowed by **flow typing** (after `y = 10`, `y` can be treated as `Int`).
- The rules for variable declaration and scope (a variable assigned inside an `if` is visible afterwards, block parameters are visible only within the block, etc.) are the same as in Ruby.
- Assignment to an `@ivar` is only possible inside `initialize` if the field is immutable.
- `x.foo!(args)` is sugar for `x = x.foo(args)` when the receiver's type has no method `foo!`: the receiver must be a local variable or a field, the result must fit its type (`s.size!` is an error), and the value of the expression is the new value. A chain rebinds the same place step by step (`s.strip!.upcase!`). Only the variable is rebound; the old value is unchanged for anything else that refers to it (`b = a; a.push!(1)` leaves `b` as it was), which differs from Ruby's mutating `!` methods. A real `foo!` (the mutating methods of builders such as `sort!`) is called as usual. The common collection updates (`push!`, `put!`, `add!`, `set!`, `delete!`) run in place when nothing else refers to the collection. The receiver cannot be another object's attribute: `obj.items.push!(x)` is an error, and `obj.items = obj.items.push(x)` copies the array every time (the object still holds it while `push` runs; in a loop that is quadratic). To update a collection another object holds, give that object a method and write `@items.push!(x)` inside it, where the update is in place.

## 11. Expressions and control structures

Same as Ruby: `if`/`unless`/`elsif`/`else`, `while`/`until`, modifier forms, `case/when`, `case/in`, `begin/rescue/else/ensure`, `loop`, `break`/`next`/`retry`/`return`, `and`/`or`/`not`, `&&`/`||`/`!`, `..`/`...` (including endless ranges), `&.`, `=>` (rightward assignment / pattern), `in` (pattern test), string interpolation `#{}`, `__FILE__`/`__LINE__`/`__method__` (a `String` in Quarz, a `Symbol` in Ruby).

Different from Ruby:

- `for … do … end` is the comprehension expression below; where its value is not used it runs as a loop (nested `each`), building nothing.
- All control structures are expressions (as in Ruby), but if the branches of an `if` have different types, the result is a union type. An `if` without `else` has type `T?`.
- Truthiness is as in Ruby: only `nil` and `false` are falsy. However, a condition that is known from its type to be always true / always false (`if 3`, `if some_int`) produces a warning.
- Variable types are narrowed by `while` and `if` conditions ([02-types.md](02-types.md) §6).

### `for` comprehensions

An expression that flattens nested blocks: it desugars to a chain of `flat_map`/`filter`/`map` (the shape of Ruby's Feature #22132). The body follows `do`, or starts on the next line.

```ruby
def pairs(n: Int, v: Int) -> Array[[Int, Int]]
  for i in 0...n,
      j in 0...n when i + j == v
    [i, j]
  end
end
# => (0...n).flat_map { |i| (0...n).filter { |j| i + j == v }.map { |j| [i, j] } }

for x in xs when x.even? do x * 2 end       # one line
for k, v in hash do "#{k}=#{v}" end          # tuple destructuring, as for block parameters
for u in find_user(id), o in latest_order(u) do [u, o] end   # Result[[User, Order], E]
```

- One iterator uses `map`; with several, all but the last use `flat_map`. `when` filters that iterator's sequence. The right-hand side of `in` and the guard are argument-level expressions (no commas, no modifier `if`).
- The variables are block parameters, so nothing leaks out; later iterators, guards and the body see the earlier variables. The guard's block and the body's block are siblings, so a temporary assigned in a guard is not visible in the body.
- Any type with `flat_map`/`map` (and `filter`, for `when`) works: `Enumerable`, `Range`, `Result` (`flat_map` is an alias of `and_then`; guards are not available). The type is inferred from the desugared expression as usual.
- The body runs once per combination, in order, and its value is the element of the result; `next v` gives `v` for that element, and `return` returns from the enclosing method. `break` inside the body or a guard is a compile error (it could only leave the innermost generated block).
- Where its value is not used (a statement before the last of a body, the last of a body whose value is discarded: a method or block declared to return `Nil`, a file's top level), a `for` whose sources all have `each` runs as nested `each` calls instead (`source.each { |x| if guard then … end }`), which build no collection; the body still runs once per combination, in order. With a source that has no `each` (a `Result`), it is the comprehension wherever it is.
- `for` is a contextual keyword: only `for variable in` starts a comprehension.

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

- Available patterns: value patterns, pin `^x`, alternatives `|`, array patterns (`*rest`, find pattern), hash patterns, `Const(...)`/`Const[...]` (matching the declared fields of the class, `data` or variant), binding `=> name`, guards `if`/`unless`, `nil`.
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
rescue IOError, SystemCallError => e
  warn "I/O error: #{e.message}"
else
  puts "ok"
ensure
  cleanup
end

value = risky rescue default   # the modifier form is also allowed
```

- The exception hierarchy follows Ruby (`Exception` > `StandardError` > ...). The argument of `raise` is an exception class, an exception object, or a string (`RuntimeError`). A bare `raise` in a `rescue` clause (also inside a block there, but not in a `def`) re-raises the exception being handled, keeping its backtrace; elsewhere it is a compile error. `raise e` does the same with `rescue E => e` (also with `rescue A, B => e`).
- Exceptions are handled within the task that raised them. The handling of exceptions that escape a task is described in [04-concurrency.md](04-concurrency.md).
- Exception objects must be Shareable (because they propagate to other tasks; not enforced yet).
- The type of `raise` is `Nothing` (the bottom type), so narrowing such as `x = arg || raise ArgumentError` is possible.

## 13. String, array and hash literals

```ruby
s  = "name: #{name}\n"     # String
s2 = 'raw \n'
s3 = <<~EOS
  heredoc
EOS
a  = [1, 2, 3]             # Array[Int]
t  = [1, "a"]              # [Int, String]: elements of different types make a tuple (02-types.md §5)
h  = { name: "alice", age: 30 }     # Hash[Symbol, String | Int]
h2 = { "a" => 1, "b" => 2 }         # Hash[String, Int]
r  = 1..10                 # Range[Int]
set = Set[1, 2, 3]         # Set[Int]
bytes = b"\x00\xff"        # Bytes (binary)
```

- Strings are always UTF-8 and immutable. Binary data is a separate type, `Bytes`.
- `Array`/`Hash`/`Set` created from literals are immutable: updates return new values. The empty literals `[]` and `{}` take their element types from the context ([02-types.md](02-types.md) §5).
- The keys of `{ a: 1 }` are `Symbol`s; the keys of `{ "a" => 1 }` are `String`s. Mixing them gives `Hash[Symbol | String, Int]`.

## 14. FFI

```ruby
extern "C"
  def strlen(s: CString) -> SizeT
  def getpid -> Int32
end

puts strlen("hello")
```

C functions can be declared and called directly. There are FFI types such as `CString`, `Pointer[T]` and the fixed-width integers. C functions that may block are called inside `Task.blocking { }`. (FFI is planned: the parser accepts `extern "C"` blocks, but the checker rejects them, and the FFI types do not exist yet.)
