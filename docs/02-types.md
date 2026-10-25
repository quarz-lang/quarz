# Type System

日本語版: [02-types.ja.md](02-types.ja.md)

Quarz is statically typed. The structure of classes, modules and methods is fixed at compile time, and every method call is resolved at compile time. To keep the Ruby feel, however, the language is designed so that you rarely need to write types anywhere other than at method boundaries.

Design principles:

1. **Write types at method boundaries, not inside them.** Parameter types are required; return types and local variables are inferred. This keeps compile times short and error messages clear.
2. **nil is not a value of ordinary types.** A value of type `String` is never `nil`; if `nil` is possible, write `String?`.
3. **Union types and flow typing.** Union types such as `Int | String` can be used directly and narrowed with `if`/`case/in`/`is_a?`.
4. **Immutable means covariant.** Immutable collections are covariant in their element type, so an `Array[Int]` can be passed where an `Array[Int | Nil]` is expected.

## 1. Type Syntax

| Type | Example | Description |
|---|---|---|
| Class / module | `Int`, `String`, `Comparable[T]` | Nominal types |
| Generics | `Array[Int]`, `Hash[String, Int]` | Type arguments in square brackets |
| Nilable | `String?` | Shorthand for `String \| Nil` |
| Union | `Int \| String \| Nil` | |
| Tuple | `[Int, String]` | Fixed length and per-element types |
| Procedure | `(Int, String) -> Bool`, `() -> Nil` | Type of blocks and lambdas |
| Top | `Object` | Supertype of every type |
| Bottom | `Nothing` | Type of `raise`, `exit` and infinite loops. Subtype of every type |
| Type variable | `T`, `K`, `V` | Declared type parameters |
| Self type | `Self` | The receiver's class (in a class method, its instances: `def self.build -> Self = new`), where a method hands a value out: `def dup -> Self`, `&: (Self) -> Nil`. Not where the caller hands one in (a parameter, a block's result): a subclass would receive its parent's values; use a type parameter (`Comparable[T]`). In the body, `Self` is the class or a subclass, not known which: only `self`, what calls on it return as `Self`, and `new` on a class method's receiver are a `Self` (`Shape.new` is not) |

Writing `Array[Int]` in expression context yields an expression denoting the type itself, so it can be used as in `Array[Int].new` (there is no `Array.[]` constructor as in Ruby).

## 2. Built-in Types

| Type | Ruby counterpart | Notes |
|---|---|---|
| `Nil` | `NilClass` | The only value is `nil` |
| `Bool` | `TrueClass`/`FalseClass` | `true`/`false` |
| `Int` | `Integer` | **64-bit**. Arithmetic whose result leaves the range raises `OverflowError` (so compiled code keeps every `Int` a machine word), and a negative exponent (`2 ** -1`) raises `ArgumentError` (`2.0 ** -1` is `0.5`). Integer literals are `Int`s |
| `Integer` | `Integer` | **Arbitrary precision**. Arithmetic with an `Int` gives an `Integer`; an `Int` becomes one only explicitly (`to_integer`), and a literal is one where an `Integer` is expected or when it is too large for an `Int`. `Integer#to_i` raises `OverflowError` when the value does not fit |
| `Int8`..`Int64`, `UInt8`..`UInt64` | - | Fixed-width integers (*planned*). Overflow raises an exception (always an exception, never undefined behavior or wrapping, even with `--release`) |
| `Float` | `Float` | IEEE 754 double precision |
| `Float32` | - | For FFI and numerical computation (*planned*) |
| `String` | `String` | Immutable. Always UTF-8 |
| `Bytes` | String (ASCII-8BIT) | Immutable byte sequence |
| `Symbol` | `Symbol` | |
| `Array[out T]` | `Array` | Immutable |
| `Hash[K, out V]` | `Hash` | Immutable, preserves insertion order |
| `Set[out T]` | `Set` | Immutable |
| `Range[T]` | `Range` | |
| `Regexp`, `MatchData` | Same names | |
| `Proc` = `(A...) -> R` | `Proc` | Generic name for procedure types |
| `Enumerator[T]`, `Lazy[T]` | Same names | External iterators (`Lazy[T]` is *planned*) |
| `Channel[T]`, `Task[T]`, `Atom[T]`, `Scope` | - | Concurrency primitives |
| `Array::Builder[T]`, `Hash::Builder[K, V]`, `String::Builder`, `Bytes::Builder`, `Set::Builder[T]` | Mutable `Array` etc. | Mutable, task-local |
| `Class` | `Class` | The type of `obj.class` (written without type arguments). Very limited reflection such as `name` |

Numeric operations have the same meaning as in Ruby: `7 / 2` is `3`, `-7 / 2` is `-4`, `7 % -2` is `-1`, `1 + 1.5` is `2.5`. Mixed operations are defined as overloads such as `Int#+(Float) -> Float`. Fixed-width integers (planned) and `Int` will never be mixed implicitly; conversions will be explicit, with `to_i`/`to_i64` and friends.

## 3. Generics

```ruby
class Stack[T]
  @items: Array[T] = []
  def push(x: T) -> Stack[T] = Stack[T].from(@items.push(x))
  def peek -> T? = @items.last?
end

def max_by[T, U: Comparable[U]](xs: Array[T], &key: (T) -> U) -> T?
  ...
end

module Container[out T]      # covariant
  abstract def get -> T
end
```

- Classes, modules, `data`, `enum` and methods can have type parameters.
- Constraints are written as `T: Comparable[T]`. Multiple constraints: `T: Comparable[T] & Describable` (with any modules).
- Variance is declared with `out` (covariant) / `in` (contravariant); unmarked parameters are invariant. The compiler checks the positions: a covariant parameter may appear where values come out (results, the parameters of a block the method takes, a lower bound), a contravariant one where they go in, and neither in a `var` field. `initialize`, class methods and private methods are not checked, since they see the exact type.
- A method type parameter can have a **lower bound**, `U >: T`: `U` is `T` or a supertype of it. This is how a covariant type takes values: `Array[out T]` has `push[U >: T](value: U) -> Array[U]`, so `[1].push("a")` is an `Array[Int | String]`, and an `Array[Int]` seen as an `Array[Object]` never receives a `String` itself. Without type arguments, `U` is the bound joined with the types the arguments give it. Methods that only look a value up take `Object` instead (`delete(value: Object)`, `-(other: Array[Object])`).
- Type arguments of methods are inferred at the call site. To be explicit: `max_by[Person, Int](people) { |p| p.age }`.
- The implementation defaults to **monomorphization**: specialized code is generated for each unboxed type such as `Int`/`Float`, while reference types share code. The interpreter follows the same policy. (Planned: today generic code is compiled once, over tagged values.)

## 4. Union Types and Nil Safety

```ruby
def find(id: Int) -> User?
  users[id]?
end

user = find(1)
user.name              # error: User? has no method name
user.name if user      # OK: narrowed
user&.name             # String?
name = user&.name || "anon"
u = find(1) || raise NotFound    # raise has type Nothing, so u is User
```

- `nil` is the only value of type `Nil`, and is not a value of any other type.
- `T?` is sugar for `T | Nil`. Arbitrary unions such as `Int | String | Nil` can also be written.
- On a value of union type you can only call methods that are common to all member types (with compatible return types). Anything else requires narrowing first.
- Unions are normalized: `Int | Int` → `Int`, `Int | Object` → `Object`, `(Int | String) | Nil` → `Int | String | Nil`.

## 5. Type Inference

Inference is **bidirectional and local**. Since parameter types are known, inference is confined to a single method body; there is no whole-program inference.

- **Local variables**: the type of the first assignment. `x = 1` gives `Int`.
- **Return type**: when omitted, the type of the body (the union of the `return` types and the last expression). For methods that call themselves recursively, `abstract def`, `extern def`, and methods exported to `.qzi` as public API (planned), an uninferable return type is an error and an annotation is required.
- **Empty literals**: `[]`, `{}` and `Set[]` follow the expected type if there is one; otherwise they carry a type variable such as `Array[?T]`, fixed by the later uses in the same method. Only uses of the values fix it (an assignment to a typed place, an argument, `push`): a pattern or type test narrows a value of a type not fixed yet only inside its branch (and `case`/`in` on it needs no `else` to be exhaustive), an `if` whose value is not used does not join its branches, and joining it with another type leaves it undecided (`x = xs[0] if c` is `?T?`, `xs[0] || "s"` is `?T | String`); calling a method other than `Object`'s on such a union is a use that decides `?T` as the rest.

```ruby
counts = words.reduce({}) { |h, w| h.put(w, h.fetch(w, 0) + 1) }   # {} is Hash[String, Int]
names: Array[String] = []          # from the expected type
xs = []                            # Array[?T] for now
xs = xs.push(1)                    # ... fixed here: xs is Array[Int]
```

- **Block parameters**: determined by the type of the `&block` they are passed to. In `[1, 2].map { |x| x * 2 }`, `x` is `Int`.
- **Type arguments of generic methods**: determined by unification from the argument and block types.
- **Numeric literals**: `1` is treated as a `Float` when the expected type is `Float` (and as an `Int32` when the expected type is `Int32`, once fixed-width integers exist). The defaults are `Int`/`Float`.
- **Tuples and arrays**: an array literal follows the expected type (a tuple or an array). With none, elements whose types join into a union make a tuple, and elements with a common type an array: `[w, w.size]` is `[String, Int]`, `[1, 2]` is `Array[Int]`, and `[circle, rect]` is `Array[Shape]`. `return a, b` and the right-hand side of a multiple assignment follow the same rule. A tuple is also an array of its elements' join, so array methods apply to it; tuples of comparable elements compare element by element (`<`, `<=>`, `sort`, `max`), as arrays of one comparable element type do. A local variable assigned a tuple literal (`t = [1, "a"]`) is declared as that array and narrowed to the tuple: `t[0]` is an `Int`, and `t = t.push(2)` is allowed.

## 6. Flow Typing (Narrowing)

Conditional branches narrow the types of local variables.

```ruby
def describe(x: Int | String | Nil) -> String
  return "nothing" if x.nil?          # from here on, x: Int | String
  if x.is_a?(Int)
    "int #{x + 1}"                    # x: Int
  else
    "str #{x.upcase}"                 # x: String
  end
end

case v
in Int => n then n + 1
in String => s then s.size
end

while (line = io.gets?)             # line: String (inside the loop)
  puts line
end
```

Conditions that narrow: truthiness tests (`if x`), `x.nil?`, `x.is_a?(T)`, `x in Pattern` (in the true branch only), `case/in`, `==`/`!=` comparisons against `nil`, `true`/`false` (the equal side is a `Bool`) and data-less enum variants (the equal side is the variant, the other side is not), combinations with `&&`/`||`/`!`/`and`/`or`/`not`, early exits via `return`/`raise`/`next`/`break`, and assignment.

A test narrows only to what holds when it passes. A number pattern matches equal numbers of the other number classes (`in 1` on an `Int | Float` leaves both), and a comparison with `true`/`false` or a variant narrows only values whose `==` and `!=` are the built-in ones: no class the value may be of (its class or a subclass, anywhere in the program) defines its own. A generic class in a pattern or `when` without arguments (`in Box`, `when Box`) takes them from the value's type; where that does not give them, an `Object` is narrowed only to a class that admits no wrong value with `Object` arguments (the built-in collections, `data` types holding their parameters covariantly, classes with covariant unbounded parameters), and otherwise stays an `Object`. The built-in value classes (`Int`, `String`, `Array`, ...) have no subclasses.

What gets narrowed: **local variables, immutable fields (`@x`), and `data` fields** (when read as `@name` in the `data` body; reader calls such as `p.name` are method calls). `var` fields and the results of arbitrary method calls (`user.name`) are not narrowed, because they may change in between; assign them to a local variable first. Since the default design has no mutable fields, most Ruby idioms such as `@x && @x.foo` work as is.

## 7. Casts

```ruby
n = obj.as(Int)         # TypeError on failure
n = obj.as?(Int)        # Int?
f = n.to_f              # a conversion method (not a cast)
```

Downcasts are checked at run time (`as`, `as?` and `is_a?`), together with the elements of built-in collections and tuples (`obj.as(Array[String])` checks every element; an empty array passes). Other type arguments cannot be checked at run time: `obj.as(Box[Int])` is an error unless `obj` may only be a `Box` that is already a `Box[Int]` (`Box[Int]?`). Unsafe reinterpreting casts exist only in the FFI layer (`Pointer#cast`).

## 8. Method Resolution and Overloading

- Calls are resolved by the static type of the receiver. The candidates are the methods of that class, its superclasses, the modules it includes, and the `extension`s in effect in the scope.
- When a method name is overloaded, the most specific overload is chosen by the number of arguments, keywords and types. Ambiguity is an error. (Currently the first declared overload that matches is chosen, and ambiguity is not reported.)
- Methods that may be overridden in a subclass become virtual calls (vtable). Because the class hierarchy is fixed for the whole program, methods without overrides are replaced by static calls at link time (class hierarchy analysis).
- Calls on a receiver of module type are interface calls (a per-class module implementation table).
- `respond_to?` is folded to a compile-time constant. `send`/`public_send`/`method`/`define_method`/`method_missing`/`instance_variable_get` do not exist.

## 9. Shareable

`Shareable` is a marker module denoting "a type whose values can safely be passed to another task". The compiler derives it for `data` and `enum` types from their fields; a class or module declares it with `include Shareable`, and the compiler holds it, and every class that inherits or includes it, to the rules. The details are in [03-data-model.md](03-data-model.md) §5; from the type system's point of view it is used as follows.

```ruby
class Channel[T: Shareable]
class Atom[T: Shareable]
def self.spawn[T: Shareable](&block: () -> T) -> Task[T]   # the variables captured by the block must be Shareable too
```

`include Shareable` is a promise that the subtypes keep: a value of a Shareable type is Shareable whatever its class. So whether a type is Shareable is decided where it is defined, from its own declaration and its ancestors', without looking at the rest of the program (which separate compilation needs).

A procedure type is not Shareable: a block reads and assigns the variables of the code around it, which another task must not. `shareable (A) -> R` is the type of one that is. A block or lambda written where such a type is expected (a block parameter `&job: shareable (Int) -> Nil`, an argument, an annotated variable) captures by value, as a `Task.spawn` block does: the variables it reads are copied when it is made, their values must be Shareable (and so must `self`, if it uses it), and it cannot assign them. Any task may then call it, at once with others: a worker pool or a server loop can take one and run it in tasks of its own.

```ruby
def each_in_tasks(n: Int, &job: shareable (Int) -> Nil) -> Nil
  Task.scope { |s| n.times { |i| s.spawn { job.call(i) } } }
end
label = "item"
each_in_tasks(3) { |i| puts "#{label} #{i}" }    # copies `label`
log: shareable (String) -> Nil = ->(s: String) { STDERR.puts(s) }
```

A shareable procedure is a procedure (`shareable (A) -> R` is a subtype of `(A) -> R`); a procedure is not a shareable one, so `f: shareable () -> Int = g` with `g = ->() { 1 }` is an error: annotate where the lambda is written.

## 10. Alternatives Not Adopted

- **Structural typing (Go interfaces, TypeScript)**: attractive because it is close to duck typing, but in Ruby what we expect is not merely "has `each`" but "what `each` means". We chose nominal modules plus retroactive conformance via `extension`, which gives the same flexibility while making the intent to conform explicit.
- **A dynamic type `Dynamic`**: considered for prototyping convenience, but having even one requires run-time method tables for every class and hinders optimization in both the interpreter and the AOT compiler. Prototyping convenience will instead come from stronger inference.
- **Whole-program inference**: lets you omit parameter types, but sacrifices compile time and the quality of error messages. "Write types at method boundaries" is Quarz's trade-off.
