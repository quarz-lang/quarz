# Type System

日本語版: [02-types.ja.md](02-types.ja.md)

Quarz is statically typed. The structure of classes, modules and methods is fixed at compile time, and every method call is resolved at compile time. To keep the Ruby feel, however, the language is designed so that you rarely need to write types anywhere other than at method boundaries.

Design principles:

1. **Write types at method boundaries, not inside them.** Parameter types are required; return types and local variables are inferred. This gives us both per-file separate compilation and fast type checking when the interpreter starts.
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
| Self type | `self` | Used as in `def dup -> self` |

Writing `Array[Int]` in expression context yields an expression denoting the type itself, so it can be used as in `Array[Int].new` (there is no `Array.[]` constructor as in Ruby).

## 2. Built-in Types

| Type | Ruby counterpart | Notes |
|---|---|---|
| `Nil` | `NilClass` | The only value is `nil` |
| `Bool` | `TrueClass`/`FalseClass` | `true`/`false` |
| `Int` | `Integer` | **Arbitrary precision**. Implemented as a 63-bit tagged integer that is promoted to a heap bignum on overflow (same behavior as Ruby) |
| `Int8`..`Int64`, `UInt8`..`UInt64` | - | Fixed-width integers. Overflow raises an exception (always an exception, never undefined behavior or wrapping, even with `--release`) |
| `Float` | `Float` | IEEE 754 double precision |
| `Float32` | - | For FFI and numerical computation |
| `String` | `String` | Immutable. Always UTF-8 |
| `Bytes` | String (ASCII-8BIT) | Immutable byte sequence |
| `Symbol` | `Symbol` | |
| `Array[out T]` | `Array` | Immutable, persistent |
| `Hash[K, out V]` | `Hash` | Immutable, persistent, preserves insertion order |
| `Set[out T]` | `Set` | Immutable, persistent |
| `Range[T]` | `Range` | |
| `Regexp`, `MatchData` | Same names | |
| `Proc` = `(A...) -> R` | `Proc` | Generic name for procedure types |
| `Enumerator[T]`, `Lazy[T]` | Same names | External iterators |
| `Channel[T]`, `Task[T]`, `Atom[T]`, `Scope` | - | Concurrency primitives |
| `Array::Builder[T]`, `Hash::Builder[K, V]`, `String::Builder`, `Bytes::Builder`, `Set::Builder[T]` | Mutable `Array` etc. | Mutable, task-local |
| `Class[T]` | `Class` | The type of `obj.class`. Very limited reflection such as `name` |

Numeric operations have the same meaning as in Ruby: `7 / 2` is `3`, `-7 / 2` is `-4`, `7 % -2` is `-1`, `1 + 1.5` is `2.5`. Mixed operations are defined as overloads such as `Int#+(Float) -> Float`. Fixed-width integers and `Int` are never mixed implicitly; convert explicitly with `to_i`/`to_i64` and friends.

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
- Constraints are written as `T: Comparable[T]`. Multiple constraints: `T: Comparable[T] & Hashable`.
- Variance is declared with `out` (covariant) / `in` (contravariant); unmarked parameters are invariant. The compiler checks, for example, that a covariant type parameter does not appear in a parameter position of a method.
- Type arguments of methods are inferred at the call site. To be explicit: `max_by[Person, Int](people) { |p| p.age }`.
- The implementation defaults to **monomorphization**: specialized code is generated for each unboxed type such as `Int`/`Float`, while reference types share code. The interpreter follows the same policy.

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

Inference is **bidirectional and local**. Since parameter types are known, inference is confined to a single method body; there is no whole-program inference (whole-program inference as in Crystal is not adopted, because compile time grows superlinearly as the code base grows).

- **Local variables**: the type of the first assignment. `x = 1` gives `Int`.
- **Return type**: when omitted, the type of the body (the union of the `return` types and the last expression). For methods that call themselves recursively, `abstract def`, `extern def`, and methods exported to `.qzi` as public API, an uninferable return type is an error and an annotation is required.
- **Empty literals**: `[]`, `{}` and `Set[]` follow the expected type if there is one; otherwise they carry a type variable such as `Array[?T]` that is unified within the same statement.

```ruby
counts = words.reduce({}) { |h, w| h.put(w, h.fetch(w, 0) + 1) }   # {} is Hash[String, Int]
names: Array[String] = []          # from the expected type
xs = []                            # error: element type undetermined. Write xs: Array[Int] = []
```

- **Block parameters**: determined by the type of the `&block` they are passed to. In `[1, 2].map { |x| x * 2 }`, `x` is `Int`.
- **Type arguments of generic methods**: determined by unification from the argument and block types.
- **Numeric literals**: `1` is treated as a `Float` when the expected type is `Float`, and as an `Int32` when the expected type is `Int32`. The defaults are `Int`/`Float`.
- **Tuples and arrays**: `[1, "a"]` is a tuple if the expected type is a tuple, otherwise `Array[Int | String]`. `return a, b` and the right-hand side of a multiple assignment are tuples.

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

Conditions that narrow: truthiness tests (`if x`), `x.nil?`, `x.is_a?(T)`, `x in Pattern`, `case/in`, `==` comparisons against singletons (`nil`/`true`/`false`/data-less enum variants), combinations with `&&`/`||`/`!`/`and`/`or`/`not`, early exits via `return`/`raise`/`next`/`break`, and assignment.

What gets narrowed: **local variables, immutable fields (`@x`), and `data` fields**. `var` fields and the results of arbitrary method calls (`user.name`) are not narrowed, because they may change in between; assign them to a local variable first. Since the default design has no mutable fields, most Ruby idioms such as `@x && @x.foo` work as is.

## 7. Casts

```ruby
n = obj.as(Int)         # TypeError on failure
n = obj.as?(Int)        # Int?
f = n.to_f              # a conversion method (not a cast)
```

Downcasts are checked at run time. Unsafe reinterpreting casts exist only in the FFI layer (`Pointer#cast`).

## 8. Method Resolution and Overloading

- Calls are resolved by the static type of the receiver. The candidates are the methods of that class, its superclasses, the modules it includes, and the `extension`s in effect in the scope.
- When a method name is overloaded, the most specific overload is chosen by the number of arguments, keywords and types. Ambiguity is an error.
- Methods that may be overridden in a subclass become virtual calls (vtable). Because the class hierarchy is fixed for the whole program, methods without overrides are replaced by static calls at link time (class hierarchy analysis).
- Calls on a receiver of module type are interface calls (a per-class module implementation table).
- `respond_to?` is folded to a compile-time constant. `send`/`public_send`/`method`/`define_method`/`method_missing`/`instance_variable_get` do not exist.

## 9. Shareable

`Shareable` is a marker module derived automatically by the compiler, denoting "a type whose values can safely be passed to another task". The details are in [03-data-model.md](03-data-model.md) §5; from the type system's point of view it is used as follows.

```ruby
class Channel[T: Shareable]
class Atom[T: Shareable]
def spawn[T: Shareable](&block: () -> T) -> Task[T]   # the variables captured by the block must be Shareable too
```

Users cannot write `include Shareable`; it is determined by the structure of the type.

## 10. Alternatives Not Adopted

- **Structural typing (Go interfaces, TypeScript)**: attractive because it is close to duck typing, but in Ruby what we expect is not merely "has `each`" but "what `each` means". We chose nominal modules plus retroactive conformance via `extension`, which gives the same flexibility while making the intent to conform explicit.
- **A dynamic type `Dynamic`**: considered for prototyping convenience, but having even one requires run-time method tables for every class and hinders optimization in both the interpreter and the AOT compiler. Prototyping convenience will instead come from stronger inference.
- **Whole-program inference (Crystal)**: lets you omit parameter types, but sacrifices compile time and the quality of error messages. "Write types at method boundaries" is Quarz's trade-off.
