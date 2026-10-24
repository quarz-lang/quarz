# Data Model and Immutability

日本語版: [03-data-model.ja.md](03-data-model.ja.md)

The principle in Quarz is "values are immutable by default; mutability is explicit and task-local". This principle supports both the safety of concurrent programming (no shared mutable state) and execution efficiency (uniqueness detection via reference counting lets immutable values be updated in place).

## 1. Everything Is an Object

As in Ruby, integers and `nil` are objects with methods (`3.times`, `nil.to_s`). The representation, however, is chosen by the compiler. Small `Int` values are tagged immediates, `Float` is an unboxed double wherever the type is statically known, and `Bool`/`Nil` are immediates. Only strings, collections, instances of user-defined classes, `Integer`s and closures live on the heap.

## 2. Immutable Built-in Data

The following types are **immutable**. There are no methods that modify a value; there are only methods that return "the modified new value".

| Type | Implementation | Main "update" operations (return a new value) |
|---|---|---|
| `String` | Flat UTF-8 byte sequence (large concatenations temporarily use a rope) | `+`, `*`, `sub`, `gsub`, `upcase`, `strip`, `insert`… |
| `Array[T]` | Persistent vector with 32-way branching (RRB-Tree). Up to 32 elements fit in a single node | `push`, `pop`, `shift`, `unshift`, `set`, `insert`, `delete_at`, `+`, `map`, `select`, `sort`, `concat`… |
| `Hash[K, V]` | HAMT + a persistent vector that preserves insertion order. Up to 8 elements use a linear array | `put`, `delete`, `merge`, `update`, `select`, `transform_values`… |
| `Set[T]` | HAMT | `add`, `delete`, `\|`, `&`, `-`… |
| `Range[T]`, `Tuple`, `Symbol`, numbers, `Bool`, `Nil`, `Regexp` | | |

The Implementation column is the design. Currently `Array` is a flat vector (an array of only `Int`s or only `Float`s stores machine words), `Hash` an insertion-ordered hash table (one whose keys and values are all `Int` is stored unboxed), `Set` an insertion-ordered hash set, and `String` a flat UTF-8 string (at most 15 bytes inside the value itself; no rope). An update is in place when the reference is unique, as below, and otherwise copies the whole collection, in O(n).

```ruby
a = [1, 2, 3]
b = a.push(4)        # a is still [1, 2, 3], b is [1, 2, 3, 4]
h = { name: "alice" }
h2 = h.put(:city, "Paris")
s = "abc"
t = s + "d"
```

Of Ruby's destructive methods (`push`/`<<`/`[]=`/`sort!`/`map!`/`concat`/`delete`/`clear`/`gsub!`…), the immutable types only have the "return a new value" versions. `<<`, `[]=` and `!`-suffixed methods are not defined on immutable types. If you write `arr << x`, the compiler reports an error suggesting that you use `Array::Builder` or write `arr = arr.push(x)` (likewise `<<` on `Set`, `String` and `Bytes`, and `[]=` on `Array` and `Hash`).

Discarding the result of a pure method produces a warning: today the methods of the built-in immutable types (`Array`, `Hash`, `Set`, `String`, `Bytes`, and `Enumerable`/`Comparable` on them) that take no block, so `xs.push(1)` or `xs.sort` as a statement is reported. Marking other methods or types is planned.

```ruby
arr.push(4)          # warning: result unused. arr does not change
arr = arr.push(4)    # OK
```

### Complexity and "update in place when unique"

With the persistent structures of the design, an update would be `O(log32 n)`, effectively constant in practice; today an update of a shared collection copies it, in O(n). In either case, since Quarz's memory management is reference counting ([05-execution.md](05-execution.md) §5), if there is only one reference to `arr` at the point of `arr.push(4)`, the **original array's storage is updated in place** instead of creating a new array.

```ruby
def collect(n: Int) -> Array[Int]
  acc: Array[Int] = []
  n.times { |i| acc = acc.push(i * i) }   # acc always has exactly one reference → appended in place every time, amortized O(1)
  acc
end
```

Passing a value on does not add a reference when the variable is not read again: the value moves into the call, and a parameter takes it over. A helper that returns the updated collection keeps it unique, so this loop is linear as well:

```ruby
def add(xs: Array[Int], v: Int) -> Array[Int] = xs.push(v)

ys: Array[Int] = []
n.times { |i| ys = add(ys, i) }   # ys moves into add, xs.push updates it in place
```

This is the same technique as "functional but in-place" in Lean 4 / Koka, and it lets straightforward Ruby-style loops run about as fast as with a mutable array. If the reference is shared, it automatically falls back to copying (only the nodes on the path; currently the whole collection), so the semantics always remain immutable.

## 3. Builders (Mutable, Task-Local)

For complex construction, the boundary with FFI, and algorithms that genuinely need mutation (heap sort, the visited set in a graph search, and so on), mutable versions of the types are provided.

```ruby
buf = String::Builder.new
buf << "hello" << " " << "world"
buf.to_s                            # => "hello world" (O(1): freezes the buffer and hands it over)

squares = Array.build do |b|        # b: Array::Builder[Int]
  10.times { |i| b << i * i }
end                                 # => Array[Int]

index = Hash.build do |b|           # b: Hash::Builder[String, Int]
  words.each_with_index { |w, i| b[w] = i }
end

str = String.build { |b| b << "x" * 3; b << "y" }
```

- Builders have almost the same API as Ruby's mutable `Array`/`Hash`/`String` (`<<`, `[]=`, `push`, `pop`, `sort!`, `map!`, `delete`, `clear`, `concat`…). Destructive methods return `self`.
- `to_a`/`to_h`/`to_s`/`freeze` extract the immutable value in O(1): they hand the contents over and leave the Builder empty, ready to be filled again. If you only want to peek repeatedly, use `snapshot` (an O(n) copy).
- Builders are **not Shareable**. Sending one over a channel, capturing one in a `spawn` block, putting one in an `Atom` or making one a constant are compile errors, and a class with a Builder field is not Shareable.
- In the `Array.build { }` form, the compiler can guarantee that the Builder does not escape the block, and can optimize the allocation.

## 4. Immutability of User-Defined Classes

```ruby
class Node
  @value: Int
  @children: Array[Node] = []
  def initialize(@value: Int, @children: Array[Node] = []); end
  def add(child: Node) -> Node = Node.new(@value, @children.push(child))
end

class Counter
  var @count: Int = 0
  def increment -> Nil
    @count += 1
  end
end
```

- Fields are immutable by default. They are assigned in `initialize` and cannot be changed outside it.
- `var @x: T` makes a field mutable. An object with mutable fields is a **mutable object**.
- A mutable object can only be used inside the task that created it (§5; not yet enforced everywhere: a task's result is not checked).
- All fields of a `data` are immutable; `with` creates "a copy with some fields changed".

The Ruby-style design of "line up `attr_accessor`s and change state through setters" requires writing `var` in Quarz, making the intent explicit. The number of `var`s is a measure of how risky a class is with respect to concurrency.

### Lifetimes and `deinitialize`

Memory is reference counted ([05-execution.md](05-execution.md) §5), so a value is released when its last reference goes, and most values are released at their last use. A value whose release can be observed lives to the end of its scope instead, as in Swift (since 5.7), C++ and Rust:

```ruby
class TempFile
  @path: String
  def initialize(@path: String) end
  def deinitialize
    File.delete(@path)
  end
end

def with_scratch -> Nil
  f = TempFile.new("/tmp/scratch")
  File.write("/tmp/scratch", "data")   # f is not used after this line,
  run_tool("/tmp/scratch")             # but the file is still there
end                                    # here f goes, and the file with it
```

- `def deinitialize` (no parameters; in a class or a module a class includes, not in a `data` type, enum, built-in value class or extension) runs when an instance's last reference goes. An exception it raises is reported on standard error as a warning and goes no further.
- A local variable, parameter or block parameter lives to the end of its scope (the method, or each pass of the block), or until it is reassigned, when its type may hold such a value: any class or module type (a subclass may define `deinitialize` or hold an IO handle, and subclasses are not looked at, as for Shareable), a procedure (what it captured), an `Enumerator`, a type parameter, and a built-in collection, `data` type, enum, union or tuple holding one of these. `Int`, `String`, `Array[Int]` and `data Point = (x: Float, y: Float)` are released at their last use, and the in-place updates of §2 are unaffected. So a server socket used only to learn its port stays open: `server = TCPServer.new(host, 0); port = server.local_address.port` and the rest of the method can connect to it.
- A statement's unused value of such a type (`Lock.new(..)` on its own line) is released at the end of the statement; one returned from the method lives on with the caller.
- `deinitialize` runs where the release happens when that is the end of a scope or statement, or the reassignment of such a variable (the old value goes there, even when it was last read earlier, by a loop over it, say); a release elsewhere (the reassignment of a variable a block captures, an element dropped from a collection) runs it when the method that released it returns, or at the next end of a scope, whichever comes first. It runs on the worker that dropped the last reference, as part of the task running there.
- Objects still referenced when the program exits are not finalized. Use `ensure` (or a block-taking API, `File.open(path) { }`) for what must happen at a definite point; `deinitialize` is for releasing what an object owns.

## 5. Shareable

A type is `Shareable` when its values **can safely be passed to another task**. For `data` and `enum` types the compiler derives it from their fields; a class declares it with `include Shareable` (or inherits it), and the compiler checks the class and every subclass against the rules where each is defined. A class is not Shareable just because its fields are: a subclass could add mutable state, and a value of the class's type may be of the subclass.

Shareable:

- `Nil`, `Bool`, numbers, `Symbol`, `String`, `Bytes`, `Regexp`, `Range[T]` (T Shareable)
- Immutable collections `Array[T]`/`Hash[K, V]`/`Set[T]`/tuples (all element types Shareable)
- `data` types (all fields Shareable), `enum` types (all variants' fields Shareable); a generic one when its type arguments are
- Classes that include `Shareable`, directly or through an ancestor or an included module: each must have no `var` fields and only Shareable fields, and so must every subclass, or its definition is an error (`class Oops < RuntimeError` with a `var` field is one: `Exception` includes `Shareable`)
- `Channel[T]`, `Task[T]`, `Atom[T]`, `Scope` (these are internally synchronized)
- Shareable procedures, `shareable (A) -> R` ([02-types.md](02-types.md) §9): a block or lambda written where one is expected captures by value, like a `spawn` block, so its captured values must be Shareable and it cannot assign them. Other procedure types are not Shareable
- Exception objects (`Exception` includes `Shareable`, so every exception class is held to the rules)
- `IO` handles (the standard streams, open files, sockets): the runtime serializes access

Not Shareable:

- The various Builders
- `Enumerator` (it has a position, and its receiver may be a mutable object)
- Classes that do not include `Shareable` (whatever their fields); including it is an error for one with `var` or non-Shareable fields
- Modules that do not include `Shareable`; a module that does can only be included by Shareable classes (an `extension` that includes it in a non-Shareable class is an error)
- Procedures that capture Builders or mutable objects, procedures that assign to outer local variables

Where Shareable is required:

| Place | Reason |
|---|---|
| `T` of `Channel[T]` | Sent to other tasks |
| Variables captured by `spawn`/`scope.spawn` blocks | Executed in a new task |
| `T` of `Atom[T]` | Read and written from multiple tasks |
| Constants | Visible from every task |
| `T` of `Task[T]` (return value) | Passed to another task via `await` (the `spawn`, `scope.spawn` or `Task.blocking` block's result) |
| Exceptions | Propagate across task boundaries |

```ruby
counter = Counter.new            # mutable
spawn { counter.increment }      # error: Counter is not Shareable

total = 0
spawn { total += 1 }             # error: a spawn block cannot assign to outer variables

n = Atom.new(0)
spawn { n.update { |v| v + 1 } } # OK

class Account
  include Shareable              # a promise, checked here and in every subclass
  @inbox: Channel[Msg]
end
class Audited < Account
  var @count: Int = 0            # error: `Audited` must be Shareable
end
```

To pass a mutable object to another task, convert it to an immutable value. A Builder's `to_a` is O(1).

## 6. Equality and Identity

- `==` is **structural equality**. It is generated automatically for `data`/`enum`, element-wise for collections, and defaults to identity for user classes (overridable).
- `hash` is defined consistently with `==`. Generated automatically for `data`/`enum`/collections.
- `equal?` is identity. Do not attach meaning to the identity of immutable values; the implementation is free to share or copy equal values (interning of small strings, returning `self` from `with` when no field changes, and so on).
- `eql?` is dropped. Static typing turns confusions like `{ 1 => "a" }[1.0]` into type errors, so the single pair `==`/`hash` suffices.
- `Hash` keys and `Set` elements must be `Hashable` (have `==` and `hash`). They do not need to be Shareable, but as in Ruby, be aware that using a mutable object as a key means its `hash` may change. (Currently there is no `Hashable` constraint, and keys compare as `==` does for the built-in types and `data`/`enum` values, but class instances by identity: a user-defined `==`/`hash` is not consulted yet.)

## 7. Strings

- `String` is always a valid UTF-8 sequence and is immutable. Ruby's multiple encodings do not exist. Other encodings are handled with `Bytes`, `String#encode` and `Bytes#decode` (UTF-8, ASCII, ISO-8859-1; an `Encoding` module is planned).
- `size`/`[]`/`each_char` work in code points, `bytesize` in bytes (`byteslice` is planned), and `graphemes` in grapheme clusters. O(1) indexing of ASCII-only strings through an internal flag is planned.
- String interpolation `"#{a}#{b}"` and chains of `+` are combined by the compiler into a single buffer allocation.
- `Symbol` and `String` are distinct types. Convert with `to_sym`/`to_s`.

## 8. Rewriting Ruby Idioms

| Ruby | Quarz |
|---|---|
| `arr << x` | `arr = arr.push(x)`, or `Array.build { \|b\| b << x }` |
| `h[k] = v` | `h = h.put(k, v)` |
| `h[k] \|\|= []` | `h = h.put(k, h.fetch(k, []))`, or `h.fetch(k) { [] }` |
| `str << "x"` | `String.build { \|b\| b << "x" }` |
| `arr.sort!` / `arr.map!` | `arr = arr.sort` / `arr = arr.map { }` |
| `arr.delete(x)` | `arr = arr.delete(x)` |
| `obj.freeze` | Unnecessary (immutable by default) |
| `obj.dup` | Unnecessary for immutable values (`dup` returns a built-in immutable value as it is) |
| `Struct.new(:a, :b)` | `data X = (a: T, b: U)` |
| `attr_accessor :x` | `var @x: T` + `attr_accessor :x` |
| `@cache \|\|= compute` | `var @cache: T? = nil` + `@cache \|\|= compute` (`Lazy`/`memoize` are planned) |
| `$stdout.puts` | `STDOUT.puts` |
| `@@count += 1` | `COUNT = Atom.new(0)` + `COUNT.update { \|n\| n + 1 }` |

## 9. Alternatives Not Adopted

- **Rust-style ownership and borrowing**: lets the type system track "moves" of mutable objects, but loses the Ruby feel. Quarz simply confines mutable objects to a task and requires conversion to an immutable value when crossing the boundary. Since freezing a Builder is O(1), we judged the practical loss to be small.
- **Erlang-style deep copying of messages**: immutable values can be shared, so copying is unnecessary.
- **Dynamic per-object immutability via `freeze`**: immutability does not appear in the type, so it cannot be used for static checking.
- **Mutable collections by default with `freeze` recommended**: improves compatibility with Ruby but is not "safe by default". Keeping Ruby's mutable API intact on the Builder side keeps the rewriting burden low.
