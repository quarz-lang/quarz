# Compile-Time Metaprogramming: `static def`, `Meta` and `Quoted`

Quarz defines its classes statically: no reopening, no `define_method`, no `method_missing`, no `eval` ([01-syntax.md](01-syntax.md) §3, [07-ruby-diff.md](07-ruby-diff.md)). This document adds, without giving that up, code that runs **while the program is compiled**: a method marked `static def` can be called from a class body, where it sees the class being declared, and everything it runs is ordinary, type-checked Quarz. The aim is what a library does in Ruby with a line like `has_many Comment` in a class body: generate typed members of that class. This document covers the compile-time execution itself, reflection, the generation of methods and fields (`Meta::ClassDef#def_method`, `def_field`, §5), and blocks received as typed trees (`Quoted`, §6).

The mechanisms:

| Mechanism | Role | Counterpart |
|---|---|---|
| `static def` | A method, checked and lowered like any other, that a class body's statement can run at compile time | D's CTFE, Zig's `comptime` calls, Scala 3's `inline` |
| `static` statement | A call, in a class body, of a `static def` class method of a dependency | A Rails class macro (`has_many`), run when the class is compiled |
| `Meta` | What compile-time code sees of the program: `Meta::ClassDef` (the class being declared, which takes the generated members), `Meta::Field`, `Meta::MethodSig` | `Module#instance_methods` and friends, at compile time only |
| `def_method` | A method of the class being declared whose body is a block of the `static def`, with the values it captured baked in | `define_method`, but typed, checked where the block is written, and compiled like a written method |
| `Quoted[P]` | A block parameter type: the block is checked as a `P` and received as a typed tree (`Meta::Expr`) too | C#'s `Expression<Func<>>`, Quill's `quote` |
| `static(call)` | A `static def`'s call with constant arguments, run while compiling, its value baked into the program | D's CTFE of an enum's initializer, Zig's `comptime` |

No macros over strings or over untyped syntax trees: what runs at compile time is checked code, and what it builds is checked code.

## 1. `static def`

```ruby
# An ORM library (a cog)
abstract class Model
  static def self.has_many(target: Type[Model]) -> Void
    fk = target.field("#{name.downcase}_id".to_sym)
    raise ArgumentError, "#{target.name} has no foreign key to #{name}" unless fk
    ...
  end
end
```

- `static` is a contextual keyword ([01-syntax.md](01-syntax.md) §1), recognized before `def` (with `private`, `native` and so on in any order). It marks instance methods and class methods alike. `abstract static def` does not exist; a `static native def` is one of the prelude's compile-time natives (§4).
- A `static def`'s body is ordinary Quarz, checked and lowered to QIR like any method. What `static` adds is that a class body's statement may **call it at compile time** (§2).
- Whether a `static def` is also an ordinary method, callable at run time, depends on what it reaches. One that reflects on a class (`fields`, `methods`, …, §4) or whose signature names `Meta::ClassDef` is **compile-time only**: a call of it from code that is not static (a method body, the top level) is a compile error, at the call. One that reaches none of that, such as a pure function of its arguments or a helper that prints, can be called from both.
- The decision is made from the method's QIR, after lowering, by the same reachability analysis that drops unused code (`quarz_ir::shake`): a `static def` is compile-time only when it, or anything it calls (a method's overrides in subclasses included), reaches a compile-time-only native or method, or when its signature names `Meta::ClassDef` anywhere. The error for a run-time call is therefore reported once the program checks otherwise, by `quarz check` as by `run` and `build`.
- The `self` of a `static` class method is the class it was called on, typed `Meta::ClassDef[Self]` (§4): a `Type[Self]` with the class's own class methods, `Type`'s `name` and `<=`, and the reflection. At run time, in a `static def` that is not compile-time only, `self` is the class value itself; this is sound because a method is compile-time only exactly when it uses the compile-time-only part.

## 2. The `static` statement

```ruby
# The application
class Post < Model
  @title: String
  def initialize(@title: String); end
  has_many Comment
end
```

A class body holds declarations ([01-syntax.md](01-syntax.md) §3) and **statements of one shape: a call, on the class being declared, of a `static def` class method**. The callee is found as any call on the class is (a class method of the class or of an ancestor); one that is not a `static def` class method is an error, and so is any other statement. Module bodies take them too; the top level does not. The callee comes from the class hierarchy, or from a generic module the class extends with itself:

```ruby
module Macros[T <: Model]
  static def has_many(target: Type[Model]) -> Void   # self: Meta::ClassDef[T]
    ...
  end
end

class Post < Model
  extend Macros[Post]
  has_many Comment
end
```

A module's `static def` (an instance method of the module, a class method of the class that extends it) has for `self` the `Meta::ClassDef` of the module's first type parameter, which `extend Macros[Post]` makes the class itself, so that the bound (`T <: Model`) types what the lifted blocks do with `self` as a `static def self.` of `Model` would. A module with `static def`s is therefore extended, never included (by a class or by an `extension`), and only as `extend M[C]` with `C` the extending class's own instance type (`extend Macros[Box[E]]` in `class Box[E]`: not `Box[Int]`, whose members would go into every `Box`, nor a subclass), and with arguments that meet the bounds of the module's type parameters (with the arguments substituted: `module F[T <: Comparable[T]]`), since the `static def`s were checked under them: anything else is an error at the `extend`. An `extension` declares no `static def`. A statement calling a `static def` of a module without type parameters is refused with what to write instead. A class under `Post` runs the module's `static def`s too, as it does its superclasses' class methods.

In the REPL, a class body's `static` statements run when the input that declares the class is entered, before its code is checked, and those of a file it requires when that file is loaded: an input's statement calls the `static def`s of the inputs entered before and of the files required, not of its own input (nor a file's of its own file), and what a statement prints goes to the session's output. A call of a compile-time-only `static def` (§1) in an input is an error there, as in a program.

The statements run while the program is checked, after every file is declared (so a statement sees the fields and methods written later in its class) and before the bodies are checked. The checker type-checks the statement with `self` a `Meta::ClassDef[C]`, then the compiler lowers the callee and everything it reaches (checking those bodies first, on demand), and runs the statement on the interpreter. What a run prints with `puts`, `p` and friends goes to the compiler's standard error, from `quarz check` too.

**Order.** The statements of a cog run in a fixed order, file name order and text order within a file, so that errors are reproducible, and the members a statement generates are declared in the order of its `def_method` calls. The statements of one cog do not depend on one another through the declarations: the reflection answers from the declarations as they stood when the cog's statements started, and a block checked in the `static def` cannot name what another statement generates. They do share the interpreter's state (a constant initialized by one statement is initialized for the next), as the methods of one program do.

**Where the callee may come from (the staging rule).** A `static def` must be lowered before it can run, with everything it reaches; so a statement in cog U may call only a `static def` declared in a **cog U depends on** (directly or through its dependencies, [10-cogs.md](10-cogs.md) §2), in the standard library, or, in a script, in a file U `require`s (loaded before it). Calling a `static def` of the same cog, or of the same script file, is an error. This is the rule of Rust's procedural macros (another crate) and of Scala 3's macros (another compilation unit); for an ORM cog used by an application, it costs nothing.

**Failure.** An exception the statement does not rescue is a compile error at the statement, with the exception's class and message and the compile-time backtrace: this is how `has_many` says that `Comment` has no `post_id`. A statement that runs longer than ten seconds is cut off with an error; so is one that would reach a native it may not call (§3).

**The statement itself** is checked like an expression in a class method: its arguments are expressions (`has_many Comment`, `scope(:recent) { ... }`), evaluated when it runs.

## 3. What compile-time code may do

The interpreter that runs a statement is the one of `quarz run`, inside the compiler: a `static def` behaves at compile time exactly as it would at run time ([05-execution.md](05-execution.md)'s "one runtime"). What it may reach is restricted so that a compilation is a pure function of the sources:

- No native that acts on the outside world or waits: `IO`, `File`, `Dir`, `Process` (so `ENV`), `Task`, `Channel`, `Selector`, `Atom`, `Signal`, `Random`, the sockets, `Time.now` and its kin, `sleep`, `exit`, `gets`. Pure arithmetic of the same classes stays (`20.ms`, a `Duration`, a `Time` made from parts). A statement whose callee reaches one of these is refused before it runs, naming the native and the calls leading to it: the reach follows calls and the overrides of the called methods in subclasses (not those in the denied classes themselves, whose values only a denied native can make). `puts`, `print`, `p`, `pp` and `warn` are allowed and write to the compiler's standard error.
- A time limit of ten seconds per statement, and the interpreter's stack limit.
- Nothing reads a file (`Meta.read_file`, for schemas, is deferred: §9).
- Dependency cogs' `static def`s run under these rules in every `quarz check` ([10-cogs.md](10-cogs.md) §6).

## 4. `Meta`: reflection

```ruby
module Meta
  data Field = (name: Symbol, type: Type[Object], mutable: Bool, default: Bool)
  enum ParamKind = Required | Optional | Rest | Keyword | Block
  data Param = (name: Symbol, type: Type[Object], kind: ParamKind)
  data MethodSig = (name: Symbol, params: Array[Param], result: Type[Object], static: Bool)
  class ClassDef[T] < Type[T]
  end
end
```

- The reflection methods of `Type[T]` ([02-types.md](02-types.md) §1) exist at compile time only: `fields -> Array[Meta::Field]` (the class's fields, its own and inherited, in declaration order), `field(name: Symbol) -> Meta::Field?`, `methods -> Array[Meta::MethodSig]` (the public instance methods, in declaration order, the most derived definition of each), `method?(name: Symbol) -> Bool`, `includes?(m: Type[Object]) -> Bool`. Called outside a `static def` or a `static` statement, they are an error. Types in `Meta::Field` and `Meta::Param` are classes (`Type[Object]` values): type arguments are erased, and a type parameter or a union shows as `Object`.
- `Meta::ClassDef[T]` is the type of `self` in a `static` class method and in a `static` statement: a `Type[T]` (so the class's name, `<=`, `==` and its class methods are there, and an implicit-self call reaches the class's class methods) with the reflection. It is the class that will take the generated members; the methods that generate them are the next part of this document. The `data` types and the enum of `Meta` are ordinary values, usable at run time too.
- `Type` cannot be subclassed by a program: `Meta::ClassDef` is the prelude's.

## 5. Generation: `def_method`

```ruby
abstract class Model
  static def self.has_many[T <: Model](target: Type[T]) -> Void
    fk = target.field("#{name.downcase}_id".to_sym) || raise "#{target.name} has no foreign key to #{name}"
    doc "The #{target.name}s whose #{fk.name} is this #{name}'s id."
    def_method(target.name.downcase.pluralize.to_sym) { target.relation.where(fk.name, id) }
  end
end

class Post < Model
  has_many Comment      # Post#comments -> Relation[Comment]
end
```

`Meta::ClassDef[T]` generates methods of `T`, the class whose `ClassDef` it is (for `self`, the class the statement is declared in):

```ruby
def_method[R](name: Symbol, *, visibility: Symbol = :public, &body: T.() -> R) -> Void
def_method[A, R](name: Symbol, param: Symbol, *, visibility: Symbol = :public, &body: T.(A) -> R) -> Void
def_method[A, B, R](name: Symbol, params: [Symbol, Symbol], *, visibility: Symbol = :public, &body: T.(A, B) -> R) -> Void
def_class_method[R](name: Symbol, *, visibility: Symbol = :public, &body: Type[T].() -> R) -> Void
def_field[U](name: Symbol, type: Type[U], default: U, *, var: Bool = false, reader: Bool = false, writer: Bool = false) -> FieldRef[T, U]
field_ref[U](name: Symbol) -> FieldRef[T, U]
doc(text: String) -> Void
```

- **The block is the body.** `def_method(name) { ... }` makes `name` a method of the class whose body is the block, lifted: the block's QIR, copied, becomes the method's function. The block is a block with a receiver ([01-syntax.md](01-syntax.md) §9): its `self` is an instance of `T` (`Type[T]` for `def_class_method`), so it calls the class's methods and reads its fields as a method would, and its last expression is the method's value. The parameters take the names given (`:by`, `[:x, :y]`), not the block's own, and their types and the result type come from the block's procedure type (`A`, `B`, `R`, inferred from the annotations and the body); the parameter count is the overload's. `visibility:` is `:public`, `:private` or `:protected`; `doc` gives the next generated method its documentation comment.
- **Checked where it is written.** The block is type-checked in the `static def`, once, under its constraints (`T <: Model` above): names resolve lexically, so the generated method sees the library's namespace, not the class's; what is unhygienic is the method's name, which is passed for that. The signature substitutes the type arguments of the statement's call (`T := Comment`) and `Self` (the class generated into); a type parameter of another method, such as a helper the `static def` calls `def_method` through, cannot be carried and is an error.
- **Captured values are baked in.** A variable of the `static def` the block reads (`target`, `fk`) is a compile-time value, which the generated method embeds as a constant where the block read it (the method is specialized to it, as Scala 3's `inline` or Zig's `comptime` arguments specialize). What can be baked is what is immutable and has a literal or a construction without code of its own: `nil`, booleans, numbers, strings, symbols, regexps, classes (`Type[T]` values), enum variants, `data` values (`Meta::Field` is one), field handles (`Meta::FieldRef`), and arrays, hashes and ranges of such. The checker refuses a capture whose type cannot be (a procedure, an object of an ordinary class); a capture typed `Object` or by a type parameter is decided when the statement runs, and a value that cannot be baked is an error at the statement. A `Meta::ClassDef` (the `static def`'s `self`) cannot be captured: an implicit call of a method of the enclosing `self` from the block is an error.
- **Field handles.** A generated method cannot name a field the `static def` received as a `Symbol` (Quarz has no `@#{name}`), so `def_field` gives a handle to the field it adds, a `Meta::FieldRef[T, U]`, and `field_ref[U](name)` one to a field of the class by name: its own, inherited, or generated by this statement or another, whose declared type is exactly `U` (fields are invariant; `U` is written, any type, `field_ref[Array[Int]](:tags)`, or a type parameter of the `static def` the statement calls, given by the statement: a generic helper that makes the handle with its own type parameter is refused, since its type argument is not known when the handle is checked). A block given to `def_method` that captures a handle reads the field with `ref.get(self)` and writes it with `ref.set(self, value)`, its arguments by position; since the handle is baked, these are the field read and write themselves, as `@name` in the class's own methods (no call, nothing looked up when the method runs). The object is the generated method's `self`, for now: the handle's `T` is the `static def`'s view of the class (`Model` in `Model`'s static def), while the field belongs to the class generated into (`Post`), which only `self` is sure to be; the `obj` parameter stays so that a later form may take another object, tested at run time. A handle is resolved when the statement has run, every member it generates declared by then: a missing field, one of another type, a field of a class the class generated into does not inherit from (a handle made for another class), or `set` on a field that is not `var` is an error at the statement. `get` and `set` on anything but a variable of the `static def` the block captures, or on another object than `self`, are an error, and only `def_field` and `field_ref` make a handle (no `FieldRef.new`, no subclass); it has its `name` and `owner` and nothing else observable.

```ruby
static def self.counter(field: Symbol) -> Void
  ref = def_field(field, Int, 0, var: true, reader: true)
  def_method("bump_#{field}".to_sym) do -> Void
    ref.set(self, ref.get(self) + 1)
  end
end
```

- **A block that becomes a method's body cannot leave the method it was written in.** It cannot assign a variable it captures (it is captured by value), `return` (its value is its last expression), `break` out of itself, nor `yield` to the `static def`'s block. Nested blocks inside it are copied with it and may `break` out of themselves as usual.
- **Run-time code.** The block runs when the generated method is called, not at compile time: it is checked as ordinary code, so it cannot call the reflection, and a call in it of a compile-time-only `static def` is an error at the call (§1).
- **The generated method is a declaration of the class**, in the file of the `static` statement, indistinguishable from a written one everywhere else: it is found by lookup, overrides and is overridden, implements an abstract method (a class with `static` statements in an ancestor, itself included, has what it must implement checked after those statements ran), is checked for duplicates and return types (the declaration-time checks of the class, its descendants and its includers run again after the statement, but for what a deferred class must implement, checked once after all of its file's statements), is compiled to machine code by `quarz build`, and `quarz check --tree` lists it with `"generated": true` and no body. A name the class already has (written or generated earlier) is an error at the statement, and so are `initialize`, `deinitialize` and `new`, whose bodies the compiler holds to rules of their own. The block's parameters are plain (no `*rest`, keywords, defaults or `&block`), and their types and the result type must be settled by the block (annotate a parameter nothing else types, or the result: `do |x: Int| -> Relation[T] ... end`; a declared result type is the generated method's); a block that never returns (it only raises) gives the method the result type `Nothing`, so that it can stand for any method, an abstract one's implementation included.
- **`def_field(name, type, default)`** adds a field `@name` to the class, of a class type without type parameters (a `Type` value carries none: `Int`, `String`, a `data` type), with a default that is a compile-time value baked into the class as a method's captures are, assignable in the class's methods when `var:` is true, and with the accessors `reader:` and `writer:` ask for (what `attr_reader` and `attr_writer` make). The class's own methods read and assign it as any field (`@hits`, in `initialize` too), its `initialize` need not assign it, and `Meta::Field` shows it with a default. It cannot go into a `data` type, an enum or a module, and a field the class or an ancestor has by that name is an error. The field comes after the class's own, so the fields of its subclasses move: what the compiler checked and lowered of them before the statement (a method a `static` statement reached) is checked and lowered again.

- **Showing what was generated.** `quarz check --expand` prints, for each class that a statement generated into, the members as declarations under the statement that made them (its fields first, then its methods in the order it made them): a field with its baked default (a `data` value as `p` shows it, since it was made without its `initialize`), the accessors as `attr_reader`/`attr_writer`, a method's signature with its `doc` as a comment and, for its body, where the block is (`def title -> String = <block at model.qz:6>`). The output is the same on every check. `quarz doc` documents a generated method with the `doc` given for it, or else with an overridden method's, never with the comment above the statement, and names the statement it came from (``generated by `props :title, :body` at post.qz:5``; `generated_by` in `--json`).

## 6. `Quoted`: a block as a typed tree

```ruby
class Relation[T]
  def where(&cond: Quoted[shareable Q[T].() -> Cond]) -> Relation[T]
    ...   # cond.expr: the block's body as a Meta::Expr, cond.captures: what it read
  end
end

posts.where { published && views > min }
```

A block parameter typed `Quoted[P]`, `P` a procedure type, receives the block written at the call **as a tree** as well as a closure. The block is checked as a `P`, as any block is (so `views > "x"` is a type error), and the call passes a `Quoted[P]`:

- `expr -> Meta::Expr`: the body, a `Meta::Expr::Block` of the block's parameters and statements;
- `captures -> Array[Object]`: the values the tree's `Capture` nodes stand for, read at the call;
- `proc -> P`: the block as a closure, to run it as written (with a receiver, `recv.instance_exec(&q.proc)`);
- `file -> String`: the file it is written in; each node has its `line`.

A `Quoted` is made only from a block literal given for such a parameter: `&proc` with a procedure is an error there (and so is `&:name`), `&q` passes a `Quoted` on to another `Quoted` parameter (`&q.proc` to a procedure one), and `Quoted.new` is an error, as is a subclass of `Quoted`. A method that overrides or implements another takes its block as the other does, as a `Quoted` or as a procedure, and a call whose possible methods (a union receiver's) differ in that is an error. A `Quoted` is a snapshot at the call: **a quoted block captures the variables it reads by value when the call is made; a later reassignment outside is not seen by the tree nor by `proc`** (after `n = 1; q = r.where { |x| x == n }; n = 2`, the tree's capture is `1` and `q.proc.call(2)` is `false`). `Quoted[P]` is Shareable when `P` is a `shareable` procedure type, whose block captures only Shareable values: `PUBLISHED = posts.where { published }` can then be a constant. Inside the method the parameter is an ordinary value: `yield` to it is an error, and its closure runs with `cond.proc.call(...)`.

The tree (`Meta::Expr`, an enum; every variant has a `line`):

| Variant | For |
|---|---|
| `Lit(value)` | a literal (`nil`, `true`, a number, a string, a symbol, a regexp, `Bytes`), and a constant whose value could be baked (§5: a literal, a class, an enum variant, `data` of such, arrays and hashes of such); a class named is a `Lit` of the class |
| `Capture(index, name)` | anything else read from outside the block: a variable of the code around it, `self` when `P` has no receiver (written, or the receiver of a call without one), a field (`@x`, named with its `@`), another constant; its value is `captures[index]`, each read at most once |
| `Arg(name, depth)` | a parameter of the `depth`-th enclosing `Block` of the tree (0: the innermost) |
| `SelfRef` | `self`, when `P` has a receiver (`Q[T].() -> Cond`) |
| `Call(recv, method, args, block)` | a call of the method the checker chose: `recv` is `nil` for an implicit receiver when `P` has one (the block's `self`, which is the `Capture` of `self` otherwise), `block` a `Block` (`&:name` becomes one: `{ \|x\| x.name }`); a construction is a call of `new`, its `index` that of the `initialize` it runs in the class declaring it |
| `And`, `Or`, `Not` | the built-in `&&`, `\|\|` and `!`; a type's own `&&` or `\|\|` (`Cond#&&`) is the `Call` it is made of, `a.&&() { b }` |
| `If(cond, then_expr, else_expr)` | `if`, `unless` (its condition under a `Not`) and `?:` with one statement a branch |
| `ArrayLit`, `HashLit`, `Interp` | array and hash literals, and a string with interpolation (its parts) |
| `Block(params, body)` | the quoted block itself, and a block given to a call inside it |

`method` is a `Meta::MethodRef(owner, name, singleton, index, extension)`: the class that declares the method, its name and side, and which of the owner's methods of that name it is (`index`, in declaration order, stable within one compiled program), with the extension's module when an extension declares it. Nodes carry no types: a `Type` value has no type arguments, and the method a call resolved to is what a translator needs. A `for` comprehension ([01-syntax.md](01-syntax.md) §11) is calls of `flat_map`, `filter` and `map` with blocks, so a type whose methods take `Quoted` blocks receives one as trees.

**What can be quoted** is exactly the above: literals, variables, `self`, fields, constants, calls with positional arguments and blocks (or `&:name`), `&&`, `||`, `!`, `if`/`unless`/`?:` of single statements, array and hash literals, interpolated strings and `for` comprehensions; a block's parameters are plain. Anything else in a quoted block, nested blocks included, is an error at its node:

```
app.qz:8:15: error: an assignment cannot be quoted: a block given as a `Quoted` holds literals, variables, `self`, calls, `&&`, `||`, `!`, `if` and blocks (docs/14 §6)
```

(assignments, loops, `case`, `begin`/`rescue`, `return`, `break`, `next`, `yield`, `super`, lambdas and procedure calls, `raise`, `&.`, ranges, keyword and splat arguments, interpolated symbols and regexps). **The tree is built once per call site and shared**: it holds only literals, constants' values and the methods resolved (what a call reads from outside is a `Capture`, whose value is in `captures`, read at each call), so a program builds it as a constant of its own the first time the call runs, and every later call, in any task, gets the same `Meta::Expr` value (`a.expr.equal?(b.expr)` for two calls of one site). Its values are Shareable (literals, and constants, which are), and building it reads nothing that can change, so when it is built changes nothing. The REPL and compile-time runs (§2) build it at each call instead, with the same result, and so does a method a `static` statement ran at compile time, whose code the program reuses (its trees are then equal but not the same value). What a translator does with the tree (SQL, say) runs at run time, in this stage.

## 7. Implementation notes

- The parser marks `static def` (`MethodDef::is_static`) and parses `static(...)` as `ExprKind::Static` (§8). The declarer records a class body's call statements as `World::static_stmts`, in order. The checker checks each statement with `self: Meta::ClassDef[C]` (`Checker::check_static_stmt`), verifies the callee and the staging rule, and hands it to a `StaticRunner` (`quarz_types::StaticRunner`, implemented in `quarz-cli`, `static_run.rs`), which lowers the statement and the callee's reach with `Lowerer::lower_static` (rounds: a method whose body is not checked yet is returned, checked by the host, and the next round continues), refuses an impure reach (`quarz_vm::natives::compile_time_allowed`), and runs the statement on an `Interp` with a deadline (`Interp::deadline`) and the reflection data (`Interp::reflect`, a snapshot of the checker's declarations).
- A compile-time run lowers, besides what the callee reaches, the methods the runtime calls by name everywhere (`to_s`, `initialize`, `hash`, `==`...: `quarz_ir::shake::RUNTIME_NAMES`), except those of the classes whose statements have not all run yet (the one running included) and of their descendants (`Lowerer::static_skip`): their bodies may use members still to be generated (an `initialize` assigning a generated field), so they are checked and lowered only once a call resolves to them (a construction reaches the `initialize` of the class it makes, `new` in an inherited class method those of every class it may make) or the statements ran (a method they generate under a name reached before is reached then); a run that dispatches to one by name before then finds no body, and the error says so. A method of another name is reached as usual, so a `static def` that calls an overridable method of the class generated into sees the class's body as written so far.
- `def_field` (§5): the native hands the runner the field (`Reflect::def_field`), which adds it to the class (`StaticHost::add_generated_field`: a `FieldInfo` with `baked_default`, whose initializer the lowerer makes from the value), marks the methods of the class's descendants checked so far as unchecked (`Output::ivar_fields` holds field indices), and invalidates what the compile-time lowering did with the old layouts (`Lowerer::invalidate_layout`: the functions that read, write or construct one of the classes, and the methods whose blocks do, are lowered again in the next round; the classes' field defaults too), and the constants initialized so far at compile time forget their values (an instance with the old layout may be among them). A class with `static` statements in an ancestor is listed in `World::conformance_deferred` instead of checked when declared; `Checker::check_static_stmts_of` checks it (`Declarer::recheck_conformance`) after the statements of its file.
- Generation (§5): the checker marks a block given to a `Meta::ClassDef` native as lifted (`Output::lifted_blocks`, its procedure type; the capture rules of a task block with the bakeable types instead of the shareable ones) and records the type arguments of a `static def`'s call (`Output::type_args`). `def_method` (a native, `Reflect::generate`) hands the runner the block's function, from `Closure`, and the values of the frame slots it reads outside itself (`captured_slots`, as a `Task.spawn` block copies them), which the runner turns into `Baked` values; after the statement's run it declares each method (`MethodInfo::generated`: the function, the captures, where) through `StaticHost::add_generated`, then `Declarer::recheck_classes` runs the declaration-time checks of the classes concerned again. The final lowering continues the runner's `Lowerer` (`lower_checked_with`; its functions so far are `Lowerer::done`), and the method's function is the block's copied with each captured `FrameGet` replaced by the instructions that make the value (`lift.rs`; a `data` value by its constructor given every physical field, or, for a type whose body has its own `initialize`, allocated without one and its physical fields stored), its nested blocks copied the same way. A call of `Meta::FieldRef#get`/`#set` on a register holding a baked handle becomes the field access (`Baker::field_get`/`field_set`, as `FnBuilder`'s, flat data fields included); the lowering passes `def_field` and `field_ref` their call's node under the keyword `__site` (`quarz_ir::FIELD_REF_SITE`), the handle carries it, and the runner checks each handle a statement's methods captured against the field and the `U` recorded there (`Runner::check_handles`, `lift::handle_sets` for `set`).
- Order and the cache ([05-execution.md](05-execution.md) §2): cog by cog in dependency order (a script file by file), the statements run first, then the cog's files are keyed and read back from the cache, so that the generated members, which the kept checks refer to and which belong to the statement's file's interface, exist; a change in a dependency's `static def` that changes what it generates changes the file's key. A method of the cog that a statement reaches (an override, `Post.table_name`) is checked from its syntax before the file is read back, which overlays the same results.
- The compile-time interpreter is the ordinary one, installed by the `quarz` command for `check` and `build` too. A compiled program embeds none of it, nor the reflection: the natives of a `static def` that only a statement calls are not in its table (`quarz_ir::shake`).
- The compile-time-only decision (`static_run::compile_time_only_calls`) lowers every `static def` with its reach after the check and walks it for the compile-time-only natives (`quarz_vm::natives::compile_time_only`) and `Meta::ClassDef` in signatures; the calls recorded in `Output::static_calls` are then reported.
- The statements run on every check, read back or not; what they generate is part of the interface, so nothing of their reach needs hashing into the key. When a constant's type turns out to differ from what a cached file was checked with, the check starts over, with a fresh runner.
- The REPL (`quarz-cli`'s `session.rs`) gives each input's check a runner continuing the session's own lowerer and running on its interpreter state (`Runner::continuing`; the session keeps `Lowerer::done` up to date with what it loads), so the functions a statement lowers and generates are the session's; `Session::feed` and `Session::require` run the unit's statements before checking its code, the staging rule being that of the unit (`Checker::repl_unit`), and a `def_field` leaves the constants of earlier inputs initialized (`SharedState::reset_consts_from`): no instance of a class declared later can be in them.
- `Quoted` (§6): the declarer takes `Quoted[P]` as a block parameter's type; the checker checks the block as `P`, records the call (`Output::quoted_blocks`, with whether `P` has a receiver) and refuses what cannot be quoted (`Checker::check_quotable`), noting the constants that are literals of the tree (`Output::quoted_lits`). The lowering (`func/quote.rs`) makes the closure as usual, a snapshot (`Proc#__snapshot`), and then the `Quoted`: the tree's nodes are `data` values constructed by the initializer of a constant the final lowering adds after the checker's (`Lowerer::quoted_once`, `add_quoted_const`: outside the checker's world, so outside the cache; the REPL and compile-time runs, whose worlds grow after lowering, build the tree in place), a variable reference deeper than the quoted levels being a capture whose source (a variable's place from the call, `self`, a field or constant) is read at the call; no new instruction. `World::class_shareable` takes `Quoted` as shareable, its type argument deciding.
- `static(call)` (§8): the checker checks the call (`Checker::check_static_expr`: a `static def` of a dependency, constant receiver and arguments, a block capturing nothing, a bakeable result type) and records it (`Output::static_exprs`); once every file is checked (and on each REPL input), `Checker::eval_static_exprs` hands each to the runner (`StaticRunner::eval`, the statements' path, `Runner::execute`), whose value is baked into `Output::static_values`, recomputed on every check; the lowering makes the baked value where the expression is (`FnBuilder::baked_value`, `lift::Baker`).
- Compile-time runs happen on a root task of the compiler's interpreter, so constants initialize and blocks run as in a program. A denied native reached in spite of the analysis (a callback a native makes, such as `to_s` for `puts`) raises at the call, which becomes the statement's error.

## 8. `static(call)`: a value computed at compile time

```ruby
class Q
  static def self.sql(table: String, cols: Array[Symbol]) -> Sql = ...
end

def posts_query -> Sql = static(Q.sql("posts", [:title, :views]))   # run while compiling
```

`static(call)` runs a call of a `static def` while the program is compiled and puts its value in the program, where the expression is: in a method, at the top level, in a constant's initializer or a field's default, anywhere an expression goes. The value is baked as a generated method's captures are (§5: a literal, a class, an enum variant, `data`, and arrays, hashes and ranges of such), made without running code; its type is the call's.

- **One call of a `static def`**, of the cogs (or required files) the file depends on, as for a `static` statement (§2); a chain is nested: `static(static(Q.relation).to_sql)`. An implicit receiver (`static(make(1))`) is the class the expression is written in, whose class method it calls. A `static def` that is compile-time only (§1) can be called here, since this runs at compile time.
- **Its receiver and arguments are constants**, positional: literals (arrays, hashes and ranges of constants), constants, classes, enum values and other `static(...)`. A block given to the call captures nothing (its variables are its own; a variable, `self`, a field or an implicit-receiver method of the code around it is an error, as a task block's non-shareable captures are); a constant it reads is part of it, and it may call compile-time-only `static def`s, since it runs at compile time.
- **Its result can be baked.** A result typed as something that cannot be (a procedure, an object of an ordinary class) is an error at the expression; one typed `Object` or by a module is judged by its value, an error at the expression when it cannot be baked.
- **The value is made once and shared**: the program makes it as a constant of its own the first time the expression runs, every later evaluation (in any task) reading the same value (`a.equal?(b)`), as a quoted block's tree is (§6); the REPL makes it at each evaluation.
- **It runs as a `static` statement does** (§3: what it may reach, the time limit), when every file is checked, and on every check: the cache keeps a file's check but not these values, so a change of a dependency's `static def` is seen. What it raises is an error at the expression; what it prints goes to the compiler's standard error. In the REPL it runs when its input is entered.
- In code that itself runs at compile time (a `static def` a statement runs), the call is made there and then, as a direct call would be (what it reflects on is the classes as declared so far, which a later statement may still change); that code is lowered again for the program once the values are known (`Lowerer::relower_static_fallbacks`), so the program bakes it there too. A block given to `def_method` cannot use `static(...)` (it is copied into the generated method, not lowered again): compute the value in the `static def` and use it in the block, where it is baked.

Errors look like:

```
app.qz:6:17: error: `static(...)`'s receiver and arguments are constants: literals, constants, classes and `static(...)` (docs/14 §8)
app.qz:9:10: error: `boom` raised ArgumentError: bad 2
```

## 9. Later

- `Meta.read_file` (schemas), an on-demand order between statements of one cog, `def_data`, `extend_type`, an `inherited` hook.
