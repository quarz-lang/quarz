# Compile-Time Metaprogramming: `static def` and `Meta`

Quarz defines its classes statically: no reopening, no `define_method`, no `method_missing`, no `eval` ([01-syntax.md](01-syntax.md) §3, [07-ruby-diff.md](07-ruby-diff.md)). This document adds, without giving that up, code that runs **while the program is compiled**: a method marked `static def` can be called from a class body, where it sees the class being declared, and everything it runs is ordinary, type-checked Quarz. The aim is what a library does in Ruby with a line like `has_many Comment` in a class body: generate typed members of that class. This document covers the compile-time execution itself, reflection, and the generation of methods and fields (`Meta::ClassDef#def_method`, `def_field`, §5).

The mechanisms:

| Mechanism | Role | Counterpart |
|---|---|---|
| `static def` | A method, checked and lowered like any other, that a class body's statement can run at compile time | D's CTFE, Zig's `comptime` calls, Scala 3's `inline` |
| `static` statement | A call, in a class body, of a `static def` class method of a dependency | A Rails class macro (`has_many`), run when the class is compiled |
| `Meta` | What compile-time code sees of the program: `Meta::ClassDef` (the class being declared, which takes the generated members), `Meta::Field`, `Meta::MethodSig` | `Module#instance_methods` and friends, at compile time only |
| `def_method` | A method of the class being declared whose body is a block of the `static def`, with the values it captured baked in | `define_method`, but typed, checked where the block is written, and compiled like a written method |

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

A class body holds declarations ([01-syntax.md](01-syntax.md) §3) and **statements of one shape: a call, on the class being declared, of a `static def` class method**. The callee is found as any call on the class is (a class method of the class or of an ancestor); one that is not a `static def` class method is an error, and so is any other statement. Module bodies take them too; the top level does not. The callee comes from the class hierarchy: a `static def` of a module, reached through `extend`, is refused with a message naming the route (its `self` could not be typed soundly: §8 records the form that will allow it).

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
- Nothing reads a file (`Meta.read_file`, for schemas, is deferred: §8).
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
def_field[U](name: Symbol, type: Type[U], default: U, *, var: Bool = false, reader: Bool = false, writer: Bool = false) -> Void
doc(text: String) -> Void
```

- **The block is the body.** `def_method(name) { ... }` makes `name` a method of the class whose body is the block, lifted: the block's QIR, copied, becomes the method's function. The block is a block with a receiver ([01-syntax.md](01-syntax.md) §9): its `self` is an instance of `T` (`Type[T]` for `def_class_method`), so it calls the class's methods and reads its fields as a method would, and its last expression is the method's value. The parameters take the names given (`:by`, `[:x, :y]`), not the block's own, and their types and the result type come from the block's procedure type (`A`, `B`, `R`, inferred from the annotations and the body); the parameter count is the overload's. `visibility:` is `:public`, `:private` or `:protected`; `doc` gives the next generated method its documentation comment.
- **Checked where it is written.** The block is type-checked in the `static def`, once, under its constraints (`T <: Model` above): names resolve lexically, so the generated method sees the library's namespace, not the class's; what is unhygienic is the method's name, which is passed for that. The signature substitutes the type arguments of the statement's call (`T := Comment`) and `Self` (the class generated into); a type parameter of another method, such as a helper the `static def` calls `def_method` through, cannot be carried and is an error.
- **Captured values are baked in.** A variable of the `static def` the block reads (`target`, `fk`) is a compile-time value, which the generated method embeds as a constant where the block read it (the method is specialized to it, as Scala 3's `inline` or Zig's `comptime` arguments specialize). What can be baked is what is immutable and has a literal or a construction without code of its own: `nil`, booleans, numbers, strings, symbols, regexps, classes (`Type[T]` values), enum variants, `data` values (`Meta::Field` is one), and arrays, hashes and ranges of such. The checker refuses a capture whose type cannot be (a procedure, an object of an ordinary class); a capture typed `Object` or by a type parameter is decided when the statement runs, and a value that cannot be baked is an error at the statement. A `Meta::ClassDef` (the `static def`'s `self`) cannot be captured: an implicit call of a method of the enclosing `self` from the block is an error.
- **A block that becomes a method's body cannot leave the method it was written in.** It cannot assign a variable it captures (it is captured by value), `return` (its value is its last expression), `break` out of itself, nor `yield` to the `static def`'s block. Nested blocks inside it are copied with it and may `break` out of themselves as usual.
- **Run-time code.** The block runs when the generated method is called, not at compile time: it is checked as ordinary code, so it cannot call the reflection, and a call in it of a compile-time-only `static def` is an error at the call (§1).
- **The generated method is a declaration of the class**, in the file of the `static` statement, indistinguishable from a written one everywhere else: it is found by lookup, overrides and is overridden, implements an abstract method (a class with `static` statements in an ancestor, itself included, has what it must implement checked after those statements ran), is checked for duplicates and return types (the declaration-time checks of the class, its descendants and its includers run again after the statement, but for what a deferred class must implement, checked once after all of its file's statements), is compiled to machine code by `quarz build`, and `quarz check --tree` lists it with `"generated": true` and no body. A name the class already has (written or generated earlier) is an error at the statement, and so are `initialize`, `deinitialize` and `new`, whose bodies the compiler holds to rules of their own. The block's parameters are plain (no `*rest`, keywords, defaults or `&block`), and their types and the result type must be settled by the block (annotate a parameter nothing else types); a block that never returns (it only raises) gives the method the result type `Nothing`, so that it can stand for any method, an abstract one's implementation included.
- **`def_field(name, type, default)`** adds a field `@name` to the class, of a class type without type parameters (a `Type` value carries none: `Int`, `String`, a `data` type), with a default that is a compile-time value baked into the class as a method's captures are, assignable in the class's methods when `var:` is true, and with the accessors `reader:` and `writer:` ask for (what `attr_reader` and `attr_writer` make). The class's own methods read and assign it as any field (`@hits`, in `initialize` too), its `initialize` need not assign it, and `Meta::Field` shows it with a default. It cannot go into a `data` type, an enum or a module, and a field the class or an ancestor has by that name is an error. The field comes after the class's own, so the fields of its subclasses move: what the compiler checked and lowered of them before the statement (a method a `static` statement reached) is checked and lowered again.

- **Showing what was generated.** `quarz check --expand` prints, for each class that a statement generated into, the members as declarations under the statement that made them (its fields first, then its methods in the order it made them): a field with its baked default (a `data` value as `p` shows it, since it was made without its `initialize`), the accessors as `attr_reader`/`attr_writer`, a method's signature with its `doc` as a comment and, for its body, where the block is (`def title -> String = <block at model.qz:6>`). The output is the same on every check. `quarz doc` documents a generated method with the `doc` given for it, or else with an overridden method's, never with the comment above the statement, and names the statement it came from (``generated by `props :title, :body` at post.qz:5``; `generated_by` in `--json`).

## 6. Implementation notes

- The parser marks `static def` (`MethodDef::is_static`) and reserves `static(...)` (§7). The declarer records a class body's call statements as `World::static_stmts`, in order. The checker checks each statement with `self: Meta::ClassDef[C]` (`Checker::check_static_stmt`), verifies the callee and the staging rule, and hands it to a `StaticRunner` (`quarz_types::StaticRunner`, implemented in `quarz-cli`, `static_run.rs`), which lowers the statement and the callee's reach with `Lowerer::lower_static` (rounds: a method whose body is not checked yet is returned, checked by the host, and the next round continues), refuses an impure reach (`quarz_vm::natives::compile_time_allowed`), and runs the statement on an `Interp` with a deadline (`Interp::deadline`) and the reflection data (`Interp::reflect`, a snapshot of the checker's declarations).
- A compile-time run lowers, besides what the callee reaches, the methods the runtime calls by name everywhere (`to_s`, `initialize`, `hash`, `==`...: `quarz_ir::shake::RUNTIME_NAMES`), except those of the classes whose statements have not all run yet (the one running included) and of their descendants (`Lowerer::static_skip`): their bodies may use members still to be generated (an `initialize` assigning a generated field), so they are checked and lowered only once a call resolves to them (a construction reaches the `initialize` of the class it makes, `new` in an inherited class method those of every class it may make) or the statements ran (a method they generate under a name reached before is reached then); a run that dispatches to one by name before then finds no body, and the error says so. A method of another name is reached as usual, so a `static def` that calls an overridable method of the class generated into sees the class's body as written so far.
- `def_field` (§5): the native hands the runner the field (`Reflect::def_field`), which adds it to the class (`StaticHost::add_generated_field`: a `FieldInfo` with `baked_default`, whose initializer the lowerer makes from the value), marks the methods of the class's descendants checked so far as unchecked (`Output::ivar_fields` holds field indices), and invalidates what the compile-time lowering did with the old layouts (`Lowerer::invalidate_layout`: the functions that read, write or construct one of the classes, and the methods whose blocks do, are lowered again in the next round; the classes' field defaults too), and the constants initialized so far at compile time forget their values (an instance with the old layout may be among them). A class with `static` statements in an ancestor is listed in `World::conformance_deferred` instead of checked when declared; `Checker::check_static_stmts_of` checks it (`Declarer::recheck_conformance`) after the statements of its file.
- Generation (§5): the checker marks a block given to a `Meta::ClassDef` native as lifted (`Output::lifted_blocks`, its procedure type; the capture rules of a task block with the bakeable types instead of the shareable ones) and records the type arguments of a `static def`'s call (`Output::type_args`). `def_method` (a native, `Reflect::generate`) hands the runner the block's function, from `Closure`, and the values of the frame slots it reads outside itself (`captured_slots`, as a `Task.spawn` block copies them), which the runner turns into `Baked` values; after the statement's run it declares each method (`MethodInfo::generated`: the function, the captures, where) through `StaticHost::add_generated`, then `Declarer::recheck_classes` runs the declaration-time checks of the classes concerned again. The final lowering continues the runner's `Lowerer` (`lower_checked_with`; its functions so far are `Lowerer::done`), and the method's function is the block's copied with each captured `FrameGet` replaced by the instructions that make the value (`lift.rs`; a `data` value by its constructor given every physical field, or, for a type whose body has its own `initialize`, allocated without one and its physical fields stored), its nested blocks copied the same way.
- Order and the cache ([05-execution.md](05-execution.md) §2): cog by cog in dependency order (a script file by file), the statements run first, then the cog's files are keyed and read back from the cache, so that the generated members, which the kept checks refer to and which belong to the statement's file's interface, exist; a change in a dependency's `static def` that changes what it generates changes the file's key. A method of the cog that a statement reaches (an override, `Post.table_name`) is checked from its syntax before the file is read back, which overlays the same results.
- The compile-time interpreter is the ordinary one, installed by the `quarz` command for `check` and `build` too. A compiled program embeds none of it, nor the reflection: the natives of a `static def` that only a statement calls are not in its table (`quarz_ir::shake`).
- The compile-time-only decision (`static_run::compile_time_only_calls`) lowers every `static def` with its reach after the check and walks it for the compile-time-only natives (`quarz_vm::natives::compile_time_only`) and `Meta::ClassDef` in signatures; the calls recorded in `Output::static_calls` are then reported.
- The statements run on every check, read back or not; what they generate is part of the interface, so nothing of their reach needs hashing into the key. When a constant's type turns out to differ from what a cached file was checked with, the check starts over, with a fresh runner.
- The REPL (`quarz-cli`'s `session.rs`) gives each input's check a runner continuing the session's own lowerer and running on its interpreter state (`Runner::continuing`; the session keeps `Lowerer::done` up to date with what it loads), so the functions a statement lowers and generates are the session's; `Session::feed` and `Session::require` run the unit's statements before checking its code, the staging rule being that of the unit (`Checker::repl_unit`), and a `def_field` leaves the constants of earlier inputs initialized (`SharedState::reset_consts_from`): no instance of a class declared later can be in them.
- Compile-time runs happen on a root task of the compiler's interpreter, so constants initialize and blocks run as in a program. A denied native reached in spite of the analysis (a callback a native makes, such as `to_s` for `puts`) raises at the call, which becomes the statement's error.

## 7. Reserved: `static(expr)`

`static(expr)`, the evaluation of an expression at compile time (a call of a `static def` with constant arguments, whose result becomes a constant of the program: a query's SQL, for instance), is reserved: the parser refuses it today. Its rules come with the second part of this design.

## 8. Later

- A module's `static def` as a statement's callee, through a generic module whose parameter is the extending class: `module Macros[T <: Model]` with `static def has_many` seeing `self: Meta::ClassDef[T]`, used as `extend Macros[Post]` (`include`/`extend` already take type arguments), so that the bound gives the lifted blocks' `self` its type without new syntax.
- `Quoted[P]`, a block parameter received as a typed expression tree, and `Meta::Expr`.
- `Meta.read_file` (schemas), an on-demand order between statements of one cog, `def_data`, `extend_type`, an `inherited` hook.
