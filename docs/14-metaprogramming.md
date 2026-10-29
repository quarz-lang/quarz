# Compile-Time Metaprogramming: `static def` and `Meta`

Quarz defines its classes statically: no reopening, no `define_method`, no `method_missing`, no `eval` ([01-syntax.md](01-syntax.md) §3, [07-ruby-diff.md](07-ruby-diff.md)). This document adds, without giving that up, code that runs **while the program is compiled**: a method marked `static def` can be called from a class body, where it sees the class being declared, and everything it runs is ordinary, type-checked Quarz. The aim is what a library does in Ruby with a line like `has_many Comment` in a class body: generate typed members of that class. This document covers the first part, the compile-time execution itself and reflection; the generation of members (`Meta::ClassDef#def_method`) follows it.

The mechanisms:

| Mechanism | Role | Counterpart |
|---|---|---|
| `static def` | A method, checked and lowered like any other, that a class body's statement can run at compile time | D's CTFE, Zig's `comptime` calls, Scala 3's `inline` |
| `static` statement | A call, in a class body, of a `static def` class method of a dependency | A Rails class macro (`has_many`), run when the class is compiled |
| `Meta` | What compile-time code sees of the program: `Meta::ClassDef` (the class being declared), `Meta::Field`, `Meta::MethodSig` | `Module#instance_methods` and friends, at compile time only |

No macros over strings (D's `mixin`) or over untyped syntax trees (Crystal's macros, Rust's procedural macros): what runs at compile time is checked code, and what it builds is checked code (see [08-crystal-diff.md](08-crystal-diff.md)).

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

A class body holds declarations ([01-syntax.md](01-syntax.md) §3) and **statements of one shape: a call, on the class being declared, of a `static def` class method**. The callee is found as any call on the class is (a class method of the class or of an ancestor); one that is not a `static def` class method is an error, and so is any other statement. Module bodies take them too; the top level does not. A module cannot provide one yet (a `static def` of a module, brought in by `extend`, is not accepted as a callee): that comes with the generation of members.

The statements run while the program is checked, after every file is declared (so a statement sees the fields and methods written later in its class) and before the bodies are checked. The checker type-checks the statement with `self` a `Meta::ClassDef[C]`, then the compiler lowers the callee and everything it reaches (checking those bodies first, on demand), and runs the statement on the interpreter. What a run prints with `puts`, `p` and friends goes to the compiler's standard error, from `quarz check` too.

**Order.** The statements of a cog run in a fixed order, file name order and text order within a file, so that errors are reproducible. The statements of one cog do not depend on one another through the declarations: the reflection answers from the declarations as they stood when the cog's statements started. They do share the interpreter's state (a constant initialized by one statement is initialized for the next), as the methods of one program do.

**Where the callee may come from (the staging rule).** A `static def` must be lowered before it can run, with everything it reaches; so a statement in cog U may call only a `static def` declared in a **cog U depends on** (directly or through its dependencies, [10-cogs.md](10-cogs.md) §2), in the standard library, or, in a script, in a file U `require`s (loaded before it). Calling a `static def` of the same cog, or of the same script file, is an error. This is the rule of Rust's procedural macros (another crate) and of Scala 3's macros (another compilation unit); for an ORM cog used by an application, it costs nothing.

**Failure.** An exception the statement does not rescue is a compile error at the statement, with the exception's class and message and the compile-time backtrace: this is how `has_many` says that `Comment` has no `post_id`. A statement that runs longer than ten seconds is cut off with an error; so is one that would reach a native it may not call (§3).

**The statement itself** is checked like an expression in a class method: its arguments are expressions (`has_many Comment`, `scope(:recent) { ... }`), evaluated when it runs.

## 3. What compile-time code may do

The interpreter that runs a statement is the one of `quarz run`, inside the compiler: a `static def` behaves at compile time exactly as it would at run time ([05-execution.md](05-execution.md)'s "one runtime"). What it may reach is restricted so that a compilation is a pure function of the sources:

- No native that acts on the outside world or waits: `IO`, `File`, `Dir`, `Process` (so `ENV`), `Task`, `Channel`, `Selector`, `Atom`, `Signal`, `Random`, the sockets, `Time.now` and its kin, `sleep`, `exit`, `gets`. Pure arithmetic of the same classes stays (`20.ms`, a `Duration`, a `Time` made from parts). A statement whose callee reaches one of these is refused before it runs, naming the native and the calls leading to it: the reach follows calls and the overrides of the called methods in subclasses (not those in the denied classes themselves, whose values only a denied native can make). `puts`, `print`, `p`, `pp` and `warn` are allowed and write to the compiler's standard error.
- A time limit of ten seconds per statement, and the interpreter's stack limit.
- Nothing reads a file (`Meta.read_file`, for schemas, is planned with the generation of members).
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

## 5. Implementation notes

- The parser marks `static def` (`MethodDef::is_static`) and reserves `static(...)` (§6). The declarer records a class body's call statements as `World::static_stmts`, in order. The checker checks each statement with `self: Meta::ClassDef[C]` (`Checker::check_static_stmt`), verifies the callee and the staging rule, and hands it to a `StaticRunner` (`quarz_types::StaticRunner`, implemented in `quarz-cli`, `static_run.rs`), which lowers the statement and the callee's reach with `Lowerer::lower_static` (rounds: a method whose body is not checked yet is returned, checked by the host, and the next round continues), refuses an impure reach (`quarz_vm::natives::compile_time_allowed`), and runs the statement on an `Interp` with a deadline (`Interp::deadline`) and the reflection data (`Interp::reflect`, a snapshot of the checker's declarations).
- The compile-time interpreter is the ordinary one, installed by the `quarz` command for `check` and `build` too. A compiled program embeds none of it, nor the reflection: the natives of a `static def` that only a statement calls are not in its table (`quarz_ir::shake`).
- The compile-time-only decision (`static_run::compile_time_only_calls`) lowers every `static def` with its reach after the check and walks it for the compile-time-only natives (`quarz_vm::natives::compile_time_only`) and `Meta::ClassDef` in signatures; the calls recorded in `Output::static_calls` are then reported.
- The cache of a file's check ([05-execution.md](05-execution.md) §2) does not yet carry what a statement ran: a change to a dependency's `static def` body is seen when the dependency is checked again, which the members it generates will require (the next part adds the reach's hash to the key). When a constant's type turns out to differ from what a cached file was checked with, the check starts over before any statement runs, with a fresh runner.
- Compile-time runs happen on a root task of the compiler's interpreter, so constants initialize and blocks run as in a program. A denied native reached in spite of the analysis (a callback a native makes, such as `to_s` for `puts`) raises at the call, which becomes the statement's error.

## 6. Reserved: `static(expr)`

`static(expr)`, the evaluation of an expression at compile time (a call of a `static def` with constant arguments, whose result becomes a constant of the program: a query's SQL, for instance), is reserved: the parser refuses it today. Its rules come with the second part of this design.

## 7. Later

- `Meta::ClassDef`'s generation: `def_method` and `def_class_method` from blocks with a receiver (their captured values baked into the generated method as constants), `def_field`, `doc`, `quarz check --expand` to show what was generated.
- `Quoted[P]`, a block parameter received as a typed expression tree, and `Meta::Expr`.
- `Meta.read_file` (schemas), the cache key of what a statement ran, an on-demand order between statements of one cog, `def_data`, `extend_type`, an `inherited` hook.
