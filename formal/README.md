# Formal models

`quarz-core/` is a Lean 4 model of the core of the checker: narrowing
(docs/02 §6), the rules compiled code trusts. Its point is that a rule is
changed in Lean first, where a hole shows up as a proof that does not go
through, before it is changed in `check.rs`.

## QCore

A small language with Quarz's core and nothing else (`QuarzCore/`):

- `Types`: atoms (`Nil`, `Bool`, `Int`, `Str`, `Float`, a class with its
  type arguments, a type parameter of the enclosing class; the value
  classes final, and a `data` type or an enum's variant without type
  arguments whose `==` is the built-in one, as nothing subclasses it; a
  class never: a subclass may define `==`), unions as
  lists of atoms, the class table (each class with its parameters'
  variances and bounds and the arguments it gives its superclass), `≤`
  (a class is below another when its chain gives that class arguments
  below the other's as the parameters' variances say: `out` as they
  are, `in` the other way, an invariant one both ways; a parameter is
  below what its bound is below, with the bounds of the class whose
  types are compared, none for values' types), substitution of a class's
  parameters, the variance check of where a type names a parameter
  (docs/02 §3). `≤` recurses into the arguments with fuel, as much as
  the two atoms are deep, which is enough (LeLemmas.lean) because a
  superclass's arguments take no arguments themselves (below).
- `Syntax`: literals, locals and fields, `self`, `new` with the type
  arguments the checker inferred (the fields' defaults, then
  `initialize`), calls (with an anonymous block, live
  during the call: `yield`), built-in calls
  (`prim`: opaque, typed by their declarations; one may raise, as the
  oracle says), `if`, `while`, `return`,
  `raise e` (an exception: a value of the class named `Exception`, or any
  value in a program without it), `rescue body x handler els` (an
  exception the body raises in `x`, then the handler; otherwise `els`),
  `ensure body ens` (`ens` after the body however it ends, its result
  kept unless `ens` raises or returns), `lambda ps own ret body` (a
  procedure closed over the frame's locals by reference: design §13.8
  and §13.10, its parameters and `own` fresh at each call, reading the
  frame's locals as declared, since it may run when they hold other
  values, and assigning them at their declared types) and
  `callProc f args`, `absurd` (where no value gets: what a `case/in` on a closed
  type reaches when no arm matches), the tests (`nil?`, `is_a?`, `==`/`!=` against `nil`, `true`,
  `false`, as forms, not calls), `&&`, `||` (`a || b` of `a`'s truthy
  part and `b`'s type, `a && b` of `a`'s falsy part and `b`'s), `!`. An
  assignment's value tested narrows its local too (`if (x = e)`). A read of a local or of
  an immutable field carries the type the checker gave it there.
- `Typing`: `check`, the rules as a function; `Typed`, the same rules as
  a syntax-directed relation, which the metatheory is about; `Check`:
  `check_typed`, the function accepts what the relation derives.
- `Semantics`: a definitional interpreter with fuel (Amin and Rompf,
  POPL 2017). It is stuck where a type error would be, when a read's
  value is not of its annotated type, and when a field is read before it
  is set, so that narrowing and definite assignment being sound are part
  of "a checked program never gets stuck". Built-in calls answer from an
  oracle, assumed to give values of their result types. An object
  carries the type arguments it was made with (ghost: no program
  observes them), a frame the arguments `self`'s class gives the
  method's owner, and a read's annotation, which may name the class's
  parameters, is checked with those substituted: the theorem holds up to
  type arguments (a value read as a `Box[Int]` was made as one).
- `Program`: a whole program checked (the class table and the methods
  well formed: no class below a `data` type or a variant, an enum's
  subclasses its variants (without parameters), superclass arguments as
  many as the parameters, in a
  positive position and within the superclass's bounds, no more bounds
  than parameters, `new`'s type arguments within the bounds, overrides take at least and give at most what they
  override, as the subclass sees the overridden signature; the variance
  check of each method's signature but `initialize`'s, and of each
  class's fields; the fields' defaults and each `initialize` checked).
  The proof needs the method check (a call through a covariant view, a
  `Box[Object]` holding a `Box[Int]`, runs the method with the object's
  own arguments: its parameters must take what the view gives, its
  result and block give what the view says) and the superclass one (the
  chain keeps arguments' order); the fields' check it does not need (a
  field is read and written only by its object's methods, which see the
  exact arguments), the Rust checker has it.

`initialize` (docs/01 §3): a field must be assigned there when it has no
default and its type does not admit `nil` (`var` or not). In
`initialize`, the narrowing environment's field entries are the fields
set so far (those with a default, those that admit `nil`, and those
assigned on every path there; a loop's body and a block count for
nothing after them); a field is read, `self` used (so a call on it) and
`return` taken only where the rules say it is set (every field, for
`self` and `return`); a block in it assigns no immutable field. A
default runs before `initialize`, reading only the fields before it that
hold a value, and checked as a block of `initialize` is, but that it
never uses `self`. `super(args)` in `initialize` (not in a block of
it: the Rust checker rejects one there too) runs the superclass's
`initialize` on the object: the class's own
fields to assign must be set before it, and the inherited ones are set
after it (docs/01 §3), so the superclass's `initialize`, which may call
a method the subclass overrides once its own fields are set, finds the
subclass's set. After `super`, every field is at its declared type: a
narrowing of a field before `super` does not survive it (the Rust checker
keeps the class's own, which the model's invariants cannot yet tell from
the inherited ones: stricter than the Rust checker, not unsound). An
`initialize` that does not set every field by its end, by `super` or
itself, is rejected. No call reaches `initialize` but `new` and `super`
(the Rust checker enforces this too). A `while` un-narrows what its body
assigns before the test and the body, a field included: in `initialize`,
a field set before the loop and assigned again in its body counts as
unset after the loop, so `@x = 1; while c; @x = nil; ...; end` is
rejected where the Rust checker accepts it (it widens the field to its
declared type): stricter than the Rust checker, not unsound.
The model
accepts more than the Rust checker where soundness does not need the
Rust rule: an immutable field that admits `nil` and that `initialize`
does not assign holds `nil` (docs/01 §3 requires the assignment); a
type naming a generic class with arguments outside its bounds
(`h: Holder[Int]`) is accepted in annotations and signatures, the bounds
being checked where an object is made (`new`) and in superclass
arguments; a call on a value of a parameter whose bound is a union of
classes finds each class's method (the Rust checker reports the method
undefined), and one whose bound is `Nothing` is vacuous (no value).

Not in v1 (design in `/tmp`, kept by the maintainers): array, hash, find, range and pin patterns, generic `data`
types and `enum`s, `rescue`/`ensure` in `initialize` and in defaults
(fields being set: design §12) and `retry` but at the end of a clause
of a `begin` used as a statement, `super`
outside `initialize` (Ruby's `super` in other methods), in a block of
it, or with a block, Shareable and tasks, extensions and overloads. Of
generics: method type parameters and lower bounds `U >: T` (but a
built-in call's, which the translator instantiates), the built-in
generic classes but `Array` (`Hash`, `Range`, `Set`), and `is_a?(C[args])` where the static type does
not fix the arguments but for `Object` arguments of covariant
parameters (docs/02 §7: the Rust checker rejects the rest too, as it
does `is_a?(C)` of a generic class without arguments).

The model's range for generics (a choice of the model, not a language
rule): a superclass's arguments take no arguments themselves
(`class IntBox < Box[Int]`, `class Pair[A, B] < Box[A]`,
`class X[T] < Box[T?]`, not `class X < Box[Box[Int]]`), which bounds the
types `≤` compares (with such arguments, expansive inheritance and
variance make subtyping undecidable: Kennedy and Pierce, 2007; the
Rust checker refuses only expansive inheritance, as docs/02 §3 says,
so this range is stricter than the language); a
parameter's bound is one type, closed, whose atoms take no arguments
(`T <: Shape`, `T <: Int | String`; not `T <: Comparable[T]` nor
`T <: A & B`). The conformance translator puts other programs out of
range. Where values flow (arguments, results, assignments, reads'
annotations), the checker compares with the bounds of the method's
class, and a call on a parameter's value finds the bound's method; a
narrowing (`is_a?`, `nil?`, truthiness, `==`) and a loop's environment
compare without them, so a test of a `T <: Shape` value against `Shape`
keeps `T` on its false side where the Rust checker may drop it:
stricter, not unsound; likewise for the true side of such a test (the
model narrows `x : T?` to `Shape`, where the Rust checker keeps `T`),
for truthiness of a bounded parameter (`T <: Shape` is never falsy, the
model keeps `T` on the false side), for a loop's environment, and for
`is_a?(C[args])` checks, whose arguments compared through bounds the
model rejects as not checkable (`x : OBox[T]?`, `x.is_a?(OBox[Shape])`).
So that these do not show as disagreements, the conformance translator
puts out of range a method of a class with a bounded parameter that
tests or loops, and a field default that tests or loops in a program
with a bounded parameter.
A union bound is compared atom by atom (a `T` is below `X | Y` when the
whole bound is below `X`, or below `Y`), as the Rust checker does. The variance
check applies to every method of the model, where the Rust checker
skips private methods and the accessors `attr_reader`/`attr_writer`
make (whose signatures pass it anyway): the translator puts a private
method of a class with a variant parameter out of range. Narrowing
removes atoms as written (`Ty.remove`, `Ty.keep`, and the class test's
`a != b`), so where the Rust checker compares two spellings of one type
(`Box[Int | Nil]`, `Box[Nil | Int]`) by subtyping, the model may keep an
atom it could drop: stricter, not unsound.

The top level's class has no type parameters (`Program.check`; the Rust
top level's has none). A field default is checked in each class inheriting
the field, and run with the object's class's arguments; one whose type
names a parameter of the declaring class is thus rejected in a subclass
that fixes it (`class IntBox < Box[Int]` with a default of type `T` in
`Box`), where the Rust checker checks it once, in the declaring class:
stricter, not unsound.

## Status

- `run_sound` (Soundness.lean) is proved: a program `Program.check`
  accepts, run with any fuel and any oracle giving values of the types
  asked for, never gets stuck. In particular each read of a local or an
  immutable field gives a value of its annotation, which `check` accepts
  only when it is at least what the rules narrow the path to: with the
  Rust checker's types as annotations (`conformance.sh`), the types
  compiled code relies on hold, type arguments included (an object's
  ghost arguments are its `new`'s, so a read annotated `Box[Int]` gives
  an object made as a `Box[Int]`, or as one below it as `Box`'s
  variance says). No field is read before it is set: an
  object's immutable fields only after its defaults, `initialize` or
  `super` assigned them. (`eval`
  checks reads, not writes: an ill-typed write would show at its read.)
  `#print axioms` shows only Lean's standard ones (`Axioms.lean`).
- The proof is by induction on the fuel over the interpreter's functions
  (`Good`: SoundDefs.lean, EvalCases.lean, StepCases.lean,
  ConstructCases.lean for `new`, which gives an object with every field
  set: `ConstructPost`; `init_run` in EvalCases.lean runs an
  `initialize` for `new` and for `super`, on an object whose fields are
  set but those its class has to assign, and gives its frame `InitSelf`;
  the lemmas about frames, fields and `initialize` these share are in
  FrameLemmas.lean), with the invariants of Invariants.lean:
  the store typed (the fields set), a frame's locals where the ghost
  location types say, its block chain as it was checked (`ChainAt`: for
  each block, what held at its call minus what it assigns: after the
  call, that holds, as the body may have stopped anywhere, an exception
  the method rescued), the narrowing environment
  holding, and writes confined to what the expression may assign (`Ext`:
  objects keep the fields set, so a value of a made object keeps its
  type, `Store.typeOf` giving none to an object not made; and an object's
  immutable fields change only in its own defaults and `initialize`).
- `check_typed` (Check.lean): what `check` accepts, `Typed` derives.
- `lake exe fuzz [N]` makes N random programs over a fixed class table
  with generic classes (`Box[T]`, `IntBox < Box[Int]`, `Pair[S, T]`,
  `OBox[out T]` with `each`, `Cell[T]` with a `var` field and `set`,
  `Sink[in T]`, `IntOBox < OBox[Int]`, `AHold[T <: A]` calling `A#get`
  through its bound, `data` types `DPt` and `DEq` (the latter with its
  own `==`), an enum `Sh` with variants `Ci` and `Pt`; one program in
  four with a generated `initialize` assigning a field and calling
  `super` in some order, one in four opening with uses of the boxes:
  boxes of either argument assigned to the box locals, what they give
  assigned to an `Int` local, tests of them; one in four a variance
  scenario: boxes, cells and sinks seen through a wider argument, called,
  written and given blocks through it, read back at the narrow one, and
  holders made with an argument within the bound or not, `== nil`
  tests of data values, and `case/in` on an enum covering one variant or
  both),
  runs those `check` accepts,
  and fails on one that gets stuck: a quick check of rule changes before
  their proofs are redone. With `≤` made to ignore the type arguments it
  finds a stuck program (a `Box[Str]` read as a `Box[Int]`) within
  20000, and so it does with invariant parameters compared as covariant
  ones (a `Str` set through a `Cell[Object]` that is a `Cell[Int]`) and
  with `new`'s arguments not checked against the bounds (an `AHold[E]`,
  `E` no `A`, whose `ag` calls `get` on an `E`), and with a `data` type
  taken as final though it defines `==` (a `DEq` read as `nil` after
  `de == nil`), and with an enum expanded to one of its variants only (a
  `case/in` missing `Pt` reaching `absurd`).
- `./conformance.sh` turns what `quarz check --tree` prints (docs/05 §1)
  into QCore and checks it with the model, for `corpus/` (in range by
  design) and every fixture and example (mostly out of range for now).
  The program's generic classes are in range when each parameter has at
  most one bound, closed and of atoms taking no arguments, and their
  superclass's arguments take no arguments; methods
  a `static` statement generated (docs/14 §5: their bodies are not in
  the tree) and `Type[T]` types are out of range; a `data` type without
  type parameters is in range, so is an `enum` (its variants, a
  variant without data written as its value); patterns become tests and
  assignments in the translator, the model having none: `C` an
  `is_a?(C)`, `C(p, ...)` and `C(k: p, ...)` (a `data` type's or a
  variant's fields) that test, then each field read into a temporary
  and matched (a field pattern matching every value of the field's type
  tests nothing, as the Rust checker's coverage has it), `p | q` an
  `||` (without bindings), `nil`, `true`, `false` the tests of them, a
  number `(is_a?(Int) || is_a?(Float)) &&` an opaque equality (another
  numeric class's equal number matches too, docs/02 §6), a string
  `is_a?(String) &&` one, `x` and `p => x` assignments, made where the
  compiled program makes them (a binding before a field test that fails
  stays made); a guard follows the pattern's test and assignments. The
  tests read the subject again where the program reads it once: a
  `case` or match whose pattern or guard may assign its subject is out
  of range. `case/in` is its arms' tests in
  order, `v => p` raises where `p`'s test fails, `v in p` is its test,
  and `x == V` (`!=`) with a variant `V` without data an `is_a?(V)` (out
  of range if the program defines `==` or `!=`). Without `else`, a closed subject (variants,
  `data`, `nil`, `Bool`, as the Rust checker's `is_closed_type`, or
  more than one member once enums are expanded) ends in `absurd`, so the
  checker requires the arms to cover it (an enum is expanded to its
  variants on a test's false side), an open one in `raise`; a capture
  is declared with the type the match narrows the subject to (an enum
  as its variants, on both sides of a test), a `var` field subject is
  read once into a local. An arm's names are its own (docs/01 §11):
  fresh locals of the arm, shadowing an outer one, its guard and body a
  scope; `v in p` and `v => p` bind into the enclosing scope only once
  the whole pattern matched (into temporaries while it tests; a `v in p`
  rebinding an existing local is out of range, as the model's `&&`
  cannot keep the local as it was on the false side). A local declaration
  (`y: T = e`, `y := e`, docs/01 §10) at the top of a block's, a
  lambda's, an arm's or a `rescue` clause's body is a fresh local for
  the rest of it, as is one at the method's top hiding nothing but in an
  enclosing scope; inside an `if`, a loop or a guard of such a scope it
  is out of range; elsewhere it declares the method's local with its
  declared type. Later arms see the subject
  narrowed by the earlier ones' false sides, and arms after an `in x`
  are not checked, where the Rust checker checks each arm with the whole
  subject type: more lenient, not unsound. A `data` type without
  type parameters is in range (its generated `initialize` assigns each
  field in order; `to_h`, and `with` without keyword arguments, are
  built-in calls); the model's `!=` is `!(==)`, so a program defining
  its own `!=` is out of range where it tests `!= nil`; an integer
  literal the Rust checker types as a `Float` is one; a read of a type
  parameter narrowed by a
  class test (`T & C`) is annotated `C`, a larger type than the Rust
  checker's, so a weaker claim.
  `begin`/`rescue`/`else`/`ensure` (docs/01 §12) becomes `rescue` and
  `ensure`: the exception held in a local no program can spell, each
  clause a class test of it (a clause without a class `StandardError`),
  its variable (a local of the clause, fresh, shadowing one outside:
  quarz#126) assigned, the last raising it again (as a bare `raise` in
  a clause does); without `else`, the body's value held in a local too.
  The built-in exception classes are classes of the model without
  fields, their methods built-in calls, an exception made (`E.new(m)`,
  `raise E, m`, `raise "m"`) an opaque built-in call of its class. A
  `retry`, at the end of a clause of a `begin` used as a statement, makes
  it a loop: a flag the clause sets, the body run again while it is set
  (`while`'s rule, what the body and the clauses assign un-narrowed at
  its start, is the rule for a body a `rescue` retries), `ensure`
  outside the loop.
  `Array[out T]` is the model's class of kind `builtin` (design §14):
  right below `Object`, without fields, no method, nothing below it and
  no `new` of it. Its values are opaque (`Value.builtin`, their class
  and arguments ghost in the store): a built-in call whose declared
  result is one such class makes one, any other built-in result comes
  from the oracle. An array literal is a built-in call (its elements of
  the element type the checker gave it), and an array's methods are
  built-in calls typed by their declarations, `Array`'s parameter the
  receiver's element type and the method's own parameters what the
  call's result type says (the checker's instantiation). The model does
  not keep elements: an element read gives a value of the declared
  type, which the theorem assumes of built-in calls (so the variance of
  `Array` is the declaration's, not checked against element reads).
  `xs == nil` of an array narrows nothing (a class atom is not final),
  stricter than the Rust checker.
  A block given to a built-in method (`each`, `map`, `times`) is the
  translator's alone (design §14, part B): scoped as a block (its own
  locals and parameters, the two-locals rule), it becomes the call,
  its result held in a fresh local, then a loop running the body any
  number of times (`while` on a built-in `Bool`), its parameters
  assigned values of their types from built-in calls and its value
  given to one taking the block's result type, then the result. So
  `while`'s rule types it: the body starts with what it assigns and the
  pinned locals un-narrowed, and after it so are they, the rest kept. A
  `break`, `next` or `return` in such a block is out of range, as are a
  block the built-in keeps (`at_exit`'s, run later), one in a field
  default, and an annotated block parameter. (A model
  construct, `primBlk`, would be the alternative if a proof needs to
  tell such a block from a loop.)
  A procedure type `(A1, .., An) -> R` is the model's class
  `ProcN[in A1, .., in An, out R]` (kind `proc`: right below `Object`,
  without fields, no method, nothing below it and no `new` of it; its
  values are procedures), so procedure types compare as the variances
  say. A lambda's own locals (the names first assigned in it) are fresh
  at each call, as in Quarz. What the method's lambdas assign of its
  locals (`Ctx.pinned`) is un-narrowed after every call (a method's,
  a block's, `yield`, `new`, `super`, a procedure's, a built-in one,
  which may call the program's `to_s`, an `==` that may call one) and
  where a block, a `rescue` handler, an `ensure` clause and each pass of
  a loop start: any of these may run a lambda, which writes such a local at its
  declared type (the proof: the store marks the locations of pinned
  locals, ghost, and any call may write a marked location). The Rust
  checker never narrows such a local once the lambda is made, and
  narrows it before: the model un-narrows it after a call before the
  lambda is made too, so a program narrowing it there across a call
  disagrees (stricter, not unsound: design §13.10). The translator puts
  `!x` of an object out of range (a class may define `!`, which the
  model's `!` does not call). Its body sees the method's locals as declared, where the
  Rust checker keeps the narrowing of one assigned once (design §13.4,
  R2b, later), so a read the Rust checker narrows further is a model
  limit for now: the translator puts such a read out of range (one of a
  local or a field the body does not test itself), as it does a shareable
  procedure type (it captures by value). A named block parameter (a
  block the method may keep) is a last parameter of procedure type,
  `yield` a call of it (out of range when the method assigns it), and a
  block given to such a method a lambda; `&p` passes a procedure (into
  an anonymous block, a block calling it). Out of range: `&p` to a
  built-in method, `&` of an expression but a local into an anonymous
  block, a block of a generic method keeping it, and a block given to a
  union receiver when a method of that name keeps its block. A `-> Void` block's body gets `nil` at its
  end, as a `-> Void` lambda's does. The Rust checker counts any block as one that
  may run later while the method it is given to is not known
  (`prescan_repeated`); the model resolves the call first, so it is only
  more precise there.
  `x op= e` (a local or a field of `self`) is `x = x op e`, the read of
  `x` at the type the checker gave its current value (`op_targets`, the
  tree's format 5), so its narrowing there is checked; `||=` and `&&=`
  with the model's `||` and `&&` (out of range where a program defines
  them), another operator the method the checker resolved.
  A block that declares its result type (`do |x| -> T ... end`, the
  tree's `block_results`, format 6) has its body checked against `T`
  and gives `T`, as a `def`'s return type does (a built-in call taking
  the body's value at `T` and giving `T`); `-> Void` discards the value.
  This holds for a block given to a method, to a built-in method, and
  for one a method keeps. A generic built-in method's type
  parameters are what the call's result type says (the checker's
  instantiation; a lower bound widens it), as an array method's are.
  Closures' stage C2 (pinned locals un-narrowed only once a lambda
  assigning them is made, design §15) is deferred until a program needs
  it: none in the corpus, the fixtures or the examples does.
  `x.m!` that the checker resolved to `m` (the sugar for `x = x.m`,
  docs/01 §10, on a local) is that assignment.
  A disagreement is the Rust checker narrowing further than the rules
  allow, or the model being stricter: either is looked at. The methods
  `attr_reader` and `attr_writer` make are methods of the model; another
  built-in method called on the implicit receiver is a `prim` taking
  `self` (it may read the fields), but for a `Kernel` function: so a
  call of either before every field is set disagrees (as `attr_reader`
  calls did before #70). Found by the model with generics: the Rust
  checker takes a value of a type parameter's type as always truthy
  (`if @v ... else @v end` with `@v : T` types the else branch
  `Nothing`), while an unbounded `T` may be `Bool` or `Int?` (a
  `T <: Shape` is indeed never falsy); the model keeps `T` on the falsy
  side. And: the Rust checker did not compare a superclass's type
  arguments with its bounds (`class G[U] < H[U]` with
  `class H[T <: Shape]` checked, and `G[Int].new` then read a field of an
  `Int` at run time), as the model's `wfClasses` does; #116 made it
  (superclasses, included modules' arguments and bounds too). And with variance: expansive inheritance
  (`class N[in Z]; class C[X] < N[N[C[C[X]]]]`), out of the model's
  range, made the Rust checker's subtype check recurse without end on
  `def f(x: C[Int]) -> N[C[Int]] = x` (a stack overflow); the class is
  now refused (docs/02 §3). And with
  `rescue`: `raise K, m` (and `raise K`) makes a `K` without running its
  `initialize` or its fields' defaults, so a field it declares is `nil`
  where its type says otherwise (the translator puts such a `raise` out
  of range); a clause's variable that names an existing local is
  narrowed to the exception's classes whatever its declared type; a
  `retry` in a block in a clause is accepted and fails at run time
  (these three fixed since: 8ccb796, quarz#126). And: in a
  generic class, `b : Box[T]` tested with `is_a?(IntBox)` (`IntBox <
  Box[Int]`) is narrowed to nothing by the Rust checker, so the branch
  goes unchecked (`s: String = b` checks, and fails at run time); the
  model's true side keeps `IntBox`.
- Known disagreements that are the model's limits, not the Rust
  checker's holes (none in the corpus, the fixtures or the examples):
  a class test of a type parameter's value (`x.is_a?(A)` or `in A` with
  `x : T`): the Rust checker narrows to `T & A`, still a `T`; the model,
  without intersection types, to `A`, so a use of `x` as a `T` after it
  is rejected. Two others the translator puts out of range: a read of a
  local not assigned on every path before it (`if c; x = 3; end; y =
  x`: the Rust checker reads it as `T?`, the model's environment has no
  entry for it; branches a test makes dead count here, so this is
  stricter than the model), and a name that is two locals for the Rust
  checker, docs/02 §6, and one for the model, which declares a name once
  per method: first assigned in a block and assigned again outside it or
  in another block, a block parameter named like another local, or two
  blocks' parameters of one name and different types (dead code counts:
  the model declares a name where it is first written).

## Setup

[elan](https://github.com/leanprover/elan) installs the toolchain
`lean-toolchain` names; `lake` fetches Batteries and Plausible.

```sh
cd formal/quarz-core
lake build                 # the model, the proofs, the examples' #guards
lake exe fuzz 20000
cargo build && ./conformance.sh
lake env lean Axioms.lean  # no sorryAx
```

Where `release.lean-lang.org` is not reachable (the devcontainer's
proxy), the toolchain is the GitHub release's archive, linked:
`elan toolchain link leanprover/lean4:v4.35.0 DIR`.
