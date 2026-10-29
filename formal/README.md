# Formal models

`quarz-core/` is a Lean 4 model of the core of the checker: narrowing
(docs/02 §6), the rules compiled code trusts. Its point is that a rule is
changed in Lean first, where a hole shows up as a proof that does not go
through, before it is changed in `check.rs`.

## QCore

A small language with Quarz's core and nothing else (`QuarzCore/`):

- `Types`: atoms (`Nil`, `Bool`, `Int`, `Str`, `Float`, a class with its
  type arguments, a type parameter of the enclosing class; the value
  classes final, and a `data` type without type arguments whose `==` is
  the built-in one, as nothing subclasses it; a class never: a subclass
  may define `==`), unions as
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
  (`prim`: opaque, typed by their declarations), `if`, `while`, `return`,
  `raise`, the tests (`nil?`, `is_a?`, `==`/`!=` against `nil`, `true`,
  `false`, as forms, not calls), `&&`, `||`, `!`. A read of a local or of
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
  well formed: no class below a `data` type, superclass arguments as many
  as the parameters, in a
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

Not in v1 (design in `/tmp`, kept by the maintainers): closures (lambdas,
named blocks, what a closure assigns being un-narrowed from where it is
made), patterns, `enum`, generic `data` types, `rescue`/`ensure`, `super`
outside `initialize` (Ruby's `super` in other methods), in a block of
it, or with a block, Shareable and tasks, extensions and overloads. Of
generics: method type parameters and lower bounds `U >: T`, the
built-in generic classes (`Array`, `Hash`: built-in calls' arguments and
results stay opaque), and `is_a?(C[args])` where the static type does
not fix the arguments but for `Object` arguments of covariant
parameters (docs/02 §7: the Rust checker rejects the rest too, as it
does `is_a?(C)` of a generic class without arguments).

The model's range for generics (a choice of the model, not a language
rule): a superclass's arguments take no arguments themselves
(`class IntBox < Box[Int]`, `class Pair[A, B] < Box[A]`,
`class X[T] < Box[T?]`, not `class X < Box[Box[Int]]`), which bounds the
types `≤` compares (with such arguments, expansive inheritance and
variance make subtyping undecidable: Kennedy and Pierce, 2007); a
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
  each block, what held at its call minus what it assigns, and the call's
  environment joined with the body's end), the narrowing environment
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
  own `==`); one program in
  four with a generated `initialize` assigning a field and calling
  `super` in some order, one in four opening with uses of the boxes:
  boxes of either argument assigned to the box locals, what they give
  assigned to an `Int` local, tests of them; one in four a variance
  scenario: boxes, cells and sinks seen through a wider argument, called,
  written and given blocks through it, read back at the narrow one, and
  holders made with an argument within the bound or not, and `== nil`
  tests of data values),
  runs those `check` accepts,
  and fails on one that gets stuck: a quick check of rule changes before
  their proofs are redone. With `≤` made to ignore the type arguments it
  finds a stuck program (a `Box[Str]` read as a `Box[Int]`) within
  20000, and so it does with invariant parameters compared as covariant
  ones (a `Str` set through a `Cell[Object]` that is a `Cell[Int]`) and
  with `new`'s arguments not checked against the bounds (an `AHold[E]`,
  `E` no `A`, whose `ag` calls `get` on an `E`), and with a `data` type
  taken as final though it defines `==` (a `DEq` read as `nil` after
  `de == nil`).
- `./conformance.sh` turns what `quarz check --tree` prints (docs/05 §1)
  into QCore and checks it with the model, for `corpus/` (in range by
  design) and every fixture and example (mostly out of range for now).
  The program's generic classes are in range when each parameter has at
  most one bound, closed and of atoms taking no arguments, and their
  superclass's arguments take no arguments; methods
  a `static` statement generated (docs/14 §5: their bodies are not in
  the tree) and `Type[T]` types are out of range; a `data` type without
  type parameters is in range (its generated `initialize` assigns each
  field in order; `to_h`, and `with` without keyword arguments, are
  built-in calls); the model's `!=` is `!(==)`, so a program defining
  its own `!=` is out of range where it tests `!= nil`; an integer
  literal the Rust checker types as a `Float` is one; a read of a type
  parameter narrowed by a
  class test (`T & C`) is annotated `C`, a larger type than the Rust
  checker's, so a weaker claim.
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
  side. And: the Rust checker does not compare a superclass's type
  arguments with its bounds (`class G[U] < H[U]` with
  `class H[T <: Shape]` checks, and `G[Int].new` then reads a field of an
  `Int` at run time); the model's `wfClasses` does. And with variance: expansive inheritance
  (`class N[in Z]; class C[X] < N[N[C[C[X]]]]`), out of the model's
  range, makes the Rust checker's subtype check recurse without end on
  `def f(x: C[Int]) -> N[C[Int]] = x` (a stack overflow).

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
