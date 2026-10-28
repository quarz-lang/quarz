# Formal models

`quarz-core/` is a Lean 4 model of the core of the checker: narrowing
(docs/02 §6), the rules compiled code trusts. Its point is that a rule is
changed in Lean first, where a hole shows up as a proof that does not go
through, before it is changed in `check.rs`.

## QCore

A small language with Quarz's core and nothing else (`QuarzCore/`):

- `Types`: atoms (`Nil`, `Bool`, `Int`, `Str`, `Float`, a class with its
  type arguments, a type parameter of the enclosing class; the value
  classes final, a class never: a subclass may define `==`), unions as
  lists of atoms, the class table (each class with its parameters and
  the arguments it gives its superclass), `≤` (a class is below another
  when its chain gives that class the same arguments: the parameters
  are invariant), substitution of a class's parameters.
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
  well formed: superclass arguments as many as the parameters, overrides
  take at least and give at most what they override, as the subclass
  sees the overridden signature; the fields' defaults and each
  `initialize` checked).

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
accepts more than the Rust checker in one place, which soundness does
not need: an immutable field that admits `nil` and that `initialize`
does not assign holds `nil` (docs/01 §3 requires the assignment).

Not in v1 (design in `/tmp`, kept by the maintainers): closures (lambdas,
named blocks, what a closure assigns being un-narrowed from where it is
made), patterns, `data`/`enum`, `rescue`/`ensure`, `super`
outside `initialize` (Ruby's `super` in other methods), in a block of
it, or with a block, Shareable and tasks, extensions and overloads. Of
generics: variance and bounds (a class's parameters are invariant and
unbounded here), method type parameters and lower bounds `U >: T`, the
built-in generic classes (`Array`, `Hash`: built-in calls' arguments and
results stay opaque), and `is_a?(C[args])` where the static type does
not fix the arguments (docs/02 §7: the Rust checker rejects it too, as
it does `is_a?(C)` of a generic class without arguments).

The top level's class has no type parameters (`Program.check`; the Rust
top level's has none). A class's type arguments are compared as lists
of atoms, so `Box[Int | Nil]` and `Box[Nil | Int]` are unrelated types
here where the Rust checker takes the arguments as the same: stricter,
not unsound (a disagreement a program writing a union's members in two
orders would show). A field default is checked in each class inheriting
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
  an object made as a `Box[Int]`). No field is read before it is set: an
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
  with generic classes (`Box[T]`, `IntBox < Box[Int]`, `Pair[S, T]`; one
  program in three with a generated `initialize` assigning a field and
  calling `super` in some order, one in three opening with uses of the
  boxes: boxes of either argument assigned to the box locals, what they
  give assigned to an `Int` local, tests of them), runs those `check`
  accepts, and fails on one that gets stuck: a quick check of rule
  changes before their proofs are redone. With `≤` made to ignore the
  type arguments it finds a stuck program (a `Box[Str]` read as a
  `Box[Int]`) within 20000.
- `./conformance.sh` turns what `quarz check --tree` prints (docs/05 §1)
  into QCore and checks it with the model, for `corpus/` (in range by
  design) and every fixture and example (mostly out of range for now).
  The program's generic classes are in range when their parameters are
  invariant and unbounded; a read of a type parameter narrowed by a
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
  `Nothing`), while `T` may be `Bool` or `Int?`; the model keeps `T` on
  the falsy side.

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
