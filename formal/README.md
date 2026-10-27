# Formal models

`quarz-core/` is a Lean 4 model of the core of the checker: narrowing
(docs/02 §6), the rules compiled code trusts. Its point is that a rule is
changed in Lean first, where a hole shows up as a proof that does not go
through, before it is changed in `check.rs`.

## QCore

A small language with Quarz's core and nothing else (`QuarzCore/`):

- `Types`: atoms (`Nil`, `Bool`, `Int`, `Str`, classes; the value classes
  final, a class never: a subclass may define `==`), unions as lists of
  atoms, the class table, `≤`.
- `Syntax`: literals, locals and fields, `self`, `new`, calls (with an
  anonymous block, live during the call: `yield`), built-in calls
  (`prim`: opaque, typed by their declarations), `if`, `while`, `return`,
  `raise`, the tests (`nil?`, `is_a?`, `==`/`!=` against `nil`, `true`,
  `false`, as forms, not calls), `&&`, `||`, `!`. A read of a local or of
  an immutable field carries the type the checker gave it there.
- `Typing`: `check`, the rules as a function; `Typed`, the same rules as
  a syntax-directed relation, which the metatheory is about; `Check`:
  `check_typed`, the function accepts what the relation derives.
- `Semantics`: a definitional interpreter with fuel (Amin and Rompf,
  POPL 2017). It is stuck where a type error would be, and when a read's
  value is not of its annotated type, so that narrowing being sound is
  part of "a checked program never gets stuck". Built-in calls answer from
  an oracle, assumed to give values of their result types.
- `Program`: a whole program checked (the class table and the methods
  well formed: overrides take at least and give at most what they
  override).

Not in v1 (design in `/tmp`, kept by the maintainers): closures (lambdas,
named blocks, what a closure assigns being un-narrowed from where it is
made), generics, patterns, `data`/`enum`, `rescue`/`ensure`,
`initialize` and definite assignment, Shareable and tasks, extensions and
overloads.

## Status

- `run_sound` (Soundness.lean) is proved: a program `Program.check`
  accepts, run with any fuel and any oracle giving values of the types
  asked for, never gets stuck. In particular each read of a local or an
  immutable field gives a value of the type the checker narrowed it to.
  `#print axioms` shows only Lean's standard ones (`Axioms.lean`).
- The proof is by induction on the fuel over the interpreter's five
  functions (`Good`: SoundDefs.lean, EvalCases.lean, StepCases.lean),
  with the invariants of Invariants.lean: the store typed, a frame's
  locals where the ghost location types say, its block chain as it was
  checked (`ChainAt`: for each block, what held at its call minus what it
  assigns, and the call's environment joined with the body's end), the
  narrowing environment holding, and writes confined to what the
  expression may assign (`Ext`).
- `check_typed` (Check.lean): what `check` accepts, `Typed` derives.
- `lake exe fuzz [N]` makes N random programs over a fixed class table,
  runs those `check` accepts, and fails on one that gets stuck: a quick
  check of rule changes before their proofs are redone.
- `./conformance.sh` turns what `quarz check --tree` prints (docs/05 §1)
  into QCore and checks it with the model, for `corpus/` (in range by
  design) and every fixture and example (mostly out of range for now).
  A disagreement is the Rust checker narrowing further than the rules
  allow, or the model being stricter: either is looked at.

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
