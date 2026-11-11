# Working on Quarz

Code, comments, commit messages and the docs are in English.

## Layout

A Rust workspace, front end to back ends:

- `quarz-syntax` (lexer, parser, AST) → `quarz-types` (declaration,
  checking; the prelude is `std/prelude.qz`) → `quarz-lower` (AST → QIR,
  then the QIR passes) → `quarz-vm` (interpreter and the runtime that
  compiled code calls) or `quarz-aot` (one generator, `gen.rs`, behind a
  `Builder` trait, for LLVM IR text compiled by clang).
- `quarz-ir` is QIR itself, with `live.rs` (liveness, last reads, moves).
- `quarz-cli` is the `quarz` command and the integration tests.
- `docs/0N-*.md` describe the language and implementation.

## Designs

A design (in `docs/`, an issue, or one given in the conversation) may be
wrong. When something in it looks doubtful (a bug, a contradiction, a
weaker guarantee than it claims, a better option), do not implement it as
written, nor depart from it on your own: ask the user first, saying what
is in doubt and why.

## Before committing

```sh
cargo build                     # before cargo test: the AOT tests link target/debug/libquarz_vm.a
cargo test                      # several minutes; run it in the background
cargo clippy --all-targets -- -D warnings
cargo fmt --all -- --check
cargo +<rust-version> check --workspace --all-targets   # the MSRV in Cargo.toml
```

CI runs clippy and rustfmt with the latest stable, whose lints can be
newer than a local stable: check with that release (`cargo +<version>`)
when the local one is older.

A change confined to one standard-library module (`std/<name>.qz`, its
own natives file, Cargo and the std module list, plus what a shared
file gains that only the new module reaches: the `register` line and
feature-off stubs in `natives/mod.rs`, a new exception class in
`interp.rs`) runs locally `cargo build` with the feature on and off,
that module's tests in `std/test/` interpreted and compiled
(`tests/std.rs`), its doc examples, clippy, rustfmt and the MSRV check;
the full `cargo test` is CI's, which must be green before the pull
request leaves draft. A small checker fix that only refuses more
programs or changes a diagnostic (a new or tightened check in
`quarz-types`, with its tests, touching no other crate) runs locally
the area's binaries (`cargo test -p quarz-cli --test diagnostics` and
`cargo test -p quarz-types`), clippy, rustfmt and the MSRV check; the
full `cargo test` is CI's, which must be green before the pull request
leaves draft. Any other change that alters a path existing programs
run (an edited function or match arm in a shared file, `value.rs`, the
checker, lowering or the IR passes) runs the full `cargo test` locally
as above. The pull request says which case it was.

While iterating, run the test binary for the area, and the full run
only at the end when the case above calls for it: `cargo test -p
quarz-cli --test std` for the language and standard library
(interpreted and compiled), `--test build` for codegen and the runtime
compiled programs call, `--test builtins` for fixtures on the VM,
`--test diagnostics` and `cargo test -p quarz-types` (its
`tests/check.rs`) for the checker, `--test copies` and `--test verify`
with `std` and `build` for lowering and the IR passes, `--test threads`
for scheduling, `--test repl` for the REPL. The binaries that compile
programs link `target/debug/libquarz_vm.a`, which only `cargo build`
refreshes: build after a change to `quarz-vm`. A second `git worktree`
rebuilds its own `target/`; `CARGO_TARGET_DIR=<main checkout>/target`
there reuses the dependencies, but the two checkouts then overwrite
each other's `quarz` and runtime library (`cargo build` after each
switch), cargo runs on one target directory wait for each other's lock,
and measurements keep a separate one (see "Performance work").

Long commands and waits (tests, builds, CI): follow the `long-jobs`
skill (run them with `run_in_background`, keep the log and `exit=$?`,
never use `pgrep -f` with a plain pattern).

- Commit and push at good stopping points. Stage files by explicit path,
  never `git add -A`. Remove a stray `examples/shapes` that tests leave.
- Never print secrets (tokens, credentials). Leave credential commands to
  the user (`! command`) unless they ask.
- Write commit messages that say what changed and why, with measured
  numbers for performance work.
- Do not put a `Claude-Session:` line in commit messages, nor a Claude
  session URL (`https://claude.ai/code/session_...`) in pull request
  descriptions (leave the ones already there as they are).
- Review the work with an agent before the pull request leaves draft
  (commits on a draft are fine without it): give a fresh subagent the
  branch's diff (not your own conclusions), point it at
  `.claude/review-checklist.md` and ask it for correctness bugs. Fix the
  findings that need no decision from the user (amend, rebase or add
  commits while the PR is a draft). Keep the ones that do (a change of
  the language or its specification, a trade-off, more scope) and go on
  with the work; when all of it is done, ask the user about them
  together. When two review rounds of one pull request have each found a
  soundness hole, stop patching: report the holes and the options
  (narrow the scope, refuse the form with a compile error, split the
  pull request) to the user before the next change.
- A change to one of the relations of "One computation per relation"
  below starts with a short note agreed with the user before coding:
  which function decides the relation, which table the lowering ships,
  which readers switch to it, and what is deleted.

## Pull requests

- Open a draft pull request as soon as the branch has its first commit,
  while the local checks run: CI then runs in parallel with `cargo test`.
- Force-pushing after the subagent review or the local checks changed
  the commits is fine at any stage (amend or rebase as needed, onto
  main too): the merge names the head commit it was approved on.
- A rebase onto main that applied without conflicts needs no local rerun
  of the full suite: CI runs it on the new head. Rerun the affected tests
  locally when the rebase resolved a conflict or main changed a path the
  branch touches.
- Mark it ready for review only when the subagent review of the branch's
  diff and the local checks above that apply have passed; from then on
  review every change, added or rewritten, before pushing it.
- The description says what was verified.

## Issues

- Open work lives in GitHub issues of the repository that owns the code,
  one per defect or change. The title is a sentence in the commit-message
  style, saying what is wrong or what is wanted.
- The body has the headings **Symptom**, **Reproducer**, **Cause** (when
  known; say when it is a guess), **Direction** (`Decided (date): ...`,
  or the options with a recommendation) and **Found in** (the pull
  request or review that found it).
- Labels: `bug`, `enhancement`, `documentation`; `soundness` when a
  guarantee of the type or ownership system breaks (the highest
  priority); `performance`; `design` when a language or API decision is
  needed; `needs-decision` while it waits for the maintainer;
  `after-0.1.0`.
  Areas: `checker`, `lowering`, `vm`, `aot`, `meta`, `lean`, `stdlib`,
  `cli`. The milestone `0.1.0` is assigned by the maintainer.
- A bug found while implementing or reviewing that is outside the pull
  request's scope is filed as an issue that says which pull request
  found it, not fixed in that pull request nor left in a comment.
- A pull request that fixes an issue says `Closes #N` in its description.
  A decision taken about an issue is recorded as a comment on it.

## Tests

- `crates/quarz-cli/tests/fixtures/**/*.qz` with `.out` files: the VM's
  output must match, and the build tests compile every fixture and
  example with both backends and compare against the VM. Regenerate an
  `.out` only after checking the new output by hand.
- A change to one of the relations of "One computation per relation"
  below adds or extends a matrix fixture over the axes it touches
  (target: class, generic class, abstract class, module; path: own
  include, a superclass's include, an extension of the class, of a
  superclass, of an included module, a subclass of each; arguments:
  none, concrete, a parameter, an inference variable; scope: where the
  extension is active, elsewhere, another cog; backend: VM and
  compiled), whose expected output is derived from the rules, not from
  running the code; the fixture's header lists the cells it skips. The
  pull request names the axes.
- A checker change runs `quarz check` over every tracked `.qz` file and
  the cogs with the branch's binary and with main's, and the pull request
  lists the programs newly refused or newly accepted:
  `tools/check-diff.sh target/debug/quarz-main target/debug/quarz
  [COG_DIR...]` prints them, with main's binary built in a second clone
  or `git worktree` with its own `CARGO_TARGET_DIR` and copied there.
- `.cargo/config.toml` sets `QUARZ_THREADS=1` for `cargo test` (and
  `cargo run`), so tasks' output order is deterministic; the default is
  one worker per CPU. `tests/threads.rs` runs `tests/threads/*.qz` with
  four workers: programs there must print the same whatever the
  scheduling.
- `.cargo/config.toml` also sets `QUARZ_AOT_OPT=0` for `cargo test` and
  `cargo run` (clang's level for compiled programs, 0 to 3; the default
  is 2), the final local run before a pull request goes ready included.
  CI runs with 2, and a compiled-code bug that shows only under
  optimization is CI's to find: run the failing binary with
  `QUARZ_AOT_OPT=2` (`cargo test --test build` or `--test std`) locally
  only when debugging such a CI failure.
- The checker keeps each file's results between runs (docs/05 §2) under
  `QUARZ_CACHE_DIR`, which `.cargo/config.toml` points at
  `target/quarz-cache` for `cargo test`; `QUARZ_NO_CACHE=1` turns it off.
  A change to what the checker records, or to the key (`cache::interface`,
  `cache::cogs`), must give the same output with the cache off, on the
  first run and on the second: run the tests twice, the second with a
  warm `target/quarz-cache`, and `rm -rf` it after a change to the
  encoding without a new build id.
- `QUARZ_VERIFY=moves` (set by `.cargo/config.toml`) makes the interpreter
  check the facts compiled code trusts and the moves, and debug builds
  run the QIR verifier after each lowering pass (`QUARZ_VERIFY_IR=0`
  turns it off): a violation is a bug in the checker or a pass, to fix
  there, not by loosening the check (docs/05 §3).
- `tests/copies.rs`: loops meant to update collections in place must
  copy nothing (`QUARZ_COUNT_COPIES=1` prints the count at exit, on the
  VM and in compiled programs). A regression there makes a loop
  quadratic with unchanged output, which no other test sees.

## One computation per relation

- A semantic relation is computed by one function: subtyping
  (`World::is_subtype`), the ancestors and the method resolution order on
  both sides (`World::ancestors`, `class_side`), the override relation,
  conformance and its witnesses, signature equality, what a run-time
  type test can see (`check_testable`), block parameter binding, object
  layout (`quarz_ir::field_slots`). New code calls that function; it
  never re-derives the relation from the declarations, nor mirrors
  another crate's version by hand. A new variant of an existing
  predicate (`may_...`, `..._at_run_time`, a second `same_signature`)
  needs the user's approval, with the reason the existing one cannot be
  called.
- The runtime reads what the lowering ships in `RtWorld`; it never
  recomputes a relation from the declarations. A missing entry is an
  internal error, not a fallback rule.
- A compile-time check guards a run-time behaviour of the same scope: a
  behaviour that is global at run time (dynamic dispatch, conformance
  witnesses, constructors) is checked wherever the program can reach it
  (subclasses, module targets, other cogs), not only where an extension
  is active; a lexically scoped check guards only lexically scoped
  behaviour (extension methods under `using`).
- An approximation says so in its doc comment, with the direction of its
  error and the issue that makes it exact. One that accepts more than
  the exact rule is a soundness hole: it is not written without the
  user's decision.
- A fix that replaces a computation deletes the replaced one in the same
  pull request.

## Invariants that are easy to break

- Lowering ends with: copy propagation → `release::drop_unobserved` →
  `borrow::mark_borrows` → `regshare` (register sharing) →
  `live::mark_moves` (`Take`, `Call::moved`, `OwnedCall::unused`, and
  dropping constants and copies nothing reads into registers that never
  hold a counted value: overwriting one that may releases it) →
  `own_dying_receivers`. Anything that renumbers or moves instructions
  must run before `mark_moves`.
- `Inst::Release` ends the scope of a variable whose release may be
  observed (`World::release_observable`: IO, `deinitialize`, any class
  type, procs, type parameters); it reads and writes the same register,
  so a pass that redirects reads must not redirect it to another
  variable (see `copyprop::consumes`).
- A borrowed element register (`ArrayGetReg` with `borrow`) holds no
  count in compiled code: register sharing keeps it to itself,
  `mark_moves` never moves it, and the AOT never releases it.
- An object's fields are laid out by `quarz_ir::field_slots` (a field
  declared `Int`/`Float`/`Bool` is a machine word, its mark meaning
  "kept aside"): the runtime and `gen.rs` must both go through it, and
  only the runtime may write a mark or the aside list.
- A compiled program carries no QIR instructions and no interpreter:
  an instruction its code does not do inline calls the runtime's entry
  for its kind (`ffi_ops.rs`, `qz_op_*`, listed in `gen::OPS`), which
  runs the interpreter's code for it (`ops.rs`). Only the `quarz`
  command installs the interpreter (`Interp::install_interpreter`: for
  `run`, the REPL, and the compile-time runs of `static` statements in
  `check` and `build`); nothing a compiled program reaches may name
  `Inst`, `Block` or the interpreter, or the linker keeps them.
- Natives are registered with `native!`/`fast!`/`owned!`
  (`natives/mod.rs`): each is a function of its own, exported as
  `qzn.`/`qzf.`/`qzo.` and its first key, and a compiled program's table
  lists only those its methods use. Register a key once (a second one
  is a duplicate symbol), and build the full registries
  (`natives::all`) only through the installed interpreter.
- `quarz_ir::shake` keeps a method found by name only when its owner
  can have values. A native must declare, in its result or block type,
  every class whose values it makes (beyond the literals' classes and
  exceptions, which are always live): a value of a class shake thought
  dead finds its methods dropped, in compiled programs only.
- In register sharing, a result never shares with its own operands (the
  AOT may release a destination before reading operands), counted and
  non-counted registers stay apart (`live::heap_possible`, shared with
  the AOT), and `ClearRegs` keeps clearing registers that may hold a
  counted value: a stale reference keeps a collection shared.
- Arguments the caller does not read again move into the call, and the
  callee's `Arg` takes them out of an argument list the call owns
  (`Activation::args_owned`). A pure-region entry and a failed typed
  check must not re-read an `Arg` that already took its value.
- The interpreter's function tables (`Interp::funcs`, `pools`, the
  bodies) are extend-only: entries are pushed, never removed, replaced or
  moved (`vm::entry` reads them without borrowing, for tasks suspended in
  a call while the REPL loads more).

## Performance work

- Pin to one core (`taskset -c N`) and count with
  `perf stat -e instructions:u`, and cycles for the real effect. On a
  hybrid CPU, pin to a performance core and read its (`cpu_core`) line.
- Compare against a build of the previous commit in a separate
  `git worktree` with its own `CARGO_TARGET_DIR` (and
  `QUARZ_RT_LIB=<that target>/release/libquarz_vm.a` for its AOT
  builds).
- Measure compiled programs built by an installed or directly run
  `quarz` (`target/release/quarz build`, as `bench/` does), or with
  `QUARZ_AOT_OPT=2`: through `cargo run` they are compiled at -O0.
- Compiled benchmarks in `bench/` take 20–200 ms (start-up is about
  1 ms of that): still short enough that AOT cycles can differ by several
  percent between builds with identical instruction counts (code layout):
  identical instructions with different cycles is not a regression in
  itself.
- For start-up, use `valgrind --tool=callgrind`: sampling misattributes
  short runs.
- `bench/compare/run.sh` compares with Go, Rust, Crystal, Spinel and
  Ruby; its README records the versions and the latest results.
