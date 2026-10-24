# Working on Quarz

Code, comments, commit messages and the English docs are in English.

## Layout

A Rust workspace, front end to back ends:

- `quarz-syntax` (lexer, parser, AST) → `quarz-types` (declaration,
  checking; the prelude is `std/prelude.qz`) → `quarz-lower` (AST → QIR,
  then the QIR passes) → `quarz-vm` (interpreter and the runtime that
  compiled code calls) or `quarz-aot` (one generator, `gen.rs`, behind a
  `Builder` trait, for LLVM IR text compiled by clang).
- `quarz-ir` is QIR itself, with `live.rs` (liveness, last reads, moves).
- `quarz-cli` is the `quarz` command and the integration tests.
- `docs/0N-*.md` describe the language and implementation; each has a
  `.ja.md` twin that must be updated with it.

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

- Commit and push at good stopping points. Stage files by explicit path,
  never `git add -A`. Remove a stray `examples/shapes` that tests leave.
- Never print secrets (tokens, credentials). Leave credential commands to
  the user (`! command`) unless they ask.
- Write commit messages that say what changed and why, with measured
  numbers for performance work.

## Tests

- `crates/quarz-cli/tests/fixtures/**/*.qz` with `.out` files: the VM's
  output must match, and the build tests compile every fixture and
  example with both backends and compare against the VM. Regenerate an
  `.out` only after checking the new output by hand.
- `.cargo/config.toml` sets `QUARZ_THREADS=1` for `cargo test` (and
  `cargo run`), so tasks' output order is deterministic; the default is
  one worker per CPU. `tests/threads.rs` runs `tests/threads/*.qz` with
  four workers: programs there must print the same whatever the
  scheduling.
- `tests/copies.rs`: loops meant to update collections in place must
  copy nothing (`QUARZ_COUNT_COPIES=1` prints the count at exit, on the
  VM and in compiled programs). A regression there makes a loop
  quadratic with unchanged output, which no other test sees.

## Invariants that are easy to break

- Lowering ends with: copy propagation → `release::drop_unobserved` →
  `borrow::mark_borrows` → `regshare` (register sharing) →
  `live::mark_moves` (`Take`, `Call::moved`, `OwnedCall::unused`) →
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
  runs the interpreter's code for it (`ops.rs`). Only `quarz run` and
  the REPL install the interpreter (`Interp::install_interpreter`);
  nothing a compiled program reaches may name `Inst`, `Block` or the
  interpreter, or the linker keeps them.
- Natives are registered with `native!`/`fast!`/`owned!`
  (`natives/mod.rs`): each is a function of its own, exported as
  `qzn.`/`qzf.`/`qzo.` and its first key, and a compiled program's table
  lists only those its methods use. Register a key once (a second one
  is a duplicate symbol), and build the full registries
  (`natives::all`) only through the installed interpreter.
- In register sharing, a result never shares with its own operands (the
  AOT may release a destination before reading operands), counted and
  non-counted registers stay apart (`live::heap_possible`, shared with
  the AOT), and `ClearRegs` keeps clearing registers that may hold a
  counted value: a stale reference keeps a collection shared.
- Arguments the caller does not read again move into the call, and the
  callee's `Arg` takes them out of an argument list the call owns
  (`Activation::args_owned`). A pure-region entry and a failed typed
  check must not re-read an `Arg` that already took its value.

## Performance work

- Pin to one core (`taskset -c N`) and count with
  `perf stat -e instructions:u`, and cycles for the real effect. On a
  hybrid CPU, pin to a performance core and read its (`cpu_core`) line.
- Compare against a build of the previous commit in a separate
  `git worktree` with its own `CARGO_TARGET_DIR` (and
  `QUARZ_RT_LIB=<that target>/release/libquarz_vm.a` for its AOT
  builds).
- Compiled benchmarks in `bench/` last only milliseconds: lengthen them
  before concluding. AOT cycles can differ by several percent between
  builds with identical instruction counts (code layout): identical
  instructions with different cycles is not a regression in itself.
- For start-up, use `valgrind --tool=callgrind`: sampling misattributes
  short runs.
- `bench/compare/run.sh` compares with Go, Rust, Crystal, Spinel and
  Ruby; its README records the versions and the latest results.
