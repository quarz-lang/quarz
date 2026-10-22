# Working on Quarz

Respond to the user in Japanese. Code, comments, commit messages and the
English docs stay in English.

## Layout

A Rust workspace, front end to back ends:

- `quarz-syntax` (lexer, parser, AST) → `quarz-types` (declaration,
  checking; the prelude is `std/prelude.qz`) → `quarz-lower` (AST → QIR,
  then the QIR passes) → `quarz-vm` (interpreter and the runtime that
  compiled code calls) or `quarz-aot` (one generator, `gen.rs`, behind a
  `Builder` trait for LLVM IR text compiled by clang, and Cranelift).
- `quarz-ir` is QIR itself, with `live.rs` (liveness, last reads, moves).
- `quarz-cli` is the `quarz` command and the integration tests.
- `docs/0N-*.md` describe the language and implementation; each has a
  `.ja.md` twin that must be updated with it.

## Before committing

```sh
cargo build                     # before cargo test: the AOT tests link target/debug/libquarz_vm.a
cargo test                      # about 4 minutes; run it in the background
cargo +1.99.1 clippy --all-targets -- -D warnings   # CI's stable
cargo +1.99.1 fmt --all -- --check
cargo +1.96 check --workspace --all-targets         # the MSRV (rust-version)
```

- Commit and push at good stopping points, with
  `git -c commit.gpgsign=false commit`. Stage files by explicit path,
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
- `tests/copies.rs`: loops meant to update collections in place must
  copy nothing (`QUARZ_COUNT_COPIES=1` prints the count at exit, on the
  VM and in compiled programs). A regression there makes a loop
  quadratic with unchanged output, which no other test sees.

## Invariants that are easy to break

- Lowering ends with: copy propagation → `regshare` (register sharing)
  → `live::mark_moves` (`Take`, `Call::moved`, `OwnedCall::unused`) →
  `own_dying_receivers`. Anything that renumbers or moves instructions
  must run before `mark_moves`.
- `quarz build` embeds the QIR it compiled, and deoptimization resumes
  the interpreter on the compiled code's registers. A backend may lower
  differently (`Sharing::Numbers` for Cranelift) only because of that.
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

- Pin with `taskset -c 3`. The CPU is hybrid: read the `cpu_core` line
  of `perf stat -e instructions:u` (and cycles for the real effect).
- Compare against a build of the previous commit in a separate
  `git worktree` with its own `CARGO_TARGET_DIR` (and
  `QUARZ_RT_LIB=<that target>/release/libquarz_vm.a` for its AOT
  builds).
- Compiled benchmarks in `bench/` last only milliseconds: lengthen them
  before concluding. AOT cycles vary about ±5% between builds with
  identical instruction counts (code layout).
- For start-up, use `valgrind --tool=callgrind`: sampling misattributes
  short runs.
- `bench/compare/run.sh` compares with Go, Rust, Crystal, Spinel and
  Ruby; its README records the versions and the latest results.
