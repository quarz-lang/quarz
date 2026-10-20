# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-20, with the LLVM backend)

Same machine and versions as below; Quarz at the LLVM-backend commit,
`quarz build` compiling through `clang -O2` (the default backend).
Milliseconds, best of 10 runs. The Cranelift backend (`--backend
cranelift`, for development) gives fib 6.8, loop 9.3, collections 33.4,
objects 8.4, strings 31.4 on the same runs.

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    146.0 |       5.0 |  2.3 |  1.8 |  70.1 |        61.1 |
| loop        |    439.4 |       4.4 |  3.5 |  3.6 | 117.9 |       118.9 |
| collections |    539.5 |      31.8 | 30.1 | 13.6 | 239.2 |       215.7 |
| objects     |    104.7 |       7.2 |  2.1 |  1.4 | 316.3 |       255.6 |
| strings     |     89.6 |      34.7 | 36.9 | 17.1 | 173.7 |       169.0 |

## Results (2026-10-19, Cranelift, after the direct-call, unboxing, inlining, lean-call, allocation, array, hashing and equality rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at the equality commit, VM =
`quarz run`, AOT = `quarz build`. Milliseconds, best of 5 runs, process
start-up included (about 2 ms for a compiled Quarz program). `fib` and
`loop` are short enough that the numbers wander by a few milliseconds
between runs.

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    137.1 |       6.1 |  2.2 |  1.8 |  68.2 |        56.1 |
| loop        |    402.8 |       9.0 |  3.9 |  3.4 | 107.0 |       109.3 |
| collections |    483.1 |      31.8 | 29.4 | 13.0 | 223.7 |       203.1 |
| objects     |     96.6 |       7.4 |  1.9 |  1.6 | 284.5 |       226.8 |
| strings     |     77.4 |      29.1 | 33.1 | 15.4 | 154.7 |       148.9 |

First measurement, at commit 93874ea (before direct calls between
compiled bodies, inline reference counting, inline field and frame
access and the reusable block caller):

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    152.7 |      47.3 |  2.7 |  1.7 |  65.3 |        55.9 |
| loop        |    494.4 |      42.9 |  3.8 |  4.2 | 109.1 |       109.3 |
| collections |    864.5 |     558.0 | 29.1 | 13.3 | 225.9 |       201.5 |
| objects     |    353.7 |     177.6 |  1.9 |  1.6 | 283.8 |       229.7 |
| strings     |    152.5 |     117.9 | 32.0 | 15.1 | 159.4 |       146.7 |

## Reading the numbers

- Compiled Quarz is now on a par with Go and Rust on the counting
  loop (its Int locals are unboxed and stay in registers), 2.2–2.8× slower on
  `fib` (one level of the recursion is inlined and the remaining calls
  go through a typed entry that passes `Int`s as machine values and,
  with LLVM, pushes no activation, backtraces being recovered from the
  native stack; what remains is the nil stores for the inlined callee's
  registers and the result's status check), 1.1–2.3× on the collection pipeline
  (its blocks are loops in the caller, the array and hash updates are in
  place and the appends inline, `Int`/`Float` array elements are stored
  unboxed and read inline, numeric equality is inline; what remains is
  the hash table with boxed keys and values), 4× on `objects` (a `Vec2`
  that stays in its function is not allocated, and the one stored in
  the particle is held in place; what remains is the boxed fields and
  the loop over boxed particles) and
  on a par with Go and 2× slower than Rust on `strings` (interpolation
  builds in one buffer, the string natives take their arguments by
  reference, strings of at most 15 bytes live in the value; what
  remains is the builder's growth and the per-call entry into the
  runtime).
- Against Ruby, compiled Quarz is ahead everywhere: 9–11× on `fib`,
  12× on `loop`, 6–7× on `collections`, 33–40× on `objects`, 5× on
  `strings`.
- The VM is 2–4× slower than Ruby's interpreter on calls and loops and
  2–3× faster than it on objects and 2× on strings.

What separates compiled Quarz from Go and Rust now is the value
representation: every value is a 24-byte tagged box, every copy of a
heap value bumps a reference count, every object and every long string
is heap-allocated. Arrays of `Int`/`Float` store their elements
unboxed, strings of at most 15 bytes live in the value, small data
values are held in place in the objects that store them, and copy
propagation removed most of the reference-count traffic on
temporaries; unboxed `Int`/`Float` fields and `Int`-keyed hashes would
be the next steps, and they are changes to
the runtime's data structures rather than to the compiler.
