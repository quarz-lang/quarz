# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-19, after the direct-call, unboxing, inlining, lean-call, allocation, array, hashing and equality rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at the equality commit, VM =
`quarz run`, AOT = `quarz build`. Milliseconds, best of 5 runs, process
start-up included (about 2 ms for a compiled Quarz program). `fib` and
`loop` are short enough that the numbers wander by a few milliseconds
between runs.

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    146.5 |       8.6 |  2.3 |  1.7 |  66.3 |        56.8 |
| loop        |    417.1 |       8.7 |  3.4 |  3.5 | 110.2 |       111.2 |
| collections |    495.4 |      32.6 | 28.6 | 14.1 | 228.5 |       205.5 |
| objects     |    156.0 |      14.9 |  1.8 |  1.4 | 289.0 |       230.9 |
| strings     |     81.0 |      37.2 | 31.7 | 15.1 | 155.2 |       148.4 |

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

- Compiled Quarz is now 2.5× slower than Go and Rust on the counting
  loop (its Int locals are unboxed and stay in registers), 3.5–4.5× on
  `fib` (one level of the recursion is inlined and the remaining calls
  build their activation inline), 1.1–2.5× on the collection pipeline
  (its blocks are loops in the caller, the array and hash updates are in
  place and the appends inline, `Int`/`Float` array elements are stored
  unboxed and read inline, numeric equality is inline; what remains is
  the hash table with boxed keys and values), 9–10× on `objects` (a
  `Vec2` that stays in its function is not allocated, the one stored in
  the particle is: its allocation and release are most of the time) and
  1.2–2.5× on `strings` (interpolation builds in one buffer, the string
  natives take their arguments by reference, strings of at most 15
  bytes live in the value; what remains is the allocation of the longer
  ones and the builder).
- Against Ruby, compiled Quarz is ahead everywhere: 7–8× on `fib`,
  12× on `loop`, 6–7× on `collections`, 16–20× on `objects`, 4× on
  `strings`.
- The VM is 2–4× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

What separates compiled Quarz from Go and Rust now is the value
representation: every value is a 24-byte tagged box, every copy of a
heap value bumps a reference count, every object and every long string
is heap-allocated. Arrays of `Int`/`Float` store their elements
unboxed, strings of at most 15 bytes live in the value, and copy
propagation removed most of the reference-count traffic on
temporaries; typed storage for `Int`/`Float` fields and for
`Int`-keyed hashes would be the next steps, and they are changes to
the runtime's data structures rather than to the compiler.
