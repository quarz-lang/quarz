# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-19, after the direct-call, unboxing, inlining, lean-call and allocation rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at the in-place-update commit, VM =
`quarz run`, AOT = `quarz build`. Milliseconds, best of 5 runs, process
start-up included (about 5 ms for a compiled Quarz program, which is
most of `fib` and `loop` now). (The machine ran about 10% slower than
for the first table below; compare columns within one table.)

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    155.8 |      15.1 |  2.8 |  1.8 |  66.4 |        56.7 |
| loop        |    538.4 |       9.0 |  3.3 |  3.5 | 110.3 |       111.4 |
| collections |    642.8 |     191.1 | 27.6 | 13.2 | 224.4 |       202.4 |
| objects     |    188.5 |      28.9 |  2.1 |  1.7 | 284.7 |       228.8 |
| strings     |    148.4 |      82.7 | 32.1 | 15.0 | 153.4 |       150.1 |

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

- Compiled Quarz is now 2.5–3× slower than Go and Rust on the counting
  loop (its Int locals are unboxed and stay in registers), 5–8× on
  `fib` (one level of the recursion is inlined and the remaining calls
  build their activation inline; a third of the time is start-up),
  7–14× on the collection pipeline (its blocks are loops in the caller
  and the array and hash updates are in place; what remains is boxed
  elements and hashing), 14–17× on `objects` (a `Vec2` that stays in
  its function is not allocated, the one stored in the particle is) and
  3–5× on `strings`.
- Against Ruby, compiled Quarz is ahead everywhere: 4× on `fib`, 12×
  on `loop`, 1.1–1.2× on `collections`, 8–10× on `objects`, 1.8× on
  `strings`.
- The VM is 2–5× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

The next steps that would narrow the gap to Go and Rust are unboxed
`Int`/`Float` fields and array elements (a `Vec2` stored in an object
still boxes its floats), a faster start-up (the embedded module is
decoded at every start), and a cheaper object layout.
