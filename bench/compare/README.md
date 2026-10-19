# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-19, after the direct-call, unboxing, inlining and lean-call rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at the lean-call commit, VM =
`quarz run`, AOT = `quarz build`. Milliseconds, best of 5 runs, process
start-up included. (The machine ran about 10% slower than for the first
table below; compare columns within one table.)

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    152.3 |       8.9 |  2.2 |  1.8 |  64.6 |        54.7 |
| loop        |    533.6 |      10.0 |  3.2 |  5.0 | 104.3 |       104.3 |
| collections |    626.5 |     177.9 | 26.5 | 13.6 | 216.2 |       199.2 |
| objects     |    241.5 |      39.7 |  1.9 |  1.7 | 274.3 |       222.1 |
| strings     |    145.5 |      83.2 | 30.2 | 15.5 | 151.2 |       144.9 |

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

- Compiled Quarz is now 2–3× slower than Go and Rust on the counting
  loop (its Int locals are unboxed and stay in registers), 4–5× on
  `fib` (one level of the recursion is inlined and the remaining calls
  build their activation inline), 7–13× on the collection pipeline (its blocks are now
  loops in the caller; what remains is the persistent array and hash
  updates), 20–30× on `objects` (every `Vec2` is still heap-allocated
  and reference-counted, where Go and Rust keep it in registers) and
  3–5× on `strings`.
- Against Ruby, compiled Quarz is ahead everywhere: 6–7× on `fib`,
  10× on `loop`, 1.1–1.2× on `collections`, 5.6–6.9× on `objects`,
  1.7–1.8× on `strings`.
- The VM is 2–5× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

The next steps that would narrow the gap to Go and Rust are escape
analysis or inline allocation for short-lived objects such as `Vec2`,
and in-place updates of persistent collections in more shapes than
`xs = xs.push(v)`.
