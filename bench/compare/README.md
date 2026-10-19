# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-19, after the direct-call, unboxing and inlining rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at the inlining commit, VM =
`quarz run`, AOT = `quarz build`. Milliseconds, best of 5 runs, process
start-up included. (The machine ran about 15% slower than for the first
table below; compare columns within one table.)

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    156.0 |      15.2 |  2.8 |  1.8 |  66.9 |        56.1 |
| loop        |    551.9 |      14.3 |  3.1 |  4.0 | 110.5 |       110.0 |
| collections |    647.7 |     186.9 | 32.2 | 14.6 | 226.6 |       206.8 |
| objects     |    255.3 |      42.1 |  2.1 |  1.4 | 288.5 |       235.1 |
| strings     |    155.9 |      85.4 | 32.1 | 15.9 | 157.2 |       149.7 |

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

- Compiled Quarz is now 3.5–4.5× slower than Go and Rust on the
  counting loop (its Int locals are unboxed and stay in registers),
  5–8× on `fib` (one level of the recursion is inlined; the rest is the
  call protocol), 6–13× on the collection pipeline (its blocks are now
  loops in the caller; what remains is the persistent array and hash
  updates), 20–30× on `objects` (every `Vec2` is still heap-allocated
  and reference-counted, where Go and Rust keep it in registers) and
  3–5× on `strings`.
- Against Ruby, compiled Quarz is ahead everywhere: 3.7–4.4× on `fib`,
  8× on `loop`, 1.1–1.2× on `collections`, 5.6–6.9× on `objects`,
  1.8× on `strings`.
- The VM is 2–5× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

The next steps that would narrow the gap to Go and Rust are a lighter
activation for the calls that remain (building it inline instead of in
the runtime, and passing unboxed numbers), escape analysis or inline
allocation for short-lived objects such as `Vec2`, and in-place updates
of persistent collections in more shapes than `xs = xs.push(v)`.
