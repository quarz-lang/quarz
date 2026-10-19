# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-19, after the direct-call, inline-access and unboxing rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at commit abbeb13, VM = `quarz run`,
AOT = `quarz build`. Milliseconds, best of 5 runs, process start-up
included. (The machine ran about 10% slower than for the first table
below; compare columns within one table.)

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    165.0 |      23.2 |  2.8 |  1.7 |  64.6 |        56.9 |
| loop        |    512.5 |      15.1 |  3.3 |  3.4 | 107.5 |       108.7 |
| collections |    788.0 |     278.4 | 27.1 | 14.5 | 219.3 |       202.4 |
| objects     |    334.2 |      68.6 |  2.2 |  1.6 | 280.1 |       227.8 |
| strings     |    142.9 |      85.2 | 31.9 | 15.7 | 151.2 |       151.6 |

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

- Compiled Quarz is now 4.5× slower than Go and Rust on the counting
  loop (its Int locals are unboxed), 8–14× on `fib` (dominated by the
  call protocol), 10–20× on the collection pipeline, 30–40× on
  `objects` and 3–5× on `strings`. Values other than local numbers are
  still 24-byte tagged, reference-counted boxes: `Vec2.new` allocates,
  and `map`/`select` run a block per element. Go and Rust keep `Vec2`
  in registers and inline the calls.
- Against Ruby, compiled Quarz is ahead everywhere: 2.8× on `fib`, 7×
  on `loop`, 3.3–4× on `objects`, 1.8× on `strings`; `collections`
  (278 ms) is the one program still behind Ruby (219 ms, 202 ms with
  YJIT): its blocks run through the generic block protocol.
- The VM is 2–5× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

The next steps that would narrow the gap to Go and Rust are inlining
small methods and blocks into their callers (the call protocol is what
is left in `fib`), unboxed numbers across calls (parameters and fields
of static type `Int`/`Float`), and cheaper object construction.
