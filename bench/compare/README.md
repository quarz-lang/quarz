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
(with and without `--yjit`); Quarz at commit 29b957c, VM = `quarz run`,
AOT = `quarz build`. Milliseconds, best of 5 runs, process start-up
included. (The machine ran about 15% slower than for the first table
below; compare columns within one table.)

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    168.0 |      24.4 |  2.6 |  1.7 |  68.0 |        58.9 |
| loop        |    557.0 |       9.2 |  3.4 |  3.4 | 113.9 |       115.6 |
| collections |    875.3 |     294.7 | 29.3 | 15.0 | 233.9 |       212.4 |
| objects     |    352.1 |      70.0 |  2.2 |  1.6 | 296.6 |       236.7 |
| strings     |    155.5 |      88.4 | 32.7 | 15.6 | 158.4 |       151.2 |

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

- Compiled Quarz is now 2.7× slower than Go and Rust on the counting
  loop (its Int locals are unboxed and stay in registers), 9–14× on
  `fib` (dominated by the call protocol), 10–20× on the collection
  pipeline, 30–45× on `objects` and 3–6× on `strings`. Values other than local numbers are
  still 24-byte tagged, reference-counted boxes: `Vec2.new` allocates,
  and `map`/`select` run a block per element. Go and Rust keep `Vec2`
  in registers and inline the calls.
- Against Ruby, compiled Quarz is ahead everywhere: 2.4–2.8× on `fib`,
  12× on `loop`, 3.4–4.2× on `objects`, 1.7–1.8× on `strings`;
  `collections` (295 ms) is the one program still behind Ruby (234 ms,
  212 ms with YJIT): its blocks run through the generic block protocol.
- The VM is 2–5× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

The next steps that would narrow the gap to Go and Rust are inlining
small methods and blocks into their callers (the call protocol is what
is left in `fib`), passing unboxed numbers through calls (arguments and
results are still boxed at the call boundary), and cheaper object
construction.
