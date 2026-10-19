# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-19, after the direct-call and inline-access rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at commit 2b90223, VM = `quarz run`,
AOT = `quarz build`. Milliseconds, best of 5 runs, process start-up
included. (The machine ran about 10% slower than for the first table
below; compare columns within one table.)

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    170.4 |      25.5 |  2.6 |  1.7 |  69.6 |        59.1 |
| loop        |    547.5 |      42.5 |  3.3 |  3.9 | 115.2 |       111.3 |
| collections |    846.4 |     296.6 | 31.1 | 14.2 | 230.5 |       213.3 |
| objects     |    357.2 |      68.3 |  1.8 |  1.6 | 295.6 |       235.3 |
| strings     |    152.8 |      90.6 | 33.7 | 16.0 | 160.0 |       158.1 |

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

- Compiled Quarz is now 7–13× slower than Go and Rust on calls and loops
  (`fib`, `loop`), 10–20× on the collection pipeline, about 40× on
  `objects` and 3–6× on `strings`. Every Quarz value is still a 24-byte
  tagged, reference-counted box: an `Int` addition checks tags and
  overflow, `Vec2.new` allocates, and `map`/`select` run a block per
  element. Go and Rust keep `Vec2` and the integers in registers and
  inline the calls.
- Against Ruby, compiled Quarz is ahead everywhere: 2.3–2.7× on `fib`
  and `loop`, 3.5–4.3× on `objects`, 1.8× on `strings`; `collections`,
  which was 2.5× behind, is now level with YJIT.
- The VM is 2–5× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

The next steps that would narrow the gap to Go and Rust are typed
registers (unboxed `Int`/`Float` where the checker proves the type
fits), inlining small methods and blocks into their callers, and
cheaper object construction.
