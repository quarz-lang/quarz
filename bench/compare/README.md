# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-19)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at commit 93874ea, VM = `quarz run`,
AOT = `quarz build`. Milliseconds, best of 5 runs, process start-up
included.

| program     | quarz-vm | quarz-aot |   go | rust | ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|-----:|------------:|
| fib         |    152.7 |      47.3 |  2.7 |  1.7 | 65.3 |        55.9 |
| loop        |    494.4 |      42.9 |  3.8 |  4.2 | 109.1 |      109.3 |
| collections |    864.5 |     558.0 | 29.1 | 13.3 | 225.9 |      201.5 |
| objects     |    353.7 |     177.6 |  1.9 |  1.6 | 283.8 |      229.7 |
| strings     |    152.5 |     117.9 | 32.0 | 15.1 | 159.4 |      146.7 |

## Reading the numbers

- Compiled Quarz is 10–20× slower than Go and Rust on calls and loops
  (`fib`, `loop`), 20–40× on the collection pipeline and about 100× on
  `objects`. Every Quarz value is a 24-byte tagged, reference-counted
  box: an `Int` addition checks tags and overflow, `Vec2.new` allocates,
  and `map`/`select` call a block per element through the runtime. Go and
  Rust keep `Vec2` and the integers in registers and inline the calls.
- Against Ruby, compiled Quarz is ahead on `fib`, `loop` (2.5×),
  `objects` and `strings`, and behind on `collections` (2.5×): the
  persistent arrays update in place when uniquely referenced, but the
  blocks of `map`/`select`/`reduce` go through a generic call path that
  Ruby's specialised instructions avoid.
- The VM is 2–5× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

The next steps that would narrow the gap to Go and Rust are typed
registers (unboxed `Int`/`Float` where the checker proves the type
fits), direct calls between compiled methods, and running the blocks of
`map`/`select` inline instead of through `call_block`.
