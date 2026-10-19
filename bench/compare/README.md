# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-19, after the direct-call, unboxing, inlining, lean-call, allocation and array rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at the object-layout commit, VM =
`quarz run`, AOT = `quarz build`. Milliseconds, best of 5 runs, process
start-up included (about 2 ms for a compiled Quarz program). `fib` and
`loop` are short enough that the numbers wander by a few milliseconds
between runs (`perf stat` puts `fib` at 10 ms).

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    158.7 |      14.5 |  2.1 |  1.7 |  64.7 |        55.8 |
| loop        |    532.2 |       9.7 |  4.2 |  4.3 | 106.7 |       107.7 |
| collections |    630.4 |     119.7 | 28.2 | 14.0 | 221.3 |       198.6 |
| objects     |    184.6 |      19.4 |  2.0 |  1.5 | 282.3 |       226.6 |
| strings     |    144.6 |      79.0 | 29.7 | 15.0 | 151.9 |       146.4 |

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

- Compiled Quarz is now 2–2.5× slower than Go and Rust on the counting
  loop (its Int locals are unboxed and stay in registers), 5–7× on
  `fib` (one level of the recursion is inlined and the remaining calls
  build their activation inline), 4–8× on the collection pipeline (its
  blocks are loops in the caller, the array and hash updates are in
  place and array elements are read inline; what remains is boxed
  elements and hashing), 10–13× on `objects` (a `Vec2` that stays in
  its function is not allocated, the one stored in the particle is) and
  3–5× on `strings`.
- Against Ruby, compiled Quarz is ahead everywhere: 4× on `fib`, 11×
  on `loop`, 1.7–1.8× on `collections`, 12–15× on `objects`, 1.9× on
  `strings`.
- The VM is 2–5× slower than Ruby's interpreter on calls and loops and
  on a par for objects and strings.

The next steps that would narrow the gap to Go and Rust are typed
storage for `Int`/`Float` fields and array elements (every value is
still a 24-byte tagged box, which also costs the reference-count
checks on every copy), and hashing and string building in `strings`
and `collections`.
