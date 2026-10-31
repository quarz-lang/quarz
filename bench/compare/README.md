# Quarz against Go, Rust, Crystal, Spinel and Ruby

The programs in `go/`, `rust/`, `crystal/` and `ruby/` do the same work
as `bench/*.qz` and print the same results;
[Spinel](https://github.com/matz/spinel) (a compiler from a Ruby subset
to C) compiles the `ruby/` programs as they are. `tak` is
`tak(3n, 2n, n)` with `n` from the command line, and `startup` prints
one line: the start-up every row includes.

`run.sh` builds everything, checks that the outputs agree, and prints
the best wall-clock time of each, then how many runs it took: about
20 s of runs per cell, 3 to 20 (`RUNS=n` fixes it). Each run is a fresh
process, so Ruby's YJIT warms up inside it. It needs a release build of
Quarz and `go`, `rustc` and `ruby` on the path; Crystal and Spinel are
used when found (`CRYSTAL`, `CRYSTAL_LINK_FLAGS`, `SPINEL`). A full run
takes about 10 minutes:

```sh
cargo build --release
taskset -c 3 bench/compare/run.sh
```

## Results (2026-10-31, Quarz at `e48c7b2`)

12th Gen Intel Core i7-1260P, pinned to one performance core on an idle
machine; Go 1.27.2, rustc 1.99.1 (`-O`), Crystal 1.22.0 (`--release`),
Spinel `78f436e06` with gcc 14.2.0, Ruby 4.0.5, clang 19.1.7.
quarz-vm is `quarz run`, quarz-aot is `quarz build`. Milliseconds, best
of the runs in the second table, start-up included. Not comparable with
earlier tables (in git history), whose programs did 6–120× less work.

| program       | quarz-vm | quarz-aot |    go |  rust | crystal | spinel |    ruby | ruby --yjit |
|---------------|---------:|----------:|------:|------:|--------:|-------:|--------:|------------:|
| startup       |      5.5 |       1.0 |   0.8 |   0.6 |     1.2 |    0.5 |    44.3 |        44.4 |
| fib           |   4104.5 |      79.6 |  87.9 |  45.9 |    97.7 |  (0.8) |  1445.4 |       257.7 |
| loop          |   5924.2 |      80.8 |  67.7 |  81.5 |    85.2 |   90.1 |  2459.3 |      2447.8 |
| collections   |   1853.9 |     123.1 | 218.6 | 106.0 |   178.6 |  275.1 |  1476.8 |      1248.1 |
| objects       |   1718.4 |      19.5 |   9.7 |  11.2 |    14.0 |  711.5 | 10894.6 |      8278.3 |
| strings       |    271.3 |     117.6 | 187.4 |  88.0 |   154.0 |  126.8 |   624.6 |       586.7 |
| dispatch      |   4234.2 |      54.2 |  90.0 |  87.1 |    23.1 |   58.6 |  3445.6 |       705.4 |
| tak(30,20,10) |   4891.2 |      60.0 | 114.1 | 105.9 |   105.4 |   64.8 |  2059.7 |       344.0 |

Runs per cell:

| program       | quarz-vm | quarz-aot | go | rust | crystal | spinel | ruby | ruby --yjit |
|---------------|---------:|----------:|---:|-----:|--------:|-------:|-----:|------------:|
| startup       |       20 |        20 | 20 |   20 |      20 |     20 |   20 |          20 |
| fib           |        5 |        20 | 20 |   20 |      20 |     20 |   14 |          20 |
| loop          |        3 |        20 | 20 |   20 |      20 |     20 |    8 |           8 |
| collections   |       11 |        20 | 20 |   20 |      20 |     20 |   13 |          16 |
| objects       |       12 |        20 | 20 |   20 |      20 |     20 |    3 |           3 |
| strings       |       20 |        20 | 20 |   20 |      20 |     20 |   20 |          20 |
| dispatch      |        5 |        20 | 20 |   20 |      20 |     20 |    6 |          20 |
| tak(30,20,10) |        4 |        20 | 20 |   20 |      20 |     20 |   10 |          20 |

## Reading the numbers

- Compiled Quarz is mostly between Go and Rust: faster than both on calls
  (`dispatch`, `tak`: a call that returns at once is inlined as a test,
  and the class tests before an inlined `area` cost less than an
  indirect call), slower on `objects`, where every Quarz object is on
  the heap and Go's and Rust's particles are plain structs.
- Spinel's `fib` (in parentheses) is not a call benchmark: gcc merges
  the duplicate calls of the pure function, so the work is far from
  exponential.
- Compiled Quarz is 5–560× faster than Ruby (3–425× with YJIT). The VM
  is faster than Ruby's interpreter on `objects` and `strings` and
  slower on calls (`fib`, `tak`: 2.4–2.8×).
- What separates compiled Quarz from Rust is mostly the value
  representation: 16-byte tagged values, reference counts, and objects
  always on the heap. A one-word
  representation was tried and set aside (branch `value-8byte`).
