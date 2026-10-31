# Quarz against Go, Rust, Crystal, Spinel and Ruby

The programs in `go/`, `rust/`, `crystal/` and `ruby/` do the same work
as `bench/*.qz` and print the same results; [Spinel](https://github.com/matz/spinel)
(a compiler from a Ruby subset to C, with whole-program type inference)
compiles the `ruby/` programs as they are. Besides the programs in
`bench/README.md`, `tak` is the Takeuchi function, `tak(n * 3, n * 2, n)`
with `n` from the command line, which measures calls, and `startup`
prints one line: every row includes the process's start-up, which that
row shows on its own. The sizes are chosen so that a compiled Quarz run
takes tens of milliseconds or more (`objects` takes 20, the others
50–125), the interpreters up to seconds.

`run.sh` builds everything, checks that every program prints the same
thing, runs each one several times and prints the best wall-clock time,
then a second table of how many runs each took: after a first run of
`t` ms, `clamp(round(20000 / t), 3, 20)` in all, so about 20 s per cell
(at least 3 runs, at most 20); `RUNS=n` makes it `n` everywhere. A full
run takes about 10 minutes. Each run is a fresh process, as a
command-line user gets: Ruby's `--yjit` warms up inside the measured run
(at these sizes a few percent at most), and Quarz has no warm-up of its
own.
It needs a release build of Quarz and `go`, `rustc` and `ruby` on the
path; Crystal and Spinel are used when found (`CRYSTAL`, with
`CRYSTAL_LINK_FLAGS` if the compiler needs extra link flags, and
`SPINEL` name them), their columns showing `-` otherwise:

```sh
cargo build --release
taskset -c 3 bench/compare/run.sh
```

The development container has all of them at the versions below (Go
from go.dev, Crystal from its GitHub release, Spinel built at its
commit). Elsewhere, put them
on the path or name them as above.

## Results (2026-10-31, Quarz at `e48c7b2`)

These sizes are new: the numbers are not comparable with the earlier
tables (in git history), whose shortest programs (1–3 ms) measured
start-up more than the program.

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.99.1 (`-O`), Crystal
1.22.0 (`--release`), Spinel at `78f436e06` (2026.09.12+11364) with gcc
14.2.0, Ruby 4.0.5 with and without `--yjit`, clang 19.1.7. quarz-vm is
`quarz run`, quarz-aot is `quarz build` (through LLVM). Every program
pinned to one performance core (`taskset -c 3`), all in one run on an
otherwise idle machine; milliseconds, the best of the runs below,
process start-up included.

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

The start-up row is in every other row: 1.0 ms of compiled Quarz's
20–125 (0.4 ms of it is creating the process: `/bin/true` takes that
long), 5.5 ms of `quarz run`'s (most of it parsing and checking the
prelude) and 44 ms of Ruby's.

Quarz allocates with mimalloc below 32 KiB and with the system's malloc
above, and leaves transparent huge pages off (docs/05-execution.md §9).

## Reading the numbers

- **Go and Rust.** Compiled Quarz is faster than Go on `fib` (1.1×), the
  collection pipeline (1.8×), `strings` (1.6×), `dispatch` (1.7×) and
  `tak` (1.9×), and faster than Rust on `dispatch` (1.6×) and `tak`
  (1.8×), on a par with it on the loop: a call that returns at once is
  a test inlined at the call site, while Go and Rust make every call,
  and the class tests in front of each inlined `area` cost less than
  their indirect call. It is 1.2× slower than Go on the loop and 2.0× on
  `objects`, where the particles are heap objects and Go's are plain
  structs. Rust is faster on the rest: 1.2× on the collection pipeline,
  1.3× on `strings`, 1.7× on `fib` and `objects`.
- **Crystal.** Quarz is faster on `fib` (1.2×), the loop (1.05×), the
  collection pipeline (1.5×), `strings` (1.3×) and `tak` (1.8×), and
  slower on `objects` (1.4×: Crystal's `Vec2` is a struct) and
  `dispatch` (2.3×: Crystal compiles the call on a union of the three
  classes to a switch on the type id).
- **Spinel.** Spinel's `fib` is not a call benchmark: it marks `fib`
  pure, and gcc, after inlining the recursion a few levels, merges the
  duplicate calls (`fib(n-3)` appears twice in the expansion), so the
  work is far from exponential. Elsewhere Quarz is faster: 1.1× on the
  loop, `strings`, `dispatch` and `tak`, 2.2× on `collections`, and 36×
  on `objects` (the particle's `Vec2` is held in place, while Spinel
  allocates a `Vec2` object for each `+` and `scale`).
- **Ruby.** Compiled Quarz is ahead everywhere: 18× on `fib` (3.2× with
  YJIT), 30× on the loop, 10–12× on `collections`, 425–560× on
  `objects`, 5× on `strings`, 13–64× on `dispatch` and 6–34× on `tak`
  (YJIT does best on calls). The VM is faster than Ruby's interpreter on
  `objects` (6.3×) and `strings` (2.3×), and slower on the collection
  pipeline (1.3×), `dispatch` (1.2×), the loop (2.4×), `tak` (2.4×) and
  `fib` (2.8×). With start-up a smaller share than in the earlier
  tables, the VM's per-call cost shows: its `fib` was 1.4× faster than
  Ruby's at `fib(27)`, where Ruby's 44 ms start-up was most of its time.

What separates compiled Quarz from Rust now is mostly the value
representation: every value is a 16-byte tagged box, a heap value
copied into a second place bumps a reference count, and every object is
heap-allocated (sized to its fields). Arrays of `Int`/`Float`, and hashes from `Int` to `Int`,
store their elements unboxed, arrays of objects store a word per
element, strings of at most 14 bytes live in the value, small data
values are held in place in the objects that store them (and not
allocated at all when they do not escape), a `Float` field is read and
written without a tag test or a release (the checker's definite
initialization guarantees it holds a `Float`), and most reference-count
traffic is gone: copy propagation removes the copies of temporaries,
and a value read for the last time moves rather than being copied (a
collection passed to a method and returned updated stays unique, and is
updated in place). A one-word (8-byte) value representation was tried
and set aside (branch `value-8byte`): with arrays already unboxed and
data values flattened there was little copying left to save, while
flonum conversions, kind tests through the heap header and the loss of
in-value short strings cost more instructions than it saved. The
start-up cost (under 1 M instructions in all, most of it building the
class and method tables) is the other visible difference on short
programs.
