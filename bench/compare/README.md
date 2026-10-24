# Quarz against Go, Rust, Crystal, Spinel and Ruby

The programs in `go/`, `rust/`, `crystal/` and `ruby/` do the same work
as `bench/*.qz` and print the same results; [Spinel](https://github.com/matz/spinel)
(a compiler from a Ruby subset to C, with whole-program type inference)
compiles the `ruby/` programs as they are. Besides the programs in
`bench/README.md`, `tak` is the Takeuchi function, `tak(n * 3, n * 2, n)`
with `n` from the command line, which measures calls.

`run.sh` builds everything, checks that every program prints the same
thing, runs each one several times and prints the best wall-clock time.
It needs a release build of Quarz and `go`, `rustc` and `ruby` on the
path; Crystal and Spinel are used when found (`CRYSTAL`, with
`CRYSTAL_LINK_FLAGS` if the compiler needs extra link flags, and
`SPINEL` name them), their columns showing `-` otherwise:

```sh
cargo build --release
RUNS=10 taskset -c 3 bench/compare/run.sh
```

The development container has all of them at the versions below (Go
from go.dev, Crystal from its GitHub release with the glibc shim in
`CRYSTAL_LINK_FLAGS`, Spinel built at its commit). Elsewhere, put them
on the path or name them as above.

## Results (2026-10-25, Quarz at `6f48e28`)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.99.1 (`-O`), Crystal
1.22.0 (`--release`; the release build expects a newer glibc, so a small
shim for `__isoc23_strto*` is linked in), Spinel at `78f436e06`
(2026.09.12+11364) with gcc 12.2, Ruby 4.0.5 with and without `--yjit`,
clang 14.0.6. quarz-vm is `quarz run`, quarz-aot is `quarz build`
(through LLVM). Every program pinned to one core (`taskset -c 3`), all
in one run; milliseconds, best of 20 runs, process start-up included.

| program      | quarz-vm | quarz-aot  |   go | rust | crystal | spinel |  ruby | ruby --yjit |
|--------------|---------:|-----------:|-----:|-----:|--------:|-------:|------:|------------:|
| fib          |     41.0 |        1.5 |  1.4 |  0.9 |     1.8 |  (0.5) |  56.9 |        47.0 |
| loop         |    153.3 |        2.9 |  2.4 |  2.5 |     3.2 |    2.7 |  99.0 |        98.8 |
| collections  |    232.5 |       12.9 | 19.1 | 11.9 |    19.7 |   21.1 | 213.4 |       183.7 |
| objects      |     42.8 |        1.5 |  0.9 |  0.8 |     1.5 |   14.2 | 271.8 |       216.9 |
| strings      |     49.9 |       17.8 | 33.2 | 14.4 |    26.0 |   21.2 | 142.0 |       137.8 |
| dispatch     |     91.1 |        2.0 |  2.5 |  2.3 |     1.7 |    4.8 | 106.4 |        60.8 |
| tak(24,16,8) |    124.6 |        2.3 |  3.5 |  3.1 |     4.1 |    2.4 |  97.0 |        53.3 |
| tak(27,18,9) |    785.1 |        9.3 | 18.3 | 16.7 |    19.5 |   11.4 | 368.6 |        92.8 |

Measured the same way, a program printing one line takes 0.8 ms in
Quarz (0.4 ms of it is creating the process: `/bin/true` takes that
long), against 0.7 in Go, 0.5 in Rust, 1.1 in Crystal and 0.5 in Spinel:
on the shortest programs a few tenths of a millisecond of each
difference is start-up. `quarz run` of the same line takes 7.5 ms, most
of it parsing and checking the prelude.

Quarz allocates with mimalloc below 32 KiB and with the system's malloc
above, and leaves transparent huge pages off (docs/05-execution.md §9):
with `QUARZ_THP=1` the one-line program takes 1.0 ms, and nothing
measured here gets faster.

Since `2f7f576` (2026-10-24), compiled programs became 3–29% faster
and the VM 9–31%:
- Values are 16 bytes (a tag byte and a one-word payload) rather than
  24, an object's header is 16 bytes after its counts rather than 40,
  and a heap frame is one allocation; arrays of objects store a word per
  element, and every empty array is one shared allocation.
- Loops over an `Array[Int]` or `Array[Float]` read the elements as
  machine words, and `map`/`select` building one store words from the
  start (`map` over an array with room for every element); `xs[i]` is read inline; loops over arrays of objects take
  each element's allocation with no tag test. `collections` (16.1 to
  12.9 ms) and `dispatch` (2.8 to 2.0) gained the most.
- The interpreter writes arithmetic results and field reads straight
  into registers (`objects`, `dispatch` and `loop` a quarter to a third
  fewer cycles).
- Typed calls keep their rare paths out of the hot code, which had
  shifted `fib`'s alignment when the values shrank.

## Reading the numbers

- **Go and Rust.** Compiled Quarz is faster than Go on the collection
  pipeline (1.5×), `strings` (1.9×), `dispatch` (1.25×) and `tak`
  (1.5–2.0×), and faster than Rust on `dispatch` (1.2×) and `tak`
  (1.3–1.8×): a call that returns at once is a test inlined at the call
  site, while Go and Rust make every call, and the class tests in front
  of each inlined `area` now cost less than their indirect call. It is
  1.1–1.2× slower than Go on `fib` and the counting loop and 1.7× on
  `objects`, where the particles are heap objects and Go's are plain
  structs. Rust is faster on the rest: 1.1–1.2× on the collection
  pipeline, the loop and `strings`, 1.7× on `fib` and 1.9× on
  `objects`.
- **Crystal.** Quarz is faster on `fib` and the counting loop
  (1.1–1.2×), the collection pipeline (1.5×), `strings` (1.5×) and
  `tak` (1.8–2.1×), on a par on `objects` (Crystal's `Vec2` is a struct
  and its particles plain objects), and 1.2× slower on `dispatch`
  (Crystal compiles the call on a union of the three classes to a switch
  on the type id).
- **Spinel.** Spinel's `fib` is not a call benchmark: it marks `fib`
  pure, and gcc, after inlining the recursion a few levels, merges the
  duplicate calls (`fib(n-3)` appears twice in the expansion), so the
  work is far from exponential (`fib(40)` takes about as long as
  `fib(27)`). On `tak`, which has no duplicate calls, the two are about
  equal on the short run and Quarz is 1.2× faster on the long one; it is faster on
  `collections` (1.6×), `strings` (1.2×), `objects` (9.5×: the
  particle's `Vec2` is held in place, while Spinel allocates a `Vec2`
  object for each `+` and `scale`) and `dispatch` (2.4×), and slower on
  the counting loop (1.1×).
- **Ruby.** Compiled Quarz is ahead everywhere: 31–38× on `fib`, 34× on
  the loop, 14–17× on `collections`, 145–180× on `objects`, 8× on
  `strings`, 30–53× on `dispatch` and 10–42× on `tak` (YJIT does best on
  calls). The VM is faster than Ruby's interpreter on `fib` (1.4×),
  `objects` (6.4×), `strings` (2.8×) and `dispatch` (1.2×), on a par on
  the collection pipeline (1.1× slower), and slower on the loop (1.5×)
  and `tak` (1.3–2.1×).

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
