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

## Results (2026-10-23, Quarz at `fb58823`)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.99.1 (`-O`), Crystal
1.22.0 (`--release`; the release build expects a newer glibc, so a small
shim for `__isoc23_strto*` is linked in), Spinel at `78f436e06`
(2026.09.12+11364) with gcc 12.2, Ruby 4.0.5 with and without `--yjit`,
clang 14.0.6. quarz-vm is `quarz run`, quarz-aot is `quarz build`
(through LLVM). Every program pinned to one core (`taskset -c 3`), all
in one run; milliseconds, best of 20 runs, process start-up included.

| program      | quarz-vm | quarz-aot  |   go | rust | crystal | spinel |  ruby | ruby --yjit |
|--------------|---------:|-----------:|-----:|-----:|--------:|-------:|------:|------------:|
| fib          |     47.4 |        2.1 |  1.5 |  0.9 |     1.8 |  (0.6) |  57.1 |        46.9 |
| loop         |    221.0 |        3.3 |  2.4 |  2.6 |     3.3 |    2.7 | 100.4 |       100.7 |
| collections  |    286.6 |       16.3 | 19.3 | 12.1 |    19.8 |   21.3 | 217.0 |       185.9 |
| objects      |     57.4 |        2.7 |  0.9 |  0.8 |     1.5 |   14.4 | 276.1 |       219.7 |
| strings      |     57.2 |       20.3 | 33.4 | 14.7 |    26.4 |   21.6 | 144.4 |       139.3 |
| dispatch     |    119.0 |        3.5 |  2.5 |  2.3 |     1.7 |    5.0 | 107.8 |        60.6 |
| tak(24,16,8) |    143.7 |        3.0 |  3.6 |  3.2 |     4.2 |    2.4 |  98.1 |        53.9 |
| tak(27,18,9) |    920.7 |       11.3 | 18.7 | 17.2 |    19.8 |   11.4 | 375.1 |        93.8 |

Measured the same way, a program printing one line takes 1.2 ms in
Quarz (it decodes its embedded module at start-up), 0.7 in Go, 0.6 in
Rust, 1.2 in Crystal and 0.5 in Spinel, process creation included: on
the shortest programs a few tenths of a millisecond of each difference
is start-up. `quarz run` of the same line takes 6.8 ms, most of it
parsing and checking the prelude.

Quarz allocates with mimalloc below 32 KiB and with the system's malloc
above, and leaves transparent huge pages off (docs/05-execution.md §9):
with `QUARZ_THP=1` the one-line program takes 1.7 ms, and nothing
measured here gets faster.

Since `2a5c6d4`, the VM became 1.1–1.9× faster (calls the most: `tak`
1.8–1.9×, `fib` 1.6×). Compiled code is about the same on these short
programs, where start-up weighs (and `tak` moves by a few tenths of a
millisecond with code layout alone); on the benchmarks lengthened
tenfold, compiled `objects` takes 23% fewer cycles and `dispatch` 27%
(objects sized by their fields, their addresses kept unboxed, array
elements borrowed).

## Reading the numbers

- **Go and Rust.** Compiled Quarz is 1.2× faster than Go on the
  collection pipeline and 1.6× on `strings` (Rust is 1.3× and 1.4×
  faster than Quarz there), 1.4× slower than Go on the counting loop,
  `fib` and `dispatch` and 3× on `objects`, and 1.5–1.7× faster than
  both on `tak(27,18,9)`: a call that returns at once is a test inlined
  at the call site, while Go and Rust make every call. `objects` pays
  for the particles being heap objects whose fields are 24-byte boxed
  values, against plain structs; `dispatch` for the class tests (and the
  fallback dispatch) in front of each inlined `area`, against an
  indirect call.
- **Crystal.** Quarz is on a par with it on the counting loop, slightly
  slower on `fib`, faster on the collection pipeline (1.2×), `strings`
  (1.3×) and `tak` (1.4–1.8×), and 1.8–2.1× slower on `objects`
  (Crystal's `Vec2` is a struct and its particles plain objects) and
  `dispatch` (Crystal compiles the call on a union of the three classes
  to a switch on the type id).
- **Spinel.** Spinel's `fib` is not a call benchmark: it marks `fib`
  pure, and gcc, after inlining the recursion a few levels, merges the
  duplicate calls (`fib(n-3)` appears twice in the expansion), so the
  work is far from exponential (`fib(40)` takes about as long as
  `fib(27)`). On `tak`, which has no duplicate calls, the two are about
  equal; Quarz is faster on `collections` (1.3×) and `strings` (1.1×;
  the `Int`-to-`Int` hash and in-place array updates, the builder
  appends without a temporary string), 5.3× faster on `objects` (the
  particle's `Vec2` is held in place, while Spinel allocates a `Vec2`
  object for each `+` and `scale`) and 1.4× on `dispatch`, and slower on
  the counting loop (1.2×).
- **Ruby.** Compiled Quarz is ahead everywhere: 22–27× on `fib`, 30× on
  the loop, 11–13× on `collections`, 81–102× on `objects`, 7× on
  `strings`, 17–31× on `dispatch` and 8–33× on `tak` (YJIT does best on
  calls). The VM is now faster than Ruby's interpreter on `fib` (1.2×),
  objects (4.8×) and strings (2.5×), and slower on the loop (2.2×), the
  collection pipeline (1.3×), dispatch (1.1×) and `tak` (1.5–2.5×).

What separates compiled Quarz from Rust now is mostly the value
representation: every value is a 24-byte tagged box, a heap value
copied into a second place bumps a reference count, and every object is
heap-allocated (sized to its fields). Arrays of `Int`/`Float`, and hashes from `Int` to `Int`,
store their elements unboxed, strings of at most 15 bytes live in the
value, small data values are held in place in the objects that store
them (and not allocated at all when they do not escape), a `Float`
field is read and written without a tag test or a release (the
checker's definite initialization guarantees it holds a `Float`), and
most reference-count traffic is gone: copy propagation removes the
copies of temporaries, and a value read for the last time moves rather
than being copied (a collection passed to a method and returned
updated stays unique, and is updated in place). A one-word (8-byte)
value representation was tried and set aside (branch `value-8byte`):
with arrays already unboxed and data values flattened there was little
copying left to save, while flonum conversions, kind tests through the
heap header and the loss of in-value short strings cost more
instructions than it saved. The start-up cost (about 2.2 M instructions in all, most of
it decoding the module) is the other visible difference on short
programs.
