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

## Results (2026-10-22, Quarz at `2a5c6d4`)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Crystal
1.22.0 (`--release`; the release build expects a newer glibc, so a small
shim for `__isoc23_strto*` is linked in), Spinel at `78f436e06`
(2026.09.12+11364) with gcc 12.2, Ruby 4.0.5 with and without `--yjit`,
clang 14.0.6. quarz-vm is `quarz run`, quarz-aot is `quarz build`
(through LLVM). Every program pinned to one core (`taskset -c 3`), all
in one run; milliseconds, best of 10 runs, process start-up included.

| program      | quarz-vm | quarz-aot  |   go | rust | crystal | spinel |  ruby | ruby --yjit |
|--------------|---------:|-----------:|-----:|-----:|--------:|-------:|------:|------------:|
| fib          |     75.9 |        2.0 |  1.5 |  1.1 |     1.9 |  (0.6) |  57.8 |        47.6 |
| loop         |    243.6 |        3.2 |  2.5 |  2.6 |     3.3 |    2.8 |  99.7 |       100.4 |
| collections  |    326.7 |       16.5 | 20.0 | 12.0 |    21.1 |   21.5 | 217.2 |       196.0 |
| objects      |     64.2 |        2.9 |  1.0 |  0.8 |     1.5 |   14.3 | 277.4 |       220.9 |
| strings      |     63.3 |       19.0 | 33.5 | 14.6 |    26.2 |   21.5 | 145.9 |       141.4 |
| dispatch     |    127.9 |        4.1 |  2.5 |  2.3 |     1.7 |    4.8 | 112.7 |        61.0 |
| tak(24,16,8) |    264.7 |        2.8 |  3.6 |  3.1 |     4.1 |    2.4 |  97.8 |        53.8 |
| tak(27,18,9) |   1721.6 |       11.0 | 18.5 | 16.7 |    19.6 |   11.4 | 372.0 |        94.1 |

Measured the same way, a program printing one line takes 1.0 ms in
Quarz (it decodes its embedded module at start-up), 0.7 in Go, 0.5 in
Rust, 1.1 in Crystal and 0.5 in Spinel, process creation included: on
the shortest programs a few tenths of a millisecond of each difference
is start-up. `quarz run` of the same line takes 9.4 ms, most of it
checking and lowering the prelude.

## Reading the numbers

- **Go and Rust.** Compiled Quarz is 1.2× faster than Go on the
  collection pipeline and 1.8× on `strings` (Rust is 1.4× and 1.3×
  faster than Quarz there), 1.3× slower than Go on the counting loop and
  on `fib`, 1.6× slower on `dispatch` and 3× on `objects`, and 1.5–1.7×
  faster than both on `tak(27,18,9)`: a call that returns at once is a
  test inlined at the call site, while Go and Rust make every call.
  `objects` pays for the particles being heap objects with
  reference-counted fields, walked through boxed array elements, against
  plain structs; `dispatch` for the class tests (and the fallback
  dispatch) in front of each inlined `area`, against an indirect call.
- **Crystal.** Quarz is on a par with it on `fib` and the counting loop,
  faster on the collection pipeline (1.3×), `strings` (1.4×) and `tak`
  (1.5–1.8×), and 1.9–2.4× slower on `objects` (Crystal's `Vec2` is a
  struct and its particles plain objects) and `dispatch` (Crystal
  compiles the call on a union of the three classes to a switch on the
  type id).
- **Spinel.** Spinel's `fib` is not a call benchmark: it marks `fib`
  pure, and gcc, after inlining the recursion a few levels, merges the
  duplicate calls (`fib(n-3)` appears twice in the expansion), so the
  work is far from exponential (`fib(40)` takes about as long as
  `fib(27)`). On `tak`, which has no duplicate calls, the two are about
  equal; Quarz is faster on `collections` (1.3×) and `strings` (1.1×;
  the `Int`-to-`Int` hash and in-place array updates, the builder
  appends without a temporary string), 4.9× faster on `objects` (the
  particle's `Vec2` is held in place, while Spinel allocates a `Vec2`
  object for each `+` and `scale`) and 1.2× on `dispatch`, and slightly
  slower on the counting loop.
- **Ruby.** Compiled Quarz is ahead everywhere: 24–29× on `fib`, 31× on
  the loop, 12–13× on `collections`, 76–96× on `objects`, 7–8× on
  `strings`, 15–27× on `dispatch` and 9–35× on `tak` (YJIT does best on
  calls). The VM is 1.1–2.4× slower than Ruby's interpreter on calls,
  loops, the collection pipeline and dispatch, 2.7–4.6× on `tak`, and
  faster than it on objects (4.3×) and strings (2.3×).

What separates compiled Quarz from Rust now is mostly the value
representation: every value is a 24-byte tagged box, a heap value
copied into a second place bumps a reference count, and every object is
heap-allocated. Arrays of `Int`/`Float`, and hashes from `Int` to `Int`,
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
instructions than it saved. The start-up cost (about 1.5 M instructions
decoding the module and 0.5 M in the dynamic loader, 2.5 M in all) is
the other visible difference on short programs.
