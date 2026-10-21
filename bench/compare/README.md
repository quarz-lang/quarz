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
PATH="$HOME/go-sdk/bin:$PATH" RUNS=10 taskset -c 3 bench/compare/run.sh
```

## Results (2026-10-21, Quarz at `41c014c`)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Crystal
1.22.0 (`--release`; the release build expects a newer glibc, so a small
shim for `__isoc23_strto*` is linked in), Spinel at `78f436e06`
(2026.09.12+11361) with gcc 12.2, Ruby 4.0.5 with and without `--yjit`,
clang 14.0.6. quarz-vm is `quarz run`, quarz-llvm and cranelift are
`quarz build` with each backend (LLVM is the default; Cranelift is for
development). Every program pinned to one core (`taskset -c 3`), all in
one run; milliseconds, best of 10 runs, process start-up included.

| program      | quarz-vm | quarz-llvm | cranelift |   go | rust | crystal | spinel |  ruby | ruby --yjit |
|--------------|---------:|-----------:|----------:|-----:|-----:|--------:|-------:|------:|------------:|
| fib          |    137.2 |        1.9 |       3.4 |  1.4 |  1.0 |     2.0 |  (0.6) |  57.8 |        48.4 |
| loop         |    404.9 |        3.1 |       7.9 |  2.4 |  2.6 |     3.4 |    2.8 | 101.3 |       100.4 |
| collections  |    478.7 |       19.9 |      23.7 | 19.2 | 11.9 |    21.4 |   21.6 | 216.8 |       194.9 |
| objects      |     99.5 |        3.1 |       3.4 |  1.0 |  0.8 |     1.5 |   14.1 | 267.9 |       219.9 |
| strings      |     81.2 |       18.9 |      20.1 | 33.0 | 14.3 |    26.6 |   21.6 | 144.7 |       140.0 |
| dispatch     |    209.0 |        4.7 |       5.9 |  2.5 |  2.3 |     1.8 |    4.8 | 112.2 |        61.4 |
| tak(24,16,8) |    712.0 |        2.8 |      10.7 |  3.6 |  3.1 |     3.8 |    2.5 |  98.0 |        54.3 |
| tak(27,18,9) |   4736.2 |       11.5 |      66.7 | 18.5 | 16.6 |    17.8 |   11.3 | 370.1 |        94.5 |

Measured the same way, a program printing one line takes 1.0 ms in
Quarz (it decodes its embedded module at start-up), 0.7 in Go, 0.6 in
Rust, 1.2 in Crystal and 0.6 in Spinel, process creation included: on
the shortest programs a few tenths of a millisecond of each difference
is start-up.

## Reading the numbers

- **Go and Rust.** Compiled Quarz is on a par with Go on the collection
  pipeline and 1.7× faster than it on `strings` (Rust is 1.7× and 1.3×
  faster than Quarz there), 1.3× slower than Go on the counting loop and
  on `fib`, about 2× slower on `dispatch` and 3–4× on `objects`, and
  1.4–1.6× faster than both on `tak(27,18,9)`: a call that returns at
  once is a test inlined at the call site, while Go and Rust make every
  call. `objects` pays for the particles being heap objects with
  reference-counted fields, walked through boxed array elements, against
  plain structs; `dispatch` for the class tests (and the fallback
  dispatch) in front of each inlined `area`, against an indirect call.
- **Crystal.** Quarz is on a par with it on `fib` and faster on the
  counting loop, the collection pipeline, `strings` (1.4×) and `tak`
  (1.5×), and 2–2.6× slower on `objects` (Crystal's `Vec2` is a struct
  and its particles plain objects) and `dispatch` (Crystal compiles the
  call on a union of the three classes to a switch on the type id).
- **Spinel.** Spinel's `fib` is not a call benchmark: it marks `fib`
  pure, and gcc, after inlining the recursion a few levels, merges the
  duplicate calls (`fib(n-3)` appears twice in the expansion), so the
  work is far from exponential (`fib(40)` takes about as long as
  `fib(27)`). On `tak`, which has no duplicate calls, the two are equal;
  Quarz is faster on `collections` and `strings` (the `Int`-to-`Int`
  hash and in-place array updates, the builder appends without a
  temporary string) and 4.5× faster on `objects` (the particle's `Vec2`
  is held in place, while Spinel allocates a `Vec2` object for each `+`
  and `scale`), on a par on `dispatch`, and slightly slower on the
  counting loop.
- **Ruby.** Compiled Quarz is ahead everywhere: 25–30× on `fib`, 32× on
  the loop, 10–11× on `collections`, 71–86× on `objects`, 7× on
  `strings`, 13–24× on `dispatch` and 8–32× on `tak` (YJIT does best on
  calls). The VM is 2–4× slower than Ruby's interpreter on calls, loops,
  the collection pipeline and dispatch, 13× on `tak`, and faster than it
  on objects (2.7×) and strings (1.8×).

What separates compiled Quarz from Rust now is mostly the value
representation: every value is a 24-byte tagged box, every copy of a
heap value bumps a reference count, and every object is heap-allocated.
Arrays of `Int`/`Float`, and hashes from `Int` to `Int`, store their
elements unboxed, strings of at most 15 bytes live in the value, small
data values are held in place in the objects that store them, a `Float`
field is read and written without a tag test or a release (the checker's
definite initialization guarantees it holds a `Float`), and copy
propagation removed most of the reference-count traffic on temporaries.
A one-word (8-byte) value representation was tried and set aside
(branch `value-8byte`): with arrays already unboxed and data values
flattened there was little copying left to save, while flonum
conversions, kind tests through the heap header and the loss of
in-value short strings cost more instructions than it saved. The
start-up cost (about 1 M instructions decoding the module and 0.5 M in
the dynamic loader, 2 M in all) is the other visible difference on short
programs.
