# Quarz against Go, Rust and Ruby

The programs in `go/`, `rust/` and `ruby/` do the same work as `bench/*.qz`
and print the same results. `run.sh` builds everything, runs each program
several times and prints the best wall-clock time. It needs a release
build of Quarz, `go`, `rustc` and `ruby` on the path:

```sh
cargo build --release
PATH="$HOME/go-sdk/bin:$PATH" RUNS=5 bench/compare/run.sh
```

## Results (2026-10-20, with the LLVM backend, at `f88282e`)

Same machine and versions as below, every program pinned to one core
(`taskset -c 3`); `quarz build` compiling through `clang -O2` (the
default backend). Milliseconds, best of 10 runs. The Cranelift backend
(`--backend cranelift`, for development) gives fib 3.4, loop 8.1,
collections 23.8, objects 3.4, strings 19.7 in the run of the next
section. Measured the same way, a program printing one line takes 1.0
ms in Quarz (it decodes its embedded module at start-up), 0.7 in Go and
0.6 in Rust, process creation included: 0.3–0.5 ms of each difference
on the smaller programs is start-up.

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    134.4 |       1.9 |  1.4 |  1.0 |  55.8 |        46.7 |
| loop        |    400.6 |       3.1 |  2.4 |  2.6 |  97.1 |        97.4 |
| collections |    470.7 |      19.5 | 19.1 | 11.7 | 211.6 |       191.0 |
| objects     |     99.5 |       3.1 |  0.9 |  0.8 | 273.5 |       218.9 |
| strings     |     80.8 |      19.1 | 33.4 | 14.3 | 142.9 |       138.8 |

## Spinel (2026-10-20)

[Spinel](https://github.com/matz/spinel) compiles a Ruby subset to C
(whole-program type inference, `cc -O2`). The `ruby/*.rb` programs
compile as they are; Spinel at `78f436e06` (2026.09.12+11361), gcc
12.2. Same machine, one core, milliseconds, best of 10 runs, Quarz at
`f88282e`; the `dispatch` row is `bench/dispatch.qz` and a Ruby
transcription of it (three subclasses overriding `area`, 900k calls),
the `tak` rows the Takeuchi function with `n * 3, n * 2, n` from `ARGV`.

| program     | quarz-llvm | quarz-cranelift | spinel |
|-------------|-----------:|----------------:|-------:|
| fib         |        1.9 |             3.4 |  (0.5) |
| loop        |        3.1 |             8.1 |    2.8 |
| collections |       19.6 |            23.8 |   21.4 |
| objects     |        3.2 |             3.4 |   14.4 |
| strings     |       19.1 |            19.7 |   21.3 |
| dispatch    |        4.7 |             5.9 |    4.8 |
| tak(24,16,8)|        2.7 |            10.7 |    2.4 |
| tak(27,18,9)|       11.6 |            66.8 |   11.4 |

At the first comparison (same day, before the rounds below) the LLVM
column read fib 3.7, loop 4.6, collections 33.3, objects 6.7, strings
32.4, dispatch 7.8, `tak(27,18,9)` 52.5. What closed the gap, in order:

- Typed calls stopped writing their live registers back before the call,
  and the registers of inlined callees became nil lazily (only where
  something reads the home).
- The inliner takes methods of up to 40 instructions, so `tak` is
  inlined into itself once (`tak(27,18,9)` 55 → 34 ms in one run).
- A typed function that can return without needing a frame gets a
  separate entry for that part, which LLVM inlines into its callers: a
  call that returns at once is a comparison and a branch at the call
  site. Typed entries return only their value, any other outcome being
  left in the runtime (`tak(27,18,9)`: 443 → 164 M instructions).
- The build drops what a program cannot run, so start-up went from 1.3
  to 0.7 ms.
- A hash whose keys and values are all `Int` is stored unboxed (the
  200 000 `put`s of `collections`: 14.6 → 9.5 ms).
- `b << "text #{x}"` on a `String::Builder` appends straight into the
  builder (the building loop of `strings`: 14.7 → 6.6 ms; Spinel 5.1).
- Array length, element reads and appends write registers back only on
  their runtime paths, and `xs.map(&:name)` (with `select`, `count`, ...)
  is lowered as a loop calling the method directly.

Reading the table:

- Spinel's `fib` number is not a call benchmark: it marks `fib` pure, and
  gcc, after inlining the recursion a few levels, merges the duplicate
  calls (`fib(n-3)` appears twice in the expansion), so the work is far
  from exponential: `fib(40)` takes about as long as `fib(27)`. `tak` has
  no duplicate calls to merge and measures the call protocol: Spinel's is
  a C call with three `int64` parameters that gcc inlines several levels
  deep; Quarz's calls that return at once are a test at the call site,
  the others go through a typed entry with a stack check and a frame for
  the register file.
- `loop` (and `tak(24,16,8)`) differ by about the start-up time: the
  loops themselves run at the same speed.
- `collections`, `strings` and `dispatch` are now slightly faster in
  Quarz: the `Int`-to-`Int` hash and the in-place array updates, the
  builder appends without a temporary string, and the class tests that
  devirtualization puts before inlined calls.
- `objects` is 4–5× faster in Quarz: the particle's `Vec2` is held in
  place (no allocation per step), while Spinel allocates a `Vec2` object
  for each `+` and `scale` and collects them.

## Results (2026-10-19, Cranelift, after the direct-call, unboxing, inlining, lean-call, allocation, array, hashing and equality rounds)

12th Gen Intel Core i7-1260P; Go 1.27.2, rustc 1.98.1 (`-O`), Ruby 4.0.5
(with and without `--yjit`); Quarz at the equality commit, VM =
`quarz run`, AOT = `quarz build`. Milliseconds, best of 5 runs, process
start-up included (about 2 ms for a compiled Quarz program). `fib` and
`loop` are short enough that the numbers wander by a few milliseconds
between runs.

| program     | quarz-vm | quarz-aot |   go | rust |  ruby | ruby --yjit |
|-------------|---------:|----------:|-----:|-----:|------:|------------:|
| fib         |    137.1 |       6.1 |  2.2 |  1.8 |  68.2 |        56.1 |
| loop        |    402.8 |       9.0 |  3.9 |  3.4 | 107.0 |       109.3 |
| collections |    483.1 |      31.8 | 29.4 | 13.0 | 223.7 |       203.1 |
| objects     |     96.6 |       7.4 |  1.9 |  1.6 | 284.5 |       226.8 |
| strings     |     77.4 |      29.1 | 33.1 | 15.4 | 154.7 |       148.9 |

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

- Against Go and Rust (first table), compiled Quarz is on a par with Go
  on the collection pipeline and 1.7× faster than it on `strings`
  (Rust: 1.7× and 1.3× faster than Quarz), 1.2–1.3× slower on the
  counting loop and 1.4–1.9× on `fib` (0.3–0.5 ms of which is the
  longer start-up), and 3.4–3.9× slower on `objects`, where the particles are heap
  objects with reference-counted fields walked through boxed array
  elements, against plain structs.
- Against Ruby, compiled Quarz is ahead everywhere: 25–29× on `fib`,
  31× on `loop`, 10–11× on `collections`, 70–88× on `objects`, 7× on
  `strings`.
- The VM is 2–4× slower than Ruby's interpreter on calls, loops and the
  collection pipeline, and 2–3× faster than it on objects and 2× on
  strings.

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
in-value short strings cost 1.1–1.9× more instructions. The start-up
cost (about 1 M instructions decoding the module and 0.5 M in the
dynamic loader, 2 M in all) is the other visible difference on short
programs.
