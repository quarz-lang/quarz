# Benchmarks

Small programs used to profile the interpreter. Run them with a release build:

```sh
cargo build --release
for b in fib loop collections objects strings; do
  /usr/bin/time -f "$b %es" ./target/release/quarz run bench/$b.qz
done
```

| Program | What it measures |
| --- | --- |
| `fib.qz` | method calls and integer arithmetic (`fib(27)`) |
| `loop.qz` | `while` loops, local variables and `+=` (3 M iterations) |
| `collections.qz` | `Array`/`Hash` building, `map`/`select`/`reduce` with blocks |
| `objects.qz` | object construction, field access and dynamic dispatch |
| `strings.qz` | string concatenation, interpolation and splitting |
| `dispatch.qz` | calls to a method three classes override (900k dispatched calls) |
| `toplevel_calls.qz` | calls of a top-level `def` from 4 tasks (12M calls), with `QUARZ_THREADS` workers |
| `tak.qz` | recursive calls: the Takeuchi function `tak(3n, 2n, n)`, `n` from the command line (`quarz run bench/tak.qz 8`) |

`compare/` holds the same programs in Go, Rust, Crystal and Ruby (which Spinel also compiles) and a script that times all of them side by side; see `compare/README.md` for the latest numbers.
