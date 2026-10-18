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
