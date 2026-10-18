# Execution Model: Interpreter and AOT Compiler

日本語版: [05-execution.ja.md](05-execution.ja.md)

Quarz shares one front end and one runtime across two back ends (a bytecode VM and machine code). During development, `quarz run` gives fast startup and a REPL; for production, `quarz build` gives execution speed; and **the observable behavior of the two is identical**.

```
                    ┌────────────┐   ┌──────────────┐   ┌───────────────┐
  foo.qz ─────────▶ │ Lexing and │─▶ │ Name resol.  │─▶ │  QIR (typed   │
  (+ .qzi deps)     │  parsing   │   │ & type check │   │   IR)         │
                    └────────────┘   └──────────────┘   └───────┬───────┘
                                                                 │
                       ┌─────────────────────────────────────────┼─────────────────────┐
                       │ quarz run / repl                        │ quarz build          │
                       ▼                                         ▼                      │
               ┌───────────────┐                     ┌────────────────────┐             │
               │ Register VM   │                     │ Optimization       │             │
               │ bytecode      │                     │ (devirtualization, │             │
               │ (lazily built)│                     │ inlining, RC       │             │
               └───────┬───────┘                     │ elision, unboxing) │             │
                       │                             └─────────┬──────────┘             │
                       │                                       ▼                        │
                       │                             ┌────────────────────┐             │
                       │                             │ LLVM IR → machine  │             │
                       │                             │ code               │             │
                       │                             └─────────┬──────────┘             │
                       ▼                                       ▼                        │
               ┌──────────────────────────────────────────────────────────┐             │
               │  libquarz runtime (reference counting, scheduler,        │ ◀───────────┘
               │  persistent collections, strings, bignums, IO,           │
               │  channels, regular expressions)                          │
               └──────────────────────────────────────────────────────────┘
```

## 1. Commands

| Command | Behavior |
|---|---|
| `quarz run app.qz [args]` | Type-check and run as bytecode. Type-check results for dependencies are cached (`.quarz/cache`) |
| `quarz repl` | REPL. Each input is type-checked, and definitions can be added (redefinition is not allowed; use a new name instead) |
| `quarz check app.qz` | Type-check only |
| `quarz build app.qz -o app` | Produce a native executable. `--release` optimizes, `--dev` compiles fast (no optimization) |
| `quarz test` | Run `test/**/*_test.qz` |
| `quarz fmt` | Format |
| `quarz pkg add json` | Package management. The manifest is `Quarz.toml` |

## 2. Compilation Units and Separate Compilation

- One file = one compilation unit. From each unit's type-check results, an **interface file** `.qzi` is generated (class and method signatures, field layouts, constant types, the list of `extension`s, and the QIR of small methods that are inlining candidates).
- Dependent units read only the `.qzi`. This is why parameter types are mandatory: a change to a body does not trigger recompilation of other units (as long as the signature is unchanged).
- In its final stage, `quarz build` gathers the QIR of the whole program and performs devirtualization via class hierarchy analysis (CHA) and cross-module inlining. Since no classes are created at runtime, CHA is complete.
- The standard library is distributed ahead of time as `.qzi` + native code (`libquarz-std`), so it runs as machine code from the start even under `quarz run`.

## 3. QIR

QIR is a typed intermediate representation in SSA form. The Ruby-like syntax is simplified at the point of lowering to QIR.

- All method calls are already resolved (`call Account#deposit`, `vcall Shape#area`, `icall Comparable#<=>`).
- Non-escaping blocks are inlined or become static local function calls. `break`/`next`/`return` are converted into jumps.
- `case/in` becomes a decision tree.
- Values of union types are `(tag, payload)`. Narrowing is a check on `tag`.
- `Int` arithmetic expands to "63-bit add with overflow check → bignum routine on overflow".
- Reference-count `inc`/`dec` are inserted explicitly and elided by later optimization passes.
- `safepoint` instructions are inserted at loop back-edges and method entries.

The basis for the interpreter and compiler agreeing on semantics is that both take the same QIR as input and call the same runtime functions. The only difference allowed from QIR onward is performance, and CI runs the same test suite in both modes as differential testing.

## 4. Interpreter

- **Register VM.** Each SSA value in QIR corresponds to a register, and since types are statically known, `Int`/`Float`/`Bool` are placed in registers without boxing.
- Bytecode is generated from QIR the first time a method is called (lazy compilation). Startup does only parsing and type checking, and with a warm cache the program starts running within tens of milliseconds.
- Dispatch is direct threading. Frequent operations like `Int#+` and `Array#[]` have dedicated instructions.
- Because type information is available, there are none of the inline caches or guards that a dynamic-language interpreter needs. The target is Lua/LuaJIT-interpreter-class speed, roughly 3–10× Ruby (without YJIT).
- A baseline JIT (generating machine code from QIR on the fly) could be added in the future, but since the premise is "AOT for production," its priority is low.

## 5. Memory Management

We adopt **reference counting (RC) + in-place updates via uniqueness + cycle collection restricted to mutable objects**.

### Why Reference Counting

1. **In-place updates of immutable values**: an immutable value with a reference count of 1 can perform a "return a new value" operation destructively in place (Perceus, from Lean 4 / Koka). Quarz's "immutable by default yet fast" depends on this.
2. **Compatibility with AOT**: a tracing GC needs stack maps for native code (LLVM statepoints, etc.) or conservative scanning, which is a hard part of the implementation. RC needs neither, and the boundary with C FFI is simple.
3. **No pause times**: when the scheduler runs many tasks, a GC stop-the-world hurts responsiveness.
4. **Deterministic release**: combined with `ensure`, resources like file handles can be released predictably.

### Details

- **Non-atomic counting is the default.** A value that crosses a task boundary (channel send, `spawn` capture, `Atom`, constant) has its object graph traversed at that moment to set the "shared" bit, and thereafter uses atomic operations. Subgraphs that are already shared are not rescanned. Since immutable values do not change after being shared, no other synchronization is needed.
- **RC elision**: borrow inference (no `inc`/`dec` inserted for references that are merely passed as arguments and not retained), and cancellation of a `dec` immediately following an `inc`.
- **Reuse**: if an allocation of the same size follows immediately after a `dec` that hit exactly 0, the memory is reused (`with` on `data` and `Array#push` complete without allocating).
- **Cycle collection**: an immutable value can only point to values older than itself at the time it is created, so it cannot form a cycle. The only things that can form cycles are objects with `var` fields and the boxes of captured variables that get reassigned. Only these objects are candidates, and Bacon–Rajan trial deletion runs on them at low frequency. In most programs the candidate set is small and collection cost is negligible.
- **Small `Int` values, `Float` (when the type is static), `Bool`, `Nil`, `Symbol`** are not counted.
- **Weak references** are not provided (the situations where they would be needed are limited to cycles among mutable objects, which cycle collection resolves).

### Rejected Alternatives

- **Generational tracing GC (Go/Erlang/Ruby)**: fast allocation and no counting overhead, but loses points 1–3 above. Without in-place updates of immutable values, the cost of persistent data structures is paid every time.
- **Atomic RC at all times (Swift)**: simple, but the cost of atomic operations applies everywhere. The Lean 4 approach of "atomic only for shared subgraphs" fits Quarz, where task boundaries are explicit.

## 6. Native Code Generation

- Under `--release`, QIR → LLVM IR (`inkwell`). Under `--dev`, Cranelift prioritizes build speed.
- `Int` overflow checks use `llvm.sadd.with.overflow`, `Float` is unboxed, and small `data` instances are treated as structs via scalar replacement.
- Exceptions use Itanium ABI zero-cost exceptions (landing pads). Paths without `rescue` carry no cost.
- Since task stacks are reserved with `mmap`, a stack switch is just a swap of the SP (a `switch_context` of a few dozen lines of assembly).
- The output is a statically linked single binary (including libquarz). `--shared` can also produce a shared library.

## 7. REPL and Development Experience

- `quarz repl` type-checks input and then runs it as bytecode. `class` and `def` can be added interactively, and when you want to change an existing definition, the REPL recompiles and swaps "everything that uses that definition" (hot reload). This is a REPL-only feature and does not affect program semantics.
- Type errors are shown with Ruby-style location display, along with the expected and actual types and narrowing hints ("`x` is `String?` here. You can narrow it with `if x`").
- `quarz run --watch` re-runs on file changes.

## 8. Implementation Language and Structure

The implementation language is **Rust**. The front end, VM, and runtime are all written in Rust, and `cargo build` produces a single `quarz` binary.

### Why Rust

Listing what the Quarz implementation needs from the start, the decisive factor is how much of it is covered by the Rust ecosystem.

| Need | Provision in Rust |
|---|---|
| Stackful task switching | `corosensei` |
| Work-stealing scheduler, channels | `crossbeam` deques and synchronization primitives. Race detection can be left to the compiler |
| Asynchronous IO | `io-uring`, `mio` |
| Bignums, regular expressions, Unicode | `num-bigint` (or `rug`), `regex`, `unicode-*` |
| Persistent vector / HAMT | Written in-house, since in-place updates rely on RC uniqueness. `im`/`rpds` serve as references |
| AST and type processing | `enum` and pattern matching |
| Later back ends | Cranelift is native Rust; LLVM via `inkwell` |

Other candidates considered:

- **C**: can be written in the same style as CRuby, but passed over because of the effort of vendoring the libraries in the table above and because the scheduler and channels — the parts most prone to bugs — would be written without safety nets.
- **OCaml (front end) + C (runtime)**: the best for writing a type checker, but the core of Quarz leans toward the runtime (RC, scheduler, in-place updates), and putting the type checker in a different language from that complicates the interpreter's startup path.
- **Zig**: suited to the runtime, but the language and standard library lack stability.
- **Write stage0 in Ruby and self-host early**: porting to Quarz would be easy, but every `quarz run` would type-check in Ruby, losing the fast startup of a development interpreter. Self-hosting is not required, and if done at all, it would come after the Rust implementation stabilizes.

### Guidelines for Writing in Rust

- **Confine `unsafe` to the runtime.** Tagged pointers, switching RC between non-atomic and atomic, and in-place updates lie outside Rust's ownership model; this part becomes "C written in Rust." `unsafe` goes only inside `quarz-rt`, and the VM and front end see only safe APIs.
- **Hold the AST and types in arenas.** Do not build trees of `Rc<RefCell<_>>`; refer via `Vec` + `NodeId(u32)`/`TypeId(u32)` indices. This avoids fighting the borrow checker and simplifies conversion to QIR and cache serialization.
- **The parser is hand-written recursive descent.** Ruby-family grammars require a stateful lexer (`{` for block vs. hash, `name: Type` labels, heredocs, contextual keywords), so hand-writing suits it, as with Prism.
- **Split into crates to localize compile times.**

### Crate Layout

```
quarz/
  Cargo.toml          workspace
  crates/
    quarz-syntax      lexing, parsing, AST (with positions), error reporting
    quarz-types       name resolution, type checking, Shareable derivation, .qzi read/write
    quarz-ir          QIR (the register-machine IR) and the run-time metadata (RtWorld)
    quarz-lower       checked AST → QIR
    quarz-vm          runtime (object model, RC, scheduler, channels, IO, natives) and the QIR interpreter;
                      also the static library compiled programs link against
    quarz-aot         QIR → machine code (Cranelift) and linking
    quarz-cli         quarz run / check / ir / build / repl
  std/                standard library (the part written in Quarz)
  docs/
  examples/
```

### Implementation Order

1. `quarz-syntax`: lexer, parser, AST. The goal is for `examples/` to parse.
2. `quarz-types`: name resolution and type checking. First monomorphic classes, methods, union types, and flow typing; then generics, `data`/`enum`, pattern exhaustiveness, and `extension`.
3. The minimal part of `quarz-rt`: object model and RC, `Int`/`String`/`Array`/`Hash`.
4. `quarz-vm`: QIR and the register VM. Run `examples/hello.qz` and `shapes.qz` with `quarz run`.
5. The concurrency part of `quarz-rt`: tasks, scheduler, channels, `Atom`, asynchronous IO. Run `wordcount.qz`, `pipeline.qz`, and `bank_actor.qz`.
6. Expand the standard library, REPL, separate compilation and caching via `.qzi`.
7. Native back ends (Cranelift for `--dev`, LLVM for `--release`).
8. Package management, `fmt`, LSP.

## 9. The Current Implementation (v0.0.1)

What exists today differs from the plan above in a few deliberate ways; the plan still describes where the design is going.

- **Programs are lowered to QIR and interpreted by a register VM.** The checker annotates the tree with types, resolved call targets and variable slots; `quarz-lower` turns each method, block, constant initializer and file top level into a QIR function (`quarz ir FILE` prints them); `quarz-vm` runs them. Locals captured by blocks live in heap frames, everything else in registers; keyword arguments are bound by the runtime and defaults evaluated in the callee's prologue; `break`/`return` out of blocks are status codes carried through the runtime; `ensure` is a handler block that catches every flow and resumes it, and a plain `return`/`break` that leaves an `ensure` region runs the body inline. `Int`/`Float` operators and generated field accessors bypass method dispatch. The programs in `bench/` take 0.15–0.85 s each in a release build (`fib(27)`: 0.18 s; 3 M iterations of a counting loop: 0.47 s).
- **Values are `Rc`-based.** Immutable collections are `Rc<Vec>` / `Rc<IndexMap>` and updates use `Rc::make_mut`, which copies unless the reference is unique. The evaluator moves the receiver out of the variable for the common `xs = xs.push(x)` form, so that case is updated in place; the general Perceus-style reuse described in §5 is future work. Reference counts are not atomic because the scheduler is single-threaded.
- **Tasks are stackful coroutines (`corosensei`) on one OS thread (M:1).** The scheduler is cooperative: tasks switch at channel operations, `sleep`, `await`, `Task.yield` and inside `loop`. Each task reserves 16 MiB of virtual stack (256 MiB for the main task); exceeding it raises `SystemStackError`. Deadlock (every task blocked, no timers) aborts the program with `DeadlockError`. Timers sleep the thread; file and standard I/O are synchronous.
- **The REPL** (`quarz repl`) keeps declarations, variables and running tasks across inputs; each input is checked incrementally against the accumulated program. Redefining a class or method is an error (use a new name); the hot reload described in §7 is not implemented. `require` and `require_relative` work in the REPL and run the loaded file's top level once.
- **`Bytes`, `Time` and the `json` library.** `Bytes` is an immutable byte sequence with `b"..."` literals, `Bytes::Builder`, `String#to_bytes`/`encode` and `Bytes#decode` (UTF-8, ASCII and ISO-8859-1). `Time` is a point in time with a UTC offset (`Time.now`/`utc`/`local`/`at`/`parse`/`iso8601`, `strftime`, arithmetic with `Duration`); `Time.monotonic` returns the monotonic clock as a `Duration`, and `require "time"` is accepted but not needed. `require "json"` gives `JSON.parse -> JSON::Value`, an enum with the variants `Null`, `Boolean`, `Integer`, `Number`, `Text`, `List` and `Map` (each carrying its value, with accessors such as `as_s`, `as_i?` and `[]`), `JSON.generate`/`pretty_generate` and `to_json`; a class customizes its JSON by defining `to_json -> String`. The parser and generator are native; the rest of the library is written in Quarz (`std/json.qz`).
- **`quarz build` compiles to a native executable.** `quarz-aot` translates every QIR function to machine code with Cranelift: moves, immediates, branches and `Int` arithmetic/comparisons are inlined, every other instruction calls the runtime (`qz_exec`), which executes it on the compiled function's registers; exception and `ensure` routing is compiled. The executable embeds the serialized module (the runtime needs the class and method tables, and interprets any function without machine code) and links `libquarz_vm.a` statically with the system `cc`, so the compiled program and `quarz run` share one runtime and behave identically (the test suite compiles every example and compares). There is no `--release`/`--dev` distinction yet, no class hierarchy analysis or inlining, and values stay boxed, so the gain over the VM comes from removing the dispatch loop and the per-call register allocation and from inline integer arithmetic: in `bench/`, the counting loop runs 4× faster (0.46 s → 0.11 s), `fib(27)` 1.5× (0.15 s → 0.10 s), the collection benchmark 1.2×, and call-heavy object code about the same.
- **Not implemented yet:** packages (`quarz pkg`), `.qzi` interface files and caching, `quarz build --release`/`--dev`, FFI (`extern`), `Supervisor`, `Task#on_exit`, `Date`, `JSON.decode[T]` (type arguments do not exist at run time yet), `Bytes#pack`/`unpack`, `Encoding`, `Int32`/`Float32` and the other fixed-width numbers, `%W`-style literals. `String` and `Regexp` use Rust's `regex` crate, whose syntax differs from Onigmo in places (no look-behind, no back-references in patterns).
- **Small decisions made while implementing**, documented here so the other chapters stay as the design: parameters after `*rest` are keyword-only (as after a bare `*`); `[]?` is a method name (`xs[i]?`); `x in pattern` is allowed inside argument lists; `[a, b] <=> [c, d]` on array literals is checked element-wise as tuples; a block with several parameters receiving one array or tuple spreads it over the parameters, as in Ruby; `Object` includes `Kernel`, so `puts` is a private method of every object; `IO` handles are `Shareable` (the runtime serializes access); the prelude declares built-ins with `native def`; `Comparable#clamp` returns `self` natively; pattern variables bound in different `case/in` arms are separate variables; a `case/in` that misses an alternative of a union, a `data`, an `enum`, `Nil` or `Bool` is an error, while missing values of an open type such as `Int` is a warning and a run-time `NoMatchingPatternError`; `case/when` whose type tests cover the subject needs no `else`; `loop` without `break` has type `Nothing`; floats print the way Ruby prints them; `Hash` keys and `Set` members use structural equality for the immutable built-ins and `data`/`enum` values and identity for class instances (user-defined `==` and `hash` are not consulted for keys); when a subclass or enum variant overrides one overload of an overloaded method, calls resolved to the other overloads keep going to the superclass (the runtime dispatches by signature, not only by name).
