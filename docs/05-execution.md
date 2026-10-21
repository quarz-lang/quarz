# Execution Model: Interpreter and AOT Compiler

日本語版: [05-execution.ja.md](05-execution.ja.md)

Quarz shares one front end and one runtime across two back ends (an interpreter of the QIR and machine code). During development, `quarz run` gives fast startup and a REPL; for production, `quarz build` gives execution speed; and **the observable behavior of the two is identical**.

```
                    ┌────────────┐   ┌──────────────┐   ┌───────────────┐
  foo.qz ─────────▶ │ Lexing and │─▶ │ Name resol.  │─▶ │  QIR (typed   │
  (+ required files)│  parsing   │   │ & type check │   │   IR)         │
                    └────────────┘   └──────────────┘   └───────┬───────┘
                                                                 │
                       ┌─────────────────────────────────────────┼─────────────────────┐
                       │ quarz run / repl                        │ quarz build          │
                       ▼                                         ▼                      │
               ┌───────────────┐                     ┌────────────────────┐             │
               │ QIR           │                     │ Optimization       │             │
               │ interpreter   │                     │ (devirtualization, │             │
               │               │                     │ inlining, RC       │             │
               └───────┬───────┘                     │ elision, unboxing) │             │
                       │                             └─────────┬──────────┘             │
                       │                                       ▼                        │
                       │                             ┌────────────────────┐             │
                       │                             │ LLVM IR or         │             │
                       │                             │ Cranelift → code   │             │
                       │                             └─────────┬──────────┘             │
                       ▼                                       ▼                        │
               ┌──────────────────────────────────────────────────────────┐             │
               │  libquarz runtime (reference counting, scheduler,        │ ◀───────────┘
               │  copy-on-write collections, strings, bignums, IO,        │
               │  channels, regular expressions)                          │
               └──────────────────────────────────────────────────────────┘
```

## 1. Commands

| Command | Behavior |
|---|---|
| `quarz run app.qz [args]` | Type-check, lower to QIR and interpret it (caching type-check results for dependencies is *planned*) |
| `quarz repl` | REPL. Each input is type-checked, and definitions can be added (redefinition is not allowed; use a new name instead) |
| `quarz check app.qz` | Type-check only |
| `quarz build app.qz -o app` | Produce a native executable. `--backend llvm` (the default) optimizes through LLVM, `--backend cranelift` compiles fast for development; `QUARZ_BACKEND` sets the default |
| `quarz ir app.qz` | Print the QIR of every function (for debugging the lowering); `quarz tokens` and `quarz parse` print the tokens and the syntax tree |
| `quarz test` | Run `test/**/*_test.qz` (*planned*) |
| `quarz fmt` | Format (*planned*) |
| `quarz pkg add json` | Package management; the manifest is `Quarz.toml` (*planned*) |

## 2. Compilation Units and Separate Compilation

This section is the design; none of it is built yet. Today the whole program, the prelude and the libraries it requires included, is checked and lowered on every run (§9).

- One file = one compilation unit. From each unit's type-check results, an **interface file** `.qzi` is generated (class and method signatures, field layouts, constant types, the list of `extension`s, and the QIR of small methods that are inlining candidates).
- Dependent units read only the `.qzi`. This is why parameter types are mandatory: a change to a body does not trigger recompilation of other units (as long as the signature is unchanged).
- In its final stage, `quarz build` gathers the QIR of the whole program and performs devirtualization via class hierarchy analysis (CHA) and cross-module inlining. Since no classes are created at runtime, CHA is complete.
- The standard library is distributed ahead of time as `.qzi` + native code (`libquarz-std`), so it runs as machine code from the start even under `quarz run`.

## 3. QIR

QIR (Quarz Intermediate Representation) is the intermediate representation both back ends take as input: a register machine (registers may be reassigned) with basic blocks, each block possibly covered by a handler block. The Ruby-like syntax is simplified at the point of lowering to QIR.

- Method calls are resolved where the checker can (a call names its method, dispatched on the receiver's class when a subclass overrides it); otherwise they are looked up by name at run time. Constructors, procedure calls, `yield` and `super` have their own call kinds.
- The blocks of the common iterators (`times`, `upto`, `each`, `map`, `select`, ... on `Int`, `Array` and literal ranges) are lowered in place as loops, `break`/`next` becoming jumps; other blocks are closures, and `break`/`return` out of them are status codes carried through the runtime. Small methods are inlined.
- Values are tagged (a union type needs no other representation), and `Int` arithmetic checks for overflow and continues in a big integer.
- Reference counting and task switching are done by the runtime and by the code the back ends generate, not by QIR instructions.

The basis for the interpreter and compiler agreeing on semantics is that both take the same QIR as input and call the same runtime functions. The only difference allowed from QIR onward is performance, and CI runs the same test suite in both modes as differential testing.

## 4. Interpreter

- **The interpreter executes QIR instructions directly**, without a separate bytecode. Registers hold tagged values: an `Int`, a `Float` or a `Bool` is not allocated, but carries its tag. Frequent operations (`Int`/`Float` arithmetic and comparisons, array element reads and appends, lengths, field access) have dedicated instructions.
- Because type information is available, there are none of the inline caches or guards that a dynamic-language interpreter needs. The target is Lua/LuaJIT-interpreter-class speed, roughly 3–10× Ruby (without YJIT).
- A baseline JIT (generating machine code from QIR on the fly) could be added in the future, but since the premise is "AOT for production," its priority is low.

## 5. Memory Management

We adopt **reference counting (RC) + in-place updates via uniqueness + cycle collection restricted to mutable objects**.

Today values are reference counted without atomic operations, and updates copy unless the reference is unique (§9). The shared bit with atomic counting, general reuse and cycle collection described below are not implemented: values cross to another thread only by copying (`Task.blocking`), and a cycle among mutable objects is not reclaimed.

### Why Reference Counting

1. **In-place updates of immutable values**: an immutable value with a reference count of 1 can perform a "return a new value" operation destructively in place (Perceus, from Lean 4 / Koka). Quarz's "immutable by default yet fast" depends on this.
2. **Compatibility with AOT**: a tracing GC needs stack maps for native code (LLVM statepoints, etc.) or conservative scanning, which is a hard part of the implementation. RC needs neither, and the boundary with C FFI is simple.
3. **Deterministic release**: combined with `ensure`, resources like file handles can be released predictably.

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

- One generator, written against a small instruction-builder trait, feeds two back ends: `--backend llvm` (the default) writes LLVM IR and compiles it with `clang -O2`, so the production binary gets LLVM's optimizer and unwind tables; `--backend cranelift` generates machine code in-process with Cranelift, in a tenth of the time, for development. Both produce the same calls into the same runtime; only the typed entries differ (see §9: with LLVM they push no activation, since backtraces are recovered from the native stack).
- `Int` overflow checks use `llvm.sadd.with.overflow`, `Float` is unboxed, and small `data` instances are treated as structs via scalar replacement.
- Exceptions and non-local exits (`break`/`return` out of blocks, `exit`) are status codes that every compiled function returns and its callers test; unwind tables serve only to rebuild backtraces.
- Task stacks are reserved per task, and a switch is a swap of the stack pointer (`corosensei`).
- The output links the runtime (`libquarz_vm.a`) statically and the C library dynamically. Producing a shared library (`--shared`) is *planned*.

## 7. REPL and Development Experience

- `quarz repl` type-checks input and then runs it. `class` and `def` can be added interactively. Changing an existing definition, with the REPL recompiling and swapping "everything that uses that definition" (hot reload), is *planned*: today a redefinition is an error (§9). This is a REPL-only feature and does not affect program semantics.
- Type errors are shown with Ruby-style location display, along with the expected and actual types. Narrowing hints ("`x` is `String?` here. You can narrow it with `if x`") are *planned*.
- `quarz run --watch`, re-running on file changes, is *planned*.

## 8. Implementation Language and Structure

The implementation language is **Rust**. The front end, VM, and runtime are all written in Rust, and `cargo build` produces a single `quarz` binary.

### Why Rust

Listing what the Quarz implementation needs from the start, the decisive factor is how much of it is covered by the Rust ecosystem.

| Need | Provision in Rust |
|---|---|
| Stackful task switching | `corosensei` |
| Work-stealing scheduler, channels | `crossbeam` deques and synchronization primitives (planned: today the scheduler runs on one thread and needs neither) |
| Asynchronous IO | `polling` (epoll/kqueue) for sockets. Helper threads for whole-file operations, name resolution, `connect` and child processes. Open `File` handles, directory operations and standard input are synchronous (every task stops while they wait) |
| Bignums, regular expressions, Unicode | `num-bigint` (or `rug`), `regex`, `unicode-*` |
| Persistent vector / HAMT | Written in-house, since in-place updates rely on RC uniqueness; `im`/`rpds` serve as references (planned: today collections are copy-on-write vectors and `indexmap` maps) |
| AST and type processing | `enum` and pattern matching |
| Native back ends | Cranelift is native Rust; LLVM through textual IR compiled by `clang` |

Other candidates considered:

- **C**: can be written in the same style as CRuby, but passed over because of the effort of vendoring the libraries in the table above and because the scheduler and channels — the parts most prone to bugs — would be written without safety nets.
- **OCaml (front end) + C (runtime)**: the best for writing a type checker, but the core of Quarz leans toward the runtime (RC, scheduler, in-place updates), and putting the type checker in a different language from that complicates the interpreter's startup path.
- **Zig**: suited to the runtime, but the language and standard library lack stability.
- **Write stage0 in Ruby and self-host early**: porting to Quarz would be easy, but every `quarz run` would type-check in Ruby, losing the fast startup of a development interpreter. Self-hosting is not required, and if done at all, it would come after the Rust implementation stabilizes.

### Guidelines for Writing in Rust

- **Confine `unsafe` to the runtime.** Tagged pointers, switching RC between non-atomic and atomic, and in-place updates lie outside Rust's ownership model; this part becomes "C written in Rust." `unsafe` goes only inside the runtime (`quarz-vm`; the code generator has one more), and the front end sees only safe APIs.
- **Hold the AST and types in arenas.** Do not build trees of `Rc<RefCell<_>>`; refer via `Vec` + `NodeId(u32)`/`TypeId(u32)` indices. This avoids fighting the borrow checker and simplifies conversion to QIR and cache serialization.
- **The parser is hand-written recursive descent.** Ruby-family grammars require a stateful lexer (`{` for block vs. hash, `name: Type` labels, heredocs, contextual keywords), so hand-writing suits it, as with Prism.
- **Split into crates to localize compile times.**

### Crate Layout

```
quarz/
  Cargo.toml          workspace
  crates/
    quarz-syntax      lexing, parsing, AST (with positions), error reporting
    quarz-types       name resolution, type checking, Shareable derivation (.qzi files planned)
    quarz-ir          QIR (the register-machine IR) and the run-time metadata (RtWorld)
    quarz-lower       checked AST → QIR
    quarz-vm          runtime (object model, RC, scheduler, channels, IO, natives) and the QIR interpreter;
                      also the static library compiled programs link against
    quarz-aot         QIR → machine code (LLVM through clang, or Cranelift) and linking
    quarz-cli         quarz run / check / ir / build / repl
  std/                standard library (the part written in Quarz)
  docs/
  examples/
```

### Implementation Order

1. `quarz-syntax`: lexer, parser, AST. The goal is for `examples/` to parse.
2. `quarz-types`: name resolution and type checking. First monomorphic classes, methods, union types, and flow typing; then generics, `data`/`enum`, pattern exhaustiveness, and `extension`.
3. The minimal part of the runtime: object model and RC, `Int`/`String`/`Array`/`Hash`.
4. `quarz-vm`: QIR and the register VM. Run `examples/hello.qz` and `shapes.qz` with `quarz run`.
5. The concurrency part of the runtime: tasks, scheduler, channels, `Atom`, asynchronous IO. Run `wordcount.qz`, `pipeline.qz`, and `bank_actor.qz`.
6. Expand the standard library, REPL, separate compilation and caching via `.qzi`.
7. Native back ends (Cranelift for development, LLVM for production).
8. Package management, `fmt`, LSP.

## 9. The Current Implementation (v0.0.1)

What exists today differs from the plan above in a few deliberate ways; the plan still describes where the design is going.

- **Programs are lowered to QIR and interpreted by a register VM.** The checker annotates the tree with types, resolved call targets and variable slots; `quarz-lower` turns each method, block, constant initializer and file top level into a QIR function (`quarz ir FILE` prints them); `quarz-vm` runs them. Locals captured by blocks live in heap frames, everything else in registers; keyword arguments are bound by the runtime and defaults evaluated in the callee's prologue; `break`/`return` out of blocks are status codes carried through the runtime; `ensure` is a handler block that catches every flow and resumes it, and a plain `return`/`break` that leaves an `ensure` region runs the body inline. `Int`/`Float` operators and generated field accessors bypass method dispatch. Every instruction carries its source line, so exceptions get a backtrace of `file:line:in name` frames (per task) and `__LINE__` works, interpreted or compiled.
- **Values are `Rc`-based.** Immutable collections are `Rc`-shared vectors and insertion-ordered maps, and updates use `Rc::make_mut`, which copies unless the reference is unique. An array of only `Int`s or only `Float`s stores machine words, and a hash whose keys and values are all `Int` an `Int`-to-`Int` table, in the interpreter as in compiled code. A string of at most 15 bytes lives in the value itself (no allocation, no reference count: copying it is a copy of three words); a longer one is a shared `Rc<str>`; nothing observable depends on which (`==`, `equal?`, hashing and ordering compare the text). The evaluator moves the receiver out of the variable for the common `xs = xs.push(x)` form, so that case is updated in place; the general Perceus-style reuse described in §5 is future work. Reference counts are not atomic because the scheduler is single-threaded.
- **Tasks are stackful coroutines (`corosensei`) on one OS thread (M:1).** The scheduler is cooperative: tasks switch at channel operations, `sleep`, `await`, `Task.yield`, inside `loop` and while waiting for I/O. Sockets wait on the scheduler's epoll/kqueue reactor; whole-file operations, name resolution and child processes run on helper threads while only the calling task waits; `Task.blocking { }` runs its block in a second interpreter on another thread, only immutable values crossing over. Reads and writes on an open `File` and on the standard streams are synchronous. Each task reserves 16 MiB of virtual stack (256 MiB for the main task); exceeding it raises `SystemStackError`. Deadlock (every task blocked, no timers, no pending I/O) aborts the program with `DeadlockError`.
- **The REPL** (`quarz repl`) keeps declarations, variables and running tasks across inputs; each input is checked incrementally against the accumulated program. Redefining a class or method is an error (use a new name); the hot reload described in §7 is not implemented. `require` and `require_relative` work in the REPL and run the loaded file's top level once.
- **`Bytes`, `Time` and the `json` library.** `Bytes` is an immutable byte sequence with `b"..."` literals, `Bytes::Builder`, `String#to_bytes`/`encode` and `Bytes#decode` (UTF-8, ASCII and ISO-8859-1). `Time` is a point in time with a UTC offset (`Time.now`/`utc`/`local`/`at`/`parse`/`iso8601`, `strftime`, arithmetic with `Duration`); `Time.monotonic` returns the monotonic clock as a `Duration`, and `require "time"` is accepted but not needed. `require "json"` gives `JSON.parse -> JSON::Value`, an enum with the variants `Null`, `Boolean`, `Integer`, `Number`, `Text`, `List` and `Map` (each carrying its value, with accessors such as `as_s`, `as_i?` and `[]`), `JSON.generate`/`pretty_generate` and `to_json`; a class customizes its JSON by defining `to_json -> String`. The parser and generator are native; the rest of the library is written in Quarz (`std/json.qz`).
- **`quarz build` compiles to a native executable.** `quarz-aot` translates every QIR function to machine code, with LLVM by default (the module is written as LLVM IR and compiled by `clang -O2`; `QUARZ_CLANG` names the compiler, `QUARZ_KEEP_IR` keeps the `.ll` next to the output) or with Cranelift (`--backend cranelift`: no C compiler needed, a tenth of the build time, somewhat slower code): one generator, written against a small instruction-builder trait, serves both. Moves, immediates, branches and `Int`/`Float` arithmetic and comparisons (with overflow and division checks) are inlined; calls to methods that class hierarchy analysis proves are never overridden go straight to the native (`qz_call_static`, with the block if any) or, for a compiled body, directly to it: the caller lays the parameters out in its own frame (an unboxed number as a tag and a word) and builds the callee's activation in a stack buffer; when the callee needs neither a heap frame nor a method tag and gets no block, the activation is built, pushed on the call stack, torn down and popped inline (with the native-stack check), by the offsets `quarz_vm::layout` exports, and a program refuses to start on a runtime with another layout; otherwise the runtime does it (`qz_enter`/`qz_leave`); a method whose positional parameters and result are all declared `Int`/`Float` (no block, no frame, nothing reading the argument list) also gets a *typed entry* (`qz_fn_N_t`) that takes the parameters and returns the result as a machine value (any other way out, an exception or a result that is not of the declared type, leaves a status in the runtime for the caller to read, so the normal return is a single register); with LLVM, when such a function can return without needing a frame (a part with only arithmetic, comparisons, copies and branches on unboxed values leading to a `return` of the declared type, as `tak`'s `return z if y >= x`), that part is compiled again as a separate entry function that callers call and LLVM inlines into them: leaving it (a call, an overflow, anything else) calls the full body with the same arguments, which runs the part again (it has no effects), so a call that returns at once costs a comparison and a branch at the call site, without a frame, a stack check or a call; with LLVM it pushes no activation at all (one is built, with its `self` cloned and its parameters boxed, only on the paths where the runtime or the interpreter needs it), because backtraces are recovered from the native stack: every compiled function carries unwind tables and the QIR line of each call as its DWARF line, the runtime walks the stack with the C unwinder when an exception is raised and maps the return addresses to functions and lines through the executable's own symbol and line tables, and merges those frames, by stack address, with the activations of interpreted and boxed frames (each activation records its own address, and the frames a task's coroutine stack holds are told apart by its range); with Cranelift the typed entry builds and pushes a bare activation, its `self` and boxed parameters still materialized lazily. A direct call uses the typed entry when the arguments are of the declared types, falling back to the boxed protocol otherwise and to the interpreter when the result does not fit (a BigInt); registers that only inline code writes have no nil written to their home at entry, nor those that may hold a heap value: the exit releases them under a mask, set per path, of the homes that hold one (a deoptimization hands the runtime the set of homes never written, which it sets to nil before interpreting, and sets every bit); the callee's result slot is set to nil once per function (every consumer leaves it so); the registers of an inlined callee, nil at its entry, get their nil written only where something reads the home (a read, a runtime call, a successor block, a hand-over to the interpreter), so an inlined call costs no stores for its locals; a call to a method that some class overrides is, when at most six classes can receive it and each runs a known small method, split by the lowering into exact class tests (a tag test and a class id comparison) leading to direct calls that the inliner copies in, the dispatched call staying as the fallback; otherwise it lays its arguments out as a direct call does, and `qz_enter_virtual` resolves it on the receiver's class (a class-by-method dispatch table, filled on first use, replaces the hash lookup) and builds the activation, the compiled body being called through the address it returns, or runs the call itself when the target has another shape. `yield` and constructors use dedicated entry points (a data type given all its fields is built in its allocation from the fields laid out in the caller's argument area); `x = x.push(v)` and `@items = @items.push(v)` move the collection out of the variable or field and update it in place when nothing else refers to it, the common `Array`/`Hash`/`Set` updates without even building an argument list; a `data` value that never escapes the function (built, read field by field, dropped) is not allocated at all, its field reads becoming reads of the constructor's argument registers; a field whose type is such a data type (all `Int`/`Float`/`Bool` fields, see 01-syntax §4) holds it in place, its physical fields laid out in the object (the lowering turns a read into a construction that scalar replacement removes, and a write into stores of the components), so a `Vec2` stored in a particle costs no allocation either; an array whose elements are all `Int` or all `Float` stores them unboxed (as machine words; the storage becomes boxed values when anything else is pushed, at most once per array), and so does a hash whose keys and values are all `Int` (an `Int`-to-`Int` table: lookups, `put`, `delete` and in-place updates work on it directly, other natives see it as boxed values), and an array's length, an element read by an in-range index (a word read and a tag for unboxed storage, a copy for boxed) and an append to an unshared array with room (`ArrayPush`, and `xs = xs.push(v)` on a local, a captured variable or a field) are done inline through the vector (whose word layout, with the storage kind, the runtime checks at start-up); `self`, parameters, captured variables (through the frame's slot view) and object fields (through the object's field view) are read and written inline; reference counts are bumped and lowered inline, the runtime being called only to destroy the last reference; small methods (at most 40 instructions; no frame, no handlers, no blocks; two levels deep, so a recursive method like `tak` gets a copy of itself) are inlined into their callers on the QIR, with the callee's frames reconstructed in backtraces from an origin table; a copy of a register that is only read while both registers still hold the copied value is removed by copy propagation (the copies that inlining and parameter binding produce were a reference-count increment and decrement each), and a register read for the last time by a field store, an append, a data construction or a direct call's arguments is moved there rather than copied; the blocks of `times`, `upto`, `each`, `each_with_index`, `map`, `select`, `reject`, `reduce`, `count`, `any?` and `all?` on `Int`, `Array` and literal `Int` ranges are lowered in place as counted loops (so is `&:name` given for such a block, as a direct call of the method the checker resolved for the elements) when nothing nested captures their variables (`break`/`next` are jumps, the variables are registers, a block-local is nil again each iteration), so no closure is built and no call is made per element; registers that a dataflow analysis proves hold an `Int` that fits a machine word, a `Float` or a `Bool` are unboxed into SSA variables, so arithmetic on them has no tag tests; the overload the lowering recorded for an operator (`Int#+(Int)`) gives the operand types, a parameter declared `Int`/`Float` is checked once when read, a field declared so is read straight into the unboxed variable (a `Float` field, which the checker's definite initialization guarantees holds a `Float`, with no check at all, and an unboxed `Float` stored into one writes the tag and the word with nothing to release; an `Int` field, which may hold a BigInt, has its tag checked in the object, a mismatch re-running the read in the interpreter), `Int#to_f` on an unboxed `Int` is a conversion instruction, an operand of unknown state is checked once at run time, and when a speculation fails (an Int that is a BigInt, an overflow, a division by zero) the function hands the rest of its activation to the interpreter (`qz_resume`); an unboxed register is written back to its boxed home only where memory is read (a runtime call, a handler, that hand-over, or a block that expects it boxed; an array's length, element read or append writes back only its own operands, on its runtime path), which a liveness analysis keeps to the registers still needed, and a call through a typed entry writes back only on its fallback paths; registers are initialized inline and released inline, a `return` releasing only the registers whose state allows a heap value; `==`/`!=` on `Int` and `Float` are inline comparisons; an in-place update whose result is not read (`xs = xs.push(v)` as a statement) is not stored; a constant initialized by a literal is that literal at its uses, a chain of `+` on strings (`a + b + c`) is built in one buffer like an interpolation, `b << "text #{x}"` on a `String::Builder` appends the interpolation to the builder without making a string or dispatching a call (straight into the builder when every interpolated value is a string, an integer, nil or a boolean, through a reused buffer otherwise, since a `to_s` may run code that touches the builder), a short string constant is written as the three words of its value, a longer one or a symbol is cloned from the function's pool by a direct runtime entry, and string interpolation has its own runtime entry; every other instruction calls the runtime (`qz_exec`), which executes it on the compiled function's registers; exception and `ensure` routing is compiled. Natives that iterate (`each`, `map`, `select`, `times`) and `yield` prepare a block's activation once and reuse it per call. Common natives (`String#size`/`==`/`end_with?`/`upcase`/`+`, `String::Builder#<<`, `Array#size`/`[]`, `Hash#[]`/`key?`, …) have a by-reference version that takes the receiver and arguments straight from the registers, with no argument list and no copies, used by compiled calls, by the interpreter and by `&:name` procs (which cache the method found for the last receiver class, and which the iterating natives call without building an argument list); string interpolation, `upcase`, `+` and `Int#to_s` build their result in a reused buffer (integers by the runtime's own decimal conversion), so each costs at most one allocation, and a short result none. The executable embeds the serialized module (the runtime needs the class and method tables, and interprets any function without machine code) and links `libquarz_vm.a` statically with the system `cc`, so the compiled program and `quarz run` share one runtime and behave identically (the test suite compiles every example and compares). At start-up a compiled program decodes its embedded module, so the build first drops what the program cannot run before embedding the module (`quarz_ir::shake`: methods are reachable by name, from every call, symbol, `&:name`, operator and the few names the runtime calls by itself, since Quarz cannot call a method whose name is computed at run time; a dropped function keeps its id as an empty body that fails if it ever runs, and a dropped record is encoded as one byte; `QUARZ_NO_SHAKE=1` keeps everything), which also makes the build several times faster; the embedded module is decoded, the native tables are built with a fast hasher, and nothing is freed at exit. There is no `--release`/`--dev` distinction yet, and values other than local numbers stay boxed, so what remains between compiled Quarz and Go or Rust is the tagged, reference-counted value representation, heap allocation of every object and the call protocol of the calls that remain; Cranelift's code is somewhat slower than LLVM's. Measurements against Go, Rust, Ruby and Spinel are in `bench/compare/README.md`.
- **Not implemented yet:** packages (`quarz pkg`), `.qzi` interface files and caching, `quarz build --release`/`--dev`, FFI (`extern`), `Supervisor`, `Task#on_exit`, `Date`, `JSON.decode[T]` (type arguments do not exist at run time yet), `Bytes#pack`/`unpack`, `Encoding`, `Int32`/`Float32` and the other fixed-width numbers, `%W`-style literals. `String` and `Regexp` use Rust's `regex` crate, whose syntax differs from Onigmo in places (no look-behind, no back-references in patterns).
- **Small decisions made while implementing**, documented here so the other chapters stay as the design: parameters after `*rest` are keyword-only (as after a bare `*`); `[]?` is a method name (`xs[i]?`); `x in pattern` is allowed inside argument lists; `[a, b] <=> [c, d]` on array literals is checked element-wise as tuples; a block with several parameters receiving one array or tuple spreads it over the parameters, as in Ruby; `Object` includes `Kernel`, so `puts` is a private method of every object; `IO` handles are `Shareable` (the runtime serializes access); the prelude declares built-ins with `native def`; `Comparable#clamp` returns `self` natively; pattern variables bound in different `case/in` arms are separate variables; a `case/in` that misses an alternative of a union, a `data`, an `enum`, `Nil` or `Bool` is an error, while missing values of an open type such as `Int` is a warning and a run-time `NoMatchingPatternError`; `case/when` whose type tests cover the subject needs no `else`; `loop` without `break` has type `Nothing`; floats print the way Ruby prints them; `Hash` keys and `Set` members use structural equality for the immutable built-ins and `data`/`enum` values and identity for class instances (user-defined `==` and `hash` are not consulted for keys); when a subclass or enum variant overrides one overload of an overloaded method, calls resolved to the other overloads keep going to the superclass (the runtime dispatches by signature, not only by name).
