# Quarz

日本語版: [README.ja.md](README.ja.md)

Quarz is a programming language that feels like Ruby, but is built on static typing, immutability, and concurrency.

- **Ruby-like syntax and built-in classes** — `def ... end`, blocks and `yield`, `case/in`, `#{}`, `Enumerable`/`Comparable` and exception handling are kept as they are.
- **Static class and method definitions** — there is no class reopening, no `define_method`, no `method_missing`, no `eval`. Method calls are resolved at compile time and the class hierarchy is fixed for the whole program. Additions to existing types are made with `extension`/`using`, which are confined to a lexical scope.
- **Immutable built-in data by default** — `String`/`Array`/`Hash`/`Set` are immutable: updates return new values and leave the old ones unchanged. When a reference is unique the update happens in place, so a straightforward loop is about as fast as one over a mutable array. Where mutation is needed, Builder types with the same API as Ruby are available.
- **Lightweight tasks** — `Task`s scheduled M:N like goroutines / Erlang processes, typed `Channel`s, structured concurrency (`Task.scope`) and `Atom`s that share immutable values. The type system (`Shareable`) checks that mutable objects never cross task boundaries, eliminating data races at compile time.
- **Interpreter and AOT compiler together** — one typed intermediate representation (QIR) and one runtime (libquarz) are shared: `quarz run` executes on the spot and gives you a REPL, `quarz build` produces machine code. The behavior of both is identical; only the performance differs.

## Quarz at a glance

```ruby
data WordCount(word: String, count: Int)
  include Comparable[WordCount]
  def <=>(other: WordCount) -> Int = other.count <=> count
end

def count_words(text: String) -> Hash[String, Int]
  text.downcase.scan(/[a-z']+/).tally
end

# Start a lightweight task per file and wait for all of them
counts = Task.scope do |scope|
  ARGV.map { |path| scope.spawn { count_words(File.read(path)) } }
      .map(&:await)
end

total = counts.reduce({}) { |acc, h| acc.merge(h) { |_, a, b| a + b } }

total.map { |word, count| WordCount.new(word, count) }
     .sort
     .first(10)
     .each { |wc| puts "#{wc.word}: #{wc.count}" }
```

The differences from Ruby show up in only three places: parameter types (`text: String`) and return types (`-> Hash[String, Int]`), immutable records via `data`, and `Task.scope`/`Task.spawn`/`await`. The rest is Ruby itself.

```ruby
enum Shape
  variant Circle(radius: Float)
  variant Rect(width: Float, height: Float)

  def area -> Float
    case self                       # exhaustiveness is checked at compile time
    in Circle(radius:) then Math::PI * radius ** 2
    in Rect(width:, height:) then width * height
    end
  end
end

class Account
  @id: Int                 # immutable field (assigned only in initialize)
  var @balance: Int = 0    # mutable field → this class is not Shareable
  attr_reader :id, :balance
  def initialize(@id: Int); end
  def deposit(amount: Int) -> Nil
    @balance += amount
  end
end

counter = Atom.new(0)
Task.scope do |scope|
  100.times { scope.spawn { counter.update { |n| n + 1 } } }
end
puts counter.value        # => 100
```

## Design documents

| Document | Contents |
|---|---|
| [docs/01-syntax.md](docs/01-syntax.md) | Syntax. Classes, `data`, `enum`, `module`, `extension`/`using`, method definitions, blocks, pattern matching, exceptions |
| [docs/02-types.md](docs/02-types.md) | Type system. Union types and nil safety, generics and variance, inference, flow typing, overloading |
| [docs/03-data-model.md](docs/03-data-model.md) | Immutable data and Builders, derivation rules for `Shareable`, equality, strings, rewriting Ruby idioms |
| [docs/04-concurrency.md](docs/04-concurrency.md) | Tasks, structured concurrency and cancellation, channels and `Channel.select`, `Atom`, actors and supervision, the runtime |
| [docs/05-execution.md](docs/05-execution.md) | Interpreter and AOT compiler, QIR, separate compilation, reference-counted memory management, implementation plan |
| [docs/06-stdlib.md](docs/06-stdlib.md) | Standard library. Correspondence with Ruby's built-in classes |
| [docs/07-ruby-diff.md](docs/07-ruby-diff.md) | Quick reference of changes from Ruby |
| [docs/08-crystal-diff.md](docs/08-crystal-diff.md) | Quick reference of differences from Crystal |
| [docs/09-grammar.md](docs/09-grammar.md) | Grammar sketch (EBNF) |
| [docs/10-cogs.md](docs/10-cogs.md) | Cogs (packages): git repositories pinned by commit, `Cog.toml`/`Cog.lock`, one module per cog, no `require`, the `cog` keyword |
| [docs/11-http.md](docs/11-http.md) | HTTP server: handlers returning responses, one task per connection, router, `Signal`; `HTTP::Client` later |
| [docs/12-testing.md](docs/12-testing.md) | Testing: Test::Unit-style `Test::Case`, tests found by the compiler, typed assertions, data-driven tests, `quarz test` |
| [docs/13-doc-comments.md](docs/13-doc-comments.md) | Documentation comments: the comment above a declaration, Markdown, checked links, examples run by `quarz test`, `quarz doc` |
| [examples/](examples/) | Sample code (`hello`, `shapes`, `wordcount`, `pipeline`, `bank_actor`, `extension`, `builder`) |

## Main design decisions

| Decision | Choice | Reason |
|---|---|---|
| Where type annotations go | Required on parameters; return types and locals are inferred | Shorter compile times and better error messages |
| Parameter type syntax | `name: Type`; keyword-only parameters after `*` | Reuses Ruby's label syntax without making whitespace significant |
| `nil` | A separate type, allowed only via `T?` | Turns runtime `NoMethodError`s into compile-time errors |
| Sum types | `enum` | For message types and exhaustiveness checking in `case/in` |
| Extending existing classes | `extension` + `using` (static refinements) | No reopening; the effect is limited to a lexical scope |
| Collections | Immutable values (copied on update when shared) + Builders | Safe sharing, and speed through in-place updates exploiting uniqueness |
| Shared mutable state | Forbidden. Only `Atom` and `Channel` | Data races eliminated at compile time. No locks |
| Lightweight threads | Stackful M:N tasks (`mmap` reservation + lazy commit) | Ruby-style synchronous code without async/await function coloring |
| Memory management | Reference counting + in-place updates + cycle collection limited to mutable objects | Fits AOT (no stack maps), in-place updates of immutable values |
| `arr[i]`/`h[k]` | Out of range / missing key raises. `[]?` returns `nil` | Reduces the nil checks you have to write under static typing (proven by Crystal) |

## Status

The interpreter runs every program in [examples/](examples/). It is written in Rust: `quarz-syntax` (lexer, parser), `quarz-types` (type checker), `quarz-ir`/`quarz-lower` (the QIR intermediate representation and the lowering to it), `quarz-vm` (runtime, QIR interpreter, scheduler, built-in classes) and `quarz-aot` (native code generation with LLVM through `clang`, used by `quarz build`). See [docs/05-execution.md](docs/05-execution.md) §9 for what the current implementation does and does not do.

```sh
cargo build --release
./target/release/quarz run examples/shapes.qz      # type-check and run
./target/release/quarz check examples/shapes.qz    # type-check only
./target/release/quarz parse examples/shapes.qz    # print the syntax tree
./target/release/quarz ir examples/shapes.qz       # print the QIR
./target/release/quarz build examples/shapes.qz -o shapes && ./shapes   # compile to a native executable (needs clang 14+)
./target/release/quarz repl                        # interactive session: line editing, history, completion
cargo test                                         # lexer, parser, checker, VM and compiler tests
```

## License

[MIT No Attribution](LICENSE) (MIT-0).
