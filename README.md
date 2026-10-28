# Quarz

日本語版: [README.ja.md](README.ja.md)

Quarz is a programming language that feels like Ruby, but is built on static typing, immutability, and concurrency.

- **Ruby-like syntax and built-in classes** — `def ... end`, blocks and `yield`, `case/in`, `#{}`, `Enumerable`/`Comparable` and exception handling are kept as they are.
- **Static class and method definitions** — there is no class reopening, no `define_method`, no `method_missing`, no `eval`. Method calls are resolved at compile time and the class hierarchy is fixed for the whole program. Additions to existing types are made with `extension`/`using`, which are confined to a lexical scope.
- **Immutable built-in data by default** — `String`/`Array`/`Hash`/`Set` are immutable: updates return new values and leave the old ones unchanged. When a reference is unique the update happens in place, so a straightforward loop is about as fast as one over a mutable array. Where mutation is needed, Builder types with the same API as Ruby are available.
- **Lightweight tasks** — `Task`s scheduled M:N like goroutines / Erlang processes, typed `Channel`s, structured concurrency (`Task.scope`) and `Atom`s that share immutable values. The type system (`Shareable`) checks that mutable objects never cross task boundaries, eliminating data races at compile time.
- **Interpreter and AOT compiler together** — one intermediate representation (QIR), lowered from the type-checked program, and one runtime (libquarz) are shared: `quarz run` executes on the spot and gives you a REPL, `quarz build` produces machine code. The behavior of both is identical; only the performance differs.

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
  def deposit(amount: Int) -> Void
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

For a short introduction to the language, see the [guide at quarz.dev](https://quarz.dev/guide/); the standard library's API reference is at [quarz.dev/std](https://quarz.dev/std/).

The design documents, `docs/0N-*.md`, describe the language and its implementation in full; [docs/README.md](docs/README.md) lists them, with the main design decisions.

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
