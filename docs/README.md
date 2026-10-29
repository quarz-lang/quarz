# Design documents

The documents in this directory describe the language and its implementation. For a short introduction, see the [guide at quarz.dev](https://quarz.dev/guide/); the standard library's API reference is at [api.quarz.dev](https://api.quarz.dev/).

## Documents

| Document | Contents |
|---|---|
| [01-syntax.md](01-syntax.md) | Syntax. Classes, `data`, `enum`, `module`, `extension`/`using`, method definitions, blocks, pattern matching, exceptions |
| [02-types.md](02-types.md) | Type system. Union types and nil safety, generics and variance, inference, flow typing, overloading |
| [03-data-model.md](03-data-model.md) | Immutable data and Builders, derivation rules for `Shareable`, equality, strings, rewriting Ruby idioms |
| [04-concurrency.md](04-concurrency.md) | Tasks, structured concurrency and cancellation, channels and `Channel.select`, `Atom`, actors and supervision, the runtime |
| [05-execution.md](05-execution.md) | Interpreter and AOT compiler, QIR, separate compilation, reference-counted memory management, implementation plan |
| [06-stdlib.md](06-stdlib.md) | Standard library. Correspondence with Ruby's built-in classes |
| [07-ruby-diff.md](07-ruby-diff.md) | Quick reference of changes from Ruby |
| [08-crystal-diff.md](08-crystal-diff.md) | Quick reference of differences from Crystal |
| [09-grammar.md](09-grammar.md) | Grammar sketch (EBNF) |
| [10-cogs.md](10-cogs.md) | Cogs (packages): git repositories pinned by commit, `Cog.toml`/`Cog.lock`, one module per cog, no `require`, the `cog` keyword |
| [11-http.md](11-http.md) | HTTP server: handlers returning responses, one task per connection, router, `Signal`; `HTTP::Client` later |
| [12-testing.md](12-testing.md) | Testing: Test::Unit-style `Test::Case`, tests found by the compiler, typed assertions, data-driven tests, `quarz test` |
| [13-doc-comments.md](13-doc-comments.md) | Documentation comments: the comment above a declaration, Markdown, checked links, examples run by `quarz test`, `quarz doc` |
| [14-metaprogramming.md](14-metaprogramming.md) | Compile-time metaprogramming: `static def`, class bodies' `static` statements, `Meta` reflection, the compile-time rules |
| [examples/](../examples/) | Sample programs (`bank_actor`, `builder`, `extension`, `geometry`, `hello`, `json_report`, `markdown`, `multi_file`, `pipeline`, `sales_report`, `shapes`, `wordcount`, `workers`) |

## Main design decisions

| Decision | Choice | Reason |
|---|---|---|
| Where type annotations go | Required on parameters and return types (none means `-> Void`); locals are inferred | Shorter compile times and better error messages |
| Parameter type syntax | `name: Type`; keyword-only parameters after `*` | Reuses Ruby's label syntax without making whitespace significant |
| `nil` | A separate type, allowed only via `T?` | Turns runtime `NoMethodError`s into compile-time errors |
| Sum types | `enum` | For message types and exhaustiveness checking in `case/in` |
| Extending existing classes | `extension` + `using` (static refinements) | No reopening; the effect is limited to a lexical scope |
| Collections | Immutable values (copied on update when shared) + Builders | Safe sharing, and speed through in-place updates exploiting uniqueness |
| Shared mutable state | Forbidden. Only `Atom` and `Channel` | Data races eliminated at compile time. No locks |
| Lightweight threads | Stackful M:N tasks (`mmap` reservation + lazy commit) | Ruby-style synchronous code without async/await function coloring |
| Memory management | Reference counting + in-place updates + cycle collection limited to mutable objects | Fits AOT (no stack maps), in-place updates of immutable values |
| `arr[i]`/`h[k]` | Out of range / missing key raises. `[]?` returns `nil` | Reduces the nil checks you have to write under static typing (proven by Crystal) |
