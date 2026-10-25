# Documentation Comments: `quarz doc`

日本語版: [13-doc-comments.ja.md](13-doc-comments.ja.md)

A comment written directly above a declaration documents it. The text is Markdown; a code span that names a class or a method is a link, and a fenced code block is an example that `quarz test` compiles and runs. `quarz doc` prints the documentation of a name in the terminal or generates a site for a cog. The shape is Ruby's (RDoc and Crystal document the comment above a definition), the checked links and the run examples are Rust's and Elixir's.

## 1. Shape

```ruby
# A last-in, first-out collection of `T`s. Immutable: `push` and `pop`
# return the new stack, as `Array#push` does.
#
# ```
# s = Stack[Int].new.push(1).push(2)
# s.size                 # => 2
# s.pop[1]               # => 2
# Stack[Int].new.pop     # raises Stack::Empty
# ```
class Stack[T]
  # The elements, bottom first.
  @items: Array[T]

  # Raised by `pop` on an empty stack.
  class Empty < StandardError
  end

  def initialize(items: Array[T] = [])
    @items = items
  end

  # The stack with `x` on top.
  def push(x: T) -> Stack[T] = Stack[T].new(@items.push(x))

  # The stack without its top, and the top.
  #
  # ## Raises
  #
  # `Empty` when the stack has no element: check `empty?` first.
  def pop -> [Stack[T], T]
    raise Empty.new("empty stack") if @items.empty?
    [Stack[T].new(@items[0...-1]), @items[-1]]
  end

  def size -> Int = @items.size
  def empty? -> Bool = @items.empty?
end
```

```
$ quarz doc Stack#pop
Stack#pop -> [Stack[T], T]

  The stack without its top, and the top.

  Raises

    Empty when the stack has no element: check empty? first.

$ quarz test
...
12 tests, 20 assertions, 0 failures, 0 errors, 0 pendings, 0 omissions, 0 notifications
```

- A **documentation comment** is the run of whole-line comments directly above a declaration, with no blank line between them and the declaration. A comment separated by a blank line, a comment above something that is not a documented declaration (`include`, `using`, `require`, a bare `private`, a statement) and a comment at the end of a code line are ordinary comments. There is no marker (`///`, `##`): Ruby, Crystal and Go need none, and the blank-line rule tells an implementation note from documentation.
- The text is the comment lines without their `#` and one space. Its **first paragraph is the summary**, shown in lists, in completion and in `quarz doc` of the enclosing class.
- The example in the comment is compiled and run by `quarz test` (§4); `Stack#pop` and `Array#push` are checked links (§3).
- The example is a file of an application cog, whose classes are seen bare, as a script's are. In a library cog, readers write `Mathx::Stack`, and so does its example (§4).

## 2. What Is Documented

A documentation comment goes above:

- a `class`, `module`, `data`, `enum` and an enum's `variant` line (`variant Hearts, Diamonds` documents each variant it lists; the variants of the one-line form `enum Color = Red | Green` have no documentation of their own, the enum's covers them);
- a `def`, each overload separately (§5 for `:ditto:`), `native def` included: the standard library is documented this way; a comment above a run of one-line definitions documents the first, as in Go;
- a field (`@items: Array[T]`, `var @n: Int = 0`), and so the accessor `attr_reader`/`attr_accessor` makes of it; an `attr_reader :a, :b` line documents each accessor whose field has no comment;
- a field of a `data` or a `variant` in a multi-line form, above its line:

  ```ruby
  data Suite = (
    # The class's name, as `StackTest`.
    name: String,
    # The file it is declared in.
    file: String
  )
  ```

- a constant (`LIMIT = 10`), a type alias, an `alias` (without one, the alias shows the original's documentation) and an `extension`.

A cog's overview is its `README.md`, as a crate's or a gem's: the generated site starts with it, and the root module's page is that file. The language has no `module` declaration for the root module, and a comment at the top of a file documents nothing (a file is not a unit of the API). A standard library module (`require "http"`) is documented by the comment above its `module HTTP`.

Private and protected methods, and fields without accessors, are left out unless `--private` is given, except the functions of `Kernel` (`puts`, `rand`, `exit`), which are private so that they are called without a receiver, and are the program's functions: `quarz doc puts` shows them. `:nodoc:` as the first line of a public declaration's comment hides it and its members from the output; the compiler still reads the comment, its examples run (§4), and `--private` shows it.

## 3. The Text: Markdown

The text is CommonMark, with these conventions:

- **Headings** are `##` and below: the page's `#` heading is the declaration's name. So a section is written `# ## Examples` in the source. The conventional sections are `Examples`, `Raises` (the exceptions a method raises, which the types do not say), `See also`.
- **Code spans that name a declaration are links**, checked by the compiler: `` `Array#push` `` (an instance method), `` `Array.new` `` (a class method), `` `Stack::Empty` `` (a class, a module, a constant), `` `#pop` `` and `` `.new` `` (an instance method and a class method of the class being documented), `` `pop` `` (the same, when the class has a public method of that name; otherwise plain code, a parameter's name for instance). Names resolve as they would in the declaration's scope, so a cog's own classes need no module prefix in its own comments. A span that resolves is rendered as a link; one that does not is plain code. `quarz doc --check` warns about a span of a name's shape (`Foo`, `Foo::Bar`, `Foo#bar`, `Foo.bar`, `#bar`, `.bar`) that resolves to nothing, or to a private declaration that the output leaves out.
- The methods of an `extension` are reachable only under `using` (01-syntax.md §7), so they are documented on the extension's module's page (`quarz doc Shout` lists `extension String` and `shout`) and linked from that module's own comments as `` `shout` ``; a comment elsewhere names them in prose. The prelude's always-active extensions (`extension Array[T: Comparable[T]]`) appear on the target class's page, as the methods they are to every program.
- **Admonitions**: a paragraph starting with `NOTE:`, `WARNING:`, `DEPRECATED:` or `EXPERIMENTAL:` is set off (Crystal's convention).
- **No raw HTML**: tags are shown as text, so the generated site holds nothing but what the generator wrote.
- Lists, emphasis, tables and links (`[text](url)`) as in Markdown. An indented code block is shown as code and is not an example.

Parameters, the result and the block are described in prose: the signature already gives their types and names, so a `@param x [Int]` list (YARD) would repeat it.

## 4. Examples Are Tests

A fenced code block in a documentation comment is a Quarz program, and `quarz test` compiles and runs it, as `cargo test` runs Rust's doc examples, so that the documentation cannot drift from the code.

```ruby
# ```
# Stack[Int].new.push(1).size   # => 1
# Stack[Int].new.pop            # raises Stack::Empty
# words = %w[b a].sort
# # => ["a", "b"]
# ```
```

- `expr # => text` checks that `expr.inspect` is `text` (whitespace at the ends aside): the expression statement that ends on that line, an assignment's value being what it assigned. Alone on the line after a statement, `# => text` applies to that statement. `expr # raises Klass` checks that it raises `Klass` or a subclass. What the program prints is not compared (12-testing.md §9, `capture_output`): write the result instead of printing it. Elsewhere in these docs `# =>` marks what `puts` printed; in an example it is `inspect`, and `quarz doc --check` warns about a `# =>` after `puts` or `print`, whose value is `nil` (`p` returns its argument, so `p x # => 2` holds).
- The fence's info string: none or `quarz` is run; `quarz no_run` is compiled only (a server loop, a network call); any other language (`text`, `sh`, `toml`) is shown only.
- Each example is a test of its own, named after the declaration, `Stack#pop (example 1)`, reported with the other tests of `quarz test`; a failed `# =>` says `expected => 2, was 3`. `quarz test --doc` runs the examples only, `--no-doc` leaves them out; `quarz test --doc --std` runs the standard library's (embedded in the compiler, so not given as files). `quarz test FILE...` (12-testing.md §8) also runs the examples of the files given and of what they `require_relative`.
- An example sees its cog as a user does (12-testing.md §2): a library under its module (`Mathx.square(3)`, `Mathx::Stack`), an application bare. An example of an extension's method starts with `using Shout`, as a user's file does. A standard library example writes `HTTP::Response`, and `require`s nothing: the modules load by name.
- An example may declare classes and methods. Each example is a unit of its own, so its `def`s are its own, as a file's are (01-syntax.md §2); classes are global, so an example's class must not share its name with another example's, the cog's or the tests'. Since the examples of a cog are compiled into one program (§7), name them apart (`Point` in one, `Point3` in another).

## 5. Inheritance and Repetition

- An overriding method without a documentation comment shows the overridden method's, marked with its origin (`from Base`); an including class's page lists the module's methods with theirs. A method with its own comment replaces it entirely.
- `Stack.new` is documented by the comment of `initialize`, and a `data`'s generated methods (`new`, `with`, `to_h`, the field readers) from the type's and the fields' comments.
- `:ditto:` as the whole comment repeats the previous declaration's comment: for an overload that differs only in a parameter's type.

  ```ruby
  # The first `n` elements.
  def first(n: Int) -> Array[T] = take(n)
  # :ditto:
  def first(range: Range[Int]) -> Array[T] = self[range]
  ```

## 6. Commands

| Command | Meaning |
|---|---|
| `quarz doc [FILE] NAME` | Print the documentation of `NAME` (`Stack`, `Stack#pop`, `Stack.new`, `HTTP::Response.text`, `puts`) as text, with the signature; for a class, its summary and its members' summaries. Resolved in the cog around the current directory, in the script `FILE` and what it requires when one is given, or in the standard library alone otherwise |
| `quarz doc` | The cog's public API, one line per declaration |
| `quarz doc --html [-o DIR]` | A static site of the cog (default `doc/`): one page per class and module, the `README.md` as the front page, a search box (a JSON index loaded by the page), each member with its signature, text and source location. `--std` generates the standard library's |
| `quarz doc --check` | Report dangling links (§3), an unterminated fence and a `# =>` after `puts` or `print`; `--missing` also reports public declarations without a comment (exit 0 or 1 for CI) |
| `quarz doc --json` | The API with its documentation as JSON, for other tools |
| `quarz test [--doc\|--no-doc] [--std]` | §4 |

`--private` includes private and protected members in any of these. `quarz doc` of a dependency's name (`Httpx::Client`) works for the cogs the lock names, from their sources.

The REPL's completion shows a candidate's summary.

## 7. Implementation

- **Parser.** The parser already collects every comment's span (`Parsed::comments`). It attaches to a declaration the run of whole-line comments that ends on the line before its first token, with no blank line in between, as `doc: Option<Rc<str>>` with the comment's span (for `--check`'s locations and the examples' line numbers) on the nodes `ClassDef`, `ModuleDef`, `MethodDef`, `DataDef`, `EnumDef`, `Variant`, `FieldDecl` (a class's, a data's and a variant's fields alike) and `ExtensionDef`, and on the expression kinds `AttrDecl`, `Alias`, `TypeAlias` and `ConstAssign`. `quarz parse` prints it.
- **Declaration.** `declare.rs` copies it into `ClassInfo`, `MethodInfo`, `FieldInfo`, `ConstInfo`, `TypeAliasInfo` and `ExtensionInfo`, so that anything that has the checked `World` has the docs: `quarz doc`, the REPL's completion, later the language server.
- **`quarz doc`** loads and checks the cog (or the standard library) as `quarz check` does, then walks the `World`: public declarations by namespace, overloads together, inherited and included members by `ancestors`. Links are resolved with the checker's own name resolution, in the declaration's scope. Markdown is parsed with `pulldown-cmark` (CommonMark; a dependency of `quarz-cli` only, not of the runtime), its code spans resolved and its fences classified before rendering. The text output wraps the Markdown as plain text (code spans as they are, headings as lines); the HTML output is static files plus one JSON index.
- **Examples** reuse the testing machinery (12-testing.md §5). After the cog is checked, the examples of its own files are gathered from the `World`. Each becomes a unit of its own: its declarations at the top level, its statements the one `test_example` method of a generated `Test::Case` class, with `expr # => text` rewritten to `Test::Doc.expect(expr, "text", line)` and `expr # raises K` to `Test::Doc.raises(K, line) { expr }`: two new methods of `std/test.qz`, whose failures read `expected => 2, was 3`. `check_with_extra` is extended to add several units, and the runner's generator lists the suites of the classes it generated itself (they are not in the `World` it reads the test classes from), each named `Stack#pop (example 1)` after the declaration. The examples run under the test options (`-n Stack#pop`, `--parallel`, `--release`). Each generated unit carries a map from its lines to the comment's file and line, which diagnostics render through, so a compile error in an example is reported in the comment.
- **Separate compilation**, when it comes (05-execution.md §2): an interface file carries the docs of what it exports, so `quarz doc` and the language server will work on a dependency from its interface alone.
- **The standard library.** `std/prelude.qz` and `std/*.qz` are mostly commented above their declarations, and those comments become the docs. Making them so takes a pass over the files, with the compiler's help (`--missing`, and a listing of the comments that would become docs): a module header at the top of a file (`std/http.qz`, `std/test.qz`, `std/json.qz`) moves above its `module`; a comment above a group of one-line definitions ("Aliases that Ruby programs use.") goes above each, or the others say `:ditto:`; an implementation note directly above a definition ("compiled code compares inline", "Lowering calls it") moves below a blank line or into the body; an overview placed above the first class of a file (`std/socket.qz`) moves to the module; indented example code (`std/json.qz`) becomes a fence with `# =>` checks. The repository's tests run the standard library's examples (`quarz test --doc --std`), and docs/06-stdlib.md stays the overview.

## 8. Later

- `DEPRECATED:` as a compiler warning at the call sites (the checker has the docs), with `--deny-deprecated`.
- Hover and completion documentation in an editor (the language server), and a `help` command in the REPL, which has no command layer today (every line is an expression, and `Stack#pop` lexes as a comment).
- A hosted site of the standard library's docs, and of cogs' (the `docs.rs` of cogs; 10-cogs.md §8 leaves discovery for later).
- Doc coverage in `quarz doc --missing`'s output as a percentage.
- Examples that check what a program prints (with `capture_output`, 12-testing.md §9).

## 9. Alternatives Not Adopted

- **A marker (`///`, `//!`, `##`, `#:`).** Rust needs one because `//` comments are everywhere between items; in Ruby, Crystal and Go, the comment above a definition is its documentation, and the blank-line rule keeps implementation notes out. A marker would also make the standard library's existing comments non-docs until each was edited; without one, the pass of §7 is a review of them, not a rewrite.
- **Tags (`@param`, `@return`, `@raise` of YARD and Javadoc).** The signature carries the names and types; a tag would repeat them and go stale. `Raises` is a section, because the types do not say it.
- **RDoc markup (`+code+`, `= Heading`).** Markdown is what the readers of these docs write elsewhere, and what every renderer and editor shows.
- **Doc strings as values (`@doc "..."` in Elixir, Python's docstrings below the `def`).** A class body declares only, and a string before a method would be a statement; a comment also keeps the docs out of the program's memory.
- **Hidden example lines (Rust's `# ` prefix).** In a `#` comment, a line's first `#` already begins a Quarz comment line or a Markdown heading; a third meaning for it is one too many. Examples are shown whole.
- **Examples run only on request.** The point of running them is that they cannot go stale unnoticed, which they would if a flag were needed.
- **Google/NumPy-style sections (`Args:`, `Returns:`).** Headings and prose serve, and the typed signature makes an argument list redundant.
