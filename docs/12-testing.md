# Testing: `quarz test`

日本語版: [12-testing.ja.md](12-testing.ja.md)

`require "test"` gives the `Test` module, and `quarz test` runs the tests of a cog or a script. The shape is Ruby's Test::Unit: a test is a `test_*` method of a class that inherits `Test::Case`, with `setup`/`teardown` and `assert_*`; what differs comes from the language and from Go, Rust, Zig and Swift Testing. Quarz has no reflection, so the compiler finds the tests, as `go test` finds `TestXxx` functions; the assertions are typed; and since mutable state never crosses a task, tests can run in parallel without a flag per test.

## 1. Shape

```ruby
# test/stack_test.qz
require "test"

class StackTest < Test::Case
  # A fixture is a field with an initializer: the instance is made for
  # each test, so this is Test::Unit's `setup`.
  @stack: Stack[Int] = Stack[Int].new.push(1).push(2)

  def test_pop
    rest, top = @stack.pop
    assert_equal(2, top)
    assert_equal(1, rest.size)
  end

  def test_empty_pop
    e = assert_raise(Stack::Empty) { Stack[Int].new.pop }
    assert_match(/empty/, e.message)
  end
end
```

```
$ quarz test
Loaded suite test
Started
..F.
Finished in 0.012345 seconds.

1) Failure: test_pop(StackTest) [test/stack_test.qz:12]:
<2> expected but was
<1>

4 tests, 7 assertions, 1 failures, 0 errors, 0 pendings, 0 omissions, 0 notifications
```

- A **test** is a public instance method of a `Test::Case` subclass whose name starts with `test_` and that takes no parameter (or one, with data: §4). The compiler lists them; nothing is registered at run time, and a test file has no top-level statements of its own.
- A **test case** instance is made for each test, as in Test::Unit: `setup`, the test, `teardown` run on it, and its fields are its own. A fixture is a field with an initializer (a field must be given a value where it is declared or in `initialize`, [01-syntax.md](01-syntax.md) §3), and `setup` is for what has effects, such as opening a socket or a file, with `teardown` to undo it; a fixture `setup` must make is a `var @x: T? = nil` field, narrowed at each use. The instance is confined to the task that runs the test, so tests of one class, or of different classes, can run in parallel (§6).
- A test file's top-level statements, if any, run when the file is loaded, before any test; that is where a script's tests `require_relative` the script.
- `quarz test` builds a program from the test files, a generated runner and the library, type-checks it and runs it. A type error in a test file fails the run, reported like any compile error; a test is not skipped for it.

## 2. Files and Discovery

- In a cog (an application or a library, [10-cogs.md](10-cogs.md)), `quarz test` runs `test/**/*_test.qz`. `test/test_helper.qz`, when present, is loaded first (test files `require_relative "test_helper"` as they do in Ruby; the runner also loads it, so forgetting it changes nothing). Other files under `test/` are loaded only when a test file requires them.
- The test files see a library cog as its users do, under its module (`Webkit::Router`), together with its `[dependencies]` and `[dev-dependencies]`: `quarz test` loads the cog as a dependency of a synthetic root made of the test files and the runner, whose imports are the cog's module and both dependency tables. The test files are not part of the cog's module, so a file-level `def` of the cog is not reachable (as in Go's external test packages); a test for a private detail is written where the detail is, in `src/`, as a private method the public API exercises. An application's declarations are seen bare, as its own files see them (the test files join its files, with its dependencies and dev-dependencies in their scope and so, under `quarz test`, in its files' too), and the statements of its `src/main.qz` are neither checked nor run. Test files given on the command line that are under the cog's `test/` are tested in the cog in the same way; others are scripts (§8).
- `[dev-dependencies]` are resolved and locked with the others (`Cog.lock` lists them, as Cargo's lock does): the application's only, not its dependencies'. The movement lists the cogs only they reach last, and `quarz run` and `quarz build` leave those out. Test files are loaded like a script's files, with `require_relative` between them, not like a cog's `src/`, where every file is loaded and `require_relative` is refused.
- A script is tested with `quarz test path/to/foo_test.qz` (several paths, or directories, may be given); its `require_relative` files come along.
- The compiler lists, in every loaded file, the classes that inherit `Test::Case` and are not `abstract`, and in each (own methods, inherited ones and included modules') the `test_*` methods, in file order and then declaration order. A `test_*` method with parameters other than the data one, an overloaded one or a non-public one is a compile error naming the method, not a silently ignored test, and so is a test class whose `initialize` needs arguments.
- `quarz test --list` prints the tests found, as `StackTest#test_pop`.

## 3. The Library

```ruby
module Test
  # The assertions: `Case` includes them, and so may a module of tests
  # or helpers (§7). Each counts itself through `add_assertion`.
  module Assertions
    abstract def add_assertion -> Nil

    def assert(value: Object?, message: String? = nil) -> Nil        # truthy
    def refute(value: Object?, message: String? = nil) -> Nil        # falsy
    def assert_true(value: Bool, message: String? = nil) -> Nil
    def assert_false(value: Bool, message: String? = nil) -> Nil
    def assert_equal[T](expected: T, actual: T?, message: String? = nil) -> Nil
    def refute_equal[T](expected: T, actual: T?, message: String? = nil) -> Nil
    def assert_nil(value: Object?, message: String? = nil) -> Nil
    def refute_nil(value: Object?, message: String? = nil) -> Nil
    def assert_same(expected: Object, actual: Object, message: String? = nil) -> Nil   # equal?
    def assert_in_delta(expected: Float, actual: Float, delta: Float = 0.001, message: String? = nil) -> Nil
    def assert_in_epsilon(expected: Float, actual: Float, epsilon: Float = 0.001, message: String? = nil) -> Nil
    def assert_match(pattern: Regexp, actual: String, message: String? = nil) -> Nil
    def refute_match(pattern: Regexp, actual: String, message: String? = nil) -> Nil
    def assert_includes[T](collection: Enumerable[T], element: T, message: String? = nil) -> Nil
    def refute_includes[T](collection: Enumerable[T], element: T, message: String? = nil) -> Nil
    def assert_empty(collection: Enumerable[Object], message: String? = nil) -> Nil
    def refute_empty(collection: Enumerable[Object], message: String? = nil) -> Nil
    def assert_empty(text: String, message: String? = nil) -> Nil
    def refute_empty(text: String, message: String? = nil) -> Nil
    def assert_compare[T: Comparable[T]](lhs: T, op: Symbol, rhs: T, message: String? = nil) -> Nil   # :<, :<=, :>, :>=, :==
    def assert_raise(klass: Class, message: String? = nil, &: () -> Nil) -> Exception   # klass or a subclass
    def assert_raise_message(pattern: Regexp | String, &: () -> Nil) -> Exception
    def assert_nothing_raised(message: String? = nil, &: () -> Nil) -> Nil

    def flunk(message: String = "Flunked") -> Nothing
    def pend(message: String = "pending") -> Nothing     # the test ends here, counted as pending
    def pend(message: String = "pending", &: () -> Nil) -> Nil   # pending if the block fails, a failure if it passes
    def omit(message: String = "omitted") -> Nothing     # the test ends here, counted as omitted
    def omit_if(condition: Bool, message: String = "omitted") -> Nil
    def omit_unless(condition: Bool, message: String = "omitted") -> Nil
  end

  class Case
    include Assertions

    # Before and after each test; the instance is fresh for each.
    def setup -> Nil = nil
    def teardown -> Nil = nil
    # Once around a class's tests, with no instance (class methods).
    def self.startup -> Nil = nil
    def self.shutdown -> Nil = nil

    # The test's own time limit (default: the run's, 60 s).
    def self.timeout -> Duration? = nil
    # Whether the class's tests run one at a time under --parallel (§6).
    def self.serial? -> Bool = false

    def notify(message: String) -> Nil                   # a note in the report
  end
end
```

- **Typed assertions.** `assert_equal[T](expected: T, actual: T?)`: `T` is fixed by `expected`, and `actual` must be a `T`, or nil (the common `assert_equal(1, h["k"]?)`, whose nil is a failure, not a type error). So `assert_equal(1, "1")` and `assert_equal(2, 2.0)` are compile errors, where Test::Unit fails at run time: write the literal in the actual's type (`assert_equal(2.0, x)` with `x: Float`; `assert_equal([1, 2], xs)` with `xs: Array[Int]`), and convert where the types really differ (`assert_equal("1", n.to_s)`). For nil, `assert_nil(x)`: `assert_equal(nil, x)` fixes `T = Nil` and takes nothing else. There is no `assert_predicate`: write `assert(x.empty?)`.
- **Failure messages.** `assert_equal` prints `<expected> expected but was <actual>` with `inspect`; when either is a string of several lines, it adds a line diff (` ` both, `-` expected only, `+` actual only). The optional `message` comes first.
- **Where it failed.** A failed assertion raises `Test::AssertionFailed < Exception` (not a `StandardError`, so `rescue => e` in the code under test does not swallow it). The report gives the test file and line of the assertion: the first frame of the backtrace outside the `test` library, so a helper method of the test class is reported at the assertion inside it (to report the helper's caller instead, as Go's `t.Helper()` does, call `helper!` in it... *not in the first version*).
- **`assert_raise`** returns the exception, for further assertions on it. It takes the exception class as a value (`Class`), and a subclass of it passes: the library rescues `Exception` and asks `e.is_a?(klass)`. `is_a?` takes a type written as a constant (`x.is_a?(Int)`, which narrows `x`), or a class *value*, any other expression of type `Class` (`e.is_a?(klass)`): that is the native `Object#is_a?(klass: Class) -> Bool`, which tests the class at run time and narrows nothing. The two forms are told apart as they are written, so `x.is_a?(Foo)` keeps its meaning. `Task::Cancelled` and a failed assertion inside the block are not caught. The result is an `Exception` (its `message` is there; a field of the subclass needs `as`). With a message, the raised exception's message must equal it. A typed form, `assert_raise[E: Exception](klass: Class[E]) -> E`, waits for `Class[T]` in the type system (§9).
- **Pending and omitted.** `pend` marks a test known to fail (Test::Unit's `pend`): without a block it ends the test, counted as a pending; with a block, the block is run and the test is pending if the block fails (an assertion or a `StandardError`), and a failure if it *passes* ("Pending block should not be passed"), so a fixed test is noticed. `omit` ends the test and counts it as omitted (an environment that lacks something). Both show in the summary and the report.
- `Test::Unit::TestCase` is `Test::Case` under its Ruby name, for tests moved over.

## 4. Data-driven Tests

Test::Unit's `data` runs one test method on several inputs. Here the data is a method, so the compiler can check it:

```ruby
class ParseTest < Test::Case
  def data_parse -> Hash[String, [String, Int]]
    {
      "decimal" => ["42", 42],
      "hex"     => ["0x2a", 42],
      "signed"  => ["-7", -7],
    }
  end

  def test_parse(data: [String, Int])
    text, expected = data
    assert_equal(expected, Parser.parse(text))
  end
end
```

- A test method with one parameter takes its data from the method `data_<name>` of the same class, which returns `Hash[String, T]` for the parameter's type `T` (checked when the runner is compiled; `T` is Shareable, since a row may cross into a test's task). Each entry is a test of its own, named `test_parse[hex]`, with its own instance, `setup` and `teardown`, and selectable by `-n`. `--list` calls the `data_*` methods to print the names, so it runs that much of the tests' code.
- This is Go's table test with a name per row, and Test::Unit's `data`, without a class body that runs code (a class body only declares).

## 5. The Runner

`quarz test` generates the runner, as `go test` generates its `main`, so neither the library nor the program needs reflection:

```ruby
# generated (the unit `<test-runner>`)
suites: Array[Test::Suite] = [
  Test::Suite.new("StackTest", "test/stack_test.qz", -> { StackTest.new }, [
    Test::Entry.plain("test_pop", "test/stack_test.qz", 10, ->(c: Test::Case) { c.as(StackTest).test_pop; nil }),
    Test::Entry.plain("test_empty_pop", "test/stack_test.qz", 16, ->(c: Test::Case) { c.as(StackTest).test_empty_pop; nil }),
  ], -> { StackTest.startup }, -> { StackTest.shutdown }, StackTest.timeout, StackTest.serial?),
  Test::Suite.new("ParseTest", "test/parse_test.qz", -> { ParseTest.new }, [
    Test::Entry.each("test_parse", "test/parse_test.qz", 12, ->(c: Test::Case) { c.as(ParseTest).data_parse.keys },
      ->(c: Test::Case, row: String) { t = c.as(ParseTest); t.test_parse(t.data_parse[row]); nil }),
  ], -> { ParseTest.startup }, -> { ParseTest.shutdown }, ParseTest.timeout, ParseTest.serial?),
]
exit Test.run(ARGV, suites)
```

- `Test::Suite` holds the class name, its file, how to make an instance (`shareable () -> Test::Case`; a `Test::Case` subclass has no `initialize` with parameters, or the runner's `.new` fails to compile and says so) and its entries; `Test::Entry` a test's name, file and line (of its method: a base class's or a module's for an inherited test) and call (`shareable (Test::Case) -> Nil`; for data, the rows' labels and a call taking one). Neither is generic: the suites of several classes go in one array, which a `Suite[C]` would not allow (an array of `Suite[StackTest]` and `Suite[ParseTest]` is a union, not a `Suite[Case]`), so the generated lambdas cast the instance to the suite's class with `as`, which cannot fail. Both are Shareable, and their procedures `shareable`: the generated lambdas capture nothing, so they qualify, and a test can run in another task (§6). `Test.run` runs them, prints the report and exits with 1 when a test failed or errored (0 when every test passed, pending or omitted).
- The runner is generated after the test files are declared and checked (what inherits `Test::Case` is not visible syntactically: aliases, abstract bases), and added to the checked program as one more unit (`quarz_types::check_with_extra`), the way `Session::require` adds a file to the REPL's, rather than by checking everything twice. Its warnings are not shown (a test that always raises makes the `nil` after its call unreachable); its errors are reported on the test methods.
- A test runs as: `startup` once before the class's first test, then for each test a fresh instance, `setup`, the test, `teardown` (also after a failure or a timeout: it runs uncancellably, within a limit of its own, so a test takes at most twice the limit, three times (and up to twice 50ms) with the wait for the tasks it leaves (below); what goes wrong in it is reported as the teardown's, "teardown timed out after 60s" or "teardown: RuntimeError: ...", an error of a test that passed (a failure, for an assertion that failed in it), a line added to one that failed, and an error that keeps the reason of one pending or omitted), each test inside `Task.timeout(limit)`: a test that waits forever (a channel, a socket, a `sleep`) is an error ("Task::Timeout: timed out after 60s"), not a hung run; a loop that never waits still hangs the run, as it would any program ([04-concurrency.md](04-concurrency.md) §2). The timeout is `Task::Timeout`, a `StandardError`, so a `rescue => e` in the code under test can swallow it; the runner then reports the test as failed to end. The tasks a test leaves running (spawned with `Task.spawn` in it, its `setup` or its `teardown`, and those they spawn) are cancelled once its teardown is done and waited for, as a scope's children are (one they spawn as they are cancelled, as in an `ensure`, is cancelled in turn, and may run nothing; a `Task.timeout` block or scope in them is their own code, which ends with them), so that they cannot run into the next test (nor end the run with an `exit`, unless one exits as it is cancelled); those still running after the test's limit (one that cancelling does not end: `Task.uncancellable`, or a loop that never waits, which with one worker hangs the run instead) are an error of the test, "1 task left running after the test (cancelled, not ended within 60s)", and run on; a task started in `setup` is still there for `teardown`, and one a test starts for later tests (a service kept in a constant on first use) is cancelled too: start those in `startup`. `shutdown` after the class's last test.
- What a test raises other than `Test::AssertionFailed` is an **error** (E), with its class, message and backtrace. So is a test whose instance cannot be made (a field's initializer raised), a data-driven test whose `data_*` method raised, and every test of a class whose `startup` raised (its `shutdown` then does not run); a `shutdown` that raises is reported as an error of its own; the run goes on, and exits with 1. `DeadlockError` (every task waiting, no timer pending) ends the process, as it does in any program, and the runner cannot catch it; it does not happen while a test runs under its timeout, whose timer is pending, only with `--timeout=0`.
- Order: file order, then declaration order (Go, Zig). `--order=random` with `--seed=N` for finding order dependencies (the seed is printed; Test::Unit's default is alphabetical, Rust's and minitest's random).
- Output: Test::Unit's progress (`.` pass, `F` failure, `E` error, `P` pending, `O` omission), then the failures and errors in order, then the summary line. `-v` prints each test's name and time as it ends. What the tests print goes to STDOUT as it comes (there is no capture; §9).

Options:

| Option | Meaning |
|---|---|
| `-n NAME`, `--name=NAME` | Run the tests whose `Class#method` (or method, or `method[label]`) contains `NAME`; `/regexp/` for a pattern. May repeat |
| `-v`, `--verbose` | A line per test, with its time |
| `--list` | Print the tests and exit |
| `--order=defined\|random`, `--seed=N` | Order; `random` prints its seed |
| `--fail-fast` | Stop at the first failure or error |
| `--parallel[=N]` | Run tests in up to N tasks at once (§6; default 4) |
| `--timeout=DURATION` | The limit per test (`60s`; a class's `self.timeout` overrides; `0` for none) |
| `--release` | Compile the tests natively (`quarz build`) instead of interpreting; slower to start, faster to run |
| `--junit=PATH` | Also write a JUnit XML report (CI) |
| `--locked`, `--offline` | As for `quarz run`, for a cog's dependencies |

## 6. Parallel Tests

With `--parallel`, each test of a class is a task, up to N at once, and the classes run one after another, so that `startup`/`shutdown` run once per class, before its first and after its last test. This is safe for the program's own state, by the language: a test instance is confined to its task, and anything shared must be Shareable or an `Atom`. It is not safe for the process's state (the current directory, environment variables, files, ports), which the tests then share as they would in any parallel runner; a class whose tests must run alone sets `def self.serial? -> Bool = true` (its tests run one at a time, and no other test runs meanwhile). Output lines of parallel tests interleave by the scheduling. Parallel is not the default (Rust) because of this output and the process state; the gain is for suites heavy in IO or `sleep`, where a CPU-bound suite already uses the workers through the tests' own tasks... *(a `--parallel` default is a decision for later, once suites exist)*.

## 7. Helpers and Sharing

- Helper methods go in the test class, or in a module the test classes `include` (`module Factories; def user(name: String) -> User ... end; end`). A module may also carry `test_*` methods: they are tests of every class that includes it (Test::Unit allows this). A module whose methods assert includes `Test::Assertions` (`module Sizes; include Test::Assertions; def test_empty ... end; end`), as one does `Test::Unit::Assertions` in Ruby; the class that includes it still counts the assertions, since a module included both by `Test::Case` and by a module of a subclass stays below `Test::Case` in the ancestors ([02-types.md](02-types.md) §8).
- A base class of several test classes is declared `abstract class ApiTest < Test::Case`: its own `test_*` methods are not run on it (it has no instances), only on its concrete subclasses.
- Fixtures that cost: build them in `self.startup` into a constant-like `Atom`, or in `setup` when each test needs its own.
- There are no mocks or stubs: a dependency a test replaces is a parameter or a module type the test implements with a `data`/class of its own (the type system is nominal: the fake includes the module). This is the same answer as for Go.

## 8. A Script's Tests

A script's own tests live next to it, `foo_test.qz` with `require_relative "foo"`, and run with `quarz test foo_test.qz`. `quarz run foo_test.qz` runs the file's top-level statements only, and a test file has none: it prints nothing. The runner is added by `quarz test`, not by an `at_exit` of the library (Test::Unit's autorun), since nothing can list the tests at run time.

The language and its standard library are tested this way: `std/test/*_test.qz`, which `cargo test` runs with `quarz test std/test` interpreted, compiled (`--release`) and in parallel (`crates/quarz-cli/tests/std.rs`). What only a process shows (exit statuses, an unhandled error, a deadlock, arguments, standard output) and the checker's errors stay in Rust tests.

## 9. Later

- `Class[T]`, the type of a class object with its instance type, for `assert_raise[E](klass: Class[E]) -> E` and for `rescue` on a type parameter; `x.is_a?(klass)` with a `Class[T]` could then narrow to `T`.
- `capture_output { }` (what the block printed to STDOUT/STDERR, per task) needs the runtime to redirect a task's standard streams; `assert_output` with it.
- `helper!` to report a failure at a helper's caller (Go's `t.Helper()`).
- Benchmarks (`bench_*` methods, `quarz test --bench`, as Go), `--coverage`.
- A `test "description" do ... end` declaration inside a `Test::Case` (Zig's `test "name" {}`; Rails' `test "..."`), a grammar addition the compiler would name `test_description`.
- Assertions that show their expression (`expect(x == 1)` as in Swift Testing) need the compiler to pass the source text: possible later as a built-in.

## 10. Alternatives Not Adopted

- **`describe`/`it` (RSpec, Crystal's spec):** nested blocks registering at run time, with `should`/`expect(x).to eq(y)` matchers. It needs no reflection, so it would have been the path of least resistance, but Test::Unit's classes and methods fit a language of classes and typed methods: a test is a method, a fixture a field with a type, a helper a method, and the compiler finds and checks them.
- **Run-time discovery (`at_exit` autorun, `methods.grep(/^test_/)`):** Quarz has no reflection and adding it for this would cost every program a method table.
- **Attributes (`#[test]`, `@Test`):** Quarz has no attributes; the `test_` prefix on a method of a `Test::Case` is the convention, and the compiler can check it (a `test_*` method with the wrong shape is an error).
- **One class per file, test file inside the cog's module (Go's internal tests, Rust's `mod tests`):** a test that sees private details tempts to test them; the cog's module boundary is the API, and tests are its first user.
