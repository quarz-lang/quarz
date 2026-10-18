# Standard Library

日本語版: [06-stdlib.ja.md](06-stdlib.ja.md)

The names of built-in classes and methods follow Ruby. The differences boil down to three points: "no destructive methods (immutable types)," "operations that may return `nil` have a `?` variant," and "concurrency primitives are added."

Everything listed below exists in the prelude (`std/prelude.qz`) unless it is marked *planned*. The prelude is the authoritative list: every built-in method is declared there with its type, so `quarz check` knows them all.

## 1. Kernel (functions available at the top level)

`puts`, `print`, `printf`, `p`, `pp`, `warn`, `raise`, `loop`, `sleep` (= `Task.sleep`), `spawn`, `select`, `exit`, `abort`, `at_exit`, `require`, `require_relative`, `gets`/`gets?`, `readline`, `readlines`, `rand`/`srand`, `format`/`sprintf`, `Integer(text, base = 10)`/`Float(...)`/`String(...)` (conversion; raises on failure).

`eval`, `send`, `binding`, `method`, `instance_eval`, `define_method`, `ObjectSpace`, `fork`, `system`/backticks (moved to `Process.run`/`Process.sh`) do not exist.

## 2. Object

`==`, `equal?`, `hash`, `to_s`, `inspect`, `class`, `is_a?`, `nil?`, `tap`, `then`, `dup` (mutable objects only), `as`, `as?`, `frozen?` (always true, for compatibility).

`Comparable[T]` gives `< <= > >= between? clamp(min, max) clamp(range)` to a class that defines `<=>`.

## 3. Numbers

- `Int` (arbitrary precision), `Float`. Fixed-width `Int8`…`UInt64`, `Float32` and `Rational`/`Complex` are *planned*.
- `Int`: `+ - * / % ** -@ ~ & | ^ << >> <=> abs divmod fdiv ceildiv pow(exp) pow(exp, mod) gcd lcm bit_length n[bit] bit_set? allbits? anybits? nobits? to_s(base) to_i to_f chr ord even? odd? zero? positive? negative? integer? succ pred floor/ceil/round/truncate(digits) digits(base) times upto downto step`. `Int.sqrt(n)` is the integer square root. The iteration methods return an `Enumerator` without a block. Overloads for mixed arithmetic such as `Int#/(Float) -> Float`.
- `Float`: `floor ceil round truncate` (with an optional number of digits), `divmod fdiv nan? infinite? finite? integer? next_float prev_float step to_i to_f`. `Float::INFINITY`, `NAN`, `EPSILON`, `MAX`, `MIN`, `DIG`.
- `Math`: `sqrt cbrt sin cos tan asin acos atan atan2 sinh cosh tanh asinh acosh atanh exp log log2 log10 log1p expm1 pow hypot floor ceil`. `Math::PI`, `Math::E`.
- `Random`: `Random.new(seed)` is a generator with its own state (`seed`, `rand`, `bytes(n)`); `Random.rand`, `Random.bytes`, `Random.new_seed` and `Kernel#rand`/`srand` use the default generator. `rand` takes no argument (a Float in `[0, 1)`), an Int or Float bound, or an Int or Float range. The default generator is per thread, so tasks share it.
- `Duration`: `100.ms`, `2.seconds`, `1.5.minutes`, `3.days` on `Int`/`Float`; `+ - * <=> to_f to_ms to_s`.
- `Time` (built in, immutable): `Time.now utc local at parse iso8601 monotonic`, `year month day hour min sec usec nsec wday yday`, `sunday?`…`saturday?`, `+`/`-` with a `Duration`, `-` between two times gives a `Duration`, `<=> == hash utc getlocal utc? utc_offset zone strftime iso8601 to_i to_f to_s inspect`.

## 4. Strings, Symbols, Byte Sequences

- `String` (immutable, UTF-8): `+ * % == <=> [] []? slice size length bytesize empty? chars bytes codepoints graphemes lines(chomp:) split(sep, limit) scan match match? =~ sub gsub (replacement, block or Hash) partition rpartition upcase downcase capitalize swapcase strip lstrip rstrip chomp(suffix) chop delete_prefix delete_suffix start_with? end_with? (several, or a Regexp) include? index rindex (start position, Regexp) casecmp casecmp? center ljust rjust tr delete squeeze count reverse insert prepend each_char each_line each_byte each_grapheme upto to_i(base) to_f to_sym to_s inspect encode to_bytes hex oct succ/next ord getbyte ascii_only?`. `pack`/`unpack` are *planned* on `Bytes`.
- `s[index]` and `s[range]` raise `IndexError` when out of range; `s[/regexp/]` and `[]?` return `nil`. `s[start, length]` is a slice. `String#%` is formatting (`"%05d" % 42`, `"%s %s" % [a, b]`).
- `String::Builder`: `<< push append prepend insert delete_at replace reverse! clear to_s snapshot freeze size bytesize empty?`. `String.build { |b| }`.
- `Symbol`: `to_s to_sym <=> size length empty? upcase downcase capitalize succ start_with? end_with?`. `&:name` passes a method as a block; `to_proc` is *planned*.
- `Regexp`: literals `/.../imx`, `Regexp.new(source, options)`, `Regexp.escape`, `Regexp.union`; `match match? =~ source options names to_s inspect == hash`. `MatchData`: `[] (index or name) captures named_captures names values_at to_a size pre_match post_match begin end to_s inspect`.
- `Bytes` (immutable): `b"\x00\xff"` literals, `Bytes[1, 2]`, `Bytes.from(array)`, `Bytes.from_hex`, `size [] []? slice + <=> == hash each reverse hex to_a decode decode?` + Enumerable. `Bytes::Builder` (`<< push clear to_bytes`), `Bytes.build { |b| }`. `String#to_bytes`/`encode(encoding)` and `Bytes#decode(encoding)` convert between the two (UTF-8, ASCII, ISO-8859-1).

## 5. Collections

### Enumerable[T] (module)

Available once you implement `abstract def each(&: (T) -> Nil)`. The same set of methods as Ruby: `map collect flat_map collect_concat filter_map select filter find_all reject reduce inject (with or without an initial value) sum (with a block, Int or Float) min max minmax (comparable elements, or a comparator block) min(n) max(n) min_by max_by sort (or a comparator block) sort_by group_by partition chunk_while slice_when each_slice each_cons each_with_index each_with_object each_entry zip take drop take_while drop_while find detect find_index include? member? count (with a value or a block) tally tally_by uniq (with a block) first first(n) to_a entries to_set to_h (with a block) lazy any? all? none? one? cycle reverse_each`.

`map`, `each_with_index`, `each_slice`, `each_cons` and `to_enum` return an `Enumerator[T]` without a block, so `xs.each_with_index.map { |x, i| }` and `xs.map.with_index { |x, i| }` work; `Enumerator` has `next peek rewind size each with_index(offset)` and is itself Enumerable. (`Enumerator#with_index` collects the block's results, which is what `map.with_index` needs.) `lazy` is a no-op for now: a lazily evaluated `Lazy[T]` is *planned*.

A block over a collection of tuples destructures them: `hash.map { |k, v| }`, `xs.each_with_index.map { |x, i| }`.

### Array[out T] (immutable)

- Reading: `[] []? at fetch (default or block) first first? last last? size length empty? include? index rindex (value or block) sample sample(n) shuffle slice take drop values_at bsearch each each_index reverse_each join (also `* separator`) to_a` + Enumerable. `each` returns an enumerator without a block.
- Updating (returns a new value): `push(*values) pop shift unshift insert set delete delete_at delete_if keep_if compact flatten(depth) reverse rotate sort sort_by uniq fill product combination permutation + - * & | union intersection difference intersect? concat`.
- `Array::Builder[T]` (mutable): the destructive API of Ruby's `Array`. `<< push pop shift unshift insert []= [] []? [range] first(n) last(n) index include? delete delete_at delete_if keep_if compact! reverse! rotate! shuffle! sort! (comparator block) sort_by! uniq! map! select! reject! concat fill replace slice! clear join each each_with_index` + Enumerable. Made immutable with `to_a`/`freeze` (one time only); `snapshot` copies.
- `Array.build { |b| }`, `Array.new(n) { |i| }`, `Array[Int].new`.

### Hash[K, out V] (immutable, insertion-ordered)

- Reading: `[] []? fetch (default or block) dig key? has_key? include? member? value? has_value? key keys values values_at fetch_values size length empty? each each_pair each_key each_value to_a to_h invert` + Enumerable (elements are `[K, V]` tuples, so `each { |k, v| }`, `map { |k, v| }`, `min_by { |k, v| }` …).
- Updating: `put delete merge(&block) update(k) { |v| } select filter reject delete_if keep_if compact except slice transform_values transform_keys`.
- `Hash::Builder[K, V]`: `[]= store [] []? fetch delete key? has_key? include? value? keys values size length empty? clear merge! (with a block) update(k) { |v| } select! reject! delete_if keep_if transform_values! compact! replace each each_pair each_key each_value to_h snapshot freeze` + Enumerable. `Hash.build { |b| }`, `Hash.new` (no default value; defaults via `fetch(k, default)` or `fetch(k) { }`).
- `Hash#[]` raises `KeyError` for a missing key; `[]?` returns `nil`. There is no `default`/`default_proc`.

### Set[out T], Range[T], Tuple

- `Set`: `Set[1, 2]`, `Set.new(array)`, `add add? delete merge include? member? | + & - ^ union intersection difference subset? superset? proper_subset? proper_superset? <= >= < > disjoint? intersect? select filter reject delete_if keep_if size length empty? each to_a` + Enumerable. `Set::Builder`: `<< add add? delete merge subtract select! reject! delete_if keep_if clear replace to_set freeze to_a` + Enumerable.
- `Range`: `each step reverse_each include? cover? to_a size empty? first last(n) begin end exclude_end? min max sum` + Enumerable; `each` and `step` return an enumerator without a block.
- Tuple `[A, B]`: `[0]` (statically typed), `size`, `to_a`, multiple assignment, patterns.

## 6. Procs

- Proc types `(A...) -> R`. `call`, `()`, `.()`, `[]`, `arity`. `curry`, `>>` and `<<` are *planned* (they need the checker to type the composed signature).
- There are no `Method` objects. Instead of `obj.method(:foo)`, use `->(x) { obj.foo(x) }` or `obj.:foo` (method reference syntax; `&obj.:foo` passes it as a block).

## 7. Control and Errors

- Exception hierarchy: `Exception` > (`Task::Cancelled`, `NoMemoryError`, `SystemExit`, `SystemStackError`, `DeadlockError`) / `StandardError` > (`ArgumentError`, `TypeError`, `IndexError` > `KeyError`, `RangeError` > `FloatDomainError`, `ZeroDivisionError`, `FrozenError`, `IOError` > `EOFError`, `SystemCallError`, `RuntimeError`, `NoMatchingPatternError`, `NotImplementedError`, `StopIteration`, `Channel::Closed`, `Task::Timeout`).
- `Exception#message backtrace cause full_message`.
- `Result[T, E]` (enum): `Ok(value)`/`Err(error)`. `map`, `and_then`, `unwrap`, `unwrap_or`, `ok?`, `err?`. For error handling without exceptions.

## 8. Concurrency

`Task[T]`, `Scope`, `Channel[T]`, `Atom[T]`, `Task.scope`/`sleep`/`yield`/`timeout`/`blocking`/`current`/`check_cancel`, `select`. Details in [04-concurrency.md](04-concurrency.md). `Supervisor` is *planned*.

## 9. IO and OS

- `IO`: `puts print printf write(*args) << gets gets? readline readlines read read(n) read? getc each_line flush close closed? eof? rewind tty? path`. `STDIN`/`STDOUT`/`STDERR` are the standard streams (also `Process.stdin` etc.).
- `File`: `File.open(path, mode) { |f| }` (modes `r r+ w w+ a a+`; the block form closes the file), `read read_bytes write append readlines(chomp:) each_line foreach exist? file? directory? symlink? readable? writable? executable? size mtime delete rename copy basename(path, suffix) dirname extname split join expand_path absolute_path`, `File::SEPARATOR`.
- `Dir`: `pwd getwd home tmpdir chdir (with a block) exist? empty? mkdir mkdir_p rmdir rm_rf entries children each_child glob(pattern, base:)` (`*`, `?`, `[...]`, `**`, `{a,b}`).
- `Process`: `argv env pid clock stdin stdout stderr`, `Process.run(*command)` and `Process.sh(script)` run a child process to completion and return `Process::Output(status, stdout, stderr)` with `success?`. `ENV` and `ARGV` are constants.
- Operations that "return nil at EOF" such as `gets`/`read` come in two forms: `gets?`/`read?` return `nil`, while `gets`/`read`/`readline` raise `EOFError`. Operating-system failures (a missing file, a command that is not found) raise `SystemCallError`; using a closed stream or writing to one opened for reading raises `IOError`.
- File IO is synchronous for now and blocks the scheduler while it runs; asynchronous IO that only suspends the task, `Socket` (`TCPSocket`, `TCPServer`, `UDPSocket`, `UNIXSocket`) and `Signal` are *planned*. File handles should be owned by the task that created them.

## 10. Others (loaded with `require`)

`json` (`JSON.parse -> JSON::Value`, an enum of `Null | Boolean | Integer | Number | Text | List | Map` with accessors such as `as_s`, `as_i?` and `[]`; `JSON.generate`/`pretty_generate`, `to_json`), `time` (a no-op: `Time` and `Duration` are built in), `set` (built in). *Planned*: `JSON.decode[T](str)` decoding directly into `data`, `Date`, `digest`, `base64`, `uri`, `net/http`, `csv`, `yaml`, `optparse`, `logger`, `test` (`Test::Unit`-style), `benchmark`, `ffi`.

## 11. Ruby Built-ins Not Provided

| Ruby | Reason / Replacement |
|---|---|
| `Thread`, `Mutex`, `Queue`, `ConditionVariable`, `Fiber`, `Ractor` | `Task`/`Channel`/`Atom` |
| `ObjectSpace`, `GC` | Unnecessary due to reference counting. The equivalent of `GC.stat` is `Runtime.stats` |
| `Binding`, `Method`, `UnboundMethod`, `Module#define_method` and other dynamic metaprogramming | For the sake of static definition |
| `Struct`, `OpenStruct`, `Data` | `data` |
| Monkey-patch-style extensions other than `Comparable#clamp` | `extension` |
| `Encoding` (multiple encodings) | `String` is fixed to UTF-8. `Bytes` + `encode`/`decode` |
| Global variables such as `$stdout`, `$;`, `$,` | Constants / explicit arguments |
| `Kernel#eval`, `instance_eval`, `class_eval` | None |
| `Marshal` | `Serialize` module (auto-derived for `data`/`enum`) |
