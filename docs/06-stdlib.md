# Standard Library

日本語版: [06-stdlib.ja.md](06-stdlib.ja.md)

The names of built-in classes and methods follow Ruby. The differences boil down to three points: "no destructive methods (immutable types)," "operations that may return `nil` have a `?` variant," and "concurrency primitives are added."

## 1. Kernel (functions available at the top level)

`puts`, `print`, `p`, `pp`, `warn`, `raise`, `loop`, `sleep` (= `Task.sleep`), `spawn`, `select`, `exit`, `abort`, `at_exit`, `require`, `require_relative`, `gets?`, `rand`, `format`/`sprintf`, `Integer(...)`/`Float(...)`/`String(...)` (conversion; raises on failure).

`eval`, `send`, `binding`, `method`, `instance_eval`, `define_method`, `ObjectSpace`, `fork`, `system`/backticks (moved to `Process.run`) do not exist.

## 2. Object

`==`, `equal?`, `hash`, `to_s`, `inspect`, `class`, `is_a?`, `nil?`, `tap`, `then`, `dup` (mutable objects only), `as`, `as?`, `frozen?` (always true, for compatibility).

## 3. Numbers

- `Int` (arbitrary precision), `Float`, fixed-width `Int8`…`UInt64`, `Float32`. `Rational`/`Complex` via `require "rational"`/`"complex"`.
- `Int`: `+ - * / % ** divmod abs gcd lcm pow(mod) bit_length to_s(base) times upto downto step digits chr ord even? odd? zero? clamp` and so on, the same as Ruby. Overloads for mixed arithmetic such as `Int#/(Float) -> Float`.
- `Float`: `floor ceil round truncate nan? infinite? to_i to_r`. `Float::INFINITY`, `Float::NAN`.
- `Math`: `sqrt sin cos atan2 log exp hypot` etc. `Math::PI`, `Math::E`.
- `Random`: `Random.new(seed)`, `rand`, `bytes`. `Random::DEFAULT` has an independent seed per task.
- `Duration`: `100.ms`, `2.seconds`, `1.5.minutes`, `3.days` are provided as extensions on `Int`/`Float` (enabled with `using Duration::Literals`; `require "time"` does this automatically).
- `Time` (built in, immutable): `Time.now utc local at parse iso8601 monotonic`, `year month day hour min sec usec nsec wday yday`, `+`/`-` with a `Duration`, `-` between two times gives a `Duration`, `<=> == hash utc getlocal utc? utc_offset zone strftime iso8601 to_i to_f to_s inspect`.

## 4. Strings, Symbols, Byte Sequences

- `String` (immutable, UTF-8): `+ * % == <=> [] []? size bytesize chars bytes graphemes lines split scan match match? =~ sub gsub upcase downcase capitalize swapcase strip lstrip rstrip chomp chop start_with? end_with? include? index rindex center ljust rjust tr delete squeeze count reverse each_char each_line to_i to_f to_sym to_s inspect unpack encode format hex oct succ ord` …
- `String#[]` raises `IndexError` when out of range; `[]?` returns `nil`. `String#%` is formatting.
- `String::Builder`: `<< push append insert delete_at clear to_s size`. `String.build { |b| }`.
- `Symbol`: `to_s to_proc <=> size`.
- `Bytes` (immutable): `b"\x00\xff"` literals, `Bytes[1, 2]`, `Bytes.from(array)`, `Bytes.from_hex`, `size [] []? slice + <=> == hash each reverse hex to_a decode decode?` + Enumerable. `Bytes::Builder` (`<< push clear to_bytes`), `Bytes.build { |b| }`. `String#to_bytes`/`encode(encoding)` and `Bytes#decode(encoding)` convert between the two (UTF-8, ASCII, ISO-8859-1). `pack`/`unpack` live on `Bytes`.

## 5. Collections

### Enumerable[T] (module)

Available once you implement `abstract def each(&block: (T) -> Nil)`. The same set of methods as Ruby: `map select reject filter_map flat_map reduce inject sum min max min_by max_by sort sort_by group_by partition chunk_while each_slice each_cons each_with_index each_with_object with_index zip take drop take_while drop_while find find_index include? count tally uniq first first(n) to_a to_set to_h lazy any? all? none? one? cycle`.

Called without a block, they return `Enumerator[T]`. `Enumerator` is a closure (suspension of the internal iterator is implemented with a task) with `next`/`peek`/`rewind`. `lazy` builds a lazily evaluated chain as `Lazy[T]`.

### Array[out T] (immutable)

- Reading: `[] []? at fetch first first? last last? size empty? include? index rindex sample shuffle slice dig values_at each each_index reverse_each bsearch pack join to_a to_h` + Enumerable.
- Updating (returns a new value): `push pop shift unshift insert set delete delete_at delete_if compact flatten reverse rotate sort sort_by uniq + - * & | concat fill(new array) take drop slice`.
- `Array::Builder[T]` (mutable): the destructive API of Ruby's `Array`. `<< push pop shift unshift insert []= delete delete_at delete_if compact! flatten! reverse! rotate! sort! sort_by! uniq! map! select! reject! concat fill clear replace`. Made immutable with `to_a`/`freeze` (one time only).
- `Array.build { |b| }`, `Array.new(n) { |i| }`, `Array[Int].new`.

### Hash[K, out V] (immutable, insertion-ordered)

- Reading: `[] []? fetch key? value? keys values size empty? each each_pair each_key each_value dig to_a to_h invert min_by` + Enumerable (elements are `[K, V]` tuples).
- Updating: `put delete merge(&block) update(k) { |v| } select reject filter_map transform_values transform_keys compact sort_by group_by`.
- `Hash::Builder[K, V]`: `[]= store delete merge! update clear`. `Hash.build { |b| }`, `Hash.new` (no default value; defaults via `fetch(k, default)` or `fetch(k) { }`).
- `Hash#[]` raises `KeyError` for a missing key; `[]?` returns `nil`. There is no `default`/`default_proc`.

### Set[out T], Range[T], Tuple

- `Set`: `add delete include? | & - ^ subset? superset? size each to_a`. `Set::Builder`.
- `Range`: the same as Ruby (`each step include? cover? to_a size first last min max sum`).
- Tuple `[A, B]`: `[0]` (statically typed), `size`, `to_a`, multiple assignment, patterns.

## 6. Procs

- Proc types `(A...) -> R`. `call`, `()`, `.()`, `[]`, `curry`, `>>`, `<<`, `arity`.
- There are no `Method` objects. Instead of `obj.method(:foo)`, use `->(x) { obj.foo(x) }` or `obj.:foo` (method reference syntax; `&obj.:foo` passes it as a block).

## 7. Control and Errors

- Exception hierarchy: `Exception` > (`Task::Cancelled`, `NoMemoryError`, `SystemExit`, `SystemStackError`) / `StandardError` > (`ArgumentError`, `TypeError`, `IndexError` > `KeyError`, `RangeError`, `ZeroDivisionError`, `FrozenError`, `IOError`, `SystemCallError`, `RuntimeError`, `NoMatchingPatternError`, `Channel::Closed`, `Task::Timeout`, `DeadlockError`…).
- `Exception#message backtrace cause full_message`.
- `Result[T, E]` (enum): `Ok(value)`/`Err(error)`. `map`, `and_then`, `unwrap`, `unwrap_or`, `ok?`, `err?`. For error handling without exceptions.

## 8. Concurrency

`Task[T]`, `Scope`, `Channel[T]`, `Atom[T]`, `Supervisor`, `Task.scope`/`sleep`/`yield`/`timeout`/`blocking`/`current`/`check_cancel`, `select`. Details in [04-concurrency.md](04-concurrency.md).

## 9. IO and OS

- `IO`, `File`, `Dir`, `Socket` (`TCPSocket`, `TCPServer`, `UDPSocket`, `UNIXSocket`), `Process`, `Signal`, `ENV`, `ARGV`, `STDIN`/`STDOUT`/`STDERR`.
- The API is the same as Ruby (`File.read`, `File.open(path, "w") { |f| }`, `IO#gets?`, `each_line`, `write`, `puts`). All of it is asynchronous IO that only suspends the task.
- For operations that "return nil at EOF" such as `gets`/`read`, `gets?`/`read?` return `nil`, while `gets`/`read` raise `EOFError`.
- Handles are not Shareable and are owned by the task that created them.

## 10. Others (loaded with `require`)

`json` (`JSON.parse -> JSON::Value`, an enum of `Null | Boolean | Integer | Number | Text | List | Map` with accessors such as `as_s`, `as_i?` and `[]`; `JSON.generate`/`pretty_generate`, `to_json`; `JSON.decode[T](str)` decodes directly into `data`), `time` (`Time` and `Duration` are built in; `Date`), `set` (built in), `digest`, `base64`, `uri`, `net/http`, `csv`, `yaml`, `optparse`, `logger`, `test` (`Test::Unit`-style), `benchmark`, `ffi`.

## 11. Ruby Built-ins Not Provided

| Ruby | Reason / Replacement |
|---|---|
| `Thread`, `Mutex`, `Queue`, `ConditionVariable`, `Fiber`, `Ractor` | `Task`/`Channel`/`Atom` |
| `ObjectSpace`, `GC` | Unnecessary due to reference counting. The equivalent of `GC.stat` is `Runtime.stats` |
| `Binding`, `Method`, `UnboundMethod`, `Module#define_method` and other dynamic metaprogramming | For the sake of static definition |
| `Struct`, `OpenStruct`, `Data` | `data` |
| Monkey-patch-style extensions other than `Comparable#clamp` | `extension` |
| `Encoding` (multiple encodings) | `String` is fixed to UTF-8. `Bytes` + `Encoding.decode/encode` |
| Global variables such as `$stdout`, `$;`, `$,` | Constants / explicit arguments |
| `Kernel#eval`, `instance_eval`, `class_eval` | None |
| `Marshal` | `Serialize` module (auto-derived for `data`/`enum`) |
