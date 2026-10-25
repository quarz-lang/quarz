# Standard Library

日本語版: [06-stdlib.ja.md](06-stdlib.ja.md)

The names of built-in classes and methods follow Ruby. The differences boil down to three points: "no destructive methods (immutable types)," "operations that may return `nil` have a `?` variant," and "concurrency primitives are added."

Everything listed below exists in the prelude (`std/prelude.qz`) unless it is marked *planned*. The prelude is the authoritative list: every built-in method is declared there with its type, so `quarz check` knows them all.

## 1. Kernel (functions available at the top level)

`puts`, `print`, `printf`, `p`, `pp`, `warn`, `raise`, `loop`, `sleep` (= `Task.sleep`), `Task.spawn`, `exit`, `abort`, `at_exit`, `require`, `require_relative`, `gets`/`gets?`, `readline`, `readlines`, `rand`/`srand`, `format`/`sprintf`, `Integer(text, base = 10)`/`Float(...)`/`String(...)` (conversion; raises on failure).

`eval`, `send`, `binding`, `method`, `instance_eval`, `define_method`, `ObjectSpace`, `fork`, `system`/backticks (moved to `Process.run`/`Process.sh`) do not exist.

## 2. Object

`==`, `!=`, `equal?`, `hash`, `to_s` (as in Ruby, the class name, `#<Point>`, for an instance of a class, an exception's message, and the default `inspect` of a `data` value or an enum variant (`main` for the top-level `self`); it does not call an `inspect` the class defines), `inspect`, `class` (a `Class`, with `name`), `is_a?`, `nil?`, `tap`, `then`, `dup` (returns a built-in immutable value such as an array or a string as it is, and copies builders and objects), `as`, `as?`, `frozen?` (false only for builders), `instance_exec` (runs a block with a receiver, `self.() -> R`, with `self` = the object; see [01-syntax.md](01-syntax.md) §9).

`Comparable[T]` gives `< <= > >= between? clamp(min, max) clamp(range)` to a class that defines `<=>`.

`Nil` has `to_a`, `&` and `|`; `Bool` has `&`, `|` and `^`.

## 3. Numbers

- `Int` (64-bit; overflow raises `OverflowError`), `Integer` (arbitrary precision; `Int#to_integer`, `Integer#to_i`, `Integer.parse`), `Float`. Fixed-width `Int8`…`UInt64`, `Float32` and `Rational`/`Complex` are *planned*.
- `Int`: `+ - * / % ** -@ ~ & | ^ << >> <=> abs divmod fdiv ceildiv pow(exp) pow(exp, mod) gcd lcm bit_length n[bit] bit_set? allbits? anybits? nobits? to_s(base) to_i to_f chr ord even? odd? zero? positive? negative? integer? succ pred floor/ceil/round/truncate(digits) digits(base) times upto downto step`. `Int.sqrt(n)` is the integer square root. The iteration methods return an `Enumerator` without a block. Overloads for mixed arithmetic such as `Int#/(Float) -> Float`.
- `Float`: `floor ceil round truncate` (with an optional number of digits), `divmod fdiv nan? infinite? finite? integer? next_float prev_float step to_i to_f`. `Float::INFINITY`, `NAN`, `EPSILON`, `MAX`, `MIN`, `DIG`.
- `Math`: `sqrt cbrt sin cos tan asin acos atan atan2 sinh cosh tanh asinh acosh atanh exp log log2 log10 log1p expm1 pow hypot floor ceil`. `Math::PI`, `Math::E`.
- `Random`: `Random.new(seed)` is a generator with its own state (`seed`, `rand`, `bytes(n)`); `Random.rand`, `Random.bytes`, `Random.new_seed` and `Kernel#rand`/`srand` use the default generator. `rand` takes no argument (a Float in `[0, 1)`), an Int or Float bound, or an Int or Float range. The default generator is per thread, so tasks share it.
- `Duration`: `100.ms`, `2.seconds`, `1.5.minutes`, `3.days` (`ms`, `seconds` and `minutes` on `Int` and `Float`; `hours` and `days` on `Int` only); `+ - * <=> to_f to_ms to_s`.
- `Time` (built in, immutable): `Time.now utc local at parse iso8601 monotonic`, `year month day hour min sec usec nsec wday yday`, `sunday?`…`saturday?`, `+`/`-` with a `Duration`, `-` between two times gives a `Duration`, `<=> == hash utc getlocal utc? utc_offset zone strftime iso8601 to_i to_f to_s inspect`.

## 4. Strings, Symbols, Byte Sequences

- `String` (immutable, UTF-8): `+ * % == <=> [] []? slice size length bytesize empty? chars bytes codepoints graphemes lines(chomp:) split(sep, limit) scan match matches match? =~ sub gsub (replacement or block; `gsub` with a `Regexp` also takes a Hash) partition rpartition upcase downcase capitalize swapcase strip lstrip rstrip chomp(suffix) chop delete_prefix delete_suffix start_with? end_with? (several, or a Regexp) include? index rindex (start position, Regexp) casecmp casecmp? center ljust rjust tr delete squeeze count reverse insert prepend each_char each_line each_byte each_grapheme upto to_i(base) to_f to_sym to_s inspect encode to_bytes hex oct succ/next ord getbyte ascii_only?`. `pack`/`unpack` are *planned* on `Bytes`.
- `sub`/`gsub` read a replacement string as Ruby does: `\1` to `\9` and `\k<name>` are groups (empty when a group took no part), `\0` and `\&` the match, `` \` `` and `\'` the text before and after it, `\\` a backslash. A block with two parameters (`gsub(/(\w)=(\w)/) { |s, m| "#{m[2]}=#{m[1]}" }`) receives the `MatchData` of each match after the matched text, as in Crystal, since there is no `$~`; `scan` without a block returns the whole matches (`Array[String]`), and its block also receives each `MatchData` for the groups; `matches` returns every match as a `MatchData` (`Array[MatchData]`, as Crystal's `scan` does).
- `s[index]` and `s[range]` raise `IndexError` when out of range; `s[/regexp/]` and `[]?` return `nil`. `s[start, length]` is a slice. `String#%` is formatting (`"%05d" % 42`, `"%s %s" % [a, b]`).
- `String::Builder`: `<< push append prepend insert delete_at replace reverse! clear to_s snapshot freeze size bytesize empty?`. `String.build { |b| }`.
- `Symbol`: `to_s to_sym <=> size length empty? upcase downcase capitalize succ start_with? end_with?`. `&:name` passes a method as a block; `to_proc` is *planned*.
- `Regexp`: literals `/.../imx`, `Regexp.new(source, options)`, `Regexp.escape`, `Regexp.union`; `match match? =~ source options names to_s inspect == hash`. `MatchData`: `[] (index or name) captures named_captures names values_at to_a size pre_match post_match begin end to_s inspect`. As in Ruby, `^` and `$` match at the start and end of every line (`\A` and `\z` at the text's), and `m` makes `.` match a newline too. `begin`/`end` give `nil` (`Int?`) for a group that took no part. One difference remains: a match that is not empty and needs `^` right after a newline ending the text (`/\n^/` on `"a\n"`) is found, where Ruby finds none (the regex crate has no lookahead to tell). `split`, `rindex` and `rpartition` with a Regexp follow Ruby: no empty field before an empty match where a field starts, a separator's groups after the field, and the last position a match starts at. As in Ruby too, a pattern with a named group captures with its named groups only (`\1` is then empty in a replacement), POSIX classes (`[[:alpha:]]`) are Unicode, and an inline `m` (`(?m:.)`) makes `.` match a newline.
- `Bytes` (immutable): `b"\x00\xff"` literals, `Bytes[1, 2]`, `Bytes.from(array)`, `Bytes.from_hex`, `size [] []? slice + <=> == hash each reverse hex to_a decode decode?` + Enumerable. `Bytes::Builder` (`<< push clear to_bytes`), `Bytes.build { |b| }`. `String#to_bytes` (also `b`, Ruby's name)/`encode(encoding)` and `Bytes#decode(encoding)` convert between the two (UTF-8, ASCII, ISO-8859-1).
- Bytes are searched as a String is, with the same names, arguments and rules (Ruby's empty matches, anchors per line, replacements): `start_with? end_with? include? index rindex split partition rpartition =~ match match? matches scan sub gsub`, with Bytes or a Regexp. Positions are byte offsets, the pieces are Bytes, and a match is a `Bytes::MatchData` (`MatchData`'s methods, with Bytes and byte offsets). A Regexp searches Bytes byte by byte, as Ruby's `/.../n` searches ASCII-8BIT: `.` is any byte, `\xFF` the byte 0xFF, `\w`/`\d`/`\s` and POSIX classes ASCII; a pattern that needs Unicode (`\p{L}`) is an ArgumentError there. A character beyond ASCII stands for its UTF-8 bytes (`/é+/` repeats both), and is an ArgumentError inside a class (`[é]`), as `/[é]/n` is a SyntaxError in Ruby. A String is always UTF-8: binary data is Bytes, as in Rust and Crystal, so that mixing the two is a type error rather than Ruby's `Encoding::CompatibilityError` at run time. (Open question: a module that String and Bytes would share for code written for either; for now their methods only have the same shapes, and the engine is shared underneath.)

## 5. Collections

### Enumerable[T] (module)

Available once you implement `abstract def each(&: (T) -> Nil)`. The same set of methods as Ruby: `map collect flat_map collect_concat filter_map select filter find_all reject reduce inject (with or without an initial value) sum (with a block, Int or Float) min max minmax (comparable elements, or a comparator block) min(n) max(n) min_by max_by sort (or a comparator block) sort_by group_by partition chunk_while slice_when each_slice each_cons each_with_index each_with_object each_entry zip take drop take_while drop_while find detect find_index include? member? count (with a value or a block) tally tally_by uniq (with a block) first first(n) to_a entries to_set to_h (with a block) lazy any? all? none? one? cycle reverse_each`.

`map`, `each_with_index`, `each_slice`, `each_cons` and `to_enum` return an `Enumerator[T]` without a block, so `xs.each_with_index.map { |x, i| }` and `xs.map.with_index { |x, i| }` work; `Enumerator` has `next peek rewind size each with_index(offset)` and is itself Enumerable; it is not Shareable (it has a position, and its receiver may be a mutable object). (`Enumerator#with_index` collects the block's results, which is what `map.with_index` needs.) `lazy` is a no-op for now: a lazily evaluated `Lazy[T]` is *planned*.

A block over a collection of tuples destructures them: `hash.map { |k, v| }`, `xs.each_with_index.map { |x, i| }`.

### Array[out T] (immutable)

An array whose elements are all `Int` or all `Float` keeps them unboxed; nothing observable depends on it (`sort`, `min`, `max`, `include?` and `sum` take the direct path).

An array of a comparable element type is `Comparable` (`<=> < <= > >= between? clamp`), comparing element by element as in Ruby; so is a tuple whose elements compare with the other's, position by position.

- Reading: `[] []? at fetch (default or block) first first? last last? size length empty? include? index rindex (value or block) sample sample(n) shuffle slice take drop values_at bsearch each each_index reverse_each join (also `* separator`) to_a` + Enumerable. `each` returns an enumerator without a block.
- Updating (returns a new value): `push(*values) pop shift unshift insert set delete delete_at delete_if keep_if compact flatten(depth) reverse rotate sort sort_by uniq fill product combination permutation + - * & | union intersection difference intersect? concat`.
- `Array::Builder[T]` (mutable): the destructive API of Ruby's `Array`. `<< push pop shift unshift insert []= [] []? [range] first(n) last(n) index include? delete delete_at delete_if keep_if compact! reverse! rotate! shuffle! sort! (comparator block) sort_by! uniq! map! select! reject! concat fill replace slice! clear join each each_with_index` + Enumerable. `to_a`/`freeze` hand the contents over as an immutable array without copying and leave the builder empty (it can be filled again); `snapshot` copies.
- `Array.build { |b| }`, `Array.new(n) { |i| }`, `Array[Int].new`.

### Hash[K, out V] (immutable, insertion-ordered)

- Reading: `[] []? fetch (default or block) dig (one key, like `[]?`) key? has_key? include? member? value? has_value? key keys values values_at fetch_values size length empty? each each_pair each_key each_value to_a to_h invert` + Enumerable (elements are `[K, V]` tuples, so `each { |k, v| }`, `map { |k, v| }`, `min_by { |k, v| }` …).
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
- `Exception#message backtrace cause full_message`. An exception keeps the backtrace of its first `raise`, as in Ruby (an exception shared by tasks too: of tasks raising it at once, one sets it).
- `Result[T, E]` (enum): `Ok(value)`/`Err(error)`. `map`, `and_then` (alias `flat_map`), `unwrap`, `unwrap_or`, `ok?`, `err?`. For error handling without exceptions.

## 8. Concurrency

`Task[T]`, `Scope`, `Channel[T]`, `Atom[T]`, `Task.scope`/`sleep`/`yield`/`timeout`/`blocking`/`current`/`check_cancel`, `Channel.select`/`select_loop`. Details in [04-concurrency.md](04-concurrency.md). `Supervisor` is *planned*.

## 9. IO and OS

- `IO`: `puts print printf write(*args) << gets gets? readline readlines read read(n) read? getc each_line flush close closed? eof? rewind tty? path`. `STDIN`/`STDOUT`/`STDERR` are the standard streams (also `Process.stdin` etc.).
- `File`: `File.open(path, mode) { |f| }` (modes `r r+ w w+ a a+`; the block form closes the file), `read read_bytes write append readlines(chomp:) each_line foreach exist? file? directory? symlink? readable? writable? executable? size mtime delete rename copy basename(path, suffix) dirname extname split join expand_path absolute_path`, `File::SEPARATOR`.
- `Dir`: `pwd getwd home tmpdir chdir (with a block) exist? empty? mkdir mkdir_p rmdir rm_rf entries children each_child glob(pattern, base:)` (`*`, `?`, `[...]`, `**`, `{a,b}`).
- `Process`: `argv env pid clock stdin stdout stderr`, `Process.run(*command)` and `Process.sh(script)` run a child process to completion and return `Process::Output(status, stdout, stderr)` with `success?`. `ENV` and `ARGV` are constants.
- Operations that "return nil at EOF" such as `gets`/`read` come in two forms: `gets?`/`read?` return `nil`, while `gets`/`read`/`readline` raise `EOFError`. Operating-system failures (a missing file, a command that is not found) raise `SystemCallError`; using a closed stream or writing to one opened for reading raises `IOError`.
- Sockets (`require "socket"`, as in Ruby): the `Socket` module connects and serves, with the classes of the sockets themselves:
  - `Socket.tcp(host, port, connect_timeout: nil)` (with a block: the socket is given to it and closed after) connects by Happy Eyeballs (RFC 8305): the IPv6 and IPv4 addresses are looked up at once (IPv4's answer waits up to 50 ms for IPv6's), tried alternating the families, IPv6 first, a new attempt started when one fails or has not connected in 250 ms; the first to connect wins and the others are cancelled. When none does, the last failure is raised (`SystemCallError`), or `SocketError` for a name with no address; `connect_timeout` bounds it all (`Task::Timeout`). `TCPSocket.new(host, port)` and `TCPSocket.open(host, port) { |s| }` are the same, and `TCPSocket.connect(address)` connects to one address.
  - `Socket.tcp_server_loop([host,] port, on_error: nil) { |conn, peer| }` serves until cancelled: each connection is handed to the block in a task of its own (the block is a shareable procedure, [02-types.md](02-types.md) §9) and closed when it returns; what the block raises goes to `on_error` (`shareable (Exception, Socket::Address) -> Nil`) or STDERR, and the server goes on. `Socket.accept_loop(server, on_error: nil) { }` does the same on a `TCPServer` or `UNIXServer` already listening (whose port is known first: `TCPServer.new(0)`), and `Socket.unix_server_loop(path) { |conn| }` on a UNIX socket.
  - `Socket.tcp_server([host,] port)`, `Socket.unix(path)` (with a block too), `Socket.unix_server(path)`; `Socket.getaddrinfo(host, port, family = nil)` (family 4 or 6) looks up addresses on a helper thread.
  - Addresses are `Socket::Address` (`data Address(host: String, port: Int)`, `host` numeric; `ipv6?`, and `to_s` as `127.0.0.1:80` or `[::1]:80`): `local_address`, `remote_address`, `recvfrom`.
  - `TCPServer.new([host,] port)` with `accept`, `UDPSocket` (`bind connect send recv recv_bytes recvfrom recvfrom_bytes`), `UNIXSocket`/`UNIXServer` by path. Sockets are `IO`s, so `gets gets? read read(n) read? readline readlines each_line write << puts print printf eof? close closed?` work on them, plus `readpartial readpartial? read_bytes close_write close_read`. `write` accepts `Bytes` for binary data.
- All of this only suspends the calling task (see [04-concurrency.md](04-concurrency.md) §6): sockets wait on the scheduler's reactor; whole-file, directory and metadata operations and child processes run on a helper thread, and so do the reads and writes of an open `File` or standard input that its buffer cannot serve. Writes to standard output and standard error are synchronous. `Signal.trap(:TERM) { }` runs a block on a task when a signal arrives, `Signal.trap(:INT, :ignore)`/`:default`, `Signal.list` ([11-http.md](11-http.md) §5); SIGPIPE is ignored, so writing to a closed socket raises `SystemCallError`.

## 10. Others (loaded when named, or with `require`)

`json` (`JSON.parse -> JSON::Value`, an enum of `Null | Bool | Number | String | Array | Object`, named as Rust's serde_json names them, with accessors such as `as_s`, `as_i?` and `[]`; a `Number` holds an `Int`, an `Integer` (an integer too large for an `Int`, kept exact) or a `Float`: `as_i`, `as_integer` and `as_f` give it as one, `as_i` raising `OverflowError` when it does not fit; `JSON.generate`/`pretty_generate`, `to_json`), `time` (a no-op: `Time` and `Duration` are built in), `socket` (§9), `http` (an HTTP/1.1 server, with a client to come: [11-http.md](11-http.md)). `Set` is built in; there is no `set` library to require. *Planned*: `JSON.decode[T](str)` decoding directly into `data`, `Date`, `digest`, `base64`, `uri`, `csv`, `yaml`, `optparse`, `logger`, `test` (`Test::Unit`-style, designed in [12-testing.md](12-testing.md)), `benchmark`, `ffi`.

## 11. Ruby Built-ins Not Provided

| Ruby | Reason / Replacement |
|---|---|
| `Thread`, `Mutex`, `Queue`, `ConditionVariable`, `Fiber`, `Ractor` | `Task`/`Channel`/`Atom` |
| `ObjectSpace`, `GC` | Unnecessary due to reference counting. A `Runtime.stats` with allocation counts, the equivalent of `GC.stat`, is *planned* |
| `Binding`, `Method`, `UnboundMethod`, `Module#define_method` and other dynamic metaprogramming | For the sake of static definition |
| `Struct`, `OpenStruct`, `Data` | `data` |
| Monkey-patch-style extensions other than `Comparable#clamp` | `extension` |
| `Encoding` (multiple encodings) | `String` is fixed to UTF-8. `Bytes` + `encode`/`decode` |
| Global variables such as `$stdout`, `$;`, `$,` | Constants / explicit arguments |
| `Kernel#eval`, `instance_eval`, `class_eval` | None |
| `Marshal` | A `Serialize` module (auto-derived for `data`/`enum`) is *planned*; `to_json`/`JSON.parse` work today |
