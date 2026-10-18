# 標準ライブラリ

組み込みクラスの名前とメソッド名は Ruby に合わせます。違いは「破壊的メソッドがない(不変型)」「`nil` を返しうる操作には `?` 付きの版がある」「並行プリミティブが追加される」の 3 点に集約されます。

## 1. Kernel(トップレベルで使える関数)

`puts`、`print`、`p`、`pp`、`warn`、`raise`、`loop`、`sleep`(= `Task.sleep`)、`spawn`、`select`、`exit`、`abort`、`at_exit`、`require`、`require_relative`、`gets?`、`rand`、`format`/`sprintf`、`Integer(...)`/`Float(...)`/`String(...)`(変換・失敗で例外)。

`eval`、`send`、`binding`、`method`、`instance_eval`、`define_method`、`ObjectSpace`、`fork`、`system`/バッククォート(`Process.run` に移動)はありません。

## 2. Object

`==`、`equal?`、`hash`、`to_s`、`inspect`、`class`、`is_a?`、`nil?`、`tap`、`then`、`dup`(可変オブジェクトのみ)、`as`、`as?`、`frozen?`(常に真、互換のため)。

## 3. 数値

- `Int`(任意精度)、`Float`、固定幅 `Int8`…`UInt64`、`Float32`。`Rational`/`Complex` は `require "rational"`/`"complex"`。
- `Int`: `+ - * / % ** divmod abs gcd lcm pow(mod) bit_length to_s(base) times upto downto step digits chr ord even? odd? zero? clamp` など Ruby と同じ。`Int#/(Float) -> Float` など混在演算の多重定義あり。
- `Float`: `floor ceil round truncate nan? infinite? to_i to_r`。`Float::INFINITY`、`Float::NAN`。
- `Math`: `sqrt sin cos atan2 log exp hypot` など。`Math::PI`、`Math::E`。
- `Random`: `Random.new(seed)`、`rand`、`bytes`。`Random::DEFAULT` はタスクごとに独立したシードを持つ。
- `Duration`: `100.ms`、`2.seconds`、`1.5.minutes`、`3.days` を `Int`/`Float` への拡張として提供(`using Duration::Literals` で有効化。`require "time"` が自動で行う)。
- `Time`(組み込み、不変): `Time.now utc local at parse iso8601 monotonic`、`year month day hour min sec usec nsec wday yday`、`Duration` との `+`/`-`、時刻同士の `-` は `Duration`、`<=> == hash utc getlocal utc? utc_offset zone strftime iso8601 to_i to_f to_s inspect`。

## 4. 文字列・シンボル・バイト列

- `String`(不変、UTF-8): `+ * % == <=> [] []? size bytesize chars bytes graphemes lines split scan match match? =~ sub gsub upcase downcase capitalize swapcase strip lstrip rstrip chomp chop start_with? end_with? include? index rindex center ljust rjust tr delete squeeze count reverse each_char each_line to_i to_f to_sym to_s inspect unpack encode format hex oct succ ord` …
- `String#[]` は範囲外で `IndexError`、`[]?` は `nil`。`String#%` は書式。
- `String::Builder`: `<< push append insert delete_at clear to_s size`。`String.build { |b| }`。
- `Symbol`: `to_s to_proc <=> size`。
- `Bytes`(不変): `b"\x00\xff"` リテラル、`Bytes[1, 2]`、`Bytes.from(array)`、`Bytes.from_hex`、`size [] []? slice + <=> == hash each reverse hex to_a decode decode?` + Enumerable。`Bytes::Builder`(`<< push clear to_bytes`)、`Bytes.build { |b| }`。`String#to_bytes`/`encode(encoding)` と `Bytes#decode(encoding)` で相互変換する(UTF-8、ASCII、ISO-8859-1)。`pack`/`unpack` は `Bytes` 上に。

## 5. コレクション

### Enumerable[T](モジュール)

`abstract def each(&block: (T) -> Nil)` を実装すれば使えます。Ruby と同じメソッド群: `map select reject filter_map flat_map reduce inject sum min max min_by max_by sort sort_by group_by partition chunk_while each_slice each_cons each_with_index each_with_object with_index zip take drop take_while drop_while find find_index include? count tally uniq first first(n) to_a to_set to_h lazy any? all? none? one? cycle`。

ブロックなしで呼ぶと `Enumerator[T]` を返します。`Enumerator` はクロージャ(内部イテレータの一時停止はタスクで実装)で、`next`/`peek`/`rewind` を持ちます。`lazy` は `Lazy[T]` で遅延評価のチェーンを作ります。

### Array[out T](不変)

- 読み出し: `[] []? at fetch first first? last last? size empty? include? index rindex sample shuffle slice dig values_at each each_index reverse_each bsearch pack join to_a to_h` + Enumerable。
- 更新(新しい値を返す): `push pop shift unshift insert set delete delete_at delete_if compact flatten reverse rotate sort sort_by uniq + - * & | concat fill(新しい配列) take drop slice`。
- `Array::Builder[T]`(可変): Ruby の `Array` の破壊的 API。`<< push pop shift unshift insert []= delete delete_at delete_if compact! flatten! reverse! rotate! sort! sort_by! uniq! map! select! reject! concat fill clear replace`。`to_a`/`freeze` で不変化(一回限り)。
- `Array.build { |b| }`、`Array.new(n) { |i| }`、`Array[Int].new`。

### Hash[K, out V](不変・挿入順)

- 読み出し: `[] []? fetch key? value? keys values size empty? each each_pair each_key each_value dig to_a to_h invert min_by` + Enumerable(要素は `[K, V]` タプル)。
- 更新: `put delete merge(&block) update(k) { |v| } select reject filter_map transform_values transform_keys compact sort_by group_by`。
- `Hash::Builder[K, V]`: `[]= store delete merge! update clear`。`Hash.build { |b| }`、`Hash.new`(既定値なし。既定値は `fetch(k, default)` や `fetch(k) { }` で)。
- `Hash#[]` は欠損キーで `KeyError`、`[]?` は `nil`。`default`/`default_proc` はありません。

### Set[out T]、Range[T]、Tuple

- `Set`: `add delete include? | & - ^ subset? superset? size each to_a`。`Set::Builder`。
- `Range`: Ruby と同じ(`each step include? cover? to_a size first last min max sum`)。
- タプル `[A, B]`: `[0]`(型は静的)、`size`、`to_a`、多重代入、パターン。

## 6. 手続き

- 手続き型 `(A...) -> R`。`call`、`()`、`.()`、`[]`、`curry`、`>>`、`<<`、`arity`。
- `Method` オブジェクトはありません。`obj.method(:foo)` の代わりに `->(x) { obj.foo(x) }` か `obj.:foo`(メソッド参照構文。`&obj.:foo` でブロックに渡せる)。

## 7. 制御・エラー

- 例外階層: `Exception` > (`Task::Cancelled`、`NoMemoryError`、`SystemExit`、`SystemStackError`) / `StandardError` > (`ArgumentError`、`TypeError`、`IndexError` > `KeyError`、`RangeError`、`ZeroDivisionError`、`FrozenError`、`IOError`、`SystemCallError`、`RuntimeError`、`NoMatchingPatternError`、`Channel::Closed`、`Task::Timeout`、`DeadlockError`…)。
- `Exception#message backtrace cause full_message`。
- `Result[T, E]`(enum): `Ok(value)`/`Err(error)`。`map`、`and_then`、`unwrap`、`unwrap_or`、`ok?`、`err?`。例外を使わないエラー処理に。

## 8. 並行

`Task[T]`、`Scope`、`Channel[T]`、`Atom[T]`、`Supervisor`、`Task.scope`/`sleep`/`yield`/`timeout`/`blocking`/`current`/`check_cancel`、`select`。詳細は [04-concurrency.ja.md](04-concurrency.ja.md)。

## 9. IO・OS

- `IO`、`File`、`Dir`、`Socket`(`TCPSocket`、`TCPServer`、`UDPSocket`、`UNIXSocket`)、`Process`、`Signal`、`ENV`、`ARGV`、`STDIN`/`STDOUT`/`STDERR`。
- API は Ruby と同じ(`File.read`、`File.open(path, "w") { |f| }`、`IO#gets?`、`each_line`、`write`、`puts`)。すべてタスクを止めるだけの非同期 IO です。
- `gets`/`read` などの「EOF で nil」を返す操作は `gets?`/`read?` が `nil` を返し、`gets`/`read` は `EOFError` を送出します。
- ハンドルは Shareable ではなく、作ったタスクが所有します。

## 10. その他(`require` で読み込む)

`json`(`JSON.parse -> JSON::Value`。`Null | Boolean | Integer | Number | Text | List | Map` の enum で、`as_s`・`as_i?`・`[]` などのアクセサを持つ。`JSON.generate`/`pretty_generate`、`to_json`。`JSON.decode[T](str)` で `data` へ直接デコード)、`time`(`Time` と `Duration` は組み込み。`Date`)、`set`(組み込み済み)、`digest`、`base64`、`uri`、`net/http`、`csv`、`yaml`、`optparse`、`logger`、`test`(`Test::Unit` 風)、`benchmark`、`ffi`。

## 11. Ruby の組み込みで提供しないもの

| Ruby | 理由 / 代替 |
|---|---|
| `Thread`、`Mutex`、`Queue`、`ConditionVariable`、`Fiber`、`Ractor` | `Task`/`Channel`/`Atom` |
| `ObjectSpace`、`GC` | 参照カウントのため不要。`GC.stat` 相当は `Runtime.stats` |
| `Binding`、`Method`、`UnboundMethod`、`Module#define_method` ほか動的メタプログラミング | 静的化のため |
| `Struct`、`OpenStruct`、`Data` | `data` |
| `Comparable#clamp` 以外のモンキーパッチ的拡張 | `extension` |
| `Encoding`(多重エンコーディング) | `String` は UTF-8 固定。`Bytes` + `Encoding.decode/encode` |
| `$stdout`、`$;`、`$,` などのグローバル変数 | 定数 / 明示的引数 |
| `Kernel#eval`、`instance_eval`、`class_eval` | なし |
| `Marshal` | `Serialize` モジュール(`data`/`enum` に自動導出) |
