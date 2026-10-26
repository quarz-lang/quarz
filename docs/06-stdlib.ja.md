# 標準ライブラリ

組み込みクラスの名前とメソッド名は Ruby に合わせます。違いは「破壊的メソッドがない(不変型)」「`nil` を返しうる操作には `?` 付きの版がある」「並行プリミティブが追加される」の 3 点に集約されます。

以下に挙げるものは、*予定* と注記したものを除きすべてプレリュード(`std/prelude.qz`)に存在します。プレリュードが正式な一覧です。組み込みメソッドはすべて型付きで宣言されているので、`quarz check` はそれらを把握しています。

## 1. Kernel(トップレベルで使える関数)

`puts`、`print`、`printf`、`p`、`pp`、`warn`、`raise`、`loop`、`sleep`(= `Task.sleep`)、`Task.spawn`、`exit`(Ruby と同じく `SystemExit` を投げるので `ensure` 節が実行される。他のタスクでは、Ruby のスレッドと同じくメインタスクも投げる)、`exit!`、`abort`、`at_exit`、`require`、`require_relative`、`gets`/`gets?`、`readline`、`readlines`、`rand`/`srand`、`format`/`sprintf`、`Integer(text, base = 10)`/`Float(...)`/`String(...)`(変換・失敗で例外)。

`eval`、`send`、`binding`、`method`、`instance_eval`、`define_method`、`ObjectSpace`、`fork`、`system`/バッククォート(`Process.run`/`Process.sh` に移動)はありません。

## 2. Object

`==`、`!=`、`equal?`、`hash`、`to_s`(Ruby と同じく、クラスのインスタンスではクラス名 `#<Point>`、例外ではメッセージ、`data` の値と enum のバリアントでは既定の `inspect` と同じ(トップレベルの `self` は `main`)。クラスが定義した `inspect` は呼ばない)、`inspect`、`class`(`name` を持つ `Class`)、`is_a?`(定数で書いた型なら絞り込み、`Class` の値なら実行時に判定)、`nil?`、`tap`、`then`、`dup`(配列や文字列などの組み込みの不変な値はそのまま返し、Builder とオブジェクトはコピーする)、`as`、`as?`、`frozen?`(偽になるのは Builder だけ)、`instance_exec`(レシーバ付きブロック `self.() -> R` を、そのオブジェクトを `self` にして実行。[01-syntax.ja.md](01-syntax.ja.md) §9 参照)。

`Comparable[T]` は `<=>` を定義したクラスに `< <= > >= between? clamp(min, max) clamp(range)` を与えます。

`Nil` は `to_a`、`&`、`|` を、`Bool` は `&`、`|`、`^` を持ちます。

## 3. 数値

- `Int`(64 ビット。溢れると `OverflowError`)、`Integer`(任意精度。`Int#to_integer`、`Integer#to_i`、`Integer.parse`)、`Float`。固定幅 `Int8`…`UInt64`、`Float32`、`Rational`/`Complex` は *予定*。
- `Int`: `+ - * / % ** -@ ~ & | ^ << >> <=> abs divmod fdiv ceildiv pow(exp) pow(exp, mod) gcd lcm bit_length n[bit] bit_set? allbits? anybits? nobits? to_s(base) to_i to_f chr ord even? odd? zero? positive? negative? integer? succ pred floor/ceil/round/truncate(digits) digits(base) times upto downto step`。`Int.sqrt(n)` は整数平方根。反復メソッドはブロックなしで `Enumerator` を返します。`Int#/(Float) -> Float` など混在演算の多重定義あり。
- `Float`: `floor ceil round truncate`(桁数指定可)、`divmod fdiv nan? infinite? finite? integer? next_float prev_float step to_i to_f`。`Float::INFINITY`、`NAN`、`EPSILON`、`MAX`、`MIN`、`DIG`。
- `Math`: `sqrt cbrt sin cos tan asin acos atan atan2 sinh cosh tanh asinh acosh atanh exp log log2 log10 log1p expm1 pow hypot floor ceil`。`Math::PI`、`Math::E`。
- `Random`: `Random.new(seed)` は独立した状態を持つ生成器(`seed`、`rand`、`bytes(n)`)。`Random.rand`、`Random.bytes`、`Random.new_seed` と `Kernel#rand`/`srand` は既定の生成器を使います。`rand` は引数なし(`[0, 1)` の Float)、Int または Float の上限、Int または Float の範囲を取ります。既定の生成器はスレッドごとなので、タスク間で共有されます。
- `Duration`: `100.ms`、`2.seconds`、`1.5.minutes`、`3.days`(`ms`、`seconds`、`minutes` は `Int` と `Float` に、`hours` と `days` は `Int` にだけある)。`+ - * <=> to_f to_ms to_s`。
- `Time`(組み込み、不変): `Time.now utc local at parse iso8601 monotonic`、`year month day hour min sec usec nsec wday yday`、`sunday?`…`saturday?`、`Duration` との `+`/`-`、時刻同士の `-` は `Duration`、`<=> == hash utc getlocal utc? utc_offset zone strftime iso8601 to_i to_f to_s inspect`。

## 4. 文字列・シンボル・バイト列

- `String`(不変、UTF-8): `+ * % == <=> [] []? slice size length bytesize empty? chars bytes codepoints graphemes lines(chomp:) split(sep, limit) scan match matches match? =~ sub gsub(置換文字列かブロック。`Regexp` を取る `gsub` は Hash も取る) partition rpartition upcase downcase capitalize swapcase strip lstrip rstrip chomp(suffix) chop delete_prefix delete_suffix start_with? end_with?(複数指定・Regexp) include? index rindex(開始位置・Regexp) casecmp casecmp? center ljust rjust tr delete squeeze count reverse insert prepend each_char each_line each_byte each_grapheme upto to_i(base) to_f to_sym to_s inspect encode to_bytes hex oct succ/next ord getbyte ascii_only?`。`pack`/`unpack` は `Bytes` 上に *予定*。
- `sub`/`gsub` は置換文字列を Ruby と同じく読みます。`\1`〜`\9` と `\k<name>` はグループ(マッチに加わらなかったものは空)、`\0` と `\&` はマッチ全体、`` \` `` と `\'` はその前と後、`\\` はバックスラッシュです。`$~` がないので、Crystal と同じく2引数のブロック(`gsub(/(\w)=(\w)/) { |s, m| "#{m[2]}=#{m[1]}" }`)はマッチした文字列の次に各マッチの `MatchData` を受け取ります。ブロックなしの `scan` はマッチ全体を返し(`Array[String]`)、ブロック付きでは各 `MatchData` も受け取るのでグループはそこから取ります。`matches` は各マッチを `MatchData` で返します(`Array[MatchData]`。Crystal の `scan` と同じ)。
- `s[index]`・`s[range]` は範囲外で `IndexError`、`s[/regexp/]` と `[]?` は `nil`。`s[start, length]` は部分文字列。`String#%` は書式(`"%05d" % 42`、`"%s %s" % [a, b]`)。
- `String::Builder`: `<< push append prepend insert delete_at replace reverse! clear to_s snapshot freeze size bytesize empty?`。`String.build { |b| }`。
- `Symbol`: `to_s to_sym <=> size length empty? upcase downcase capitalize succ start_with? end_with?`。`&:name` でメソッドをブロックとして渡せます。`to_proc` は *予定*。
- `Regexp`: リテラル `/.../imx`、`Regexp.new(source, options)`、`Regexp.escape`、`Regexp.union`。`match match? =~ source options names to_s inspect == hash`。`MatchData`: `[](番号または名前) captures named_captures names values_at to_a size pre_match post_match begin end to_s inspect`。Ruby と同じく、`^` と `$` は各行の先頭と末尾にマッチし(テキスト全体の先頭と末尾は `\A` と `\z`)、`m` は `.` を改行にもマッチさせます。`begin`/`end` はマッチに加わらなかったグループでは `nil` です(`Int?`)。違いが一つ残ります。空でないマッチで、テキスト末尾の改行の直後の `^` を必要とするもの(`"a\n"` に対する `/\n^/`)は、Ruby では見つかりませんが Quarz では見つかります(regex クレートには、それを見分ける先読みがありません)。`Regexp` を取る `split`・`rindex`・`rpartition` は Ruby に従います。フィールドの先頭での空マッチは区切りにならず、区切りのグループはその前のフィールドの後に入り、マッチが始まる最後の位置を探します。これも Ruby と同じく、名前付きグループのあるパターンは名前付きグループだけを取り込み(置換文字列の `\1` は空になります)、POSIX 文字クラス(`[[:alpha:]]`)は Unicode を対象にし、インラインの `m`(`(?m:.)`)は `.` を改行にもマッチさせます。
- `Bytes`(不変): `b"\x00\xff"` リテラル、`Bytes[1, 2]`、`Bytes.from(array)`、`Bytes.from_hex`、`size [] []? slice + <=> == hash each reverse hex to_a decode decode?` + Enumerable。`Bytes::Builder`(`<< push clear to_bytes`)、`Bytes.build { |b| }`。`String#to_bytes`(Ruby と同じ名前の `b` もある)/`encode(encoding)` と `Bytes#decode(encoding)` で相互変換する(UTF-8、ASCII、ISO-8859-1)。
- Bytes は String と同じ名前・引数・規則(Ruby の空マッチの扱い、行ごとのアンカー、置換文字列)で検索できる。`start_with? end_with? include? index rindex split partition rpartition =~ match match? matches scan sub gsub` が Bytes か Regexp を取る。位置はバイト単位、切り出した部分は Bytes、マッチは `Bytes::MatchData`(`MatchData` と同じメソッドを、Bytes とバイト位置で持つ)になる。Regexp は Bytes をバイト単位で検索する。Ruby の `/.../n` が ASCII-8BIT を検索するのと同じく、`.` は任意の1バイト、`\xFF` は 0xFF の1バイト、`\w`/`\d`/`\s` と POSIX クラスは ASCII だけを対象にする。Unicode が必要なパターン(`\p{L}`)は、Bytes に対しては ArgumentError になる。ASCII 以外の文字はその UTF-8 のバイト列を表し(`/é+/` は2バイトまとめて繰り返す)、文字クラスの中(`[é]`)では ArgumentError になる。Ruby でも `/[é]/n` は SyntaxError である。String は常に UTF-8 で、バイナリは Rust や Crystal と同じく Bytes で扱う。こうすると、二つを混ぜる誤りが Ruby の実行時の `Encoding::CompatibilityError` ではなく型エラーになる。(未決:String と Bytes のどちらにも使えるコードのための、共通のモジュールを用意するか。今はメソッドの形を揃え、内部の検索処理を共有しているだけ。)

## 5. コレクション

### Enumerable[T](モジュール)

`abstract def each(&: (T) -> Nil)` を実装すれば使えます。Ruby と同じメソッド群: `map collect flat_map collect_concat filter_map select filter find_all reject reduce inject(初期値あり・なし) sum(ブロック付き。Int または Float) min max minmax(比較可能な要素、または比較ブロック) min(n) max(n) min_by max_by sort(比較ブロック可) sort_by group_by partition chunk_while slice_when each_slice each_cons each_with_index each_with_object each_entry zip take drop take_while drop_while find detect find_index include? member? count(値またはブロック) tally tally_by uniq(ブロック可) first first(n) to_a entries to_set to_h(ブロック付き) lazy any? all? none? one? cycle reverse_each`。

`map`、`each_with_index`、`each_slice`、`each_cons`、`to_enum` はブロックなしで `Enumerator[T]` を返すので、`xs.each_with_index.map { |x, i| }` や `xs.map.with_index { |x, i| }` が書けます。`Enumerator` は `next peek rewind size each with_index(offset)` を持ち、それ自身 Enumerable です。Shareable ではありません(位置を持ち、受け手が可変なオブジェクトのこともあるため)。(`Enumerator#with_index` はブロックの結果を集めて返します。`map.with_index` に必要なためです)。`lazy` は今のところ何もしません。遅延評価の `Lazy[T]` は *予定*。

タプルのコレクションに対するブロックは分解して受け取れます: `hash.map { |k, v| }`、`xs.each_with_index.map { |x, i| }`。

### Array[out T](不変)

要素がすべて `Int` またはすべて `Float` の配列は要素を非ボックス化して保持します。観察できる違いはありません(`sort`、`min`、`max`、`include?`、`sum` は直接の経路を取ります)。

比較できる型を要素に持つ配列は `Comparable` で(`<=> < <= > >= between? clamp`)、Ruby と同じく要素ごとに比較します。要素が位置ごとに相手の要素と比較できるタプルも同じです。

- 読み出し: `[] []? at fetch(既定値またはブロック) first first? last last? size length empty? include? index rindex(値またはブロック) sample sample(n) shuffle slice take drop values_at bsearch each each_index reverse_each join(`* separator` も) to_a` + Enumerable。`each` はブロックなしで Enumerator を返します。
- 更新(新しい値を返す): `push(*values) pop shift unshift insert set delete delete_at delete_if keep_if compact flatten(depth) reverse rotate sort sort_by uniq fill product combination permutation + - * & | union intersection difference intersect? concat`。
- `Array::Builder[T]`(可変): Ruby の `Array` の破壊的 API。`<< push pop shift unshift insert []= [] []? [range] first(n) last(n) index include? delete delete_at delete_if keep_if compact! reverse! rotate! shuffle! sort!(比較ブロック可) sort_by! uniq! map! select! reject! concat fill replace slice! clear join each each_with_index` + Enumerable。`to_a`/`freeze` は中身をコピーせずに不変な配列として渡し、Builder は空になる(また詰められる)。`snapshot` は複製。
- `Array.build { |b| }`、`Array.new(n) { |i| }`、`Array[Int].new`。

### Hash[K, out V](不変・挿入順)

- 読み出し: `[] []? fetch(既定値またはブロック) dig(キー 1 つ。`[]?` と同じ) key? has_key? include? member? value? has_value? key keys values values_at fetch_values size length empty? each each_pair each_key each_value to_a to_h invert` + Enumerable(要素は `[K, V]` タプルなので `each { |k, v| }`、`map { |k, v| }`、`min_by { |k, v| }` …)。
- 更新: `put delete merge(&block) update(k) { |v| } select filter reject delete_if keep_if compact except slice transform_values transform_keys`。
- `Hash::Builder[K, V]`: `[]= store [] []? fetch delete key? has_key? include? value? keys values size length empty? clear merge!(ブロック可) update(k) { |v| } select! reject! delete_if keep_if transform_values! compact! replace each each_pair each_key each_value to_h snapshot freeze` + Enumerable。`Hash.build { |b| }`、`Hash.new`(既定値なし。既定値は `fetch(k, default)` や `fetch(k) { }` で)。
- `Hash#[]` は欠損キーで `KeyError`、`[]?` は `nil`。`default`/`default_proc` はありません。

### Set[out T]、Range[T]、Tuple

- `Set`: `Set[1, 2]`、`Set.new(array)`、`add add? delete merge include? member? | + & - ^ union intersection difference subset? superset? proper_subset? proper_superset? <= >= < > disjoint? intersect? select filter reject delete_if keep_if size length empty? each to_a` + Enumerable。`Set::Builder`: `<< add add? delete merge subtract select! reject! delete_if keep_if clear replace to_set freeze to_a` + Enumerable。
- `Range`: `each step reverse_each include? cover? to_a size`(`Int` の範囲のみ)`empty? first last(n) begin end exclude_end? min max sum` + Enumerable。`each` と `step` はブロックなしで Enumerator を返します。
- タプル `[A, B]`: `[0]`(型は静的)、`size`、`to_a`、多重代入、パターン。

## 6. 手続き

- 手続き型 `(A...) -> R`。`call`、`()`、`.()`、`[]`、`arity`。`curry`、`>>`、`<<` は *予定*(合成後のシグネチャを型検査器が付ける必要があります)。
- `Method` オブジェクトはありません。`obj.method(:foo)` の代わりに `->(x) { obj.foo(x) }` か `obj.:foo`(メソッド参照構文。`&obj.:foo` でブロックに渡せる)。

## 7. 制御・エラー

- 例外階層: `Exception` > (`Task::Cancelled`、`NoMemoryError`、`SystemExit`、`SystemStackError`、`DeadlockError`) / `StandardError` > (`ArgumentError`、`TypeError`、`IndexError` > `KeyError`、`RangeError` > `FloatDomainError`、`ZeroDivisionError`、`FrozenError`、`IOError` > `EOFError`、`SystemCallError`、`RuntimeError`、`NoMatchingPatternError`、`NotImplementedError`、`StopIteration`、`Channel::Closed`、`Task::Timeout`)。
- `Exception#message backtrace cause full_message`。例外は Ruby と同じく最初の `raise` のバックトレースを保ちます(タスク間で共有した例外も同じで、同時に raise したタスクのうちどれか 1 つが設定します)。`rescue` 節の中で投げられた例外と、節の中の `begin` で rescue された例外は、Ruby の `$!` と同じく、その節が処理している例外を `cause` に持ちます。ただし Ruby と違い、節から呼んだメソッドの中で投げられてそこで rescue された例外と、例外が通過中の `ensure` 節で投げられた例外は持ちません。
- `Result[T, E]`(enum): `Ok(value)`/`Err(error)`。`map`、`and_then`(別名 `flat_map`)、`unwrap`、`unwrap_or`、`ok?`、`err?`。例外を使わないエラー処理に。

## 8. 並行

`Task[T]`、`Scope`、`Channel[T]`、`Atom[T]`、`Task.scope`/`sleep`/`yield`/`timeout`/`blocking`/`current`/`check_cancel`/`uncancellable`、`Channel.select`/`select_loop`。詳細は [04-concurrency.ja.md](04-concurrency.ja.md)。`Supervisor` は *予定*。

## 9. IO・OS

- `IO`: `puts print printf write(*args) << gets gets? readline readlines read read(n) read? getc each_line flush close closed? eof? rewind tty? path`。`STDIN`/`STDOUT`/`STDERR` が標準ストリーム(`Process.stdin` なども同じ)。
- `File`: `File.open(path, mode) { |f| }`(モードは `r r+ w w+ a a+`。ブロック形式は後でファイルを閉じる)、`read read_bytes write append readlines(chomp:) each_line foreach exist? file? directory? symlink? readable? writable? executable? size mtime delete rename copy basename(path, suffix) dirname extname split join expand_path absolute_path`、`File::SEPARATOR`。
- `Dir`: `pwd getwd home tmpdir chdir(ブロック可) exist? empty? mkdir mkdir_p rmdir rm_rf entries children each_child glob(pattern, base:)`(`*`、`?`、`[...]`、`**`、`{a,b}`)。
- `Process`: `argv env pid clock stdin stdout stderr`。`Process.run(*command)` と `Process.sh(script)` は子プロセスを終了まで実行し、`success?` を持つ `Process::Output(status, stdout, stderr)` を返します。`ENV` と `ARGV` は定数。
- `gets`/`read` などの「EOF で nil」を返す操作は 2 種類あります。`gets?`/`read?` は `nil` を返し、`gets`/`read`/`readline` は `EOFError` を送出します。OS の失敗(ファイルがない、コマンドが見つからない)は `SystemCallError`、閉じたストリームの使用や読み込み専用ストリームへの書き込みは `IOError` です。
- ソケット(Ruby と同じく `require "socket"` で読み込む): 接続と待ち受けは `Socket` モジュールが受け持ち、ソケットそのもののクラスと組み合わせて使います。
  - `Socket.tcp(host, port, connect_timeout: nil)`(ブロック付きなら、ソケットをブロックに渡し、終わったら閉じる)は Happy Eyeballs(RFC 8305)で接続します。IPv6 と IPv4 のアドレスを同時に引き(IPv4 の答えが先なら、IPv6 の答えを最大 50 ms 待つ)、ファミリーを交互に、IPv6 から試します。試行が失敗するか 250 ms で接続しなければ、次の試行を始めます。最初に接続したものが勝ち、ほかは取り消されます。どれも接続できなければ最後の失敗(`SystemCallError`)を、アドレスのない名前なら `SocketError` を投げます。`connect_timeout` は全体の上限です(`Task::Timeout`)。`TCPSocket.new(host, port)` と `TCPSocket.open(host, port) { |s| }` も同じで、`TCPSocket.connect(address)` は一つのアドレスに接続します。
  - `Socket.tcp_server_loop([host,] port, on_error: nil) { |conn, peer| }` は取り消されるまで待ち受けます。接続ごとに専用のタスクでブロックに渡し(ブロックは Shareable な手続き、[02-types.ja.md](02-types.ja.md) §9)、ブロックが戻ったら閉じます。ブロックが投げた例外は `on_error`(`shareable (Exception, Socket::Address) -> Nil`)か STDERR に渡し、待ち受けは続けます。`Socket.accept_loop(server, on_error: nil) { }` は、既に待ち受けている `TCPServer` か `UNIXServer`(ポートを先に知れる: `TCPServer.new(0)`)で同じことをし、`Socket.unix_server_loop(path) { |conn| }` は UNIX ソケットで同じことをします。
  - `Socket.tcp_server([host,] port)`、`Socket.unix(path)`(ブロック付きも)、`Socket.unix_server(path)`。`Socket.getaddrinfo(host, port, family = nil)`(family は 4 か 6)は補助スレッドでアドレスを引きます。
  - アドレスは `Socket::Address` です(`data Address(host: String, port: Int)`、`host` は数値表記。`ipv6?` と、`127.0.0.1:80` や `[::1]:80` の形の `to_s` を持つ)。`local_address`、`remote_address`、`recvfrom` が返します。
  - `accept` を持つ `TCPServer.new([host,] port)`、`UDPSocket`(`bind connect send recv recv_bytes recvfrom recvfrom_bytes`)、パスで指定する `UNIXSocket`/`UNIXServer`。ソケットは `IO` なので `gets gets? read read(n) read? readline readlines each_line write << puts print printf eof? close closed?` がそのまま使え、加えて `readpartial readpartial? read_bytes close_write close_read` があります。`write` はバイナリ用に `Bytes` も受け取ります。
- これらはすべて呼び出したタスクだけを止めます([04-concurrency.ja.md](04-concurrency.ja.md) §6)。ソケットはスケジューラのリアクタで待ち、ファイル全体の操作、ディレクトリとメタデータの操作、子プロセスは補助スレッドで実行されます。開いた `File` と標準入力の読み書きも、バッファで済まないものは補助スレッドで行います。標準出力と標準エラーへの書き込みは同期処理です。`Signal.trap(:TERM) { }` はシグナルが届いたときにブロックをタスクで実行する。`Signal.trap(:INT, :ignore)`/`:default`、`Signal.list`([11-http.ja.md](11-http.ja.md) §5)。SIGPIPE は無視するので、閉じたソケットへの書き込みは `SystemCallError` になる。

## 10. その他(名指しすれば、または `require` で読み込む)

`json`(`JSON.parse -> JSON::Value`。`Null | Bool | Number | String | Array | Object` の enum で(名前は Rust の serde_json に合わせている)、`as_s`・`as_i?`・`[]` などのアクセサを持つ。`Number` は `Int`、`Integer`(`Int` に収まらない整数を桁を失わずに)、`Float` のどれかを持ち、`as_i`・`as_integer`・`as_f` でその型として取り出す。`as_i` は収まらなければ `OverflowError` を投げる。`JSON.generate`/`pretty_generate`、`to_json`)、`time`(何もしない。`Time` と `Duration` は組み込み)、`socket`(§9)、`http`(HTTP/1.1 サーバ。クライアントは後から: [11-http.ja.md](11-http.ja.md))、`test`(`quarz test` が実行する `Test::Unit` 風のテスト: [12-testing.ja.md](12-testing.ja.md))。`Set` は組み込みで、require する `set` ライブラリはない。*予定*: `data` へ直接デコードする `JSON.decode[T](str)`、`Date`、`digest`、`base64`、`uri`、`csv`、`yaml`、`optparse`、`logger`、`benchmark`、`ffi`。

## 11. Ruby の組み込みで提供しないもの

| Ruby | 理由 / 代替 |
|---|---|
| `Thread`、`Mutex`、`Queue`、`ConditionVariable`、`Fiber`、`Ractor` | `Task`/`Channel`/`Atom` |
| `ObjectSpace`、`GC` | 参照カウントのため不要。`GC.stat` 相当の、割り当て数などを返す `Runtime.stats` は*予定* |
| `Binding`、`Method`、`UnboundMethod`、`Module#define_method` ほか動的メタプログラミング | 静的化のため |
| `Struct`、`OpenStruct`、`Data` | `data` |
| `Comparable#clamp` 以外のモンキーパッチ的拡張 | `extension` |
| `Encoding`(多重エンコーディング) | `String` は UTF-8 固定。`Bytes` + `encode`/`decode` |
| `$stdout`、`$;`、`$,` などのグローバル変数 | 定数 / 明示的引数 |
| `Kernel#eval`、`instance_eval`、`class_eval` | なし |
| `Marshal` | `Serialize` モジュール(`data`/`enum` に自動導出)は*予定*。今は `to_json`/`JSON.parse` が使える |
