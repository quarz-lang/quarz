# HTTP: サーバ

`require "http"` で `HTTP` モジュールが使えます。ソケット([06-stdlib.ja.md](06-stdlib.ja.md) §9)の上に Quarz で書いた HTTP/1.1 サーバで、Puma のようにリバースプロキシの後段でアプリケーションサーバとして使うことを想定しています。TLS の終端とクライアントとの HTTP/2 はプロキシが担い、サーバはプロキシと HTTP/1.1(keep-alive、chunked)で話します。クライアント `HTTP::Client` は、同じ要求・応答の型で後から提供します。どちらも Ruby の `net/http` の API は踏襲しません。

`std/http.qz`(と、いくつかのネイティブを使う prelude の `Signal`)に実装されています。§9 で後に回したものを除きます。

## 1. 形

```ruby
require "http"

handler = HTTP.handler do |req|
  HTTP::Response.text("hello #{req.path}")
end
HTTP::Server.new(handler, port: 8080).serve
```

- **ハンドラ**は `Request` を受けて `Response` を返します。Rack のアプリケーションと同じで、Go の `http.Handler` のように応答オブジェクトに書き込む形ではありません。Quarz の値は不変で、`data` の値を返すのが自然だからです。ハンドラは関数になるので、テストはソケットなしで呼べます。ストリーミングは応答本体の種類の一つ(§4)で、ハンドラの書き方が変わるわけではありません。
- サーバは接続 1 本につきタスク 1 つで動きます([04-concurrency.ja.md](04-concurrency.ja.md))。タスクは M:N でスケジュールされるので、大きさを決めるスレッドプールはなく、ワーカー数は `QUARZ_THREADS` で決まります。ハンドラは接続のタスクで実行されるので **Shareable** です。`HTTP::Handler` を include するクラスは `var` フィールドを持たず、要求の間で共有する状態は `Atom` か `Channel` に置きます。
- 待つ操作(要求の読み込み、応答の書き出し、ハンドラ自身の IO)はすべてそのタスクだけを止めます。タイムアウトは `Task.timeout`、サーバの停止はキャンセルです。

## 2. ハンドラとミドルウェア

```ruby
module HTTP
  module Handler
    include Shareable
    abstract def call(req: Request) -> Response
  end

  # 手続きからハンドラを作る(値で捕捉します。[02-types.ja.md](02-types.ja.md) §9)
  def self.handler(&f: shareable (Request) -> Response) -> Handler
end
```

ミドルウェアは、次のハンドラを持つハンドラです。`data` はフィールドが Shareable なら Shareable で、`Handler` はそうです(Builder などの可変なオブジェクトを持つミドルウェアはエラーです)。

```ruby
data Logging(inner: HTTP::Handler)
  include HTTP::Handler
  def call(req: HTTP::Request) -> HTTP::Response
    started = Time.monotonic
    res = inner.call(req)
    STDERR.puts "#{req.method} #{req.target} #{res.status} #{Time.monotonic - started}"
    res
  end
end
```

## 3. 要求

```ruby
module HTTP
  data Request(
    method: String,                 # "GET"。クライアントが送ったトークンそのもの(Symbol ではない)
    target: String,                 # 要求行のターゲットそのまま: "/users/1?x=1"
    path: String,                   # パーセントデコード済みのパス: "/users/1"
    query: String,                  # "x=1"(なければ "")
    version: String,                # "HTTP/1.1" か "HTTP/1.0"
    headers: Headers,
    body: Body,
    remote_address: Socket::Address?,   # UNIX ソケットでは nil
    params: Hash[String, String],   # ルータが束縛したパスパラメータ(§6)。それ以外では空
    proxies: Proxies,               # サーバが信頼するプロキシ
    trusted: Bool                   # 相手がそれかどうか
  )
    def host -> String?                              # Host ヘッダ
    def content_length -> Int?
    def query_params -> Hash[String, Array[String]]  # デコード済み。同じキーが繰り返されうる
    def form_params -> Hash[String, Array[String]]   # application/x-www-form-urlencoded の本体
    def scheme -> String                             # "http"、または信頼するプロキシからの X-Forwarded-Proto
    def remote_ip -> String?                         # remote_address.host、または信頼するプロキシからの X-Forwarded-For のクライアント
    def keep_alive? -> Bool
  end
end
```

`Request` は `data` の値です。ルータは `req.with(params: ...)` で要求を作り、テストは `HTTP::Request.get("/users/1", headers)`、`HTTP::Request.post("/users", body, headers)`(`head`、`delete`、`put`、`patch` も)、`HTTP::Request.build(method, target, headers, body)` で組み立てます。`Body` が Shareable でないので `Request` も Shareable ではありません。ハンドラが別のタスクに仕事を渡すときは、必要なフィールドを先に取り出します(`spawn` のブロックの前に `path = req.path`)。

### 本体

本体はハンドラが求めたときにソケットから読むので、`Body` は接続のタスクに閉じたクラスです(Shareable ではありません)。

```ruby
class Body
  def read -> String                   # 全体。max_body_bytes を超えると HTTP::PayloadTooLarge
  def read_bytes -> Bytes
  def each_chunk(&: (Bytes) -> Nil) -> Nil   # 届いた分ずつ。上限なし
  def read_chunk(max: Int = 16_384) -> Bytes # 次の一片(終わりでは空)
  def size -> Int?                     # Content-Length があれば
  def consumed? -> Bool                # 末尾まで読んだかどうか
end
```

`Content-Length` と `Transfer-Encoding: chunked` の両方を復号します。どちらもない要求の本体は空です。`Expect: 100-continue` には、ハンドラが最初に読むときに `100 Continue` を返します。`Content-Length` の本体のうちハンドラが読まなかった分は、残りが 64 KiB 以下なら、戻った後に読み捨てます(読み取りごとに `read_timeout`)。接続を再利用するためです。それ以外のとき(chunked の本体、残りが多い、フレーミングが壊れた、送られなかった `100 Continue` をクライアントが待っている)は、応答の後に接続を閉じます。本体の読み取りが失敗した(フレーミングの誤り、`read_timeout`)ときも、応答の後に接続を閉じます。

### ヘッダ

```ruby
data Field = (name: String, value: String)        # 名前は小文字

data Headers(entries: Array[Field])               # 順序を保ち、同じ名前が繰り返されうる
  def self.empty -> Headers
  def self.of(pairs: Hash[String, String]) -> Headers
  def [](name: String) -> String?                    # 最初の値
  def all(name: String) -> Array[String]
  def key?(name: String) -> Bool
  def put(name: String, value: String) -> Headers    # その名前の値をすべて置き換える
  def add(name: String, value: String) -> Headers    # 1 つ足す
  def delete(name: String) -> Headers
  def each(&: (String, String) -> Nil) -> Nil
  def size -> Int
  def token?(name: String, token: String) -> Bool   # `Connection: keep-alive, Upgrade` は `upgrade` を持つ
end
```

名前は大文字小文字を区別しません。小文字で保持し、出力は慣用の形(`Content-Type`)で書きます。値は受け取ったままで、前後の空白だけ取り除きます。`put`、`add`、`of`(したがって `Response#header` と `Response.redirect`)は、トークンでない名前や、CR や LF など HTAB 以外の制御文字を含む値に対して、ヘッダを設定するその場で `ArgumentError` を投げます。そのようなヘッダは応答を分割してしまうからです(応答分割)。

## 4. 応答

```ruby
module HTTP
  data Response(status: Int, headers: Headers, body: ResponseBody)   # 生成される `new` は ResponseBody を取る
    def self.empty(status: Int = 204, headers: Headers = Headers.empty) -> Response
    def self.text(body: String, status: Int = 200) -> Response            # text/plain; charset=utf-8
    def self.html(body: String, status: Int = 200) -> Response
    def self.json(value: JSON::Value, status: Int = 200) -> Response      # application/json
    def self.bytes(body: Bytes, content_type: String, status: Int = 200) -> Response
    def self.redirect(location: String, status: Int = 302) -> Response
    def self.not_found(message: String = "Not Found") -> Response
    def self.stream(status: Int = 200, headers: Headers = Headers.empty,
                    &write: shareable (BodyWriter) -> Nil) -> Response
    def header(name: String, value: String) -> Response                   # with(headers: headers.put(...))
    def reason -> String                                                  # 200 なら "OK"
  end

  enum ResponseBody
    variant Empty
    variant Text(text: String)
    variant Binary(bytes: Bytes)
    variant Stream(write: shareable (BodyWriter) -> Nil)
  end

  # Stream 本体の手続きに渡される。`write` 1 回が 1 チャンクとして送られる
  class BodyWriter
    def write(data: String) -> Nil
    def write(data: Bytes) -> Nil
    def flush -> Nil
  end
end
```

本体から決まるものはサーバが付けます。`Text`、`Binary`、`Empty` には `Content-Length`、`Stream` には `Transfer-Encoding: chunked`(HTTP/1.0 のクライアントには `Stream` を枠なしで送って接続を閉じます)、それに `Date` です。フレーミングはサーバのものです。ハンドラが付けた `Transfer-Encoding` は捨て、`Content-Length` は `HEAD` 要求と `304` の応答でだけ残します(`GET`/`200` が送るはずの大きさを表します)。`204` の応答にはどちらも付けず、本体も送りません。`HEAD` 要求と `304` の応答には本体を送らず(`Stream` の手続きは実行しません)、`304` には自分の `Content-Length` を付けません。ハンドラの状態は 200 から 599 の最終応答でなければならず、それ以外は `500` で応答します(中間応答は接続の同期を崩すため)。`Stream` の手続きはヘッダを送った後、接続のタスクで動くので、クライアントがつながっている限り続けられます(server-sent events)。`write_timeout` はチャンクごとに効きます。

## 5. サーバ

```ruby
module HTTP
  class Server
    include Shareable                 # Signal.trap のブロックや他のタスクが持つ。状態は Atom と Channel に置く
    def self.new(handler: Handler, *,             # すぐに束縛する。local_address がポートを返す
                 host: String = "0.0.0.0", port: Int = 8080,
                 read_header_timeout: Duration = 10.seconds,   # 要求の最初のバイトからヘッダの終わりまで
                 idle_timeout: Duration = 60.seconds,          # 保持した接続で次の要求を待つ時間
                 read_timeout: Duration = 30.seconds,          # 要求の本体の読み取り 1 回ごと(過ぎると 408)
                 write_timeout: Duration = 30.seconds,         # 応答 1 本、またはストリームのチャンク 1 つ
                 max_header_bytes: Int = 65_536,               # 要求行とヘッダを合わせて
                 max_body_bytes: Int = 1_048_576,              # Body#read と read_bytes が受け付ける大きさ
                 max_connections: Int = 10_000,                # 同時に受け付ける数。超えると accept が待つ
                 trusted_proxies: Array[String] = [],          # X-Forwarded-* を信じる相手
                 on_error: (shareable (Exception, Request?) -> Nil)? = nil) -> Server
    def self.unix(handler: Handler, path: String, *, ...同じオプション...) -> Server   # UNIX ソケット
    def serve -> Nil                      # shutdown かキャンセルまで受け付ける
    def local_address -> Socket::Address  # 実際に束縛したポート(`port: 0` なら空いているもの)
    def shutdown(timeout: Duration = 30.seconds) -> Nil   # 停止を始めてすぐ戻る
    def wait -> Nil                       # serve が戻るまで待つ
  end

  def self.serve(port: Int = 8080, host: String = "0.0.0.0",
                 &handler: shareable (Request) -> Response) -> Nil
end
```

接続のタスクは次のことをします。

1. 要求行とヘッダを読みます。最初の要求は、始まるまでに `read_header_timeout`、最初のバイトから終わりまでにもう一度同じ時間です。同じ接続の次以降の要求は、始まるまでに `idle_timeout`、終わりまでに `read_header_timeout` です。`max_header_bytes` を超えれば `431`、形式が壊れていれば `400` で、どちらも接続を閉じます。
2. `Request` を組み立ててハンドラを呼びます。ハンドラが投げた `HTTP::Error` はその状態で応答し(§7)、それ以外の `StandardError` は本体のない `500` になって、要求と一緒に `on_error` へ(なければ STDERR へ)渡します。`Task::Cancelled` は捕まえません。ヘッダの名前がトークンでないか、値に CR や LF など HTAB 以外の制御文字を含む応答は送らず、これも `500` にします(応答分割を防ぐため。`Headers#put` と `add` がすでに拒むので、ここに届くのは `Field.new` で作ったフィールドだけです)。それ以外の失敗(ヘッダを送った後に例外を投げる `Stream` の手続き)はその接続を終えて報告し、サーバは続けます。
3. 応答を `write_timeout` の内に書き、§3 のとおり読み捨てるか閉じます。
4. 要求か応答が `Connection: close` と言った場合、要求が `Connection: keep-alive` のない HTTP/1.0 だった場合、本体を読み捨てられなかった場合を除いて、接続を保ちます。HTTP/1.0 の接続を保つのは応答に `Content-Length` があるときだけで、そのとき応答に `Connection: keep-alive` を付けます。`Transfer-Encoding` を持つ HTTP/1.0 の要求には応答してから接続を閉じます(RFC 9112 §6.1)。

前段のプロキシと要求の読み方が食い違いうるところでは、パーサは厳格です(RFC 9112 が許すより厳しい点が 2 つあります。フィールドの値は UTF-8 でなければならず obs-text は使えません。チャンク拡張の `;` の前には空白を置けません)。要求行は単一の空白で区切った `method SP target SP version` で、ターゲットに制御文字を含められません。フィールドの値は HTAB 以外の制御文字を含められません。チャンクのサイズ行とデータは CRLF で終わります。要求の前の空行は `max_header_bytes` に数え、トレーラーは 8 KiB までです。

1 本の接続の要求は順に 1 つずつ処理します(パイプラインされた要求は届いた順に読み、並行には処理しません)。接続はそれぞれ別のタスクなので、遅いハンドラが止めるのは自分の接続だけです。

受け付けのループはサーバ自身のもので、`Socket.accept_loop` と同じ形です。`max_connections` 個のトークンを持つ `Channel` からトークンを 1 つ取り(なければ待ち、クライアントはカーネルのバックログに並びます)、`accept` して、接続のタスクをサーバのスコープに生成します。タスクは終わるときにトークンを返します。`shutdown` がリスナーを閉じるとループが終わります(待っている `accept` が `IOError` を投げます)。開いている接続は `Atom` に登録し、`shutdown` が待機中のものを見つけられるようにします。`accept` の失敗(fd の枯渇、`SystemCallError`)は記録して少し待ってから再試行します。サーバはそれで死にません。

UNIX ソケットのサーバ(`Server.unix`)には相手のアドレスがありません。`remote_address` は nil で、相手は信頼するプロキシとみなすので、`remote_ip` と `scheme` は `X-Forwarded-*` ヘッダから取り、なければ nil と `"http"` です。

### プロキシの後段で

`trusted_proxies: ["127.0.0.1", "::1"]`(アドレス、または `"10.0.0.0/8"` のようなネットワーク)を指定すると、そこからの要求では `scheme` を `X-Forwarded-Proto` から、`remote_ip` を `X-Forwarded-For` から取ります。同名のヘッダの値を順につなぎ、右から見て信頼するプロキシを飛ばし、最初に現れるそれ以外のアドレスがクライアントです。なければ(ヘッダがない、壊れている、すべて信頼するプロキシ)、`remote_ip` は相手のアドレスです。それ以外の相手からのこれらのヘッダは無視します。`Host` は受け取ったまま渡します。プロキシが設定するものだからです。

### 停止とシグナル

`shutdown` は受け付けをやめ、要求を待っている接続を閉じ(読み手には `IOError`。04-concurrency §6)、ハンドラの中にいる接続は終わるのを待ち、`timeout` を過ぎたらキャンセルします(次に待つところで `Task::Cancelled`)。その後 `serve` が戻ります。`shutdown` は停止を始めたら戻るので、ハンドラから呼べます。`serve` が戻るのを待つには `wait` を使います。`serve` の前に `shutdown` すると、`serve` はすぐに戻ります。受け付けたがまだ 1 バイトも送っていない接続は待機中とみなし、閉じます。`Signal` はこの作業で、これに必要な分を加えます。

```ruby
server = HTTP::Server.new(handler, port: 8080)
Signal.trap(:TERM) { server.shutdown }
Signal.trap(:INT) { server.shutdown(timeout: 1.second) }
server.serve
```

- `Signal.trap(name) { }`(`Symbol` か `String`。`SIG` は付けても付けなくてもよい)は、シグナルが届いたときにブロックを専用のタスクで実行します(シグナルハンドラの中ではありません。ハンドラはシグナルの番号をソケットペアに書くだけで、ランタイムのタスクがそれを読みます)。ブロックは値で捕捉します。同じシグナルに複数の trap があれば、それぞれを別のタスクで実行します。`Signal.trap(name, :default)` で既定の動作に戻し(`PIPE` は無視したままで、戻せません)、`Signal.trap(name, :ignore)` で無視します。シグナルは `TERM`、`INT`、`HUP`、`USR1`、`USR2`、`QUIT`、`PIPE` です(`SIGPIPE` は `quarz run` でもコンパイルしたプログラムでも最初から無視し、閉じたソケットへの書き込みは代わりに `SystemCallError` になります)。例外を投げた trap のブロックは、それを STDERR に報告します。`Signal.list` が名前を返します。

## 6. ルータ

Go の `ServeMux` と同じく、小さなルータをライブラリに含めます。制約や正規表現、型付きのパラメータを持つパターンは cog に任せます。

```ruby
router = HTTP::Router.build do |r|
  r.get("/users/{id}") { |req| HTTP::Response.json(user_json(req.params["id"])) }
  r.post("/users", CreateUser.new(db))           # Handler でもブロックでも
  r.get("/files/{path...}") { |req| serve_file(req.params["path"]) }
  r.mount("/admin", admin_router)                # 別の Router を接頭辞の下に
  r.not_found { |req| HTTP::Response.not_found }
end
```

- パターンはセグメントからなるパスです。`{name}` はセグメント 1 つに、最後に置く `{name...}` はスラッシュを含む残り全体(空でもよい。`/files/{p...}` は `/files/` に一致し、`/files` には一致しません)に一致します。残りはデコードしたセグメントを `/` でつないだもので、`..` のセグメントもそのまま残るので、ファイルに対応させるハンドラは確かめる必要があります。それ以外は完全一致で、末尾のスラッシュは区別します。要求のパスはパーセントデコードの前にセグメントへ分けるので、エスケープされた `%2F` はセグメントを分けません(Go の `ServeMux` と同じ)。一致したパターンのうち最も特定的なものが勝ちます。左からセグメントごとに比べ、一方がリテラルで他方がパラメータである最初のセグメントでリテラルの側が勝ち、`{name}` は `{name...}` に勝ちます。同じメソッドで、同じパスに同じ特定度で一致する 2 つのパターンは `build` でエラーです。
- 他のメソッドにだけ登録されたパターンに一致するパスには `Allow` 付き(`GET` があれば `HEAD` も挙げる)の `405 Method Not Allowed` を返します。`HEAD` は `GET` のルートで処理します。`OPTIONS` は特別扱いしません。
- `mount` は接頭辞を相手のルータのパターンの前に付けます(なので、マウントした `/` は `/admin/` で、`/admin` ではありません)。両方のパラメータが `params` に入り、マウントしたルータの `not_found` は使いません。
- `Router` は `Handler` です(一度組み立てた `data` の値で、Shareable)。だからルータは入れ子にでき、ミドルウェアで包めます。

## 7. エラー

- `HTTP::Error < StandardError` と、その下の `HTTP::BadRequest`、`HTTP::PayloadTooLarge`、`HTTP::HeadersTooLarge` をパーサと `Body#read` が投げ、サーバがそれぞれ `400`、`413`、`431` にします。ハンドラは `HTTP::Error.new(status, message)` を投げて、その状態とメッセージを本体にしたテキストで応答できます。これは `on_error` には報告しません。
- 接続上の `SystemCallError` と `IOError`(相手が去った)は静かに接続を終えます。`on_error` には報告しません。

## 8. テスト

ハンドラは直接呼べます。`handler.call(HTTP::Request.get("/users/1"))` で `Response` が得られ、中を調べられます。`HTTP::Request.post("/users", "...")` は文字列から本体(`HTTP::Body.of`)を作ります。ライブラリ自身のテスト(`tests/fixtures/builtins/http_*.qz`、`signal.qz`、4 ワーカーで動かす `tests/threads/http.qz`)は、要求と応答の解析と直列化をソケットなしで行い、`port: 0` のサーバを動かして、keep-alive、パイプライン、chunked の本体、`HEAD`、HTTP/1.0、上限、`100-continue`、タイムアウト、`max_connections`、`shutdown`、UNIX ソケット、ルータを確かめます。

## 9. 後で

- **`HTTP::Client`**:`HTTP::Client.new(base_url:, timeout:)` に `get`、`post`、`request(req) -> Response`。`Socket.tcp` の上で、ホストごとに keep-alive し、`Request`/`Response` の型は同じです。Ruby の `net/http` ではありません。
- **TLS**(`rustls` クレートによる `IO` 上の `TLSSocket`)、**HTTP/2**、**WebSocket**、圧縮、範囲とキャッシュのヘッダを持つ静的ファイル配信、ルータでの `OPTIONS`、標準の形式での要求ログ。
- サーバを他の長く動くタスクと一緒に再起動する `Supervisor`([04-concurrency.ja.md](04-concurrency.ja.md) §5)は別に設計します。
- パーセントデコードとクエリの解析は、`uri` ライブラリ([06-stdlib.ja.md](06-stdlib.ja.md) §10)ができるまで `HTTP` に置き、できたらそちらへ移します。

## 10. 採用しなかった案

- **応答ライター(Go)**:`ResponseWriter` に書き込むハンドラは自然にストリーミングでき、本体の型も要りませんが、ハンドラを接続に結び付けます。テストには偽のライターが要り、ミドルウェアが状態を見るにはライターを包まねばならず、ハンドラは失敗すると分かる前に書き始められます。値を返せばハンドラは関数のままで、ストリーミングは `ResponseBody::Stream` が受け持ちます。
- **接続キュー付きのスレッドプール(Puma)**:タスクは軽く M:N でスケジュールされるので、接続ごとにタスクを作り、スケジューラがプールの役をします。`max_connections` が数を抑えます。
- **Rack の環境ハッシュ**:型付きのフィールドを持つ `data Request` はコンパイラが検査します。アプリケーションに必要なものは `Request` への拡張で足します。
- **標準ライブラリでの高機能なルータ**:`{name}` と `{name...}` を超えるパターンはフレームワークごとに違います。ルータは `Handler` に過ぎないので、cog で置き換えられます。
