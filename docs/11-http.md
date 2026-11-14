# HTTP: The Server and the Client

`require "http"` gives the `HTTP` module: an HTTP/1.1 server written in Quarz on top of the sockets ([06-stdlib.md](06-stdlib.md) §9), for use as an application server behind a reverse proxy, as Puma is used. The proxy terminates TLS and speaks HTTP/2 to the clients; the server speaks HTTP/1.1 to the proxy (or, with `tls:`, HTTPS over HTTP/1.1 to the clients themselves), with keep-alive and chunked bodies. The client, `HTTP::Client` (§9), has request and response types of its own (the server's are `HTTP::Server::Request` and `HTTP::Server::Response`) and shares `Headers`, `Body` and `Content` with the server; neither follows Ruby's `net/http`.

This is implemented in `std/http.qz` (and `Signal` in the prelude, with a few natives), except what §10 leaves for later.

## 1. Shape

```crystal
require "http"

handler = HTTP.handler do |req|
  HTTP::Server::Response.text("hello #{req.path}")
end
HTTP::Server.new(handler, port: 8080).serve
```

- A **handler** takes a `Server::Request` and returns a `Server::Response`, as a Rack application does, rather than writing into a response object as Go's `http.Handler` does. Quarz's values are immutable and a `data` value is the natural thing to return; a handler is then a function, which a test calls without a socket. Streaming is a kind of response body (§4), not a different way of writing handlers.
- The server runs one task per connection ([04-concurrency.md](04-concurrency.md)): tasks are M:N scheduled, so there is no thread pool to size; `QUARZ_THREADS` sets the workers. A handler runs on the connection's task, so it is **Shareable**: a class that includes `HTTP::Handler` has no `var` fields, and the state it shares between requests lives in an `Atom` or a `Channel`.
- Everything that waits (reading a request, writing a response, the handler's own IO) suspends only its task; timeouts are `Task.timeout`, and stopping the server is cancellation.

## 2. Handlers and Middleware

```crystal
module HTTP
  module Handler
    include Shareable
    abstract def call(req: Server::Request) -> Server::Response
  end

  # A handler from a procedure (captures by value, [02-types.md](02-types.md) §9).
  def self.handler(&f: shareable (Server::Request) -> Server::Response) -> Handler
end
```

Middleware is a handler that holds the next one. A `data` type is Shareable when its fields are, and `Handler` is (a middleware holding a Builder or another mutable object is an error):

```crystal
data Logging(inner: HTTP::Handler)
  include HTTP::Handler
  def call(req: HTTP::Server::Request) -> HTTP::Server::Response
    started = Time.monotonic
    res = inner.call(req)
    STDERR.puts "#{req.method} #{req.target.partition("?")[0]} #{res.status} #{Time.monotonic - started}"
    res
  end
end
```

## 3. Requests

```crystal
class HTTP::Server   # (its requests and responses are its own types)
  data Request(
    method: String,                 # "GET"; any token the client sent, not a Symbol
    target: String,                 # the request target as sent: "/users/1?x=1"
    path: String,                   # percent-decoded path: "/users/1"
    query: String,                  # "x=1" ("" when there is none)
    version: String,                # "HTTP/1.1" or "HTTP/1.0"
    headers: Headers,
    body: Body,
    remote_address: Socket::Address?,   # nil on a UNIX socket
    params: Hash[String, String],   # path parameters the router bound (§6); empty otherwise
    proxies: Proxies,               # the server's trusted proxies
    trusted: Bool,                  # whether the peer is one
    tls: Bool                       # whether the connection is TLS (the server's `tls:`)
  )
    def host -> String?                              # the Host header
    def content_length -> Int?
    def query_params -> Hash[String, Array[String]]  # decoded; a key may repeat
    def form_params -> Hash[String, Array[String]]   # application/x-www-form-urlencoded body
    def scheme -> String                             # "https" over tls:, else "http"; X-Forwarded-Proto from a trusted proxy
    def remote_ip -> String?                         # remote_address.host, or X-Forwarded-For's client from a trusted proxy
    def keep_alive? -> Bool
  end
end
```

`Request` is a `data` value: `req.with(params: ...)` makes the routed request, and a test builds one with `HTTP::Server::Request.get("/users/1", headers)`, `HTTP::Server::Request.post("/users", body, headers)` (also `head`, `delete`, `put`, `patch`), or `HTTP::Server::Request.build(method, target, headers, body)`. It is not Shareable, because its `Body` is not: a handler that hands work to another task copies the fields it needs out first (`path = req.path` before the `spawn` block).

### Bodies

The body is read from the socket as the handler asks for it, so `Body` is a class confined to the connection's task (not Shareable):

```crystal
class Body
  def read -> String                   # the whole body; HTTP::PayloadTooLarge past max_body_bytes
  def read_bytes -> Bytes
  def each_chunk(&: (Bytes) -> Void) -> Void   # as it arrives, without the limit
  def read_chunk(max: Int = 16_384) -> Bytes # the next piece (empty at the end)
  def size -> Int?                     # Content-Length, when there is one
  def consumed? -> Bool                # whether it has been read to the end
end
```

`Content-Length` and `Transfer-Encoding: chunked` are both decoded; a request with neither has an empty body. `Expect: 100-continue` is answered with `100 Continue` when the handler first reads. What the handler did not read of a `Content-Length` body is read and dropped after it returns when at most 64 KiB remain (each read within `read_timeout`), so that the connection can be reused; otherwise (a chunked body, more left, a body whose framing failed, or a client waiting for a `100 Continue` that was never sent) the connection is closed after the response. A body read that fails (bad framing, `read_timeout`) leaves the connection to be closed after the response.

### Headers

```crystal
data Field = (name: String, value: String)        # a name lowercased

data Headers(entries: Array[Field])               # in order; a name may repeat
  def self.empty -> Headers
  def self.of(pairs: Hash[String, String]) -> Headers
  def [](name: String) -> String?                    # the first value
  def all(name: String) -> Array[String]
  def key?(name: String) -> Bool
  def put(name: String, value: String) -> Headers    # replaces every value of the name
  def add(name: String, value: String) -> Headers    # appends one
  def delete(name: String) -> Headers
  def each(&: (String, String) -> Void) -> Void
  def size -> Int
  def token?(name: String, token: String) -> Bool   # `Connection: keep-alive, Upgrade` has `upgrade`
end
```

Names are case-insensitive: they are stored lowercased and written out in the conventional form (`Content-Type`). Values are kept as received, except that leading and trailing whitespace is removed. `put`, `add` and `of` (and so `Server::Response#header` and `Server::Response.redirect`) raise `ArgumentError` for a name that is not a token or a value with CR, LF or another control character but HTAB, where the header is set: such a header would split the response (response splitting). The message names the header, not the value, which may come from a request (a cookie, a token) and would otherwise end up in logs.

## 4. Responses

```crystal
class HTTP::Server
  data Response(status: Int, headers: Headers, body: Content)   # the generated `new` takes a Content
    def self.empty(status: Int = 204, headers: Headers = Headers.empty) -> Response
    def self.text(body: String, status: Int = 200) -> Response            # text/plain; charset=utf-8
    def self.html(body: String, status: Int = 200) -> Response
    def self.json(value: JSON::Value, status: Int = 200) -> Response      # application/json
    def self.bytes(body: Bytes, content_type: String, status: Int = 200) -> Response
    def self.redirect(location: String, status: Int = 302) -> Response
    def self.not_found(message: String = "Not Found") -> Response
    def self.stream(status: Int = 200, headers: Headers = Headers.empty,
                    &write: shareable (BodyWriter) -> Void) -> Response
    def header(name: String, value: String) -> Response                   # with(headers: headers.put(...))
    def reason -> String                                                  # "OK" for 200
  end
end

module HTTP
  enum Content                      # a body to send (a server's response's, and a client's request's)
    variant Empty
    variant Text(text: String)
    variant Binary(bytes: Bytes)
    variant Stream(write: shareable (BodyWriter) -> Void)
  end

  # Given to a Stream body's procedure: each `write` is sent as one chunk.
  class BodyWriter
    def write(data: String) -> Void
    def write(data: Bytes) -> Void
    def flush -> Void
  end
end
```

The server adds what the body implies: `Content-Length` for `Text`, `Binary` and `Empty`, `Transfer-Encoding: chunked` for `Stream` (to an HTTP/1.0 client, a `Stream` body is sent unframed and the connection closed), and `Date`. The framing is the server's: a handler's `Transfer-Encoding` is dropped, and its `Content-Length` kept only for a `HEAD` request or a `304` response (where it says what the `GET`/`200` would send). A `204` response carries neither and no body; a `HEAD` request and a `304` response get no body (a `Stream` procedure is not run then), and a `304` gets no `Content-Length` of its own. A handler's status must be a final one, 200 to 599: anything else is answered `500` (interim responses would desynchronize the connection). A `Stream` procedure runs on the connection's task after the headers are sent, so it may take as long as the client stays (server-sent events); `write_timeout` applies to each chunk.

## 5. The Server

```crystal
module HTTP
  class Server
    include Shareable                 # a Signal.trap block or another task may hold it: its state is in Atoms and Channels
    def self.new(handler: Handler, *,             # binds at once: local_address gives the port
                 host: String = "0.0.0.0", port: Int = 8080,
                 read_header_timeout: Duration = 10.seconds,   # from the first byte of a request to the end of its headers
                 idle_timeout: Duration = 60.seconds,          # waiting for the next request on a kept connection
                 read_timeout: Duration = 30.seconds,          # each read of a request's body (408 when it runs out)
                 write_timeout: Duration = 30.seconds,         # one response, or one chunk of a stream
                 max_header_bytes: Int = 65_536,               # request line and headers together
                 max_body_bytes: Int = 1_048_576,              # what Body#read and read_bytes accept
                 max_connections: Int = 10_000,                # accepted at once; beyond it, accept waits
                 trusted_proxies: Array[String] = [],          # peers whose X-Forwarded-* headers are believed
                 on_error: (shareable (Exception, Request?) -> Void)? = nil,
                 tls: TLS::ServerConfig? = nil) -> Server      # HTTPS (not with path:)
    def self.unix(handler: Handler, path: String, *, ...the same options but tls:...) -> Server   # a UNIX socket
    def serve -> Void                      # accepts until shutdown or cancellation
    def local_address -> Socket::Address  # the port actually bound (`port: 0` picks one)
    def shutdown(timeout: Duration = 30.seconds) -> Void   # begins it and returns at once
    def wait -> Void                       # until serve has returned
  end

  def self.serve(port: Int = 8080, host: String = "0.0.0.0",
                 &handler: shareable (Server::Request) -> Server::Response) -> Void
end
```

A connection's task does:

0. With `tls:` (a `TLS::ServerConfig`, [06-stdlib.md](06-stdlib.md) §9), run the TLS handshake (`config.accept`), in the connection's task so that a slow client holds up only its own connection. It counts against the first request's `read_header_timeout` to begin: the handshake and the wait for that request's first byte share it. A handshake that fails or runs out of time closes the connection quietly, as an `IOError` does (below). The config's `alpn` may hold only `http/1.1` and `http/1.0` (`ArgumentError` otherwise).
1. Read the request line and headers: the first request has `read_header_timeout` to begin and as long again from its first byte to finish; a later one on the same connection has `idle_timeout` to begin and `read_header_timeout` to finish. Over `max_header_bytes`: `431`. Malformed: `400`. Both close the connection.
2. Build the `Server::Request` and call the handler. An `HTTP::Error` it raises is answered with that status (§7); any other `StandardError`, or a `SystemStackError` (a handler that recursed without end ends its request only) or a `NoMemoryError` it raised, becomes a `500` with an empty body and goes to `on_error` with the request, or to STDERR with the method and the path as sent (still percent-encoded, so that it cannot hold a line break or an escape, and without the query, which may carry a token); `Task::Cancelled` is not caught. A response whose headers have a name that is not a token, or a value with CR, LF or another control character but HTAB, is not sent: it becomes a `500` too (response splitting; `Headers#put` and `add` already refuse those, so only fields built with `Field.new` get this far). Whatever else fails (a `Stream` procedure that raises after the headers went out) ends that connection and is reported; the server goes on.
3. Write the response under `write_timeout`, then drain or close as §3 says.
4. Keep the connection unless the request or the response said `Connection: close`, the request was HTTP/1.0 without `Connection: keep-alive`, or the body could not be drained. An HTTP/1.0 connection is kept only for a response with a `Content-Length`, and the response then says `Connection: keep-alive`; an HTTP/1.0 request with `Transfer-Encoding` is answered and the connection closed (RFC 9112 §6.1).

The parser is strict where a proxy in front could read a request differently (and stricter than RFC 9112 allows in two places: a field value must be UTF-8, without obs-text, and a chunk extension takes no whitespace before `;`): the request line is `method SP target SP version` with single spaces and no control characters in the target; a field value may hold no control character but HTAB; a chunk's size line and data end in CRLF; blank lines before a request count against `max_header_bytes`, and trailers are limited to 8 KiB.

Requests on one connection are handled one after another, in order (pipelined requests are read as they come, not in parallel). Connections are independent tasks, so a slow handler holds up only its own connection.

The accept loop is the server's own, shaped like `Socket.accept_loop`'s: take a token from a `Channel` of `max_connections` tokens (when none is left, wait, and the kernel's backlog queues the clients), `accept`, spawn the connection's task in the server's scope, which gives the token back when it ends. `shutdown` closes the listener, which ends the loop (a waiting `accept` raises `IOError`). The open connections are registered in an `Atom` so that `shutdown` can find the idle ones. A failing `accept` (file descriptors exhausted, `SystemCallError`) is logged, waited out for a moment and retried; the server does not die of it.

A server on a UNIX socket (`Server.unix`) has no peer addresses: `remote_address` is nil, and the peer counts as a trusted proxy, so `remote_ip` and `scheme` come from the `X-Forwarded-*` headers, or are nil and `"http"` without them.

### Behind a proxy

With `trusted_proxies: ["127.0.0.1", "::1"]` (addresses, or networks as `"10.0.0.0/8"`), a request from one of them has its `scheme` taken from `X-Forwarded-Proto` and its `remote_ip` from `X-Forwarded-For`: the values of every such header joined in order, read from the right, skipping the trusted proxies; the first other address is the client. When there is none (no header, a malformed one, or every address trusted), `remote_ip` is the peer's address. From any other peer, the headers are ignored. `Host` is passed on as received: the proxy sets it.

### Shutdown and signals

`shutdown` stops accepting, closes the connections waiting for a request (their reader gets `IOError`, 04-concurrency §6), lets the ones in a handler finish, and after `timeout` cancels them (`Task::Cancelled` at their next wait); then `serve` returns. `shutdown` returns once it has begun, so a handler may call it; `wait` waits for `serve` to return. A shutdown before `serve` makes `serve` return at once. A connection accepted that has not sent a byte yet counts as waiting, and is closed; with `tls:`, so does one still in its TLS handshake: the handshake runs in a task of a `Task.scope` of its own, registered in an `Atom` as the idle connections are, and `shutdown` cancels that scope, which closes the connection quietly as a failed handshake does. (The `TCPSocket` itself could not be registered: `TLS::ServerConfig#accept` takes it over when the handshake begins.) `Signal` is added with this work, enough for it:

```crystal
server = HTTP::Server.new(handler, port: 8080)
Signal.trap(:TERM) { server.shutdown }
Signal.trap(:INT) { server.shutdown(timeout: 1.second) }
server.serve
```

- `Signal.trap(name) { }` (a `Symbol` or a `String`, with or without `SIG`) runs the block on a task of its own when the signal arrives (not in the signal handler, which only writes the signal's number to a socket pair that a task of the runtime reads); the block captures by value. Several traps for one signal each run on a task of their own. `Signal.trap(name, :default)` restores the default action (not for `PIPE`, which stays ignored), `Signal.trap(name, :ignore)` ignores the signal. `KILL` and `STOP` are known to `Signal.number`, to send with `Process::Child#signal`, and a trap refuses them. Signals to trap: `TERM`, `INT`, `HUP`, `USR1`, `USR2`, `QUIT`, `CONT`, `PIPE` (`SIGPIPE` is ignored from the start, in `quarz run` and in compiled programs alike, so that a write to a closed socket raises `SystemCallError` instead). A trap block that raises reports the exception to STDERR. `Signal.list` names them.

## 6. The Router

A small router is part of the library, as Go's `ServeMux` is; patterns with constraints, regular expressions or typed parameters are left to cogs.

```crystal
router = HTTP::Router.build do |r|
  r.get("/users/{id}") { |req| HTTP::Server::Response.json(user_json(req.params["id"])) }
  r.post("/users", CreateUser.new(db))           # a Handler, or a block
  r.get("/files/{path...}") { |req| serve_file(req.params["path"]) }
  r.mount("/admin", admin_router)                # another Router, under a prefix
  r.not_found { |req| HTTP::Server::Response.not_found }
end
```

- **Patterns** (`HTTP::Pattern.parse`). A pattern starts with `/`, and `/` separates its segments.
  - `{name}` matches one segment, which must not be empty.
  - `{name...}`, only last, matches the rest of the path, slashes included. The rest may be empty: `/files/{p...}` matches `/files/` but not `/files`. The rest is the decoded segments joined with `/`, and `..` segments are kept as they are: a handler that maps it to files must check it.
  - Any other segment matches itself only, braces included (`/a{b}c` is a literal). A trailing slash is significant.
  - A pattern is refused (`ArgumentError`) when it does not start with `/`, when `{name...}` is not last, when a parameter has no name (`{}`, `{...}`), or when two parameters have the same name.
  - The request's target path is split into segments before percent-decoding (`Server::Request#path_segments`), so an escaped `%2F` does not separate segments, as Go's `ServeMux` matches. A segment that does not decode to UTF-8 text makes the path match nothing (the router's fallback answers).
- **Specificity** (`Pattern#compare_specificity`). Among the patterns that match, the most specific wins. Two patterns are compared segment by segment from the left, and the first segment where they differ decides: a literal beats `{name}`, which beats `{name...}`. When one pattern has the other's segments and more, the longer wins. Two patterns for the same method that match the same paths with equal specificity (they differ in parameter names at most, `Pattern#same_paths?`) are an error at `build`.
- **The choice among routes** is `HTTP::Routes[T]#find`, which `Router` calls and a framework's router can call with its own route values. It returns the most specific route of the request's method, a 405's allowed methods, or nothing found. `Routes` is immutable: `add` returns a new value.
- A path that matches a pattern registered for other methods only is answered `405 Method Not Allowed` with `Allow` (listing `HEAD` with `GET`); `HEAD` is served by the `GET` route; `OPTIONS` is not special.
- `mount` prepends the prefix to the other router's patterns (so the mounted `/` is `/admin/`, not `/admin`); the parameters of both are in `params`, and the mounted router's `not_found` is not used.
- `Router` is a `Handler` (a `data` value, built once, Shareable), so routers nest and middleware wraps them.

## 7. Errors

- `HTTP::Error < StandardError`, with `HTTP::BadRequest`, `HTTP::PayloadTooLarge` and `HTTP::HeadersTooLarge` raised by the parser and by `Body#read`; the server turns them into `400`, `413` and `431`. A handler may raise `HTTP::Error.new(status, message)` to answer with that status and the message as a text body; it is not reported to `on_error`.
- `SystemCallError` and `IOError` on the connection (the peer went away) end the connection quietly: they are not reported to `on_error`.

## 8. Testing

A handler is called directly: `handler.call(HTTP::Server::Request.get("/users/1"))` gives a `Response` to inspect; `HTTP::Server::Request.post("/users", "...")` builds the body (`HTTP::Body.of`) from a string. The library's own tests (`std/test/http_*_test.qz`, `tests/fixtures/builtins/signal.qz`, `tests/threads/http.qz` on four workers, and `tests/http_client.rs` for the client's proxy settings) parse and serialize requests and responses without sockets, and run servers on `port: 0` to check keep-alive, pipelining, chunked bodies, `HEAD`, HTTP/1.0, the limits, `100-continue`, the timeouts, `max_connections`, `shutdown`, UNIX sockets and the router.

## 9. The Client

An HTTP/1.1 client over `TCPSocket` and `TLSSocket`, for programs that call other services (fetching and delivering activities, webfinger, webhooks, REST APIs). Its shape is nearer Go's client and Elixir's Req than Ruby's `net/http`: a Shareable client holding a pool of kept connections, requests and responses as values, bodies streamed.

```crystal
client = HTTP::Client.new                      # Shareable: one per program, shared by tasks
res = client.get("https://example.com/users/alice",
                 headers: {"Accept" => "application/activity+json"})
res.status                 # => 200
res.json                   # JSON.parse(res.body.read); the connection goes back to the pool

req = HTTP::Client::Request.post("https://example.com/inbox", body: text,
                                 content_type: "application/activity+json")
             .header("Date", now)
client.request(signer.sign(req)).ensure_success

HTTP.get(url)              # the module functions use HTTP::Client.default
```

```crystal
module HTTP
  class Client
    include Shareable
    def self.new(*, timeout: Duration? = nil,          # the whole request: connect, send, headers, redirects
                 connect_timeout: Duration = 10.seconds, # the lookup, the connects, a proxy's tunnel, the TLS handshake
                 read_timeout: Duration = 30.seconds,    # each read, the body's included
                 write_timeout: Duration = 30.seconds,   # each write
                 max_header_bytes: Int = 65_536,
                 max_body_bytes: Int = 16_777_216,       # what body.read and read_bytes accept
                 max_redirects: Int = 10,                # 0 returns the redirect
                 tls: TLS::Config = TLS::Config.default, # its ALPN defaults to http/1.1
                 proxy: Proxy? = Proxy.from_env,
                 max_idle_per_host: Int = 4, idle_timeout: Duration = 60.seconds,
                 user_agent: String = "quarz-http/<version>",
                 fast_fallback: Bool = true)             # Socket.tcp's: false, no Happy Eyeballs
    def self.default -> Client                          # made on first use
    def request(req: Request) -> Response
    def get(url: String | URI, headers: Headers | Hash[String, String] = Headers.empty) -> Response   # head, delete alike
    def post(url: String | URI, body: String | Bytes = "", content_type: String? = nil,
             headers: Headers | Hash[String, String] = Headers.empty) -> Response                     # put, patch alike
    def close -> Void                                   # closes the kept connections, keeps no more

    data Request(method: String, url: URI, headers: Headers, body: Content)
      def self.new(method: String, url: String | URI, *, headers: Headers | Hash[String, String] = Headers.empty,
                   body: Content = Content::Empty) -> Request
      def self.get(url, headers = Headers.empty) -> Request     # head, delete; post, put, patch(url, body, content_type, headers)
      def self.stream(method: String, url, headers = Headers.empty,
                      &write: shareable (BodyWriter) -> Void) -> Request   # sent chunked
      def header(name: String, value: String) -> Request
      def with(*, method:, url:, headers:, body:) -> Request   # written by hand: through `new`'s checks
    end

    data Response(status: Int, version: String, headers: Headers, body: Body, url: URI, request: Request)
      def reason -> String
      def success? -> Bool                              # 2xx
      def redirect? -> Bool                             # 301, 302, 303, 307, 308
      def ensure_success -> Response                    # or StatusError
      def json -> JSON::Value
      def close -> Void                                 # drains a little, else closes the connection
    end
  end

  data Proxy(https: URI?, http: URI?, no_proxy: Array[String])
    def self.new(url: String | URI, *, no_proxy: Array[String] = []) -> Proxy
    def self.from_env -> Proxy?
    def proxy_for(target: URI) -> URI?
  end
end
```

What the client adds to a request: `Host` (from the URL; a request's own is replaced), the framing (`Content-Length` for a `Text` or `Binary` body, and `0` for an empty `POST`, `PUT` or `PATCH`; `Transfer-Encoding: chunked` for a `Stream` body; a request's own framing headers are dropped, as the server drops a handler's), `User-Agent` when the request has none. Nothing else: no `Accept-Encoding` (a `Content-Encoding` body is given as it came), no cookies, no `Expect: 100-continue`. A URL is `http` or `https` with a host, without whitespace or control characters (`ArgumentError`, as for a method that is not a token or a header that would split the request).

**Responses and bodies.** `request` returns once the headers are read; `body` is an `HTTP::Body`, the server's request body, read from the connection as it is asked for: `read`/`read_bytes` up to `max_body_bytes` (`ResponseTooLarge` past it), `read_chunk` and `each_chunk` without a limit. A `HEAD` response, a 1xx, 204 or 304 has an empty body; interim 1xx responses before the final one are skipped; a body without framing (HTTP/1.0, or `Connection: close` without a length) is read to the connection's end. A non-2xx response is a value: `ensure_success` raises for it.

**The pool.** Idle connections are kept per origin and proxy, at most `max_idle_per_host`, for `idle_timeout`, in an `Atom`, so that the client is Shareable; what one request reads (its `Reader`, its `Body`) is the calling task's. A connection goes back to the pool when its response's body has been read to the end (`read`, `read_bytes`, `each_chunk`, or `close`) with nothing buffered past it, and the response allowed it (HTTP/1.1, no `Connection: close`, not a 101, not both `Transfer-Encoding` and `Content-Length`). A response dropped before its body ends closes its connection: the body's owner closes it in `deinitialize`, so a half-read connection is never reused. A kept connection found closed (no byte of the response came) is replaced once by a new connection, when that cannot do the request twice: its body is not a `Stream` (whose procedure runs once), and nothing of it was sent or it is idempotent (`GET`, `HEAD`, `PUT`, `DELETE`, `OPTIONS`). Whatever ends a request early (an error, a timeout, a cancellation) closes its connection. The status lines and headers of a response share `max_header_bytes`. No pipelining.

**Connecting.** `Socket.tcp` (the addresses tried by Happy Eyeballs, or in order with `fast_fallback: false`), then, for `https`, `TLSSocket.connect` with the host as the server name, all within `connect_timeout`. Through a proxy (`Proxy.from_env` by default: `https_proxy`/`HTTPS_PROXY` for `https` targets, `http_proxy`/`HTTP_PROXY` for `http` ones, a URL that is not `http` with a host, `socks5://` say, ignored with one warning on standard error; `HTTP_PROXY` ignored when `REQUEST_METHOD` is set, as Go does, since a CGI request's `Proxy` header sets it (httpoxy); `no_proxy`/`NO_PROXY` as curl reads it: names with their subdomains, with or without a leading dot, addresses (only themselves; no CIDR networks yet), each with an optional `:port` (`[::1]:8080`), `*`): an `https` target goes through `CONNECT host:port`, then the TLS handshake over the tunnel; an `http` target is sent to the proxy in absolute form (without the URL's user information). The user information of a target URL is never sent, as a header or otherwise: a program that wants `Authorization: Basic` sets it. The proxy URL's user information is sent as `Proxy-Authorization: Basic`. A proxy that refuses the tunnel is `ProxyError` with its status.

**Redirects** (Go's rules). Up to `max_redirects`: 301, 302 and 303 are followed with `GET` and no body (a `HEAD` stays `HEAD`), 307 and 308 with the same method and body (a `Stream` body cannot be sent again: `RedirectError`). `Location` is resolved against the request's URL (`URI#resolve`). When a redirect leaves the origin (`URI#origin`: scheme, host and port), `Authorization`, `Cookie` and `Proxy-Authorization` are dropped. A redirect's body is drained (or its connection closed) before the next request. More than `max_redirects` is `TooManyRedirects`. A signed request should set `max_redirects: 0` and sign again: the client cannot.

**Errors.** `HTTP::Client::Error < StandardError` (not `HTTP::Error`, whose status is for a server to answer with): `ConnectError` (the name has no address, refused, unreachable, the TLS handshake, the connection failing under a request; the message carries the cause's), `TimeoutError` (`Task::Timeout` of `timeout`, `connect_timeout`, `read_timeout` and `write_timeout`), `ProtocolError` (a bad status line, header or framing, headers over `max_header_bytes`, a connection closed without a response), `ResponseTooLarge`, `RedirectError`, `TooManyRedirects`, `ProxyError` (`status`), `StatusError`. An exception is Shareable and a response's body is not, so `StatusError` carries the response's `status`, `headers`, `url` and its `body` as `Bytes` (read by `ensure_success`, nil when it could not be; the message names the status and the URL, never the body), and `TooManyRedirects` the last redirect's `status`, `headers` and `url`.

## 10. Later

- **HTTP/2**, **WebSocket**, compression, static files with ranges and caching headers, an automatic `OPTIONS` answer in the router, request logging in a standard format.
- A `Supervisor` for restarting a server with other long-lived tasks ([04-concurrency.md](04-concurrency.md) §5) is designed separately.
- The client's: compression (`Accept-Encoding`), cookies, HTTP/2, `Expect: 100-continue`, UNIX-socket targets, and an address filter against SSRF (a program checks `URI` and `Socket.getaddrinfo` before calling, for now).
- `HTTP.parse_query` and the percent-decoding could become thin wrappers over `uri` ([06-stdlib.md](06-stdlib.md) §10).

## 11. Alternatives Not Adopted

- **A response writer (Go)**: a handler that writes into a `ResponseWriter` streams naturally and needs no body types, but it ties a handler to a connection: testing one needs a fake writer, middleware must wrap the writer to see the status, and a handler can start writing before it knows it will fail. Returning a value keeps handlers functions; `Content::Stream` covers the streaming cases.
- **A thread pool with a connection queue (Puma)**: tasks are cheap and M:N scheduled, so each connection is a task and the scheduler is the pool; `max_connections` bounds them.
- **Rack's environment hash**: a `data Request` with typed fields is checked by the compiler; an extension on `Request` adds what an application needs.
- **A full-featured router in the standard library**: patterns beyond `{name}` and `{name...}` differ between frameworks; a cog can replace the router, since it is only a `Handler`.
