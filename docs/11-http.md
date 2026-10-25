# HTTP: The Server

日本語版: [11-http.ja.md](11-http.ja.md)

`require "http"` gives the `HTTP` module: an HTTP/1.1 server written in Quarz on top of the sockets ([06-stdlib.md](06-stdlib.md) §9), for use as an application server behind a reverse proxy, as Puma is used. The proxy terminates TLS and speaks HTTP/2 to the clients; the server speaks HTTP/1.1 to the proxy, with keep-alive and chunked bodies. A client, `HTTP::Client`, will follow with the same request and response types; neither follows Ruby's `net/http`.

This is the design. Nothing of it is implemented yet; the sections say what the first version does and what is left for later.

## 1. Shape

```ruby
require "http"

handler = HTTP.handler do |req|
  HTTP::Response.text("hello #{req.path}")
end
HTTP::Server.new(handler, port: 8080).serve
```

- A **handler** takes a `Request` and returns a `Response`, as a Rack application does, rather than writing into a response object as Go's `http.Handler` does. Quarz's values are immutable and a `data` value is the natural thing to return; a handler is then a function, which a test calls without a socket. Streaming is a kind of response body (§4), not a different way of writing handlers.
- The server runs one task per connection ([04-concurrency.md](04-concurrency.md)): tasks are M:N scheduled, so there is no thread pool to size; `QUARZ_THREADS` sets the workers. A handler runs on the connection's task, so it is **Shareable**: a class that includes `HTTP::Handler` has no `var` fields, and the state it shares between requests lives in an `Atom` or a `Channel`.
- Everything that waits (reading a request, writing a response, the handler's own IO) suspends only its task; timeouts are `Task.timeout`, and stopping the server is cancellation.

## 2. Handlers and Middleware

```ruby
module HTTP
  module Handler
    include Shareable
    abstract def call(req: Request) -> Response
  end

  # A handler from a procedure (captures by value, [02-types.md](02-types.md) §9).
  def self.handler(&f: shareable (Request) -> Response) -> Handler
end
```

Middleware is a handler that holds the next one. A `data` type is Shareable when its fields are, and `Handler` is (a middleware holding a Builder or another mutable object is an error):

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

## 3. Requests

```ruby
module HTTP
  data Request(
    method: String,                 # "GET"; any token the client sent, not a Symbol
    target: String,                 # the request target as sent: "/users/1?x=1"
    path: String,                   # percent-decoded path: "/users/1"
    query: String,                  # "x=1" ("" when there is none)
    version: String,                # "HTTP/1.1" or "HTTP/1.0"
    headers: Headers,
    body: Body,
    remote_address: Socket::Address?,   # nil on a UNIX socket
    params: Hash[String, String]    # path parameters the router bound (§6); empty otherwise
  )
    def host -> String?                              # the Host header
    def content_length -> Int?
    def query_params -> Hash[String, Array[String]]  # decoded; a key may repeat
    def form_params -> Hash[String, Array[String]]   # application/x-www-form-urlencoded body
    def scheme -> String                             # "http", or X-Forwarded-Proto from a trusted proxy
    def remote_ip -> String?                         # remote_address.host, or X-Forwarded-For's client from a trusted proxy
    def keep_alive? -> Bool
  end
end
```

`Request` is a `data` value: `req.with(params: ...)` makes the routed request, and a test builds one with `HTTP::Request.new(...)` (its body an `HTTP::Body.of("...")`), or with `HTTP::Request.get("/users/1", headers: ..., body: "")` and the other method names. It is not Shareable, because its `Body` is not: a handler that hands work to another task copies the fields it needs out first (`path = req.path` before the `spawn` block).

### Bodies

The body is read from the socket as the handler asks for it, so `Body` is a class confined to the connection's task (not Shareable):

```ruby
class Body
  def read -> String                   # the whole body; HTTP::PayloadTooLarge past max_body_bytes
  def read_bytes -> Bytes
  def each_chunk(&: (Bytes) -> Nil) -> Nil   # as it arrives, without the limit
  def size -> Int?                     # Content-Length, when there is one
  def consumed? -> Bool                # whether it has been read to the end
end
```

`Content-Length` and `Transfer-Encoding: chunked` are both decoded; a request with neither has an empty body. `Expect: 100-continue` is answered with `100 Continue` when the handler first reads. What the handler did not read is drained after it returns when at most `max_body_bytes` remain and they arrive within `read_header_timeout` (so the connection can be reused); otherwise, and when the client was waiting for a `100 Continue` that was never sent, the connection is closed after the response.

### Headers

```ruby
data Headers(entries: Array[[String, String]])    # names lowercased, order kept, a name may repeat
  def self.empty -> Headers
  def self.of(pairs: Hash[String, String]) -> Headers
  def [](name: String) -> String?                    # the first value
  def all(name: String) -> Array[String]
  def key?(name: String) -> Bool
  def put(name: String, value: String) -> Headers    # replaces every value of the name
  def add(name: String, value: String) -> Headers    # appends one
  def delete(name: String) -> Headers
  def each(&: (String, String) -> Nil) -> Nil
  def size -> Int
end
```

Names are case-insensitive: they are stored lowercased and written out in the conventional form (`Content-Type`). Values are kept as received, except that leading and trailing whitespace is removed.

## 4. Responses

```ruby
module HTTP
  data Response(status: Int, headers: Headers, body: ResponseBody)   # the generated `new` takes a ResponseBody
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
    def reason -> String                                                  # "OK" for 200
  end

  enum ResponseBody
    variant Empty
    variant Text(text: String)
    variant Binary(bytes: Bytes)
    variant Stream(write: shareable (BodyWriter) -> Nil)
  end

  # Given to a Stream body's procedure: each `write` is sent as one chunk.
  class BodyWriter
    def write(data: String) -> Nil
    def write(data: Bytes) -> Nil
    def flush -> Nil
  end
end
```

The server adds what the body implies: `Content-Length` for `Text`, `Binary` and `Empty`, `Transfer-Encoding: chunked` for `Stream` (to an HTTP/1.0 client, a `Stream` body is sent unframed and the connection closed), and `Date`. A `1xx` or `204` response carries neither `Content-Length` nor `Transfer-Encoding` and no body; a `HEAD` request and a `304` response get the headers the `GET`/`200` would have and no body (a `Stream` procedure is not run then). A `Stream` procedure runs on the connection's task after the headers are sent, so it may take as long as the client stays (server-sent events); `write_timeout` applies to each chunk.

## 5. The Server

```ruby
module HTTP
  class Server
    include Shareable                 # a Signal.trap block or another task may hold it: its state is in Atoms and Channels
    def self.new(handler: Handler, *,
                 host: String = "0.0.0.0", port: Int = 8080,
                 read_header_timeout: Duration = 10.seconds,   # from the first byte of a request to the end of its headers
                 idle_timeout: Duration = 60.seconds,          # waiting for the next request on a kept connection
                 write_timeout: Duration = 30.seconds,         # one response, or one chunk of a stream
                 max_header_bytes: Int = 65_536,               # request line and headers together
                 max_body_bytes: Int = 1_048_576,              # what Body#read and read_bytes accept
                 max_connections: Int = 10_000,                # accepted at once; beyond it, accept waits
                 trusted_proxies: Array[String] = [],          # peers whose X-Forwarded-* headers are believed
                 on_error: (shareable (Exception, Request?) -> Nil)? = nil) -> Server
    def self.unix(handler: Handler, path: String, *, ...the same options...) -> Server   # a UNIX socket
    def serve -> Nil                      # accepts until shutdown or cancellation
    def local_address -> Socket::Address  # the port actually bound (`port: 0` picks one)
    def shutdown(timeout: Duration = 30.seconds) -> Nil
  end

  def self.serve(port: Int = 8080, host: String = "0.0.0.0",
                 &handler: shareable (Request) -> Response) -> Nil
end
```

A connection's task does:

1. Read the request line and headers: the first request within `read_header_timeout` of the accept; a later one on the same connection has `idle_timeout` to begin and `read_header_timeout` from its first byte to finish. Over `max_header_bytes`: `431`. Malformed: `400`. Both close the connection.
2. Build the `Request` and call the handler. An `HTTP::Error` it raises is answered with that status (§7); any other `StandardError` becomes a `500` with an empty body and goes to `on_error` with the request, or to STDERR; `Task::Cancelled` is not caught.
3. Write the response under `write_timeout`, then drain or close as §3 says.
4. Keep the connection unless the request or the response said `Connection: close`, the request was HTTP/1.0 without `Connection: keep-alive`, or the body could not be drained. An HTTP/1.0 connection is kept only for a response with a `Content-Length`, and the response then says `Connection: keep-alive`.

Requests on one connection are handled one after another, in order (pipelined requests are read as they come, not in parallel). Connections are independent tasks, so a slow handler holds up only its own connection.

The accept loop is the server's own, shaped like `Socket.accept_loop`'s: take a token from a `Channel` of `max_connections` tokens (when none is left, wait, and the kernel's backlog queues the clients), `accept`, spawn the connection's task in the server's scope, which gives the token back when it ends. A `Channel.select` on the listener and the shutdown channel ends the loop. The open connections are registered in an `Atom` so that `shutdown` can find the idle ones. A failing `accept` (file descriptors exhausted, `SystemCallError`) is logged, waited out for a moment and retried; the server does not die of it.

A server on a UNIX socket (`Server.unix`) has no peer addresses: `remote_address` is nil, and the peer counts as a trusted proxy, so `remote_ip` and `scheme` come from the `X-Forwarded-*` headers, or are nil and `"http"` without them.

### Behind a proxy

With `trusted_proxies: ["127.0.0.1", "::1"]` (addresses, or networks as `"10.0.0.0/8"`), a request from one of them has its `scheme` taken from `X-Forwarded-Proto` and its `remote_ip` from `X-Forwarded-For`: the values of every such header joined in order, read from the right, skipping the trusted proxies; the first other address is the client. When there is none (no header, a malformed one, or every address trusted), `remote_ip` is the peer's address. From any other peer, the headers are ignored. `Host` is passed on as received: the proxy sets it.

### Shutdown and signals

`shutdown` stops accepting, closes the connections waiting for a request (their reader gets `IOError`, 04-concurrency §6), lets the ones in a handler finish, and after `timeout` cancels them (`Task::Cancelled` at their next wait); then `serve` returns. `Signal` is added with this work, enough for it:

```ruby
server = HTTP::Server.new(handler, port: 8080)
Signal.trap(:TERM) { server.shutdown }
Signal.trap(:INT) { server.shutdown(timeout: 1.second) }
server.serve
```

- `Signal.trap(name) { }` runs the block on a task of its own when the signal arrives (not in the signal handler); the block captures by value. Several traps for one signal run in the order they were set. `Signal.trap(name, :default)` restores the default action, `Signal.trap(name, :ignore)` ignores the signal. Signals: `TERM`, `INT`, `HUP`, `USR1`, `USR2`, `QUIT`, `PIPE` (`SIGPIPE` is to be ignored at the runtime's start, in `quarz run` and in compiled programs' `qz_main` alike, so that a write to a closed socket raises `SystemCallError` instead; today only `quarz run` ignores it, through Rust's start-up). `Signal.list` names them.

## 6. The Router

A small router is part of the library, as Go's `ServeMux` is; patterns with constraints, regular expressions or typed parameters are left to cogs.

```ruby
router = HTTP::Router.build do |r|
  r.get("/users/{id}") { |req| HTTP::Response.json(user_json(req.params["id"])) }
  r.post("/users", CreateUser.new(db))           # a Handler, or a block
  r.get("/files/{path...}") { |req| serve_file(req.params["path"]) }
  r.mount("/admin", admin_router)                # another Router, under a prefix
  r.not_found { |req| HTTP::Response.not_found }
end
```

- A pattern is a path with segments; `{name}` matches one segment and `{name...}`, last, matches the rest of the path (possibly empty), including slashes. Matching is exact otherwise; a trailing slash is significant. The request's target path is split into segments before percent-decoding, so an escaped `%2F` does not separate segments (as Go's `ServeMux` matches). Among the patterns that match, the most specific wins: compared segment by segment from the left, the first segment where one has a literal and the other a parameter decides for the literal, and `{name}` wins over `{name...}`; two patterns for the same method that match the same paths with equal specificity are an error at `build`.
- A path that matches a pattern registered for other methods only is answered `405 Method Not Allowed` with `Allow` (listing `HEAD` with `GET`); `HEAD` is served by the `GET` route; `OPTIONS` is not special.
- `mount` prepends the prefix to the other router's patterns; the parameters of both are in `params`.
- `Router` is a `Handler` (a `data` value, built once, Shareable), so routers nest and middleware wraps them.

## 7. Errors

- `HTTP::Error < StandardError`, with `HTTP::BadRequest`, `HTTP::PayloadTooLarge` and `HTTP::HeadersTooLarge` raised by the parser and by `Body#read`; the server turns them into `400`, `413` and `431`. A handler may raise `HTTP::Error.new(status, message)` to answer with that status and the message as a text body; it is not reported to `on_error`.
- `SystemCallError` and `IOError` on the connection (the peer went away) end the connection quietly: they are not reported to `on_error`.

## 8. Testing

A handler is called directly: `handler.call(HTTP::Request.get("/users/1"))` gives a `Response` to inspect; `HTTP::Request.post("/users", body: "...")` builds the body (`HTTP::Body.of`) from a string. The library's own tests parse and serialize requests and responses without sockets (`tests/fixtures/http/`), and run a server on `port: 0` with four workers in `tests/threads/` to check keep-alive, chunked bodies, pipelining, timeouts, the limits and `shutdown`.

## 9. Later

- **`HTTP::Client`**: `HTTP::Client.new(base_url:, timeout:)` with `get`, `post` and `request(req) -> Response`, over `Socket.tcp`, keep-alive per host, the same `Request`/`Response` types. Not Ruby's `net/http`.
- **TLS** (a `TLSSocket` over an `IO`, with the `rustls` crate), **HTTP/2**, **WebSocket**, compression, static files with ranges and caching headers, an automatic `OPTIONS` answer in the router, request logging in a standard format.
- A `Supervisor` for restarting a server with other long-lived tasks ([04-concurrency.md](04-concurrency.md) §5) is designed separately.
- The percent-decoding and query parsing live in `HTTP` until there is a `uri` library ([06-stdlib.md](06-stdlib.md) §10), which takes them over.

## 10. Alternatives Not Adopted

- **A response writer (Go)**: a handler that writes into a `ResponseWriter` streams naturally and needs no body types, but it ties a handler to a connection: testing one needs a fake writer, middleware must wrap the writer to see the status, and a handler can start writing before it knows it will fail. Returning a value keeps handlers functions; `ResponseBody::Stream` covers the streaming cases.
- **A thread pool with a connection queue (Puma)**: tasks are cheap and M:N scheduled, so each connection is a task and the scheduler is the pool; `max_connections` bounds them.
- **Rack's environment hash**: a `data Request` with typed fields is checked by the compiler; an extension on `Request` adds what an application needs.
- **A full-featured router in the standard library**: patterns beyond `{name}` and `{name...}` differ between frameworks; a cog can replace the router, since it is only a `Handler`.
