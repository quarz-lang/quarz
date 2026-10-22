# TCP echo throughput

A line echo server in Quarz (`echo.qz`: a task per connection writing
back each line it reads) against the same server in Go (`server.go`: a
goroutine per connection), driven by one load generator (`client.go`:
N connections, each sending a 64-byte line and waiting for it to come
back). `run.sh` builds everything and prints the round trips per second
for each number of connections:

```sh
cargo build --release
bench/net/run.sh            # 1 16 64 256 connections
bench/net/run.sh 64         # one count
```

The single-threaded servers are pinned to one CPU, the multi-threaded Go
server gets two physical cores, and the client runs on the other CPUs
(`SERVER_CPU`, `SERVER_CPUS`, `CLIENT_CPUS`; see the script).

## Results (2026-10-22, Quarz at `db9b660`)

12th Gen Intel Core i7-1260P, Go 1.27.2; round trips per second, 5 s
after a second of warm-up. Quarz runs its tasks on one OS thread (M:1),
so its columns compare with Go limited to one thread; the last column is
Go on two physical cores (`GOMAXPROCS=4`, CPUs 0-3).

| connections | quarz-vm | quarz-llvm | cranelift | go, 1 thread | go, 4 threads |
|------------:|---------:|-----------:|----------:|-------------:|--------------:|
|           1 |   81,229 |     79,530 |    71,212 |       73,758 |        71,905 |
|          16 |  128,515 |    127,320 |   130,106 |      164,190 |       251,683 |
|          64 |  118,399 |    118,347 |   124,800 |      165,938 |       310,766 |
|         256 |  111,188 |    113,063 |   111,863 |      156,564 |       306,331 |

The same configuration varies by 10-15% from run to run.

## Reading the numbers

- With one connection the round trip's latency decides, and Quarz is on
  a par with Go. With more, Quarz reaches 70-80% of Go on one thread.
- The interpreter and compiled code are about equal: the time goes to
  the scheduler and the system calls, not to the program.
- Per round trip, Quarz makes one `sendto` and about 1.5 `recvfrom`
  like Go, but also about 1.7 `epoll_ctl`, 0.55 `epoll_pwait`, 0.55
  `timerfd_settime` and 0.55 failed `read`s (strace, 64 connections). Go
  registers each socket with epoll once, edge-triggered, and polls only
  when every goroutine is blocked (about 0.01 `epoll_pwait` per round
  trip).
- Go on several threads doubles its throughput from 16 connections on,
  which is what an M:N scheduler would bring.
