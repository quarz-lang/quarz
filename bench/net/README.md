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

The single-threaded servers are pinned to one CPU, the multi-threaded
ones (Quarz with `QUARZ_THREADS=4`, Go with all its threads) get two
physical cores, and the client runs on the other CPUs (`SERVER_CPU`,
`SERVER_CPUS`, `CLIENT_CPUS`; see the script).

## Results (2026-10-22)

12th Gen Intel Core i7-1260P, Go 1.27.2; round trips per second, 5 s
after a second of warm-up.

With four worker threads (Quarz at the commit adding them; one worker,
the first two columns, compares with Go limited to one thread; the
four-thread columns with Go on the same two physical cores, CPUs 0-3,
`GOMAXPROCS=4`):

| connections | quarz-vm | quarz-llvm | vm, 4 threads | llvm, 4 threads | go, 1 thread | go, 4 threads |
|------------:|---------:|-----------:|--------------:|----------------:|-------------:|--------------:|
|           1 |  113,593 |    111,854 |       108,349 |         108,635 |      108,761 |       106,307 |
|          16 |  203,878 |    201,903 |       308,572 |         314,959 |      197,923 |       306,614 |
|          64 |  184,377 |    186,671 |       326,199 |         329,824 |      198,540 |       367,166 |
|         256 |  178,260 |    182,901 |       311,000 |         318,484 |      191,585 |       360,440 |

Before, with one thread (M:1), the reactor using epoll directly (each
socket registered once, edge-triggered):

| connections | quarz-vm | quarz-llvm | go, 1 thread | go, 4 threads |
|------------:|---------:|-----------:|-------------:|--------------:|
|           1 |   94,538 |    104,304 |      103,713 |        92,024 |
|          16 |  181,248 |    191,697 |      165,135 |       280,170 |
|          64 |  185,339 |    188,760 |      197,360 |       356,403 |
|         256 |  168,216 |    168,992 |      149,548 |       340,948 |

Before (Quarz at `db9b660`, through the `polling` crate):

| connections | quarz-vm | quarz-llvm | go, 1 thread | go, 4 threads |
|------------:|---------:|-----------:|-------------:|--------------:|
|           1 |   81,229 |     79,530 |       73,758 |        71,905 |
|          16 |  128,515 |    127,320 |      164,190 |       251,683 |
|          64 |  118,399 |    118,347 |      165,938 |       310,766 |
|         256 |  111,188 |    113,063 |      156,564 |       306,331 |

The same configuration varies by 10-20% from run to run (compare
columns of one run, or medians of several).

## Reading the numbers

- Quarz is now on a par with Go on one thread, from one connection to
  256. The interpreter and compiled code are about equal: the time goes
  to the scheduler and the system calls, not to the program.
- Per round trip (strace, 64 connections) Quarz makes one `sendto`,
  about 1.4 `recvfrom` (the last one finding nothing) and 0.36
  `epoll_wait`, like Go's one `write` and 1.45 `read`s; Go polls less
  (about 0.01 `epoll_wait`), from its scheduler when goroutines block.
- Before, the `polling` crate re-armed every descriptor after each event
  (oneshot) and re-armed a timerfd and its notifier around every wait:
  about 1.7 `epoll_ctl`, 0.55 `timerfd_settime` and 0.55 failed `read`s
  more per round trip. Polling the reactor only every 32 task switches
  instead of at each measured slower (the woken tasks waited longer).
- On four worker threads Quarz goes from about 200k to 310-330k round
  trips per second, as Go does from one thread to four: equal at 16
  connections, about 90% of Go at 64 and 256. A connection's task stays
  on the worker it started on (round robin), and its socket is
  registered with that worker's epoll; Go moves goroutines between
  threads.
