# Concurrent Programming

日本語版: [04-concurrency.ja.md](04-concurrency.ja.md)

Quarz's concurrency model consists of three parts.

1. **Tasks** — lightweight threads corresponding to goroutines / Erlang processes. They are M:N scheduled, and hundreds of thousands can run at once. (The current scheduler runs every task on one OS thread, M:1; see §7.)
2. **Channels** — typed message queues. All communication and synchronization between tasks goes through them.
3. **Atom** — a shared cell holding an immutable value. Updated via CAS, so multiple tasks can read and write it safely.

And there is one rule that spans the whole language: **mutable objects never cross task boundaries** ([03-data-model.md](03-data-model.md) §5). This eliminates data races at compile time. The language provides no locks (a `Mutex` for FFI purposes, in an `FFI` module, is planned along with FFI).

## 1. Tasks

```ruby
t = spawn { heavy_computation(42) }   # Task[Int]
puts t.await                          # wait for completion and receive the value

Task.sleep(100.ms)
Task.yield                            # yield to other tasks
Task.current                          # the current Task
```

- `spawn { }` creates a new task, registers it with the scheduler, and returns immediately. The `T` in the returned `Task[T]` is the type of the block.
- The block **captures by value**. Outer local variables are copied at the time of `spawn`, and the block cannot assign to outer variables. Every captured value must be Shareable. (Currently the captured variables are shared rather than copied, so the task sees a later reassignment made by the spawning code; and `self` is not checked: a `spawn` block in a method can use the object's fields even when it is mutable. `Task.blocking` does copy.)
- `await` waits for the task to complete and returns its value. If the task ended with an exception, that exception is re-raised on the side that called `await`.
- Tasks switch cooperatively at safepoints inserted by the compiler (method entry, loop back-edges, channel operations, allocation). Even a pure computational loop switches at loop boundaries, so no single task can monopolize the scheduler. (Currently tasks switch only at operations that wait (a channel operation that must wait, `sleep`, `await`, IO), at `Task.yield` and at each iteration of `loop`; a `while` loop or an iterator that does none of these keeps the scheduler until it finishes.)
- Each task has its own stack (§7), so Ruby methods can be called recursively as usual. There is no function coloring like `async`/`await`. Blocking operations (channels, IO, `sleep`) can be called from anywhere, and only the calling task stops.

## 2. Structured Concurrency (`Task.scope`)

In practice, most concurrent work is "throw out some jobs and wait for all of them." `Task.scope` is the basic form for writing that safely.

```ruby
results = Task.scope do |scope|
  tasks = urls.map { |url| scope.spawn { fetch(url) } }
  tasks.map(&:await)
end
```

- When leaving the `Task.scope` block, it waits for every task created with `scope.spawn` to complete. The value of the block is the value of `Task.scope`.
- If a task in the scope ends with an exception, **the remaining tasks are cancelled**, and after waiting for them to complete, the exception is re-raised to the caller of `Task.scope`. If multiple tasks failed, the first exception is raised and the rest are attached as a `cause` chain (currently the others are discarded).
- If the block body itself raises, the same thing happens: child tasks are cancelled and waited for before the exception propagates.
- Scopes can be nested. Cancellation propagates inward through nested scopes. (Currently, when the task that runs a scope is cancelled while it waits in the scope, the scope re-raises at once, without waiting for the children it cancels.)
- A top-level `spawn` (without a `scope`) belongs to the program's root scope. When the main top-level code finishes, the program exits and any remaining tasks are cancelled (the same as Ruby's main thread exiting). (Currently they are dropped without running their `ensure` clauses.) Long-lived services should wait explicitly with `Task.scope`.

### Cancellation

```ruby
Task.scope do |scope|
  worker = scope.spawn { loop { process(queue.receive) } }
  Task.sleep(1.second)
  worker.cancel
end

Task.timeout(5.seconds) { slow_call }     # raises Task::Timeout when exceeded; the block runs in a child task
```

- `cancel` sets a "cancellation request" on the target task. The requested task receives a `Task::Cancelled` exception at the next blocking operation it performs (channel, IO, `sleep`, `await`), or when it calls `Task.check_cancel`.
- `Task::Cancelled` is a direct subclass of `Exception`, not `StandardError`, so `rescue => e` does not catch it. `ensure` runs as usual, so cleanup goes there.
- Cancellation is a request, not a force. Computation-only loops need to call `Task.check_cancel` periodically (an option to check automatically at safepoints, `--cancel-at-safepoints`, is planned). Likewise `Task.timeout` interrupts its block only at a wait; currently, cancelling the task that waits in `Task.timeout` does not cancel the block.
- `Task#done?` tells whether a task has finished; `Scope#cancel` cancels the scope's children, and the scope then returns normally.

## 3. Channels

```ruby
ch = Channel[String].new               # capacity 0 (synchronous)
ch = Channel[String].new(capacity: 16) # bounded buffer

ch.send("hello")     # waits until received if the buffer is full
msg = ch.receive     # waits until sent if empty. Channel::Closed if closed and empty
msg = ch.receive?    # nil if closed and empty (type is String?)
ch.try_send("x")     # returns Bool without waiting
ch.close             # send raises Channel::Closed afterwards. Remaining elements can still be received
ch.each { |m| ... }  # keeps receiving until closed
```

`try_receive`, `closed?`, `empty?` and `size` are also available, and a channel is `Enumerable`.

- The `T` of `Channel[T]` must be Shareable.
- A channel with capacity 0 is a rendezvous between sender and receiver and can be used for synchronization.
- `send`/`receive` establish happens-before. Updates made before a `send` are visible after the corresponding `receive`. This is the entirety of Quarz's memory model (since there is no shared mutable state, there is nothing else to specify).
- If every task is waiting on a channel and the program deadlocks, the runtime stops the program with `DeadlockError` (the same as Go's "all goroutines are asleep"). It prints the blocked tasks and exits with status 1; it is not an exception that can be rescued, and `ensure` and `at_exit` do not run.

### `select`

Executes exactly one of several channel operations, whichever becomes possible first. When several are ready, the first one written wins; a closed channel in a `receive` or `send` raises `Channel::Closed`.

```ruby
select do |s|
  s.receive(jobs) { |job| handle(job) }
  s.receive(quit) { |_| done = true }
  s.send(results, value) { puts "sent" }
  s.after(1.second) { puts "timeout" }
  s.default { puts "nothing ready" }       # makes it non-blocking when present
end
```

Since `select` is often used in the same shape inside a `loop`, `Channel.select_loop` is provided as well. Calling `s.stop` inside a handler exits the loop (each handler is a separate block, so by Ruby's rules `break` only exits `s.receive` and does not stop the loop).

## 4. Atom

State that is updated from multiple tasks goes into an `Atom`. Its contents are an immutable value, so an update is the operation "compute a new value from the old one and swap it in."

```ruby
counter = Atom.new(0)
counter.update { |n| n + 1 }         # atomic update via a CAS loop. The block is re-run on conflict
                                     # (on today's single thread: when the value changed while the block waited)
counter.value                        # read (also `get`)
counter.set(0)
counter.compare_and_set(old, new)    # Bool (compares with ==)

registry = Atom[Hash[String, Channel[Message]]].new({})
registry.update { |h| h.put(name, ch) }
```

- Keep the `update` block pure, without side effects (it may be re-executed).
- Updates to persistent data structures are cheap thanks to structural sharing, so even with a large `Hash` in an `Atom`, `update` is O(log n). (Currently collections are not persistent structures, see [03-data-model.md](03-data-model.md) §2: an update in an `Atom` copies the hash, O(n).)
- Putting an `Atom` in a constant gives you a replacement for Ruby's class variables and global variables.

```ruby
STATS = Atom.new({ requests: 0, errors: 0 })
STATS.update { |s| s.put(:requests, s[:requests] + 1) }
```

## 5. Actors and Erlang-style Design

An Erlang process + mailbox can be expressed as a task + a single channel. If the message type is an `enum`, the combination of `receive` and `case/in` gets exhaustiveness checking.

```ruby
enum Msg
  Deposit(amount: Int)
  | Withdraw(amount: Int, reply: Channel[Result[Int, String]])
  | Balance(reply: Channel[Int])
  | Stop
end

def account_actor(inbox: Channel[Msg]) -> Nil
  balance = 0
  inbox.each do |msg|
    case msg
    in Msg::Deposit(amount:)
      balance += amount
    in Msg::Withdraw(amount:, reply:)
      if amount <= balance
        balance -= amount
        reply.send(Result::Ok.new(balance))
      else
        reply.send(Result::Err.new("insufficient funds"))
      end
    in Msg::Balance(reply:)
      reply.send(balance)
    in Msg::Stop
      break
    end
  end
end

Task.scope do |scope|
  inbox = Channel[Msg].new(capacity: 64)
  scope.spawn { account_actor(inbox) }

  inbox.send(Msg::Deposit.new(100))
  reply = Channel[Result[Int, String]].new
  inbox.send(Msg::Withdraw.new(30, reply))
  case reply.receive
  in Result::Ok(value:) then puts "balance: #{value}"
  in Result::Err(error:) then warn error
  end
  inbox.send(Msg::Stop)
end
```

The actor's state (`balance`) is a local variable of the task, so nothing outside that task can touch it. Mutable objects such as Builders are also fine as long as they are used strictly inside the actor.

### Supervision and Restart

An Erlang supervisor can be written as a combination of `Task.scope` and a restart loop. The standard library will provide `Supervisor` (*planned*, as is `Task#on_exit` below).

```ruby
Supervisor.run(strategy: :one_for_one, max_restarts: 5, within: 10.seconds) do |sup|
  sup.child(:db) { db_actor(db_inbox) }
  sup.child(:http) { http_server(8080) }
end
```

- When a child task ends with an exception, it is restarted according to the strategy.
- `Task#on_exit { |result| }` delivers an exit notification (the equivalent of Erlang's `monitor`). The equivalent of `link` is `Task.scope` itself.

## 6. Blocking Operations and IO

- IO in the standard library only suspends the calling task; code is written synchronously. Sockets (`TCPSocket`, `TCPServer`, `UDPSocket`, `UNIXSocket`, `UNIXServer`) are non-blocking descriptors that the scheduler's reactor (`epoll`/`kqueue`, through the `polling` crate) watches: an operation that would block parks the task until the descriptor is ready, and the run loop waits on the reactor when nothing is runnable. Whole-file operations (`File.read`, `File.write`, …), name resolution, `connect` and child processes (`Process.run`) run on a helper thread that wakes the task through the reactor. Reads and writes on an open `File` handle are buffered and synchronous.
- A parked IO operation is interrupted like any other wait: `Task.timeout` and `cancel` raise in the waiting task, and the socket stays usable afterwards.
- The standard streams (`STDIN`, `STDOUT`, `STDERR`) are blocking for now: reading from the terminal stops the scheduler.
- `IO` handles are Shareable: any task may read and write them, and the runtime serializes access. What that guarantees:
  - **One write call goes out whole.** The bytes of one `write`, `print`, `puts`, `printf` or `<<` are never interleaved with another task's output on the same handle (a socket write that has to wait keeps its turn; the others wait for it). The writes of one task appear in its order; between tasks, the order of the calls is whatever the scheduling gives.
  - **One read call takes a whole unit.** `gets` returns a whole line and `read(n)` up to `n` bytes taken together. When several tasks read the same handle, which task receives which line is not specified, but nothing is read twice or lost.
  - **Closing fails what waits.** When a task closes a handle that another task is waiting on, the waiting operation raises `IOError` (`closed stream`), as does any later use.
- `Task.blocking { }` runs its block on a helper thread (one is started whenever none is idle, so a long computation never holds up file IO), and only the calling task waits. Values are owned by one thread, so the block is *copied* to the helper: its captured variables must be Shareable (the same rule as `spawn`), they cannot be assigned inside the block, and only immutable values cross over (numbers, strings, symbols, arrays, hashes, sets, ranges, `data`/`enum` values; a proc made inside the block can be returned, but one cannot be captured, since proc types are not Shareable yet). A `Channel`, `Atom`, `Task` or any mutable value is rejected with `ArgumentError`, since it would have to be shared rather than copied. The block's result or exception comes back the same way, and what it prints is written out when it finishes. Cancelling the waiting task raises in it, but the helper thread runs the block to its end. Use it for long computations and for blocking foreign functions; for IO, the standard library already suspends only the task.

```ruby
digest = Task.blocking { expensive_hash(data) }     # the scheduler keeps running other tasks
```

```ruby
rows = Task.blocking { legacy_c_query(sql) }
```

## 7. Runtime Structure

This is the design. Currently one OS thread runs every task (M:1, see [05-execution.md](05-execution.md) §9); each task has a 16 MiB virtual stack (256 MiB for the main task), which cannot be changed; timers are a binary heap; channels and reference counts are not synchronized, since nothing is shared between threads (`Task.blocking` copies values). The work-stealing scheduler, `QUARZ_THREADS`, `spawn(stack:)`, the timing wheel, lock-free channels and the shared flag below are planned.

- **Scheduler**: work-stealing, with a run queue per OS thread (defaults to the number of CPU cores). `QUARZ_THREADS=1` pins it to a single thread, which is useful for tests that need determinism.
- **Stacks**: virtual memory is reserved per task with `mmap` (default 1 MiB, changeable with `spawn(stack: 8.mib)`), and physical pages are committed only when touched. A guard page sits at the top, and overflow raises `SystemStackError`. On 64-bit systems the address space is ample, so even with a million tasks, real memory is only what is actually used (typically 4–8 KiB per task). Stack copying as in Go was not adopted because it would require rewriting pointers into the stack in AOT-compiled code.
- **Preemption**: cooperative (safepoints). Room is left to add asynchronous signal-based preemption in the future.
- **Timers**: a timing wheel. Used by `sleep`/`after`/`timeout`.
- **Channels**: lock-free MPMC queue + waiter list.
- **Relation to reference counting**: a value that crosses a task boundary (sent on a channel, captured by `spawn`, placed in an `Atom`) gets a "shared" flag set at that moment, and only its subsequent reference-count operations become atomic (the same scheme as Lean 4). Values confined to a task keep non-atomic count operations.

## 8. Rejected Alternatives

- **Locks and shared mutable memory (Java/Go's Mutex)**: even Go relies on detection tools for data races. Confining mutable objects to tasks and sharing only immutable values and `Atom`s eradicates "forgot the lock" bugs, for Ruby programmers too.
- **async/await (function coloring)**: requires marking the call sites of blocking operations, making naive Ruby-style code (just calling `gets`) impossible. Lightweight tasks with their own stacks are cheap and preserve the Ruby feel.
- **Erlang-style per-process heaps**: given that immutable values can be shared, the reason to separate heaps is not to avoid message copying but GC independence; with reference counting there are no GC pauses in the first place.
- **Ruby's Ractor**: the goals are close, but Quarz checks Shareable statically as a type rather than turning it into a runtime error.
