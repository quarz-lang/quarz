# Concurrent Programming

日本語版: [04-concurrency.ja.md](04-concurrency.ja.md)

Quarz's concurrency model consists of three parts.

1. **Tasks** — lightweight threads corresponding to goroutines / Erlang processes. They are M:N scheduled, and hundreds of thousands can run at once.
2. **Channels** — typed message queues. All communication and synchronization between tasks goes through them.
3. **Atom** — a shared cell holding an immutable value. Updated via CAS, so multiple tasks can read and write it safely.

And there is one rule that spans the whole language: **mutable objects never cross task boundaries** ([03-data-model.md](03-data-model.md) §5). This eliminates data races at compile time. The language provides no locks (a `Mutex` for FFI purposes lives in the `FFI` module).

## 1. Tasks

```ruby
t = spawn { heavy_computation(42) }   # Task[Int]
puts t.await                          # wait for completion and receive the value

Task.sleep(100.ms)
Task.yield                            # yield to other tasks
Task.current                          # the current Task
```

- `spawn { }` creates a new task, registers it with the scheduler, and returns immediately. The `T` in the returned `Task[T]` is the type of the block.
- The block **captures by value**. Outer local variables are copied at the time of `spawn`, and the block cannot assign to outer variables. Every captured value must be Shareable.
- `await` waits for the task to complete and returns its value. If the task ended with an exception, that exception is re-raised on the side that called `await`.
- Tasks switch cooperatively at safepoints inserted by the compiler (method entry, loop back-edges, channel operations, allocation). Even a pure computational loop switches at loop boundaries, so no single task can monopolize the scheduler.
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
- If a task in the scope ends with an exception, **the remaining tasks are cancelled**, and after waiting for them to complete, the exception is re-raised to the caller of `Task.scope`. If multiple tasks failed, the first exception is raised and the rest are attached as a `cause` chain.
- If the block body itself raises, the same thing happens: child tasks are cancelled and waited for before the exception propagates.
- Scopes can be nested. Cancellation propagates inward through nested scopes.
- A top-level `spawn` (without a `scope`) belongs to the program's root scope. When the main top-level code finishes, the program exits and any remaining tasks are cancelled (the same as Ruby's main thread exiting). Long-lived services should wait explicitly with `Task.scope`.

### Cancellation

```ruby
Task.scope do |scope|
  worker = scope.spawn { loop { process(queue.receive) } }
  Task.sleep(1.second)
  worker.cancel
end

Task.timeout(5.seconds) { slow_call }     # raises Task::Timeout when exceeded
```

- `cancel` sets a "cancellation request" on the target task. The requested task receives a `Task::Cancelled` exception at the next blocking operation it performs (channel, IO, `sleep`, `await`), or when it calls `Task.check_cancel`.
- `Task::Cancelled` is a direct subclass of `Exception`, not `StandardError`, so `rescue => e` does not catch it. `ensure` runs as usual, so cleanup goes there.
- Cancellation is a request, not a force. Computation-only loops need to call `Task.check_cancel` periodically (there is also an option to check automatically at safepoints: `--cancel-at-safepoints`).

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

- The `T` of `Channel[T]` must be Shareable.
- A channel with capacity 0 is a rendezvous between sender and receiver and can be used for synchronization.
- `send`/`receive` establish happens-before. Updates made before a `send` are visible after the corresponding `receive`. This is the entirety of Quarz's memory model (since there is no shared mutable state, there is nothing else to specify).
- If every task is waiting on a channel and the program deadlocks, the runtime stops the program with `DeadlockError` (the same as Go's "all goroutines are asleep").

### `select`

Executes exactly one of several channel operations, whichever becomes possible first.

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
counter.value                        # read
counter.set(0)
counter.compare_and_set(old, new)    # Bool

registry = Atom[Hash[String, Channel[Message]]].new({})
registry.update { |h| h.put(name, ch) }
```

- Keep the `update` block pure, without side effects (it may be re-executed).
- Updates to persistent data structures are cheap thanks to structural sharing, so even with a large `Hash` in an `Atom`, `update` is O(log n).
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
  Withdraw(amount: Int, reply: Channel[Result[Int, String]])
  Balance(reply: Channel[Int])
  Stop
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

An Erlang supervisor can be written as a combination of `Task.scope` and a restart loop. The standard library provides `Supervisor`.

```ruby
Supervisor.run(strategy: :one_for_one, max_restarts: 5, within: 10.seconds) do |sup|
  sup.child(:db) { db_actor(db_inbox) }
  sup.child(:http) { http_server(8080) }
end
```

- When a child task ends with an exception, it is restarted according to the strategy.
- `Task#on_exit { |result| }` delivers an exit notification (the equivalent of Erlang's `monitor`). The equivalent of `link` is `Task.scope` itself.

## 6. Blocking Operations and IO

- All IO in the standard library (`File`, `Socket`, `IO`, `Process`) is built on the asynchronous runtime (io_uring / epoll / kqueue), and only the calling task waits. Code is written synchronously.
- `IO` handles are not Shareable and can only be used from the owning task. To let other tasks read or write, mediate through a channel.
- To push a potentially blocking C function (FFI) or a long computation onto an OS thread, use `Task.blocking { }`. It runs on a dedicated thread pool and the scheduler does not stall.

```ruby
rows = Task.blocking { legacy_c_query(sql) }
```

## 7. Runtime Structure

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
