//! Tasks, the scheduler, channels and timers.
//!
//! Every task (including the main program) runs on its own stackful
//! coroutine. A blocking operation registers the task as a waiter on the
//! resource and suspends; the scheduler resumes tasks that became ready,
//! fires timers, and reports deadlock when nothing can make progress.
//!
//! The scheduler lives in a `RefCell` inside the interpreter. Nothing may
//! hold a borrow of it across a suspension, so suspending is done by the
//! free function [`suspend_raw`] after all borrows are released, and the
//! run loop takes a coroutine out of the scheduler before resuming it.

use crate::rc::Rc;
use std::cell::{Cell, RefCell};
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, VecDeque};
#[cfg(not(target_os = "linux"))]
use std::os::fd::BorrowedFd;
use std::os::fd::RawFd;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[cfg(target_os = "linux")]
use crate::epoll::{Event as IoEvent, Poller};
use corosensei::{Coroutine, CoroutineResult, Yielder};
#[cfg(not(target_os = "linux"))]
use polling::{Event, Events, Poller};

use crate::value::Value;

pub type TaskId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TaskState {
    Ready,
    Running,
    Waiting,
    Done,
}

/// The outcome of a task: its value or the exception it died with.
#[derive(Clone, Debug)]
pub enum TaskResult {
    Value(Value),
    Error(Value),
}

/// The coroutine's return: the task's result, or a request to exit the
/// program.
pub enum TaskExit {
    Result(TaskResult),
    Exit(i32),
}

pub struct TaskHandle {
    pub id: TaskId,
    pub state: Cell<TaskState>,
    pub result: RefCell<Option<TaskResult>>,
    /// Tasks waiting for this one to finish.
    pub joiners: RefCell<Vec<TaskId>>,
    pub cancel_requested: Cell<bool>,
    pub scope: RefCell<Option<Rc<ScopeInner>>>,
    pub name: RefCell<String>,
    /// The coroutine's yielder, set when the task first runs.
    pub yielder: Cell<Option<*const Yielder<(), ()>>>,
    /// Lowest stack address the task may use (for `SystemStackError`).
    pub stack_limit: Cell<usize>,
    /// Its native stack (see `STACK_RANGE`).
    pub stack_range: Cell<(usize, usize)>,
}

impl std::fmt::Debug for TaskHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Task#{} ({:?})", self.id, self.state.get())
    }
}

impl TaskHandle {
    pub fn is_done(&self) -> bool {
        self.state.get() == TaskState::Done
    }
}

/// A `Task.scope` with its child tasks.
pub struct ScopeInner {
    pub owner: TaskId,
    pub children: RefCell<Vec<Rc<TaskHandle>>>,
    pub cancelled: Cell<bool>,
}

impl std::fmt::Debug for ScopeInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Scope(owner {})", self.owner)
    }
}

pub struct ChannelInner {
    pub buffer: RefCell<VecDeque<Value>>,
    pub capacity: usize,
    pub closed: Cell<bool>,
    pub recv_waiters: RefCell<VecDeque<TaskId>>,
    pub send_waiters: RefCell<VecDeque<TaskId>>,
    /// Rendezvous bookkeeping for unbuffered channels.
    pub pushed: Cell<u64>,
    pub taken: Cell<u64>,
}

impl std::fmt::Debug for ChannelInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Channel(cap {}, len {})",
            self.capacity,
            self.buffer.borrow().len()
        )
    }
}

impl ChannelInner {
    pub fn new(capacity: usize) -> Rc<ChannelInner> {
        Rc::new_shared(ChannelInner {
            buffer: RefCell::new(VecDeque::new()),
            capacity,
            closed: Cell::new(false),
            recv_waiters: RefCell::new(VecDeque::new()),
            send_waiters: RefCell::new(VecDeque::new()),
            pushed: Cell::new(0),
            taken: Cell::new(0),
        })
    }

    /// Add a value to the buffer: it now crosses to the task that takes
    /// it.
    pub fn put(&self, value: Value) {
        value.share();
        self.buffer.borrow_mut().push_back(value);
    }

    /// Whether a value can be pushed right now.
    pub fn can_send(&self) -> bool {
        let len = self.buffer.borrow().len();
        if self.capacity == 0 {
            len == 0
        } else {
            len < self.capacity
        }
    }

    pub fn can_receive(&self) -> bool {
        !self.buffer.borrow().is_empty()
    }
}

/// A `select` in progress: the registered alternatives.
#[derive(Debug, Default)]
pub struct SelectorState {
    pub receives: Vec<(Rc<ChannelInner>, Value)>,
    pub sends: Vec<(Rc<ChannelInner>, Value, Value)>,
    pub after: Option<(Duration, Value)>,
    pub default: Option<Value>,
    pub stopped: bool,
}

pub type TaskCoroutine = Coroutine<(), (), TaskExit>;

/// Tasks waiting for a file descriptor to become readable or writable.
#[derive(Default)]
struct IoWaiters {
    readers: Vec<TaskId>,
    writers: Vec<TaskId>,
}

/// The IO reactor: an `epoll`/`kqueue` poller that the run loop waits on
/// when nothing is runnable, plus the completions of work pushed to
/// other threads (file IO, DNS, child processes), which wake the waiting
/// task through the poller's notification.
pub struct Reactor {
    pub poller: Arc<Poller>,
    #[cfg(target_os = "linux")]
    events: Vec<IoEvent>,
    #[cfg(not(target_os = "linux"))]
    events: Events,
    waiters: HashMap<RawFd, IoWaiters>,
    completions: Arc<Mutex<Vec<TaskId>>>,
    pending_jobs: usize,
}

impl Reactor {
    fn new() -> Reactor {
        Reactor {
            poller: Arc::new(Poller::new().expect("create the IO poller")),
            #[cfg(target_os = "linux")]
            events: Vec::new(),
            #[cfg(not(target_os = "linux"))]
            events: Events::new(),
            waiters: HashMap::new(),
            completions: Arc::new(Mutex::new(Vec::new())),
            pending_jobs: 0,
        }
    }

    fn idle(&self) -> bool {
        self.waiters.is_empty() && self.pending_jobs == 0
    }

    /// The interest to arm for a descriptor, from who is waiting on it
    /// (on Linux it is registered for both directions, edge-triggered,
    /// once: nothing to arm).
    #[cfg(target_os = "linux")]
    fn arm(&self, _fd: RawFd) {}

    /// The interest to arm for a descriptor, from who is waiting on it.
    #[cfg(not(target_os = "linux"))]
    fn arm(&self, fd: RawFd) {
        let Some(w) = self.waiters.get(&fd) else {
            return;
        };
        let interest = match (!w.readers.is_empty(), !w.writers.is_empty()) {
            (true, true) => Event::all(fd as usize),
            (true, false) => Event::readable(fd as usize),
            (false, true) => Event::writable(fd as usize),
            (false, false) => Event::none(fd as usize),
        };
        // SAFETY: the descriptor is registered and open while it has
        // waiters (sockets deregister before closing).
        let source = unsafe { BorrowedFd::borrow_raw(fd) };
        let _ = self.poller.modify(source, interest);
    }
}

pub struct Scheduler {
    pub tasks: Vec<Rc<TaskHandle>>,
    coroutines: Vec<Option<TaskCoroutine>>,
    ready: VecDeque<TaskId>,
    timers: BinaryHeap<Reverse<(Instant, u64, TaskId)>>,
    timer_seq: u64,
    pub current: Option<TaskId>,
    cancelled_timers: Vec<u64>,
    pub reactor: Reactor,
}

thread_local! {
    static YIELDER: Cell<Option<*const Yielder<(), ()>>> = const { Cell::new(None) };
    static STACK_LIMIT: Cell<usize> = const { Cell::new(0) };
    /// The running task's native stack, `(lowest, highest)` address: a
    /// backtrace keeps the frames found there (the unwinder continues
    /// into the stack a coroutine was resumed from).
    static STACK_RANGE: Cell<(usize, usize)> = const { Cell::new((0, usize::MAX)) };
}

/// Whether the current stack pointer is below the task's limit.
#[inline]
/// This thread's stack-limit cell (compiled code reads it through
/// `Interp::hot`).
pub fn stack_limit_cell() -> *const Cell<usize> {
    STACK_LIMIT.with(|l| l as *const Cell<usize>)
}

/// The running task's native stack range (see `STACK_RANGE`).
pub fn stack_range() -> (usize, usize) {
    STACK_RANGE.with(|r| r.get())
}

pub fn stack_exhausted() -> bool {
    let marker = 0u8;
    let sp = &marker as *const u8 as usize;
    STACK_LIMIT.with(|l| sp < l.get())
}

/// Suspend the running coroutine. Only valid inside a task, with no
/// `RefCell` borrows of the scheduler held.
pub fn suspend_raw() {
    let yielder = YIELDER
        .with(|y| y.get())
        .expect("suspend outside of a task");
    // SAFETY: the yielder lives as long as the coroutine runs, and this is
    // only called from inside it.
    unsafe { (*yielder).suspend(()) };
}

impl Default for Scheduler {
    fn default() -> Self {
        Scheduler::new()
    }
}

impl Scheduler {
    pub fn new() -> Scheduler {
        Scheduler {
            tasks: Vec::new(),
            coroutines: Vec::new(),
            ready: VecDeque::new(),
            timers: BinaryHeap::new(),
            timer_seq: 0,
            current: None,
            cancelled_timers: Vec::new(),
            reactor: Reactor::new(),
        }
    }

    // ----- IO ---------------------------------------------------------------------

    /// Register a non-blocking descriptor with the reactor (no interest
    /// yet). The owner must `deregister` it before closing it.
    pub fn register(&self, fd: RawFd) {
        #[cfg(target_os = "linux")]
        let _ = self.reactor.poller.add(fd);
        // SAFETY: the caller keeps the descriptor open until `deregister`.
        #[cfg(not(target_os = "linux"))]
        let _ = unsafe { self.reactor.poller.add(fd, Event::none(fd as usize)) };
    }

    pub fn deregister(&mut self, fd: RawFd) {
        #[cfg(target_os = "linux")]
        let _ = self.reactor.poller.delete(fd);
        // SAFETY: the descriptor is still open (deregistration precedes
        // the close).
        #[cfg(not(target_os = "linux"))]
        let _ = self
            .reactor
            .poller
            .delete(unsafe { BorrowedFd::borrow_raw(fd) });
        if let Some(w) = self.reactor.waiters.remove(&fd) {
            for id in w.readers.into_iter().chain(w.writers) {
                self.wake(id);
            }
        }
    }

    /// Record that `id` waits for `fd` to become readable (or writable);
    /// the caller then parks.
    pub fn wait_fd(&mut self, fd: RawFd, writable: bool, id: TaskId) {
        let w = self.reactor.waiters.entry(fd).or_default();
        let list = if writable {
            &mut w.writers
        } else {
            &mut w.readers
        };
        if !list.contains(&id) {
            list.push(id);
        }
        self.reactor.arm(fd);
    }

    /// Forget `id`'s interest in `fd` (its wait ended, by an event or
    /// otherwise).
    pub fn unwait_fd(&mut self, fd: RawFd, id: TaskId) {
        let Some(w) = self.reactor.waiters.get_mut(&fd) else {
            return;
        };
        w.readers.retain(|t| *t != id);
        w.writers.retain(|t| *t != id);
        if w.readers.is_empty() && w.writers.is_empty() {
            self.reactor.waiters.remove(&fd);
            // SAFETY: the descriptor is open while it is registered.
            #[cfg(not(target_os = "linux"))]
            let _ = self.reactor.poller.modify(
                unsafe { BorrowedFd::borrow_raw(fd) },
                Event::none(fd as usize),
            );
        } else {
            self.reactor.arm(fd);
        }
    }

    /// Run `job` on a helper thread; the task `id` is woken when it
    /// finishes and takes the result from the returned receiver.
    pub fn offload<T: Send + 'static>(
        &mut self,
        id: TaskId,
        job: impl FnOnce() -> T + Send + 'static,
    ) -> std::sync::mpsc::Receiver<T> {
        let (tx, rx) = std::sync::mpsc::channel();
        let completions = self.reactor.completions.clone();
        let poller = self.reactor.poller.clone();
        self.reactor.pending_jobs += 1;
        pool_submit(Box::new(move || {
            let result = job();
            let _ = tx.send(result);
            completions.lock().unwrap().push(id);
            let _ = poller.notify();
        }));
        rx
    }

    /// Wait for IO events (at most `timeout`) and wake the tasks they
    /// concern. Returns whether any task was woken.
    fn poll_io(&mut self, timeout: Option<Duration>) -> bool {
        let mut woke = false;
        let mut events = std::mem::take(&mut self.reactor.events);
        #[cfg(target_os = "linux")]
        let happened: Vec<(RawFd, bool, bool, bool)> = {
            events.clear();
            let _ = self.reactor.poller.wait(&mut events, timeout);
            events
                .iter()
                .map(|e| (e.fd, e.readable, e.writable, e.failed))
                .collect()
        };
        #[cfg(not(target_os = "linux"))]
        let happened: Vec<(RawFd, bool, bool, bool)> = {
            events.clear();
            let _ = self.reactor.poller.wait(&mut events, timeout);
            events
                .iter()
                .map(|ev| {
                    let failed = ev.is_err() == Some(true) || ev.is_interrupt();
                    (ev.key as RawFd, ev.readable, ev.writable, failed)
                })
                .collect()
        };
        self.reactor.events = events;
        let mut rearm = Vec::new();
        for (fd, readable, writable, failed) in happened {
            let Some(w) = self.reactor.waiters.get_mut(&fd) else {
                continue;
            };
            let mut woken = Vec::new();
            if readable || failed {
                woken.append(&mut w.readers);
            }
            if writable || failed {
                woken.append(&mut w.writers);
            }
            if w.readers.is_empty() && w.writers.is_empty() {
                self.reactor.waiters.remove(&fd);
            } else {
                rearm.push(fd);
            }
            for id in woken {
                self.wake(id);
                woke = true;
            }
        }
        for fd in rearm {
            self.reactor.arm(fd);
        }
        let done: Vec<TaskId> = std::mem::take(&mut *self.reactor.completions.lock().unwrap());
        for id in done {
            self.reactor.pending_jobs = self.reactor.pending_jobs.saturating_sub(1);
            self.wake(id);
            woke = true;
        }
        woke
    }

    /// When the earliest timer is due.
    fn next_timer(&mut self) -> Option<Instant> {
        loop {
            let Reverse((when, seq, _)) = self.timers.peek().cloned()?;
            if let Some(pos) = self.cancelled_timers.iter().position(|s| *s == seq) {
                self.cancelled_timers.swap_remove(pos);
                self.timers.pop();
                continue;
            }
            return Some(when);
        }
    }

    pub fn task(&self, id: TaskId) -> &Rc<TaskHandle> {
        &self.tasks[id as usize]
    }

    pub fn current_task(&self) -> Rc<TaskHandle> {
        let id = self.current.expect("no current task");
        self.tasks[id as usize].clone()
    }

    /// Create a task running `body` on its own coroutine stack.
    pub fn spawn(
        &mut self,
        body: Box<dyn FnOnce() -> TaskExit>,
        scope: Option<Rc<ScopeInner>>,
        name: String,
        stack_size: usize,
    ) -> Rc<TaskHandle> {
        let id = self.tasks.len() as TaskId;
        let handle = Rc::new_shared(TaskHandle {
            id,
            state: Cell::new(TaskState::Ready),
            result: RefCell::new(None),
            joiners: RefCell::new(Vec::new()),
            cancel_requested: Cell::new(false),
            scope: RefCell::new(scope.clone()),
            name: RefCell::new(name),
            yielder: Cell::new(None),
            stack_limit: Cell::new(0),
            stack_range: Cell::new((0, usize::MAX)),
        });
        if let Some(scope) = &scope {
            scope.children.borrow_mut().push(handle.clone());
        }
        let stack = corosensei::stack::DefaultStack::new(stack_size).expect("coroutine stack");
        let handle_for_body = handle.clone();
        let coroutine = Coroutine::with_stack(stack, move |yielder: &Yielder<(), ()>, ()| {
            handle_for_body.yielder.set(Some(yielder as *const _));
            YIELDER.with(|y| y.set(Some(yielder as *const _)));
            // Leave a margin below which calls raise SystemStackError.
            let marker = 0u8;
            let base = &marker as *const u8 as usize;
            let limit = base.saturating_sub(stack_size.saturating_sub(512 * 1024));
            handle_for_body.stack_limit.set(limit);
            STACK_LIMIT.with(|l| l.set(limit));
            // (The marker is near the top; frames above it are the
            // coroutine's own entry frames.)
            let range = (base.saturating_sub(stack_size), base + 4096);
            handle_for_body.stack_range.set(range);
            STACK_RANGE.with(|r| r.set(range));
            body()
        });
        self.tasks.push(handle.clone());
        self.coroutines.push(Some(coroutine));
        self.ready.push_back(id);
        handle
    }

    pub fn wake(&mut self, id: TaskId) {
        let task = &self.tasks[id as usize];
        if task.state.get() == TaskState::Waiting {
            task.state.set(TaskState::Ready);
            self.ready.push_back(id);
        }
    }

    /// Mark the current task ready again (for `Task.yield`); the caller
    /// then suspends.
    pub fn requeue_current(&mut self) {
        let id = self.current.expect("no current task");
        self.tasks[id as usize].state.set(TaskState::Ready);
        self.ready.push_back(id);
    }

    pub fn add_timer(&mut self, after: Duration, id: TaskId) -> u64 {
        self.timer_seq += 1;
        let seq = self.timer_seq;
        self.timers.push(Reverse((Instant::now() + after, seq, id)));
        seq
    }

    pub fn cancel_timer(&mut self, seq: u64) {
        self.cancelled_timers.push(seq);
    }

    fn fire_due_timers(&mut self, block: bool) -> bool {
        let mut fired = false;
        loop {
            let Some(Reverse((when, seq, tid))) = self.timers.peek().cloned() else {
                return fired;
            };
            if let Some(pos) = self.cancelled_timers.iter().position(|s| *s == seq) {
                self.cancelled_timers.swap_remove(pos);
                self.timers.pop();
                continue;
            }
            let now = Instant::now();
            if when > now {
                if block && !fired {
                    std::thread::sleep(when - now);
                } else {
                    return fired;
                }
            }
            self.timers.pop();
            self.wake(tid);
            fired = true;
        }
    }

    /// Take the next runnable task and its coroutine. Sleeps for the
    /// earliest timer when nothing is ready. Returns `None` when there is
    /// nothing to run at all (deadlock or completion).
    pub fn next_runnable(&mut self) -> Option<(TaskId, TaskCoroutine)> {
        self.fire_due_timers(false);
        // Keep IO flowing while tasks are busy (on Linux one epoll_wait:
        // polling only every 32 switches measured slower, the woken tasks
        // waiting longer).
        if !self.reactor.idle() {
            self.poll_io(Some(Duration::ZERO));
        }
        loop {
            while let Some(id) = self.ready.pop_front() {
                let task = &self.tasks[id as usize];
                if task.state.get() == TaskState::Done {
                    continue;
                }
                if let Some(co) = self.coroutines[id as usize].take() {
                    task.state.set(TaskState::Running);
                    self.current = Some(id);
                    return Some((id, co));
                }
            }
            if self.reactor.idle() {
                if !self.fire_due_timers(true) {
                    return None;
                }
                continue;
            }
            // Nothing runnable: wait for IO, or for the next timer.
            let timeout = self
                .next_timer()
                .map(|when| when.saturating_duration_since(Instant::now()));
            self.poll_io(timeout);
            self.fire_due_timers(false);
        }
    }

    /// Put a task back after it yielded or finished.
    pub fn after_resume(
        &mut self,
        id: TaskId,
        co: TaskCoroutine,
        result: CoroutineResult<(), TaskExit>,
    ) -> Option<i32> {
        self.current = None;
        let task = self.tasks[id as usize].clone();
        match result {
            CoroutineResult::Yield(()) => {
                self.coroutines[id as usize] = Some(co);
                if task.state.get() == TaskState::Running {
                    task.state.set(TaskState::Ready);
                    self.ready.push_back(id);
                }
                None
            }
            CoroutineResult::Return(exit) => {
                task.state.set(TaskState::Done);
                drop(co);
                match exit {
                    TaskExit::Exit(code) => Some(code),
                    TaskExit::Result(r) => {
                        let failed = matches!(r, TaskResult::Error(_));
                        // The result (or exception) passes to whoever
                        // awaits the task.
                        match &r {
                            TaskResult::Value(v) | TaskResult::Error(v) => v.share(),
                        }
                        *task.result.borrow_mut() = Some(r);
                        let joiners = std::mem::take(&mut *task.joiners.borrow_mut());
                        for j in joiners {
                            self.wake(j);
                        }
                        // A failing child cancels its siblings and wakes the
                        // scope's owner so that the failure propagates at
                        // once.
                        if failed {
                            let scope = task.scope.borrow().clone();
                            if let Some(scope) = scope {
                                if !scope.cancelled.get() {
                                    scope.cancelled.set(true);
                                    let children: Vec<Rc<TaskHandle>> =
                                        scope.children.borrow().clone();
                                    for c in children {
                                        if c.id != id && !c.is_done() {
                                            c.cancel_requested.set(true);
                                            self.wake(c.id);
                                        }
                                    }
                                }
                                self.wake(scope.owner);
                            }
                        }
                        None
                    }
                }
            }
        }
    }

    /// Names of tasks that are blocked (for the deadlock report).
    pub fn waiting_tasks(&self) -> Vec<String> {
        self.tasks
            .iter()
            .filter(|t| t.state.get() == TaskState::Waiting)
            .map(|t| format!("{} ({})", t.name.borrow(), t.id))
            .collect()
    }
}

/// Resume a task's coroutine outside of the scheduler's borrow.
pub fn resume(task: &TaskHandle, co: &mut TaskCoroutine) -> CoroutineResult<(), TaskExit> {
    let outer = YIELDER.with(|y| y.get());
    let outer_limit = STACK_LIMIT.with(|l| l.get());
    let outer_range = STACK_RANGE.with(|r| r.get());
    YIELDER.with(|y| y.set(task.yielder.get()));
    STACK_LIMIT.with(|l| l.set(task.stack_limit.get()));
    STACK_RANGE.with(|r| r.set(task.stack_range.get()));
    let r = co.resume(());
    YIELDER.with(|y| y.set(outer));
    STACK_LIMIT.with(|l| l.set(outer_limit));
    STACK_RANGE.with(|r| r.set(outer_range));
    r
}

// ----- the helper thread pool ---------------------------------------------------------

type Job = Box<dyn FnOnce() + Send + 'static>;

/// Threads for offloaded work. A job never waits for a thread: when all
/// of them are busy a new one is started, so a long `Task.blocking`
/// computation cannot hold up file IO. Idle threads are kept.
struct Pool {
    queue: Mutex<(VecDeque<Job>, usize)>,
    available: std::sync::Condvar,
}

static POOL: std::sync::OnceLock<Pool> = std::sync::OnceLock::new();

fn pool_submit(job: Job) {
    let pool = POOL.get_or_init(|| Pool {
        queue: Mutex::new((VecDeque::new(), 0)),
        available: std::sync::Condvar::new(),
    });
    let mut q = pool.queue.lock().unwrap();
    q.0.push_back(job);
    if q.1 < q.0.len() {
        // Fewer idle threads (including ones still starting) than
        // queued jobs: start one. It counts as idle until it takes a job.
        q.1 += 1;
        drop(q);
        std::thread::Builder::new()
            .name("quarz-helper".to_string())
            .spawn(move || pool_worker(pool))
            .expect("spawn a helper thread");
    } else {
        drop(q);
        pool.available.notify_one();
    }
}

fn pool_worker(pool: &'static Pool) {
    loop {
        let job = {
            let mut q = pool.queue.lock().unwrap();
            loop {
                if let Some(job) = q.0.pop_front() {
                    q.1 -= 1;
                    break job;
                }
                q = pool.available.wait(q).unwrap();
            }
        };
        job();
        pool.queue.lock().unwrap().1 += 1;
    }
}
