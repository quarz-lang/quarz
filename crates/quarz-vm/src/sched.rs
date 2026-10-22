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
use std::cell::Cell;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, VecDeque};
#[cfg(not(target_os = "linux"))]
use std::os::fd::BorrowedFd;
use std::os::fd::RawFd;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant};

#[cfg(target_os = "linux")]
use crate::epoll::{Event as IoEvent, Poller};
use corosensei::{Coroutine, CoroutineResult, Yielder};
#[cfg(not(target_os = "linux"))]
use polling::{Event, Events, Poller};

use crate::value::Value;

/// A task's number on the worker thread that runs it.
pub type TaskId = u32;

/// A task anywhere: the worker that runs it and its number there. What
/// waits for a resource (a channel, another task, a constant) records
/// this, since the task that wakes it may run on another worker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TaskRef {
    pub worker: u32,
    pub id: TaskId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum TaskState {
    Ready,
    Running,
    Waiting,
    Done,
}

/// Whether tasks run on more than one thread: set, once and for good,
/// before the second worker starts (when no lock is held: the starting
/// thread holds none, and the new one sees the flag through its start).
static MULTI_THREADED: AtomicBool = AtomicBool::new(false);

pub fn set_multi_threaded() {
    MULTI_THREADED.store(true, Ordering::Release);
}

pub fn multi_threaded() -> bool {
    MULTI_THREADED.load(Ordering::Relaxed)
}

/// A lock for state that is held only briefly and never across a wait or
/// a system call (a channel's buffer and waiters): taking it is one
/// atomic exchange and releasing it a plain store, where a `Mutex` costs
/// two locked instructions; with one worker, which alone touches it,
/// taking it is a plain store too. A thread that finds it taken spins,
/// then yields its CPU.
pub struct SpinLock<T> {
    locked: AtomicBool,
    value: std::cell::UnsafeCell<T>,
}

// SAFETY: the lock gives one thread at a time access to the value.
unsafe impl<T: Send> Sync for SpinLock<T> {}
unsafe impl<T: Send> Send for SpinLock<T> {}

pub struct SpinGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> SpinLock<T> {
    pub const fn new(value: T) -> SpinLock<T> {
        SpinLock {
            locked: AtomicBool::new(false),
            value: std::cell::UnsafeCell::new(value),
        }
    }

    #[inline]
    pub fn lock(&self) -> SpinGuard<'_, T> {
        if !multi_threaded() {
            debug_assert!(!self.locked.load(Ordering::Relaxed), "a lock taken twice");
            self.locked.store(true, Ordering::Relaxed);
        } else if self
            .locked
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            self.lock_slow();
        }
        SpinGuard { lock: self }
    }

    #[cold]
    fn lock_slow(&self) {
        let mut spins = 0u32;
        loop {
            while self.locked.load(Ordering::Relaxed) {
                if spins < 100 {
                    spins += 1;
                    std::hint::spin_loop();
                } else {
                    std::thread::yield_now();
                }
            }
            if self
                .locked
                .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                return;
            }
        }
    }
}

impl<T> std::ops::Deref for SpinGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        // SAFETY: the guard holds the lock.
        unsafe { &*self.lock.value.get() }
    }
}

impl<T> std::ops::DerefMut for SpinGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: the guard holds the lock.
        unsafe { &mut *self.lock.value.get() }
    }
}

impl<T> Drop for SpinGuard<'_, T> {
    #[inline]
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}

/// The runtime's locks: a panic while one is held leaves nothing half
/// done, so a poisoned lock is still used.
pub fn lock<T: ?Sized>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
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

/// A task, as other tasks see it (any worker may hold it: it is
/// allocated shared). Only the worker that runs the task changes its
/// state and its stack fields; the others read the state, take the
/// result, register as joiners and request cancellation.
pub struct TaskHandle {
    pub id: TaskId,
    pub worker: u32,
    state: AtomicU8,
    pub result: Mutex<Option<TaskResult>>,
    /// Tasks waiting for this one to finish.
    pub joiners: Mutex<Vec<TaskRef>>,
    cancel_requested: AtomicBool,
    pub scope: Option<Rc<ScopeInner>>,
    pub name: String,
    /// The coroutine's yielder, set when the task first runs.
    yielder: AtomicPtr<Yielder<(), ()>>,
    /// Lowest stack address the task may use (for `SystemStackError`).
    stack_limit: AtomicUsize,
    /// Its native stack (see `STACK_RANGE`).
    stack_low: AtomicUsize,
    stack_high: AtomicUsize,
}

impl std::fmt::Debug for TaskHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Task#{} ({:?})", self.id, self.state())
    }
}

impl TaskHandle {
    pub fn task_ref(&self) -> TaskRef {
        TaskRef {
            worker: self.worker,
            id: self.id,
        }
    }

    pub fn state(&self) -> TaskState {
        match self.state.load(Ordering::Acquire) {
            0 => TaskState::Ready,
            1 => TaskState::Running,
            2 => TaskState::Waiting,
            _ => TaskState::Done,
        }
    }

    /// (Its worker only. Release: what the task did, its result above
    /// all, happens before a `Done` another worker reads.)
    pub fn set_state(&self, s: TaskState) {
        self.state.store(s as u8, Ordering::Release);
    }

    pub fn is_done(&self) -> bool {
        self.state() == TaskState::Done
    }

    pub fn cancel_requested(&self) -> bool {
        self.cancel_requested.load(Ordering::Acquire)
    }

    pub fn set_cancel_requested(&self, on: bool) {
        self.cancel_requested.store(on, Ordering::Release);
    }

    /// Take the cancellation request, if any.
    pub fn take_cancel(&self) -> bool {
        // A plain load first: a request is rare, and a swap every time a
        // task waits costs a locked instruction.
        self.cancel_requested.load(Ordering::Acquire)
            && self.cancel_requested.swap(false, Ordering::AcqRel)
    }

    pub fn result(&self) -> Option<TaskResult> {
        lock(&self.result).clone()
    }

    fn stack_range(&self) -> (usize, usize) {
        (
            self.stack_low.load(Ordering::Relaxed),
            self.stack_high.load(Ordering::Relaxed),
        )
    }
}

/// A `Task.scope` with its child tasks.
pub struct ScopeInner {
    pub owner: TaskRef,
    pub children: Mutex<Vec<Rc<TaskHandle>>>,
    cancelled: AtomicBool,
}

impl std::fmt::Debug for ScopeInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Scope(owner {:?})", self.owner)
    }
}

impl ScopeInner {
    pub fn new(owner: TaskRef) -> Rc<ScopeInner> {
        Rc::new_shared(ScopeInner {
            owner,
            children: Mutex::new(Vec::new()),
            cancelled: AtomicBool::new(false),
        })
    }

    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }

    /// Mark the scope cancelled; returns whether it was not yet.
    pub fn cancel(&self) -> bool {
        !self.cancelled.swap(true, Ordering::AcqRel)
    }

    pub fn child(&self, i: usize) -> Option<Rc<TaskHandle>> {
        lock(&self.children).get(i).cloned()
    }

    pub fn children(&self) -> Vec<Rc<TaskHandle>> {
        lock(&self.children).clone()
    }
}

/// A channel. Its state is behind one lock, which no task holds while it
/// waits: a task registers as a waiter, releases the lock, and parks.
pub struct ChannelInner {
    pub capacity: usize,
    state: SpinLock<ChannelState>,
}

#[derive(Default)]
pub struct ChannelState {
    pub buffer: VecDeque<Value>,
    pub closed: bool,
    pub recv_waiters: VecDeque<TaskRef>,
    pub send_waiters: VecDeque<TaskRef>,
    /// Rendezvous bookkeeping for unbuffered channels.
    pub pushed: u64,
    pub taken: u64,
}

impl std::fmt::Debug for ChannelInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Channel(cap {}, len {})",
            self.capacity,
            self.lock().buffer.len()
        )
    }
}

impl ChannelInner {
    pub fn new(capacity: usize) -> Rc<ChannelInner> {
        Rc::new_shared(ChannelInner {
            capacity,
            state: SpinLock::new(ChannelState::default()),
        })
    }

    #[inline]
    pub fn lock(&self) -> SpinGuard<'_, ChannelState> {
        self.state.lock()
    }
}

impl ChannelState {
    /// Add a value to the buffer: it now crosses to the task that takes
    /// it.
    pub fn put(&mut self, value: Value) {
        value.share();
        self.buffer.push_back(value);
        self.pushed += 1;
    }

    /// Whether a value can be pushed right now.
    pub fn can_send(&self, capacity: usize) -> bool {
        let len = self.buffer.len();
        if capacity == 0 {
            // Unbuffered: one value in flight at a time.
            len == 0
        } else {
            len < capacity
        }
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
    /// The descriptors registered with this poller, with the serial of
    /// each (`IoWatch`): a descriptor number reused after a close is
    /// registered anew (closing one removes it from every poller).
    registered: HashMap<RawFd, u64>,
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
            registered: HashMap::new(),
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
    /// This worker's number (its tasks' `TaskRef::worker`).
    pub worker: u32,
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
            worker: 0,
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

    /// Register a non-blocking descriptor with this worker's poller, if
    /// it is not yet (the first time one of its tasks waits on it: an
    /// edge-triggered registration reports a descriptor that is ready
    /// already). The owner deregisters it before closing it.
    fn ensure_registered(&mut self, fd: RawFd, serial: u64) {
        if self.reactor.registered.get(&fd) == Some(&serial) {
            return;
        }
        #[cfg(target_os = "linux")]
        let _ = self.reactor.poller.add(fd);
        // SAFETY: the caller keeps the descriptor open until `deregister`.
        #[cfg(not(target_os = "linux"))]
        let _ = unsafe { self.reactor.poller.add(fd, Event::none(fd as usize)) };
        self.reactor.registered.insert(fd, serial);
    }

    /// Forget a descriptor about to be closed (on this worker; the close
    /// removes it from the other workers' pollers).
    pub fn deregister(&mut self, fd: RawFd) {
        if self.reactor.registered.remove(&fd).is_some() {
            #[cfg(target_os = "linux")]
            let _ = self.reactor.poller.delete(fd);
            // SAFETY: the descriptor is still open (deregistration
            // precedes the close).
            #[cfg(not(target_os = "linux"))]
            let _ = self
                .reactor
                .poller
                .delete(unsafe { BorrowedFd::borrow_raw(fd) });
        }
        if let Some(w) = self.reactor.waiters.remove(&fd) {
            for id in w.readers.into_iter().chain(w.writers) {
                self.wake(id);
            }
        }
    }

    /// Record that `id` waits for `fd` (with `serial`, see `IoWatch`) to
    /// become readable (or writable); the caller then parks.
    pub fn wait_fd(&mut self, fd: RawFd, serial: u64, writable: bool, id: TaskId) {
        self.ensure_registered(fd, serial);
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

    /// The running task, without taking a reference to its handle.
    pub fn current_ref(&self) -> TaskRef {
        TaskRef {
            worker: self.worker,
            id: self.current.expect("no current task"),
        }
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
            worker: self.worker,
            state: AtomicU8::new(TaskState::Ready as u8),
            result: Mutex::new(None),
            joiners: Mutex::new(Vec::new()),
            cancel_requested: AtomicBool::new(false),
            scope: scope.clone(),
            name,
            yielder: AtomicPtr::new(std::ptr::null_mut()),
            stack_limit: AtomicUsize::new(0),
            stack_low: AtomicUsize::new(0),
            stack_high: AtomicUsize::new(usize::MAX),
        });
        if let Some(scope) = &scope {
            lock(&scope.children).push(handle.clone());
        }
        let stack = corosensei::stack::DefaultStack::new(stack_size).expect("coroutine stack");
        let handle_for_body = handle.clone();
        let coroutine = Coroutine::with_stack(stack, move |yielder: &Yielder<(), ()>, ()| {
            let y = yielder as *const Yielder<(), ()> as *mut Yielder<(), ()>;
            handle_for_body.yielder.store(y, Ordering::Relaxed);
            YIELDER.with(|c| c.set(Some(yielder as *const _)));
            // Leave a margin below which calls raise SystemStackError.
            let marker = 0u8;
            let base = &marker as *const u8 as usize;
            let limit = base.saturating_sub(stack_size.saturating_sub(512 * 1024));
            handle_for_body.stack_limit.store(limit, Ordering::Relaxed);
            STACK_LIMIT.with(|l| l.set(limit));
            // (The marker is near the top; frames above it are the
            // coroutine's own entry frames.)
            let range = (base.saturating_sub(stack_size), base + 4096);
            handle_for_body.stack_low.store(range.0, Ordering::Relaxed);
            handle_for_body.stack_high.store(range.1, Ordering::Relaxed);
            STACK_RANGE.with(|r| r.set(range));
            body()
        });
        self.tasks.push(handle.clone());
        self.coroutines.push(Some(coroutine));
        self.ready.push_back(id);
        handle
    }

    /// Make a task of this worker ready, if it waits.
    pub fn wake(&mut self, id: TaskId) {
        let task = &self.tasks[id as usize];
        if task.state() == TaskState::Waiting {
            task.set_state(TaskState::Ready);
            self.ready.push_back(id);
        }
    }

    /// Make a task ready, if it waits, whichever worker runs it.
    pub fn wake_ref(&mut self, r: TaskRef) {
        debug_assert_eq!(r.worker, self.worker, "a task of another worker");
        self.wake(r.id);
    }

    /// Mark the current task ready again (for `Task.yield`); the caller
    /// then suspends.
    pub fn requeue_current(&mut self) {
        let id = self.current.expect("no current task");
        self.tasks[id as usize].set_state(TaskState::Ready);
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
                if task.state() == TaskState::Done {
                    continue;
                }
                if let Some(co) = self.coroutines[id as usize].take() {
                    task.set_state(TaskState::Running);
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
                if task.state() == TaskState::Running {
                    task.set_state(TaskState::Ready);
                    self.ready.push_back(id);
                }
                None
            }
            CoroutineResult::Return(exit) => {
                drop(co);
                match exit {
                    TaskExit::Exit(code) => {
                        task.set_state(TaskState::Done);
                        Some(code)
                    }
                    TaskExit::Result(r) => {
                        let failed = matches!(r, TaskResult::Error(_));
                        // The result (or exception) passes to whoever
                        // awaits the task; it is in place before the task
                        // is seen done.
                        match &r {
                            TaskResult::Value(v) | TaskResult::Error(v) => v.share(),
                        }
                        *lock(&task.result) = Some(r);
                        let joiners = {
                            // Under the joiners' lock, so that a task
                            // registering as a joiner either sees it done or
                            // is woken.
                            let mut j = lock(&task.joiners);
                            task.set_state(TaskState::Done);
                            std::mem::take(&mut *j)
                        };
                        for j in joiners {
                            self.wake_ref(j);
                        }
                        // A failing child cancels its siblings and wakes the
                        // scope's owner so that the failure propagates at
                        // once.
                        if failed {
                            if let Some(scope) = task.scope.clone() {
                                if scope.cancel() {
                                    for c in scope.children() {
                                        if c.task_ref() != task.task_ref() && !c.is_done() {
                                            c.set_cancel_requested(true);
                                            self.wake_ref(c.task_ref());
                                        }
                                    }
                                }
                                self.wake_ref(scope.owner);
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
            .filter(|t| t.state() == TaskState::Waiting)
            .map(|t| format!("{} ({})", t.name, t.id))
            .collect()
    }
}

/// Resume a task's coroutine outside of the scheduler's borrow.
pub fn resume(task: &TaskHandle, co: &mut TaskCoroutine) -> CoroutineResult<(), TaskExit> {
    let outer = YIELDER.with(|y| y.get());
    let outer_limit = STACK_LIMIT.with(|l| l.get());
    let outer_range = STACK_RANGE.with(|r| r.get());
    let y = task.yielder.load(Ordering::Relaxed);
    YIELDER.with(|c| c.set((!y.is_null()).then_some(y as *const _)));
    STACK_LIMIT.with(|l| l.set(task.stack_limit.load(Ordering::Relaxed)));
    STACK_RANGE.with(|r| r.set(task.stack_range()));
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
