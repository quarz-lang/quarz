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
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant};

#[cfg(target_os = "linux")]
use crate::epoll::{Event as IoEvent, Poller};
use corosensei::{Coroutine, CoroutineResult, Yielder};
#[cfg(not(target_os = "linux"))]
use polling::{Event, Events, Poller};

use crate::rc::SendRc;
use crate::value::{SharedValue, Value};

/// The native stack of a task (the main program's is larger).
pub const TASK_STACK: usize = 16 * 1024 * 1024;

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
    /// A task that worker `worker` runs as number `id`, registered as a
    /// child of `scope`.
    pub fn new(
        worker: u32,
        id: TaskId,
        scope: Option<Rc<ScopeInner>>,
        name: String,
    ) -> Rc<TaskHandle> {
        let handle = Rc::new_shared(TaskHandle {
            id,
            worker,
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
        handle
    }

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

/// A task to start on another worker: its handle (made by the task that
/// spawned it, which returns it at once) and its block.
pub struct SpawnRequest {
    pub handle: SendRc<TaskHandle>,
    pub block: SharedValue,
}

/// What other threads leave for a worker.
#[derive(Default)]
pub struct Inbox {
    /// Its tasks to wake.
    pub wakes: Vec<TaskId>,
    pub spawns: Vec<SpawnRequest>,
}

#[derive(Default)]
struct WorkerSlot {
    inbox: Mutex<Inbox>,
    /// Whether the inbox may hold something (read without its lock at
    /// every task switch).
    mail: AtomicBool,
    /// The worker's poller, to wake it when it waits (set when it starts).
    poller: std::sync::OnceLock<Arc<Poller>>,
    /// The numbers of its tasks, given out by whoever spawns one there.
    next_id: AtomicU32,
    started: AtomicBool,
}

/// The worker threads of a program (`QUARZ_THREADS`, 1 by default): a
/// slot each, the thread started when a task is first placed there.
/// Worker 0 is the thread that runs the main program.
pub struct Workers {
    slots: Vec<WorkerSlot>,
    next: AtomicUsize,
    /// Which workers have nothing at all to do (for deadlock detection).
    idle: Mutex<Vec<bool>>,
    stopping: AtomicBool,
    exit_code: Mutex<Option<i32>>,
}

impl Workers {
    pub fn new(count: usize) -> Arc<Workers> {
        let count = count.max(1);
        let slots: Vec<WorkerSlot> = (0..count).map(|_| WorkerSlot::default()).collect();
        slots[0].started.store(true, Ordering::Relaxed);
        Arc::new(Workers {
            slots,
            next: AtomicUsize::new(0),
            idle: Mutex::new(vec![false; count]),
            stopping: AtomicBool::new(false),
            exit_code: Mutex::new(None),
        })
    }

    /// `QUARZ_THREADS` (1 when unset or not a positive number).
    pub fn count_from_env() -> usize {
        std::env::var("QUARZ_THREADS")
            .ok()
            .and_then(|s| s.trim().parse::<usize>().ok())
            .filter(|n| *n >= 1)
            .unwrap_or(1)
    }

    pub fn count(&self) -> usize {
        self.slots.len()
    }

    /// The worker a new task goes to: each in turn. (Tasks stay where
    /// they start.) Once the program ends, the spawning one.
    pub fn place(&self, from: u32) -> u32 {
        if self.slots.len() == 1 || self.stopping.load(Ordering::Acquire) {
            return from;
        }
        (self.next.fetch_add(1, Ordering::Relaxed) % self.slots.len()) as u32
    }

    pub fn reserve_id(&self, worker: u32) -> TaskId {
        self.slots[worker as usize]
            .next_id
            .fetch_add(1, Ordering::Relaxed)
    }

    /// Mark worker `w` started; returns whether the caller is to start
    /// its thread (it was not started yet).
    pub fn claim_start(&self, w: u32) -> bool {
        !self.slots[w as usize].started.swap(true, Ordering::AcqRel)
    }

    pub fn set_poller(&self, w: u32, poller: Arc<Poller>) {
        let _ = self.slots[w as usize].poller.set(poller);
    }

    fn notify(&self, w: u32) {
        if let Some(p) = self.slots[w as usize].poller.get() {
            let _ = p.notify();
        }
    }

    fn post(&self, w: u32, f: impl FnOnce(&mut Inbox)) {
        let slot = &self.slots[w as usize];
        {
            let mut inbox = lock(&slot.inbox);
            f(&mut inbox);
            slot.mail.store(true, Ordering::Release);
        }
        self.notify(w);
    }

    pub fn post_wake(&self, r: TaskRef) {
        self.post(r.worker, |i| i.wakes.push(r.id));
    }

    pub fn post_spawn(&self, w: u32, req: SpawnRequest) {
        self.post(w, |i| i.spawns.push(req));
    }

    fn take_inbox(&self, w: u32) -> Option<Inbox> {
        let slot = &self.slots[w as usize];
        if !slot.mail.load(Ordering::Acquire) {
            return None;
        }
        let mut inbox = lock(&slot.inbox);
        slot.mail.store(false, Ordering::Relaxed);
        Some(std::mem::take(&mut *inbox))
    }

    /// Record whether worker `w` has nothing at all to do; returns whether
    /// no worker has (and nothing is on its way to one): a deadlock.
    fn set_idle(&self, w: u32, idle: bool) -> bool {
        let mut all = lock(&self.idle);
        all[w as usize] = idle;
        idle && all.iter().enumerate().all(|(i, &is_idle)| {
            let slot = &self.slots[i];
            (is_idle || !slot.started.load(Ordering::Acquire))
                && lock(&slot.inbox).wakes.is_empty()
                && lock(&slot.inbox).spawns.is_empty()
        })
    }

    /// The program ends: the other workers stop.
    pub fn stop(&self) {
        self.stopping.store(true, Ordering::Release);
        for w in 1..self.slots.len() as u32 {
            self.notify(w);
        }
    }

    fn stopping(&self) -> bool {
        self.stopping.load(Ordering::Acquire)
    }

    /// A task on another worker called `exit`: the main worker ends the
    /// program with `code`.
    fn request_exit(&self, code: i32) {
        lock(&self.exit_code).get_or_insert(code);
        self.notify(0);
    }
}

/// What a worker does next (`Scheduler::next_step`).
pub enum Next {
    Run(TaskId, TaskCoroutine),
    /// Start these tasks other workers placed here.
    Spawn(Vec<SpawnRequest>),
    /// Nothing can ever run again: every task waits, on every worker.
    Idle,
    /// The program ends (another worker than the main one).
    Stop,
    /// A task called `exit` (the main worker).
    Exit(i32),
}

pub struct Scheduler {
    /// This worker's number (its tasks' `TaskRef::worker`).
    pub worker: u32,
    pub workers: Arc<Workers>,
    /// The worker's tasks, by number (a number may be taken before its
    /// task arrives from the worker that spawned it).
    tasks: Vec<Option<Rc<TaskHandle>>>,
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

impl Scheduler {
    pub fn new(worker: u32, workers: Arc<Workers>) -> Scheduler {
        let reactor = Reactor::new();
        // From now on posting to this worker wakes it; what was posted
        // before is in its inbox, which it reads first.
        workers.set_poller(worker, reactor.poller.clone());
        Scheduler {
            worker,
            workers,
            tasks: Vec::new(),
            coroutines: Vec::new(),
            ready: VecDeque::new(),
            timers: BinaryHeap::new(),
            timer_seq: 0,
            current: None,
            cancelled_timers: Vec::new(),
            reactor,
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
        self.tasks[id as usize]
            .as_ref()
            .expect("a task of this worker")
    }

    /// How many tasks this worker has had (whether any other than the
    /// current one may want to run).
    pub fn task_count(&self) -> usize {
        self.tasks.len()
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
        self.task(id).clone()
    }

    /// Create a task of this worker running `body` on its own coroutine
    /// stack.
    pub fn spawn(
        &mut self,
        body: Box<dyn FnOnce() -> TaskExit>,
        scope: Option<Rc<ScopeInner>>,
        name: String,
        stack_size: usize,
    ) -> Rc<TaskHandle> {
        let id = self.workers.reserve_id(self.worker);
        let handle = TaskHandle::new(self.worker, id, scope, name);
        self.adopt(handle.clone(), body, stack_size);
        handle
    }

    /// Start a task made for this worker (here or by another worker).
    pub fn adopt(
        &mut self,
        handle: Rc<TaskHandle>,
        body: Box<dyn FnOnce() -> TaskExit>,
        stack_size: usize,
    ) {
        let id = handle.id;
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
        let i = id as usize;
        if self.tasks.len() <= i {
            self.tasks.resize_with(i + 1, || None);
            self.coroutines.resize_with(i + 1, || None);
        }
        self.tasks[i] = Some(handle);
        self.coroutines[i] = Some(coroutine);
        self.ready.push_back(id);
    }

    /// Make a task of this worker ready, if it waits.
    pub fn wake(&mut self, id: TaskId) {
        let Some(Some(task)) = self.tasks.get(id as usize) else {
            return;
        };
        if task.state() == TaskState::Waiting {
            task.set_state(TaskState::Ready);
            self.ready.push_back(id);
        }
    }

    /// Make a task ready, if it waits, whichever worker runs it (another
    /// worker gets it in its inbox).
    pub fn wake_ref(&mut self, r: TaskRef) {
        if r.worker == self.worker {
            self.wake(r.id);
        } else {
            self.workers.post_wake(r);
        }
    }

    /// Mark the current task ready again (for `Task.yield`); the caller
    /// then suspends.
    pub fn requeue_current(&mut self) {
        let id = self.current.expect("no current task");
        self.task(id).set_state(TaskState::Ready);
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

    /// What to do next: the next runnable task and its coroutine, or
    /// tasks to start. Sleeps for the earliest timer, IO, or (with other
    /// workers) a message, when nothing is ready.
    pub fn next_step(&mut self) -> Next {
        let multi = self.workers.count() > 1;
        self.fire_due_timers(false);
        // Keep IO flowing while tasks are busy (on Linux one epoll_wait:
        // polling only every 32 switches measured slower, the woken tasks
        // waiting longer).
        if !self.reactor.idle() {
            self.poll_io(Some(Duration::ZERO));
        }
        loop {
            if multi {
                if self.worker == 0 {
                    if let Some(code) = *lock(&self.workers.exit_code) {
                        return Next::Exit(code);
                    }
                } else if self.workers.stopping() {
                    return Next::Stop;
                }
                if let Some(inbox) = self.workers.take_inbox(self.worker) {
                    for id in inbox.wakes {
                        self.wake(id);
                    }
                    if !inbox.spawns.is_empty() {
                        return Next::Spawn(inbox.spawns);
                    }
                }
            }
            while let Some(id) = self.ready.pop_front() {
                if self.task(id).state() == TaskState::Done {
                    continue;
                }
                if let Some(co) = self.coroutines[id as usize].take() {
                    self.task(id).set_state(TaskState::Running);
                    self.current = Some(id);
                    return Next::Run(id, co);
                }
            }
            if !multi {
                if self.reactor.idle() {
                    if !self.fire_due_timers(true) {
                        return Next::Idle;
                    }
                    continue;
                }
                // Nothing runnable: wait for IO, or for the next timer.
                let timeout = self
                    .next_timer()
                    .map(|when| when.saturating_duration_since(Instant::now()));
                self.poll_io(timeout);
                self.fire_due_timers(false);
                continue;
            }
            // Nothing runnable, with other workers: wait for IO, the next
            // timer, or a message (the poller's notification). A worker
            // with no timer and no IO is idle; when every worker is, with
            // nothing on its way, no task can run again.
            let timeout = self
                .next_timer()
                .map(|when| when.saturating_duration_since(Instant::now()));
            let idle = timeout.is_none() && self.reactor.idle();
            if idle && self.workers.set_idle(self.worker, true) {
                if self.worker == 0 {
                    self.workers.set_idle(0, false);
                    return Next::Idle;
                }
                self.workers.notify(0);
            }
            self.poll_io(timeout);
            if idle {
                self.workers.set_idle(self.worker, false);
            }
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
        let task = self.task(id).clone();
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
                        if self.worker != 0 {
                            // The main worker ends the program.
                            self.workers.request_exit(code);
                            return None;
                        }
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
            .flatten()
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
