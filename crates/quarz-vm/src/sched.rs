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

use std::cell::{Cell, RefCell};
use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};
use std::rc::Rc;
use std::time::{Duration, Instant};

use corosensei::{Coroutine, CoroutineResult, Yielder};

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
        Rc::new(ChannelInner {
            buffer: RefCell::new(VecDeque::new()),
            capacity,
            closed: Cell::new(false),
            recv_waiters: RefCell::new(VecDeque::new()),
            send_waiters: RefCell::new(VecDeque::new()),
            pushed: Cell::new(0),
            taken: Cell::new(0),
        })
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

pub struct Scheduler {
    pub tasks: Vec<Rc<TaskHandle>>,
    coroutines: Vec<Option<TaskCoroutine>>,
    ready: VecDeque<TaskId>,
    timers: BinaryHeap<Reverse<(Instant, u64, TaskId)>>,
    timer_seq: u64,
    pub current: Option<TaskId>,
    cancelled_timers: Vec<u64>,
}

thread_local! {
    static YIELDER: Cell<Option<*const Yielder<(), ()>>> = const { Cell::new(None) };
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
        let handle = Rc::new(TaskHandle {
            id,
            state: Cell::new(TaskState::Ready),
            result: RefCell::new(None),
            joiners: RefCell::new(Vec::new()),
            cancel_requested: Cell::new(false),
            scope: RefCell::new(scope.clone()),
            name: RefCell::new(name),
            yielder: Cell::new(None),
        });
        if let Some(scope) = &scope {
            scope.children.borrow_mut().push(handle.clone());
        }
        let stack = corosensei::stack::DefaultStack::new(stack_size).expect("coroutine stack");
        let handle_for_body = handle.clone();
        let coroutine = Coroutine::with_stack(stack, move |yielder: &Yielder<(), ()>, ()| {
            handle_for_body.yielder.set(Some(yielder as *const _));
            YIELDER.with(|y| y.set(Some(yielder as *const _)));
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
            if !self.fire_due_timers(true) {
                return None;
            }
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
                        *task.result.borrow_mut() = Some(r);
                        let joiners = std::mem::take(&mut *task.joiners.borrow_mut());
                        for j in joiners {
                            self.wake(j);
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
    YIELDER.with(|y| y.set(task.yielder.get()));
    let r = co.resume(());
    YIELDER.with(|y| y.set(outer));
    r
}
