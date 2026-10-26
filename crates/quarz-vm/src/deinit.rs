//! `deinitialize`: a method an object's class may define, run when the
//! object's last reference goes. The release can happen anywhere (inside
//! a native updating a collection, in compiled code between two loads),
//! so the object is not finalized there: it is rebuilt from its fields and
//! queued, and the queue runs at the next point where user code may run:
//! a call's end (once its activation is gone too), a `Release`, or the
//! end of a statement or a pass (`ClearRegs`), in the interpreter or
//! compiled code. The queue and the table of classes are per thread: an object
//! released on a worker is finalized on it.

use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicBool, Ordering};

use crate::rc::Rc;
use crate::value::Object;
use quarz_ir::ClassId;

/// Whether a program of this process defines `deinitialize` at all: in
/// the common case, releasing an object costs this one load (a
/// thread-local is dearer in a static library).
static ANY: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// Per class id: whether it (or an ancestor) defines `deinitialize`
    /// (set by this thread's interpreter; empty on other threads).
    static CLASSES: RefCell<Vec<bool>> = const { RefCell::new(Vec::new()) };
    static QUEUE: RefCell<Vec<Rc<Object>>> = const { RefCell::new(Vec::new()) };
    static PENDING: Cell<bool> = const { Cell::new(false) };
    /// The queue is being run (one that runs deinitializers does not
    /// start another run from inside one).
    static RUNNING: Cell<bool> = const { Cell::new(false) };
    /// The program whose objects are queued (`set_classes`).
    static PROGRAM: Cell<u64> = const { Cell::new(0) };
}

/// Set this thread's table of the classes with a `deinitialize`, for a
/// new interpreter of program `program` (`Global::id`). What another
/// program left on this thread (releases after its last call boundary,
/// cyclic garbage not collected yet) is not this one's to finalize, nor
/// to judge by its classes: its garbage is collected first, under its own
/// table, and what that queues is leaked with the rest of its queue
/// (dropping one would release what it holds under this program's
/// table). The same program's (the REPL's previous input's) stay queued.
/// (A program still running on the thread when another one starts there
/// would lose its queue: nothing does that.)
pub fn set_classes(classes: Vec<bool>, program: u64) {
    if classes.iter().any(|c| *c) {
        ANY.store(true, Ordering::Relaxed);
    }
    let before = PROGRAM.with(|p| p.get());
    if before != program && !RUNNING.with(|r| r.get()) {
        // (Nothing to look at for the thread's first program.)
        if before != 0 {
            if crate::cycles::candidates() != 0 {
                crate::cycles::collect_now();
            }
            let stale = QUEUE.with(|q| std::mem::take(&mut *q.borrow_mut()));
            std::mem::forget(stale);
            PENDING.with(|p| p.set(false));
        }
        PROGRAM.with(|p| p.set(program));
    }
    CLASSES.with(|c| *c.borrow_mut() = classes);
}

/// Whether releasing an instance of `class` must run its `deinitialize`
/// (not once the thread is ending: its tables are gone).
#[inline]
pub fn has(class: ClassId) -> bool {
    ANY.load(Ordering::Relaxed)
        && CLASSES
            .try_with(|c| {
                c.try_borrow()
                    .is_ok_and(|c| c.get(class as usize).copied().unwrap_or(false))
            })
            .unwrap_or(false)
}

/// Queue an object for its `deinitialize`.
pub fn queue(obj: Rc<Object>) {
    let _ = QUEUE.try_with(|q| q.borrow_mut().push(obj));
    let _ = PENDING.try_with(|p| p.set(true));
}

/// Whether a program of this process defines `deinitialize`.
#[inline(always)]
pub fn enabled() -> bool {
    ANY.load(Ordering::Relaxed)
}

/// Whether objects wait for their `deinitialize` and none is running.
#[inline(always)]
pub fn pending() -> bool {
    ANY.load(Ordering::Relaxed) && PENDING.with(|p| p.get()) && !RUNNING.with(|r| r.get())
}

/// Run `f` on each queued object (in the order they were released,
/// including those released meanwhile), unless a run is in progress.
pub fn run(mut f: impl FnMut(Rc<Object>)) {
    if RUNNING.with(|r| r.replace(true)) {
        return;
    }
    loop {
        let batch = QUEUE.with(|q| std::mem::take(&mut *q.borrow_mut()));
        if batch.is_empty() {
            break;
        }
        for obj in batch {
            f(obj);
        }
    }
    PENDING.with(|p| p.set(false));
    RUNNING.with(|r| r.set(false));
}
