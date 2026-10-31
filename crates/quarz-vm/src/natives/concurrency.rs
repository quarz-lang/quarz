//! Task, Task::Scope, Channel, Channel::Selector, Atom and the Kernel entry points.

use crate::rc::Rc;
use std::cell::RefCell;
use std::time::Duration;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::sched::{
    lock, ChannelInner, ChannelState, ScopeInner, SelectorState, TaskHandle, TaskRef,
};
use crate::value::*;
use quarz_ir::FuncId;
use smallvec::smallvec;

use super::{block, int};

/// What a task block reads of the frames it was made in: for each frame
/// of the chain (0 = the innermost), the slots that its body, or a block
/// made inside it, reads (or would write: none, the checker forbids it).
/// A function with a frame of its own reaches the chain one frame up.
pub(crate) fn captured_slots(interp: &Interp, fid: FuncId) -> std::rc::Rc<Vec<Vec<u32>>> {
    if let Some(c) = interp.spawn_captures.borrow().get(&fid) {
        return c.clone();
    }
    let funcs = interp.funcs.borrow();
    let mut out: Vec<Vec<u32>> = Vec::new();
    // (function, the frames between where it starts and the chain)
    let mut work = vec![(fid, 0u32)];
    while let Some((f, skip)) = work.pop() {
        let func = &funcs[f as usize];
        let own = u32::from(func.frame_size > 0);
        let mut note = |depth: u32, slot: u32| {
            if let Some(d) = depth.checked_sub(own + skip) {
                let d = d as usize;
                if out.len() <= d {
                    out.resize(d + 1, Vec::new());
                }
                if !out[d].contains(&slot) {
                    out[d].push(slot);
                }
            }
        };
        for &(depth, slot) in &func.facts.uses {
            note(depth, slot);
        }
        for &g in &func.facts.blocks {
            work.push((g, skip + own));
        }
    }
    let c = std::rc::Rc::new(out);
    interp.spawn_captures.borrow_mut().insert(fid, c.clone());
    c
}

/// A `spawn` block captures by value: the task sees the outer variables
/// as they were at the `spawn`, not later reassignments. (The checker
/// keeps the block from assigning them and requires their values to be
/// Shareable, so a copy of the frames of the chain, sharing the values,
/// is all it takes.) Only the variables the block reads are copied: the
/// others, of whatever type, stay with this task.
fn snapshot(interp: &Interp, b: &Value) -> Value {
    let block = copy_captures(interp, b);
    // The block and what it captures pass to the new task.
    block.share();
    block
}

/// The block reading copies of the variables it captures, as they are
/// now: `snapshot` without making them shared (a quoted block's closure,
/// docs/14 §6, whose values need not be Shareable and stay with this
/// task).
fn copy_captures(interp: &Interp, b: &Value) -> Value {
    let Value::Proc(c) = b else {
        return b.clone();
    };
    let (ClosureBody::Func(f), Some(frame)) = (&c.body, &c.frame) else {
        return b.clone();
    };
    fn copy(frame: &Rc<Frame>, depth: usize, caps: &[Vec<u32>]) -> Rc<Frame> {
        let parent = if depth + 1 < caps.len() {
            frame.parent.as_ref().map(|p| copy(p, depth + 1, caps))
        } else {
            None
        };
        let src = frame.slots();
        let mut slots = vec![Value::Nil; src.len()];
        for &s in &caps[depth] {
            if let Some(v) = src.get(s as usize) {
                slots[s as usize] = v.clone();
            }
        }
        Frame::from_slots(slots, parent)
    }
    let caps = captured_slots(interp, *f);
    Value::Proc(Rc::new(Closure {
        body: ClosureBody::Func(*f),
        frame: if caps.is_empty() {
            None
        } else {
            Some(copy(frame, 0, &caps))
        },
        self_val: c.self_val.clone(),
        destructure: c.destructure,
        is_lambda: c.is_lambda,
        tag: c.tag,
        method_block: c.method_block.clone(),
        method_tag: c.method_tag,
        file: c.file,
    }))
}

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Task.spawn", |i, _, a| {
        let b = snapshot(i, &block(i, &a)?);
        Ok(Value::Task(i.spawn_task(b, None, "task")))
    });
    native!(m, "Kernel#loop", kernel_loop);
    // A shareable procedure copies what it captures when it is made.
    native!(m, "Proc#__copy_captures", |i, r, _| Ok(snapshot(i, r)));
    // A quoted block's closure: a snapshot, not shared (docs/14 §6).
    native!(m, "Proc#__snapshot", |i, r, _| Ok(copy_captures(i, r)));
    native!(m, "Kernel#sleep", |i, _, a| {
        i.sleep(duration(i, a.arg(0))?)?;
        Ok(Value::Nil)
    });
    native!(m, "Channel.select", |i, _, a| {
        let b = block(i, &a)?;
        run_select(i, &b, false)
    });
    native!(m, "Channel.select_loop", |i, _, a| {
        let b = block(i, &a)?;
        run_select(i, &b, true)
    });
    native!(m, "Task.scope", task_scope);
    native!(m, "Task.sleep", |i, _, a| {
        i.sleep(duration(i, a.arg(0))?)?;
        Ok(Value::Nil)
    });
    native!(m, "Task.yield", |i, _, _| {
        i.yield_now()?;
        Ok(Value::Nil)
    });
    native!(m, "Task.current", |i, _, _| Ok(Value::Task(
        i.current_task()
    )));
    // The block runs in a task of its own: what it raises is handed over.
    native!(m, "Task.timeout", |i, r, a| handed_over(
        i,
        task_timeout(i, r, a)
    ));
    native!(m, "Task.blocking", |i, _, a| {
        use crate::transfer::{self, WorkerExit};
        let b = block(i, &a)?;
        let closure = transfer::export(i, &b)?;
        let image = i.image();
        let argv = i.program.argv.clone();
        // What was printed before goes out first (an `exit!` on the helper
        // thread writes its own output straight away).
        i.flush();
        let outcome = i.block_on(move || transfer::run_on_thread(image, argv, closure))?;
        i.write_out_bytes(&outcome.output);
        match outcome.exit {
            WorkerExit::Value(t) => Ok(transfer::import(i, t)),
            WorkerExit::Raise(t) => handed_over(i, Err(Flow::Raise(transfer::import(i, t)))),
            // A deadlock on the helper thread (or a result it could not
            // hand back): the program ends.
            WorkerExit::Exit(code) => Err(Flow::Exit(code)),
            WorkerExit::Failed(m) => Err(i.raise(i.program.exc.system_call_error, &m)),
        }
    });
    native!(m, "Task.__contain", task_contain);
    // A task outside any `Task.__contain` block: a service the library
    // starts once for the whole program (`Signal`'s dispatcher).
    native!(m, "Task.__spawn_service", |i, _, a| {
        let b = snapshot(i, &block(i, &a)?);
        let me = i.current_task();
        let was = me.set_container(None);
        let t = i.spawn_task(b, None, "task");
        me.set_container(was);
        Ok(Value::Task(t))
    });
    native!(m, "Task.uncancellable", |i, _, a| {
        let b = block(i, &a)?;
        i.uncancellable(|| i.call_block(&b, smallvec![]))
    });
    native!(m, "Task.check_cancel", |i, _, _| {
        let t = i.current_task();
        i.check_cancel(&t)?;
        Ok(Value::Nil)
    });
    native!(m, "Task#await", |i, r, _| handed_over(
        i,
        i.await_task(task(i, r)?)
    ));
    native!(m, "Task#cancel", |i, r, _| {
        i.cancel_task(task(i, r)?);
        Ok(Value::Nil)
    });
    native!(m, "Task#done?", |i, r, _| {
        Ok(Value::Bool(task(i, r)?.is_done()))
    });
    native!(m, "Task#cancelled?", |i, r, _| {
        Ok(Value::Bool(task(i, r)?.cancel_requested()))
    });
    native!(m, "Task::Scope#spawn", |i, r, a| {
        let b = snapshot(i, &block(i, &a)?);
        let s = scope(i, r)?.clone();
        let t = i.spawn_task(b, Some(s.clone()), "task");
        // Into a cancelled scope: cancelled at once, as its siblings were.
        if s.is_cancelled() {
            i.cancel_task(&t);
        }
        Ok(Value::Task(t))
    });
    native!(m, "Task::Scope#cancel", |i, r, _| {
        let s = scope(i, r)?.clone();
        cancel_children(i, &s);
        Ok(Value::Nil)
    });
    native!(m, "Channel.new", channel_new);
    native!(m, "Channel#send", channel_send);
    native!(m, "Channel#receive", |i, r, _| {
        channel_receive(i, chan(i, r)?, true)
    });
    native!(m, "Channel#receive?", |i, r, _| {
        channel_receive(i, chan(i, r)?, false)
    });
    native!(m, "Channel#try_send", channel_try_send);
    native!(m, "Channel#try_receive", |i, r, _| {
        let c = chan(i, r)?;
        Ok(take_value(i, c).unwrap_or(Value::Nil))
    });
    native!(m, "Channel#close", channel_close);
    native!(m, "Channel#closed?", |i, r, _| {
        Ok(Value::Bool(chan(i, r)?.lock().closed))
    });
    native!(m, "Channel#empty?", |i, r, _| {
        Ok(Value::Bool(chan(i, r)?.lock().buffer.is_empty()))
    });
    native!(m, "Channel#size", |i, r, _| {
        Ok(Value::Int(chan(i, r)?.lock().buffer.len() as i64))
    });
    native!(m, "Channel#each", channel_each);
    native!(m, "Channel::Selector#receive", |i, r, a| {
        let c = chan(i, a.arg(0))?.clone();
        let b = block(i, &a)?;
        sel(i, r)?.borrow_mut().receives.push((c, b));
        Ok(Value::Nil)
    });
    native!(m, "Channel::Selector#send", |i, r, a| {
        let c = chan(i, a.arg(0))?.clone();
        let b = block(i, &a)?;
        sel(i, r)?.borrow_mut().sends.push((c, a.arg(1).clone(), b));
        Ok(Value::Nil)
    });
    native!(m, "Channel::Selector#after", |i, r, a| {
        let d = duration(i, a.arg(0))?;
        let b = block(i, &a)?;
        sel(i, r)?.borrow_mut().after = Some((d, b));
        Ok(Value::Nil)
    });
    native!(m, "Channel::Selector#default", |i, r, a| {
        let b = block(i, &a)?;
        sel(i, r)?.borrow_mut().default = Some(b);
        Ok(Value::Nil)
    });
    native!(m, "Channel::Selector#stop", |i, r, _| {
        sel(i, r)?.borrow_mut().stopped = true;
        Ok(Value::Nil)
    });
    // An atom's content is read by every task that holds the atom.
    native!(m, "Atom.new", |_, _, a| {
        let v = a.arg(0).clone();
        v.share();
        Ok(Value::Atom(Rc::new_shared(std::sync::Mutex::new(v))))
    });
    native!(m, "Atom#value", |i, r, _| Ok(lock(atom(i, r)?).clone()));
    native!(m, "Atom#get", |i, r, _| Ok(lock(atom(i, r)?).clone()));
    native!(m, "Atom#set", |i, r, a| {
        let v = a.arg(0).clone();
        v.share();
        let old = std::mem::replace(&mut *lock(atom(i, r)?), v);
        drop(old);
        Ok(Value::Nil)
    });
    native!(m, "Atom#update", atom_update);
    native!(m, "Atom#compare_and_set", |i, r, a| {
        let new = a.arg(1).clone();
        new.share();
        // By identity, as Java's `AtomicReference` and Clojure's
        // `compare-and-set!` compare (numbers, strings, symbols, bytes and
        // times by their contents, `Value::identical`): whether the value
        // is still the one read. No Quarz code runs under the lock.
        let mut cell = lock(atom(i, r)?);
        let same = cell.identical(a.arg(0));
        let old = if same {
            Some(std::mem::replace(&mut *cell, new))
        } else {
            None
        };
        drop(cell);
        drop(old);
        Ok(Value::Bool(same))
    });
}

fn duration(interp: &Interp, v: &Value) -> Result<Duration, Flow> {
    match v {
        Value::Duration(ns) => Ok(Duration::from_nanos((*ns).max(0) as u64)),
        Value::Int(s) => Ok(Duration::from_secs((*s).max(0) as u64)),
        Value::Float(s) => Ok(Duration::from_secs_f64(s.max(0.0))),
        _ => Err(interp.err_type("expected a Duration")),
    }
}

fn task<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<TaskHandle>, Flow> {
    match v {
        Value::Task(t) => Ok(t),
        _ => Err(interp.err_type("expected a Task")),
    }
}

fn scope<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<ScopeInner>, Flow> {
    match v {
        Value::Scope(s) => Ok(s),
        _ => Err(interp.err_type("expected a Task::Scope")),
    }
}

fn chan<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<ChannelInner>, Flow> {
    match v {
        Value::Channel(c) => Ok(c),
        _ => Err(interp.err_type("expected a Channel")),
    }
}

fn sel<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RefCell<SelectorState>>, Flow> {
    match v {
        Value::Selector(s) => Ok(s),
        _ => Err(interp.err_type("expected a Channel::Selector")),
    }
}

fn atom<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<std::sync::Mutex<Value>>, Flow> {
    match v {
        Value::Atom(a) => Ok(a),
        _ => Err(interp.err_type("expected an Atom")),
    }
}

fn kernel_loop(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    loop {
        match interp.call_block(&b, smallvec![]) {
            Ok(_) => {}
            Err(Flow::Raise(e)) if interp.exception_is_a(&e, interp.program.exc.stop_iteration) => {
                return Ok(Value::Nil)
            }
            Err(e) => return Err(e),
        }
        // No loop yields or checks for a cancellation by itself (as in
        // Kotlin): one that only computes calls `Task.yield`.
    }
}

// ----- scopes -------------------------------------------------------------------------

/// Cancel the scope's children, once (cancellation is a state: again would
/// only wake them for nothing; one spawned later is cancelled by
/// `Task::Scope#spawn`).
fn cancel_children(interp: &Interp, scope: &Rc<ScopeInner>) {
    if !scope.cancel() {
        return;
    }
    for c in scope.children() {
        interp.cancel_task(&c);
    }
}

fn task_scope(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let scope = ScopeInner::new(interp.sched.borrow().current_ref());
    let result = interp.call_block(&b, smallvec![Value::Scope(scope.clone())]);
    let (value, mut failure): (Value, Option<Flow>) = match result {
        Ok(v) => (v, None),
        Err(e) => {
            cancel_children(interp, &scope);
            (Value::Nil, Some(e))
        }
    };
    // Wait for every child; the first failure cancels the rest.
    loop {
        let Some(child) = scope.first_child_or_end() else {
            break;
        };
        // Once the children are cancelled (or a failure is kept), the wait
        // for them is uncancellable: the owner's cancellation, a state, would
        // otherwise interrupt every wait.
        let r = if failure.is_some() || scope.is_cancelled() {
            interp.uncancellable(|| interp.await_task(&child))
        } else {
            interp.await_task(&child)
        };
        // An error that is not the child's own result interrupted the wait.
        let interrupted = match &r {
            Err(Flow::Raise(e)) => !is_result_of(e, &child),
            _ => false,
        };
        if let (Err(Flow::Raise(e)), true) = (&r, interrupted) {
            // The wait itself was interrupted: the task running the scope
            // was cancelled. That is the scope's failure; it cancels the
            // children and still waits for them (their `ensure` runs
            // before the scope ends).
            if failure.is_none() || (is_exit(interp, e) && !failure_is_exit(interp, &failure)) {
                failure = Some(Flow::Raise(e.clone()));
            }
            cancel_children(interp, &scope);
            continue;
        }
        scope.remove_child(&child);
        match r {
            Ok(_) => {}
            Err(Flow::Raise(e)) => {
                let is_cancel = interp.exception_is_a(&e, interp.program.exc.cancelled);
                if is_cancel && scope.is_cancelled() {
                    // Cancelled by the scope itself: expected.
                } else if failure.is_none()
                    || (is_exit(interp, &e) && !failure_is_exit(interp, &failure))
                {
                    failure = handed_over(interp, Err(Flow::Raise(e))).err();
                    cancel_children(interp, &scope);
                }
            }
            Err(e) => {
                if failure.is_none() {
                    failure = Some(e);
                }
            }
        }
    }
    match failure {
        Some(e) => Err(e),
        None => Ok(value),
    }
}

/// `r`, an exception another task (or thread) raised and this one raises
/// again: the exception this one is handling becomes its cause, unless it
/// has one, as Ruby's `Thread#value` gives it.
fn handed_over(interp: &Interp, r: EvalResult) -> EvalResult {
    match r {
        // Raised before, in the other task: it lacks a cause at most.
        Err(Flow::Raise(Value::Object(o))) if o.exc_info().is_some() => {
            let o = super::raised(o, Vec::new, interp.rescued());
            Err(Flow::Raise(Value::Object(o)))
        }
        r => r,
    }
}

/// `Task.__contain(limit)`: the block, then the tasks it left (spawned
/// while it ran, and theirs) cancelled and waited for, as a scope's
/// children are, but for `limit` and a grace at most (`nil`: as long as
/// they take);
/// `[the block's value, how many still ran then]`. Those let go spawn
/// nothing into the container. An exit or a cancellation that comes to
/// this task while it waits is raised once the wait is over (the block's
/// own outcome first).
fn task_contain(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    use std::sync::atomic::Ordering;
    let limit = match args.arg(0) {
        Value::Nil => None,
        v => Some(duration(interp, v)?),
    };
    let b = block(interp, &args)?;
    let me = interp.current_task();
    let container = crate::sched::Container::new();
    crate::sched::CONTAINERS.fetch_add(1, Ordering::AcqRel);
    let was = me.set_container(Some(container.clone()));
    let r = interp.call_block(&b, smallvec![]);
    me.set_container(was);
    let mut interrupted: Option<Flow> = None;
    // The limit, and a grace past it for the tasks found late (spawned as
    // the others were cancelled; a task that respawns itself as it is
    // cancelled is let go there).
    let deadline = limit.map(|d| std::time::Instant::now() + d + grace(limit));
    let mut running = 0;
    loop {
        let left = container.take_live(false);
        if left.is_empty() {
            break;
        }
        for t in &left {
            interp.cancel_task(t);
        }
        let mut stuck = Vec::new();
        let mut late = Vec::new();
        if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            late = left;
        } else {
            for t in &left {
                // Waited for until it ends (or the deadline): what
                // interrupts the wait (an exit delivered to this task) is
                // raised afterwards, the first one.
                loop {
                    match interp.uncancellable(|| wait_until(interp, t, deadline)) {
                        Ok(true) => break,
                        Ok(false) => {
                            stuck.push(t.clone());
                            break;
                        }
                        Err(f) => {
                            interrupted.get_or_insert(f);
                        }
                    }
                }
            }
            if stuck.is_empty() {
                continue;
            }
        }
        // Given up: those found late (and what they spawn meanwhile) get a
        // grace to end; then the container is closed (what is spawned from
        // then on is listed nowhere), and those still running are let go
        // (what they spawn runs on too).
        let until = std::time::Instant::now() + grace(limit);
        let mut batch = std::mem::take(&mut late);
        loop {
            batch.extend(container.take_live(false));
            if batch.is_empty() {
                break;
            }
            for t in &batch {
                interp.cancel_task(t);
            }
            for t in &batch {
                if let Err(f) = interp.uncancellable(|| wait_until(interp, t, Some(until))) {
                    interrupted.get_or_insert(f);
                }
            }
            late.append(&mut batch);
            if std::time::Instant::now() >= until {
                break;
            }
        }
        for t in container.take_live(true) {
            interp.cancel_task(&t);
            late.push(t);
        }
        for t in stuck.iter().chain(&late) {
            t.set_container(None);
        }
        running = stuck.len() + late.iter().filter(|t| !t.is_done()).count();
        break;
    }
    // Ended: nothing is listed any more. An exit delivered as the last
    // one ended is raised here, not in the next test.
    let _ = container.take_live(true);
    if let Err(f) = interp.uncancellable(|| interp.check_cancel(&me)) {
        interrupted.get_or_insert(f);
    }
    crate::sched::CONTAINERS.fetch_sub(1, Ordering::AcqRel);
    match (r, interrupted) {
        // An exit wins over the block's failure, as in a scope.
        (Err(f), Some(e)) if !flow_is_exit(interp, &f) && flow_is_exit(interp, &e) => Err(e),
        (Err(f), _) => Err(f),
        (Ok(_), Some(f)) => Err(f),
        (Ok(v), None) => Ok(Value::array(vec![v, Value::Int(running as i64)])),
    }
}

/// How long past its limit `Task.__contain` waits for the tasks found
/// late (spawned as the others were cancelled).
fn grace(limit: Option<Duration>) -> Duration {
    limit.map_or(Duration::ZERO, |l| l.min(Duration::from_millis(50)))
}

/// Wait until `t` ends (true) or `deadline` passes (false), parking this
/// task; what interrupts the wait is raised.
fn wait_until(
    interp: &Interp,
    t: &Rc<TaskHandle>,
    deadline: Option<std::time::Instant>,
) -> Result<bool, Flow> {
    let me = interp.current_task();
    loop {
        if t.is_done() {
            return Ok(true);
        }
        let now = std::time::Instant::now();
        if deadline.is_some_and(|d| now >= d) {
            return Ok(false);
        }
        {
            let mut joiners = lock(&t.joiners);
            if t.is_done() {
                continue;
            }
            if !joiners.contains(&me.task_ref()) {
                joiners.push(me.task_ref());
            }
        }
        let timer = deadline.map(|d| interp.sched.borrow_mut().add_timer(d - now, me.id));
        let r = interp.park();
        if let Some(timer) = timer {
            interp.sched.borrow_mut().cancel_timer(timer);
        }
        lock(&t.joiners).retain(|j| *j != me.task_ref());
        r?;
    }
}

/// Whether `e` is a `SystemExit`: an exit wins over the failure a scope
/// or `Task.timeout` would raise, so that waiting does not lose it.
fn is_exit(interp: &Interp, e: &Value) -> bool {
    interp.exception_is_a(e, interp.program.exc.system_exit)
}

/// Whether a scope's failure already ends the program: a `SystemExit`, or
/// a hard exit (which no `SystemExit` replaces).
fn failure_is_exit(interp: &Interp, failure: &Option<Flow>) -> bool {
    failure.as_ref().is_some_and(|f| flow_is_exit(interp, f))
}

/// Whether `f` ends the program: a `SystemExit`, or a hard exit.
fn flow_is_exit(interp: &Interp, f: &Flow) -> bool {
    match f {
        Flow::Raise(e) => is_exit(interp, e),
        Flow::Exit(_) => true,
        _ => false,
    }
}

/// Wait until `child` is done, whatever interrupts the wait, giving the
/// `SystemExit` an interruption raised, if any (the block is the caller's,
/// `&:`, and must not outlive the call).
fn wait_out(interp: &Interp, child: &Rc<TaskHandle>) -> Option<Flow> {
    let mut exit = None;
    while !child.is_done() {
        if let Err(Flow::Raise(e)) = interp.uncancellable(|| interp.await_task(child)) {
            // Not the child's own result: what interrupted the wait.
            if is_exit(interp, &e) && !is_result_of(&e, child) {
                exit = Some(Flow::Raise(e));
            }
        }
    }
    exit
}

/// Whether `e` is the exception `child` ended with (not one that
/// interrupted the wait for it).
fn is_result_of(e: &Value, child: &Rc<TaskHandle>) -> bool {
    match (child.result(), e) {
        (Some(crate::sched::TaskResult::Error(Value::Object(r))), Value::Object(o)) => {
            Rc::ptr_eq(&r, o)
        }
        // Not an exception object (one `Task.blocking` could not hand back):
        // never one that interrupted the wait, which are fresh exceptions.
        (Some(crate::sched::TaskResult::Error(_)), e) => !matches!(e, Value::Object(_)),
        _ => false,
    }
}

/// The child's own `SystemExit` (an `ensure` of the cancelled block that
/// exits): it wins over the timeout or the cancellation, as in Ruby.
fn own_exit(interp: &Interp, child: &Rc<TaskHandle>) -> Option<Flow> {
    match child.result() {
        Some(crate::sched::TaskResult::Error(e)) if is_exit(interp, &e) => Some(Flow::Raise(e)),
        _ => None,
    }
}

fn task_timeout(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let d = duration(interp, args.arg(0))?;
    let b = block(interp, &args)?;
    // The block is the caller's: its task is the sink of the `exit`s of
    // the tasks it spawns (a scope in it takes its children's, as one in
    // the caller would).
    let child = interp.spawn_task(b, None, crate::interp::TIMEOUT_TASK);
    // And so are the exits meant for its caller, while the block runs.
    let me = interp.current_task();
    let was = me.is_sink().then(|| me.set_delegate(Some(child.clone())));
    let r = run_timeout(interp, d, &child);
    if let Some(was) = was {
        me.set_delegate(was);
    }
    // The tasks spawned in the block keep it as their sink: it lets the
    // sinks above go that have finished, so they do not pile up.
    let _ = child.live_sink();
    // An exit delivered to the block that it ended before raising: raised
    // here, in its place.
    match child.take_exit() {
        Some(status)
            if !matches!(&r, Err(Flow::Raise(e)) if is_exit(interp, e))
                && !matches!(r, Err(Flow::Exit(_))) =>
        {
            Err(Flow::Raise(super::system_exit(interp, status, "exit")))
        }
        _ => r,
    }
}

/// `Task.timeout` once its block runs in `child`.
fn run_timeout(interp: &Interp, d: std::time::Duration, child: &Rc<TaskHandle>) -> EvalResult {
    let child = child.clone();
    let me = interp.current_task();
    let timer = interp.sched.borrow_mut().add_timer(d, me.id);
    let start = std::time::Instant::now();
    loop {
        if child.is_done() {
            interp.sched.borrow_mut().cancel_timer(timer);
            return interp.await_task(&child);
        }
        if start.elapsed() >= d {
            interp.cancel_task(&child);
            // Waited for even if this task is cancelled meanwhile: the
            // block is the caller's (`&:`) and must not outlive the call.
            let exit = wait_out(interp, &child).or_else(|| own_exit(interp, &child));
            return Err(
                exit.unwrap_or_else(|| interp.raise(interp.program.exc.timeout, "timed out"))
            );
        }
        {
            let mut joiners = lock(&child.joiners);
            if child.is_done() {
                continue;
            }
            if !joiners.contains(&me.task_ref()) {
                joiners.push(me.task_ref());
            }
        }
        if let Err(e) = interp.park() {
            // Cancelled: so is the block, which is waited for (it is the
            // caller's block, `&:`, and may use the caller's locals: it
            // must not outlive the call).
            lock(&child.joiners).retain(|t| *t != me.task_ref());
            interp.sched.borrow_mut().cancel_timer(timer);
            interp.cancel_task(&child);
            let exit = wait_out(interp, &child).or_else(|| own_exit(interp, &child));
            return Err(exit.unwrap_or(e));
        }
    }
}

// ----- channels -------------------------------------------------------------------------

fn channel_new(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let capacity = match args.kw(interp, "capacity").or(args.pos.first()) {
        Some(v) => int(interp, v, "capacity")?.max(0) as usize,
        None => 0,
    };
    Ok(Value::Channel(ChannelInner::new(capacity)))
}

fn wake_all(interp: &Interp, waiters: impl IntoIterator<Item = TaskRef>) {
    for w in waiters {
        interp.wake_ref(w);
    }
}

fn closed_error(interp: &Interp) -> Flow {
    interp.raise(interp.program.exc.channel_closed, "channel is closed")
}

fn channel_send(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let c = chan(interp, recv)?;
    // A cancellation point even when it need not wait, as Kotlin's `send`.
    interp.check_cancel_current()?;
    let mut value = Some(args.arg(0).clone());
    let me = interp.sched.borrow().current_ref();
    // Whether it has waited: woken by something else, it may still be
    // listed.
    let mut waited = false;
    loop {
        let mut st = c.lock();
        if st.closed {
            drop(st);
            return Err(closed_error(interp));
        }
        if !st.can_send(c.capacity) {
            if !waited || !st.send_waiters.contains(&me) {
                st.send_waiters.push_back(me);
            }
            drop(st);
            waited = true;
            if let Err(e) = interp.park() {
                c.lock().send_waiters.retain(|t| *t != me);
                return Err(e);
            }
            continue;
        }
        st.put(value.take().expect("sent once"));
        let ticket = st.pushed;
        let mut receiver = st.recv_waiters.pop_front();
        if c.capacity > 0 {
            drop(st);
            wake_all(interp, receiver);
            return Ok(Value::Nil);
        }
        // Rendezvous: wait until a receiver has taken the value.
        while st.taken < ticket {
            if st.closed {
                drop(st);
                wake_all(interp, receiver.take());
                return Err(closed_error(interp));
            }
            if !waited || !st.send_waiters.contains(&me) {
                st.send_waiters.push_back(me);
            }
            drop(st);
            waited = true;
            wake_all(interp, receiver.take());
            if let Err(e) = interp.park() {
                c.lock().send_waiters.retain(|t| *t != me);
                return Err(e);
            }
            st = c.lock();
        }
        return Ok(Value::Nil);
    }
}

fn channel_try_send(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let c = chan(interp, recv)?;
    let mut st = c.lock();
    if st.closed {
        drop(st);
        return Err(closed_error(interp));
    }
    // Only buffered channels can accept without a waiting receiver.
    let ready = st.can_send(c.capacity) && (c.capacity > 0 || !st.recv_waiters.is_empty());
    if !ready {
        return Ok(Value::Bool(false));
    }
    st.put(args.arg(0).clone());
    if c.capacity == 0 {
        st.taken = st.pushed;
    }
    let receiver = st.recv_waiters.pop_front();
    drop(st);
    wake_all(interp, receiver);
    Ok(Value::Bool(true))
}

/// Take a value if one is there (waking the senders waiting for room or
/// for their value to be taken).
fn take_value(interp: &Interp, c: &ChannelInner) -> Option<Value> {
    let mut st = c.lock();
    let (v, senders) = take_locked(&mut st)?;
    drop(st);
    wake_all(interp, senders.into_iter().flatten());
    Some(v)
}

fn take_locked(st: &mut ChannelState) -> Option<(Value, Senders)> {
    let v = st.buffer.pop_front()?;
    st.taken += 1;
    let senders = (!st.send_waiters.is_empty()).then(|| std::mem::take(&mut st.send_waiters));
    Some((v, senders))
}

/// The senders a take wakes (usually none: nothing to build).
type Senders = Option<std::collections::VecDeque<TaskRef>>;

fn channel_receive(interp: &Interp, c: &Rc<ChannelInner>, raise_on_closed: bool) -> EvalResult {
    // A cancellation point even when a value is there, as Kotlin's
    // `receive`.
    interp.check_cancel_current()?;
    let me = interp.sched.borrow().current_ref();
    let mut waited = false;
    loop {
        let mut st = c.lock();
        if let Some((v, senders)) = take_locked(&mut st) {
            drop(st);
            wake_all(interp, senders.into_iter().flatten());
            return Ok(v);
        }
        if st.closed {
            drop(st);
            return if raise_on_closed {
                Err(closed_error(interp))
            } else {
                Ok(Value::Nil)
            };
        }
        // Woken by something else, it may still be listed.
        if !waited || !st.recv_waiters.contains(&me) {
            st.recv_waiters.push_back(me);
        }
        drop(st);
        waited = true;
        if let Err(e) = interp.park() {
            leave_receivers(interp, c, me, true);
            return Err(e);
        }
    }
}

/// Take `me` off a channel's receivers after a wait that ends otherwise
/// (cancelled, or a `select` that another channel woke). A sender that
/// took it off already meant its wake-up for a receiver: with `pass_on`,
/// it goes to the next one while a value is there.
fn leave_receivers(interp: &Interp, c: &ChannelInner, me: TaskRef, pass_on: bool) -> bool {
    let mut st = c.lock();
    let listed = st.recv_waiters.len();
    st.recv_waiters.retain(|t| *t != me);
    let taken_off = st.recv_waiters.len() == listed;
    let next = if taken_off && pass_on && !st.buffer.is_empty() {
        st.recv_waiters.pop_front()
    } else {
        None
    };
    drop(st);
    wake_all(interp, next);
    taken_off
}

fn channel_close(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let c = chan(interp, recv)?;
    let mut st = c.lock();
    st.closed = true;
    let mut waiters: Vec<TaskRef> = st.recv_waiters.drain(..).collect();
    waiters.extend(st.send_waiters.drain(..));
    drop(st);
    wake_all(interp, waiters);
    Ok(Value::Nil)
}

fn channel_each(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let c = chan(interp, recv)?.clone();
    let b = block(interp, &args)?;
    loop {
        let v = channel_receive(interp, &c, false)?;
        if v.is_nil() {
            let st = c.lock();
            if st.closed && st.buffer.is_empty() {
                return Ok(Value::Nil);
            }
        }
        interp.call_block(&b, smallvec![v])?;
    }
}

// ----- select ----------------------------------------------------------------------------

fn run_select(interp: &Interp, block: &Value, looping: bool) -> EvalResult {
    let mut unwaited: u32 = 0;
    loop {
        let state = Rc::new(RefCell::new(SelectorState::default()));
        interp.call_block(block, smallvec![Value::Selector(state.clone())])?;
        if state.borrow().stopped {
            return Ok(Value::Nil);
        }
        let how = select_once(interp, &state)?;
        if state.borrow().stopped || !looping {
            return Ok(Value::Nil);
        }
        // `select_loop` is for tasks working together: one that polls with
        // `default` lets the others run after each select, as `Task.yield`
        // does, so that it does not starve its senders; one whose cases are
        // ready every time does every 64 selects (a select that waited
        // gave way already; each select checks for a cancellation).
        unwaited = if how == Selected::Waited {
            0
        } else {
            unwaited.wrapping_add(1)
        };
        let give_way = how == Selected::Default || unwaited.is_multiple_of(64);
        // Whatever this worker's task table says: a task another worker
        // spawned here waits in its inbox until the scheduler runs.
        if how != Selected::Waited && give_way {
            interp.yield_now()?;
        }
    }
}

/// How a select went: it waited (and gave way), took `default` (polling),
/// or found a case ready.
#[derive(Clone, Copy, PartialEq)]
enum Selected {
    Waited,
    Default,
    Ready,
}

/// One select.
fn select_once(interp: &Interp, state: &Rc<RefCell<SelectorState>>) -> Result<Selected, Flow> {
    // A cancellation point even when a case is ready, as Kotlin's `select`.
    interp.check_cancel_current()?;
    let mut how = Selected::Ready;
    let me = interp.sched.borrow().current_ref();
    let timer_start = std::time::Instant::now();
    let after = state.borrow().after.clone();
    let timer = after
        .as_ref()
        .map(|(d, _)| interp.sched.borrow_mut().add_timer(*d, me.id));
    let receives: Vec<(Rc<ChannelInner>, Value)> = state.borrow().receives.clone();
    let sends: Vec<(Rc<ChannelInner>, Value, Value)> = state.borrow().sends.clone();
    // How many of the receives and sends it is listed on, waiting.
    let mut listed = (0, 0);
    // The receives whose sender took it off while it waited: the wake-up
    // meant for a receiver passes on if their value is still there once
    // the select has chosen.
    let mut taken_off: Vec<usize> = Vec::new();
    // The handler chosen and its argument.
    let chosen: Result<(Value, Option<Value>), Flow> = 'select: loop {
        unlist(interp, &receives, &sends, me, &mut listed, &mut taken_off);
        // Receives.
        for (c, handler) in &receives {
            let mut st = c.lock();
            if let Some((v, senders)) = take_locked(&mut st) {
                drop(st);
                wake_all(interp, senders.into_iter().flatten());
                break 'select Ok((handler.clone(), Some(v)));
            }
            if st.closed {
                drop(st);
                break 'select Err(closed_error(interp));
            }
        }
        // Sends.
        for (c, value, handler) in &sends {
            let mut st = c.lock();
            if st.closed {
                drop(st);
                break 'select Err(closed_error(interp));
            }
            if send_ready(c, &st) {
                st.put(value.clone());
                if c.capacity == 0 {
                    st.taken = st.pushed;
                }
                let receiver = st.recv_waiters.pop_front();
                drop(st);
                wake_all(interp, receiver);
                break 'select Ok((handler.clone(), None));
            }
        }
        // Timeout.
        if let Some((d, handler)) = &after {
            if timer_start.elapsed() >= *d {
                break 'select Ok((handler.clone(), None));
            }
        }
        // Default.
        if let Some(handler) = state.borrow().default.clone() {
            how = Selected::Default;
            break 'select Ok((handler, None));
        }
        if receives.is_empty() && sends.is_empty() && after.is_none() {
            break 'select Err(interp.err_arg("Channel.select with no alternatives"));
        }
        // Register and wait. Each channel is checked again as the task
        // registers on it: one that became ready since (another worker
        // may have sent meanwhile) means trying again, not waiting.
        let mut ready = false;
        for (c, _) in &receives {
            let mut st = c.lock();
            if !st.buffer.is_empty() || st.closed {
                ready = true;
                break;
            }
            st.recv_waiters.push_back(me);
            listed.0 += 1;
        }
        if !ready {
            for (c, _, _) in &sends {
                let mut st = c.lock();
                if st.closed || send_ready(c, &st) {
                    ready = true;
                    break;
                }
                st.send_waiters.push_back(me);
                listed.1 += 1;
            }
        }
        if !ready {
            how = Selected::Waited;
            if let Err(e) = interp.park() {
                unlist(interp, &receives, &sends, me, &mut listed, &mut taken_off);
                break 'select Err(e);
            }
        }
    };
    for i in taken_off {
        let c = &receives[i].0;
        let mut st = c.lock();
        let next = if st.buffer.is_empty() {
            None
        } else {
            st.recv_waiters.pop_front()
        };
        drop(st);
        wake_all(interp, next);
    }
    // Cancelled, or else it would wake the task's next wait.
    if let Some(t) = timer {
        interp.sched.borrow_mut().cancel_timer(t);
    }
    match chosen? {
        (handler, Some(v)) => interp.call_block(&handler, smallvec![v])?,
        (handler, None) => interp.call_block(&handler, smallvec![])?,
    };
    Ok(how)
}

/// Take a waiting `select` off the channels it is listed on (`listed`:
/// the first so many receives and sends), noting the receives whose
/// sender took it off already.
fn unlist(
    interp: &Interp,
    receives: &[(Rc<ChannelInner>, Value)],
    sends: &[(Rc<ChannelInner>, Value, Value)],
    me: TaskRef,
    listed: &mut (usize, usize),
    taken_off: &mut Vec<usize>,
) {
    for (i, (c, _)) in receives.iter().enumerate().take(listed.0) {
        if leave_receivers(interp, c, me, false) && !taken_off.contains(&i) {
            taken_off.push(i);
        }
    }
    for (c, _, _) in sends.iter().take(listed.1) {
        c.lock().send_waiters.retain(|t| *t != me);
    }
    *listed = (0, 0);
}

/// Whether a `select` can send on `c` now (an unbuffered channel needs a
/// waiting receiver).
fn send_ready(c: &ChannelInner, st: &ChannelState) -> bool {
    st.can_send(c.capacity) && (c.capacity > 0 || !st.recv_waiters.is_empty())
}

// ----- atoms --------------------------------------------------------------------------------

fn atom_update(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let cell = atom(interp, recv)?;
    loop {
        let current = lock(cell).clone();
        // The block runs without the lock (it may suspend, or use the
        // atom); the update applies only if the value is still the one
        // the block saw (another task may have changed it meanwhile).
        let new = interp.call_block(&b, smallvec![current.clone()])?;
        new.share();
        let mut g = lock(cell);
        if g.identical(&current) {
            let old = std::mem::replace(&mut *g, new.clone());
            drop(g);
            drop(old);
            return Ok(new);
        }
    }
}
