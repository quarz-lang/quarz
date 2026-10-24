//! Task, Scope, Channel, Selector, Atom and the Kernel entry points.

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
    let Value::Proc(c) = b else {
        b.share();
        return b.clone();
    };
    let (ClosureBody::Func(f), Some(frame)) = (&c.body, &c.frame) else {
        b.share();
        return b.clone();
    };
    fn copy(frame: &Rc<Frame>, depth: usize, caps: &[Vec<u32>]) -> Rc<Frame> {
        let parent = if depth + 1 < caps.len() {
            frame.parent.as_ref().map(|p| copy(p, depth + 1, caps))
        } else {
            None
        };
        let src = frame.slots.borrow();
        let mut slots: smallvec::SmallVec<[Value; 8]> = smallvec![Value::Nil; src.len()];
        for &s in &caps[depth] {
            if let Some(v) = src.get(s as usize) {
                slots[s as usize] = v.clone();
            }
        }
        Frame::from_slots(slots, parent)
    }
    let caps = captured_slots(interp, *f);
    let block = Value::Proc(Rc::new(Closure {
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
    }));
    // The block and what it captures pass to the new task.
    block.share();
    block
}

pub fn register(m: &mut super::Registry<NativeFn>) {
    m.insert("Kernel#spawn", |i, _, a| {
        let b = snapshot(i, &block(i, &a)?);
        Ok(Value::Task(i.spawn_task(b, None, "task")))
    });
    m.insert("Kernel#loop", kernel_loop);
    // A shareable procedure copies what it captures when it is made.
    m.insert("Proc#__copy_captures", |i, r, _| Ok(snapshot(i, r)));
    m.insert("Kernel#sleep", |i, _, a| {
        i.sleep(duration(i, a.arg(0))?)?;
        Ok(Value::Nil)
    });
    m.insert("Kernel#select", |i, _, a| {
        let b = block(i, &a)?;
        run_select(i, &b, false)
    });
    m.insert("Channel.select_loop", |i, _, a| {
        let b = block(i, &a)?;
        run_select(i, &b, true)
    });
    m.insert("Task.scope", task_scope);
    m.insert("Task.sleep", |i, _, a| {
        i.sleep(duration(i, a.arg(0))?)?;
        Ok(Value::Nil)
    });
    m.insert("Task.yield", |i, _, _| {
        i.yield_now();
        Ok(Value::Nil)
    });
    m.insert("Task.current", |i, _, _| Ok(Value::Task(i.current_task())));
    m.insert("Task.timeout", task_timeout);
    m.insert("Task.blocking", |i, _, a| {
        use crate::transfer::{self, WorkerExit};
        let b = block(i, &a)?;
        let closure = transfer::export(i, &b)?;
        let image = i.image();
        let argv = i.program.argv.clone();
        let outcome = i.block_on(move || transfer::run_on_thread(image, argv, closure))?;
        i.write_out_bytes(&outcome.output);
        match outcome.exit {
            WorkerExit::Value(t) => Ok(transfer::import(i, t)),
            WorkerExit::Raise(t) => Err(Flow::Raise(transfer::import(i, t))),
            WorkerExit::Exit(code) => Err(Flow::Exit(code)),
        }
    });
    m.insert("Task.check_cancel", |i, _, _| {
        let t = i.current_task();
        i.check_cancel(&t)?;
        Ok(Value::Nil)
    });
    m.insert("Task#await", |i, r, _| i.await_task(task(i, r)?));
    m.insert("Task#cancel", |i, r, _| {
        i.cancel_task(task(i, r)?);
        Ok(Value::Nil)
    });
    m.insert("Task#done?", |i, r, _| {
        Ok(Value::Bool(task(i, r)?.is_done()))
    });
    m.insert("Task#cancelled?", |i, r, _| {
        Ok(Value::Bool(task(i, r)?.cancel_requested()))
    });
    m.insert("Scope#spawn", |i, r, a| {
        let b = snapshot(i, &block(i, &a)?);
        let s = scope(i, r)?.clone();
        Ok(Value::Task(i.spawn_task(b, Some(s), "task")))
    });
    m.insert("Scope#cancel", |i, r, _| {
        let s = scope(i, r)?.clone();
        cancel_children(i, &s);
        Ok(Value::Nil)
    });
    m.insert("Channel.new", channel_new);
    m.insert("Channel#send", channel_send);
    m.insert("Channel#receive", |i, r, _| {
        channel_receive(i, chan(i, r)?, true)
    });
    m.insert("Channel#receive?", |i, r, _| {
        channel_receive(i, chan(i, r)?, false)
    });
    m.insert("Channel#try_send", channel_try_send);
    m.insert("Channel#try_receive", |i, r, _| {
        let c = chan(i, r)?;
        Ok(take_value(i, c).unwrap_or(Value::Nil))
    });
    m.insert("Channel#close", channel_close);
    m.insert("Channel#closed?", |i, r, _| {
        Ok(Value::Bool(chan(i, r)?.lock().closed))
    });
    m.insert("Channel#empty?", |i, r, _| {
        Ok(Value::Bool(chan(i, r)?.lock().buffer.is_empty()))
    });
    m.insert("Channel#size", |i, r, _| {
        Ok(Value::Int(chan(i, r)?.lock().buffer.len() as i64))
    });
    m.insert("Channel#each", channel_each);
    m.insert("Selector#receive", |i, r, a| {
        let c = chan(i, a.arg(0))?.clone();
        let b = block(i, &a)?;
        sel(i, r)?.borrow_mut().receives.push((c, b));
        Ok(Value::Nil)
    });
    m.insert("Selector#send", |i, r, a| {
        let c = chan(i, a.arg(0))?.clone();
        let b = block(i, &a)?;
        sel(i, r)?.borrow_mut().sends.push((c, a.arg(1).clone(), b));
        Ok(Value::Nil)
    });
    m.insert("Selector#after", |i, r, a| {
        let d = duration(i, a.arg(0))?;
        let b = block(i, &a)?;
        sel(i, r)?.borrow_mut().after = Some((d, b));
        Ok(Value::Nil)
    });
    m.insert("Selector#default", |i, r, a| {
        let b = block(i, &a)?;
        sel(i, r)?.borrow_mut().default = Some(b);
        Ok(Value::Nil)
    });
    m.insert("Selector#stop", |i, r, _| {
        sel(i, r)?.borrow_mut().stopped = true;
        Ok(Value::Nil)
    });
    // An atom's content is read by every task that holds the atom.
    m.insert("Atom.new", |_, _, a| {
        let v = a.arg(0).clone();
        v.share();
        Ok(Value::Atom(Rc::new_shared(std::sync::Mutex::new(v))))
    });
    m.insert("Atom#value", |i, r, _| Ok(lock(atom(i, r)?).clone()));
    m.insert("Atom#get", |i, r, _| Ok(lock(atom(i, r)?).clone()));
    m.insert("Atom#set", |i, r, a| {
        let v = a.arg(0).clone();
        v.share();
        let old = std::mem::replace(&mut *lock(atom(i, r)?), v);
        drop(old);
        Ok(Value::Nil)
    });
    m.insert("Atom#update", atom_update);
    m.insert("Atom#compare_and_set", |i, r, a| {
        let new = a.arg(1).clone();
        new.share();
        let mut cell = lock(atom(i, r)?);
        let same = *cell == *a.arg(0);
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
        _ => Err(interp.err_type("expected a Scope")),
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
        _ => Err(interp.err_type("expected a Selector")),
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
        // Give other tasks a chance in tight loops.
        if interp.sched.borrow().task_count() > 1 {
            interp.yield_now();
        }
    }
}

// ----- scopes -------------------------------------------------------------------------

fn cancel_children(interp: &Interp, scope: &Rc<ScopeInner>) {
    scope.cancel();
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
        let Some(child) = scope.first_child() else {
            break;
        };
        let r = interp.await_task(&child);
        if let (Err(Flow::Raise(e)), false) = (&r, child.is_done()) {
            // The wait itself was interrupted: the task running the scope
            // was cancelled. That is the scope's failure; it cancels the
            // children and still waits for them (their `ensure` runs
            // before the scope ends).
            if failure.is_none() {
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
                } else if failure.is_none() {
                    failure = Some(Flow::Raise(e));
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

fn task_timeout(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let d = duration(interp, args.arg(0))?;
    let b = block(interp, &args)?;
    let child = interp.spawn_task(b, None, "timeout");
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
            let _ = interp.await_task(&child);
            return Err(interp.raise(interp.program.exc.timeout, "timed out"));
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
            // Cancelled: so is the block.
            lock(&child.joiners).retain(|t| *t != me.task_ref());
            interp.sched.borrow_mut().cancel_timer(timer);
            interp.cancel_task(&child);
            return Err(e);
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
    loop {
        let state = Rc::new(RefCell::new(SelectorState::default()));
        interp.call_block(block, smallvec![Value::Selector(state.clone())])?;
        if state.borrow().stopped {
            return Ok(Value::Nil);
        }
        select_once(interp, &state)?;
        if state.borrow().stopped || !looping {
            return Ok(Value::Nil);
        }
        if interp.sched.borrow().task_count() > 1 {
            interp.yield_now();
        }
    }
}

fn select_once(interp: &Interp, state: &Rc<RefCell<SelectorState>>) -> Result<(), Flow> {
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
            break 'select Ok((handler, None));
        }
        if receives.is_empty() && sends.is_empty() && after.is_none() {
            break 'select Err(interp.err_arg("select with no alternatives"));
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
    Ok(())
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
