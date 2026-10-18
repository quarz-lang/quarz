//! Task, Scope, Channel, Selector, Atom and the Kernel entry points.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::sched::{ChannelInner, ScopeInner, SelectorState, TaskHandle};
use crate::value::*;
use smallvec::smallvec;

use super::{block, int};

pub fn register(m: &mut HashMap<&'static str, NativeFn>) {
    m.insert("Kernel#spawn", |i, _, a| {
        let b = block(i, &a)?;
        Ok(Value::Task(i.spawn_task(b, None, "task")))
    });
    m.insert("Kernel#loop", kernel_loop);
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
        let b = block(i, &a)?;
        i.call_block(&b, smallvec![])
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
        Ok(Value::Bool(task(i, r)?.cancel_requested.get()))
    });
    m.insert("Scope#spawn", |i, r, a| {
        let b = block(i, &a)?;
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
        Ok(Value::Bool(chan(i, r)?.closed.get()))
    });
    m.insert("Channel#empty?", |i, r, _| {
        Ok(Value::Bool(chan(i, r)?.buffer.borrow().is_empty()))
    });
    m.insert("Channel#size", |i, r, _| {
        Ok(Value::Int(chan(i, r)?.buffer.borrow().len() as i64))
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
    m.insert("Atom.new", |_, _, a| {
        Ok(Value::Atom(Rc::new(RefCell::new(a.arg(0).clone()))))
    });
    m.insert("Atom#value", |i, r, _| Ok(atom(i, r)?.borrow().clone()));
    m.insert("Atom#get", |i, r, _| Ok(atom(i, r)?.borrow().clone()));
    m.insert("Atom#set", |i, r, a| {
        *atom(i, r)?.borrow_mut() = a.arg(0).clone();
        Ok(Value::Nil)
    });
    m.insert("Atom#update", atom_update);
    m.insert("Atom#compare_and_set", |i, r, a| {
        let cell = atom(i, r)?;
        let same = *cell.borrow() == *a.arg(0);
        if same {
            *cell.borrow_mut() = a.arg(1).clone();
        }
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

fn atom<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RefCell<Value>>, Flow> {
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
            Err(Flow::Raise(e)) if interp.exception_is_a(&e, interp.exc.stop_iteration) => {
                return Ok(Value::Nil)
            }
            Err(e) => return Err(e),
        }
        // Give other tasks a chance in tight loops.
        if interp.sched.borrow().tasks.len() > 1 {
            interp.yield_now();
        }
    }
}

// ----- scopes -------------------------------------------------------------------------

fn cancel_children(interp: &Interp, scope: &Rc<ScopeInner>) {
    scope.cancelled.set(true);
    let children: Vec<Rc<TaskHandle>> = scope.children.borrow().clone();
    for c in children {
        interp.cancel_task(&c);
    }
}

fn task_scope(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let owner = interp.current_task().id;
    let scope = Rc::new(ScopeInner {
        owner,
        children: RefCell::new(Vec::new()),
        cancelled: Cell::new(false),
    });
    let result = interp.call_block(&b, smallvec![Value::Scope(scope.clone())]);
    let (value, mut failure): (Value, Option<Flow>) = match result {
        Ok(v) => (v, None),
        Err(e) => {
            cancel_children(interp, &scope);
            (Value::Nil, Some(e))
        }
    };
    // Wait for every child; the first failure cancels the rest.
    let mut i = 0;
    loop {
        let child = scope.children.borrow().get(i).cloned();
        let Some(child) = child else { break };
        i += 1;
        match interp.await_task(&child) {
            Ok(_) => {}
            Err(Flow::Raise(e)) => {
                let is_cancel = interp.exception_is_a(&e, interp.exc.cancelled);
                if is_cancel && scope.cancelled.get() {
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
    let me = interp.current_task().id;
    let timer = interp.sched.borrow_mut().add_timer(d, me);
    let start = std::time::Instant::now();
    loop {
        if child.is_done() {
            interp.sched.borrow_mut().cancel_timer(timer);
            return interp.await_task(&child);
        }
        if start.elapsed() >= d {
            interp.cancel_task(&child);
            let _ = interp.await_task(&child);
            return Err(interp.raise(interp.exc.timeout, "timed out"));
        }
        child.joiners.borrow_mut().push(me);
        interp.park()?;
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

fn wake_one(interp: &Interp, waiters: &RefCell<std::collections::VecDeque<u32>>) {
    if let Some(id) = waiters.borrow_mut().pop_front() {
        interp.wake(id);
    }
}

fn wake_all(interp: &Interp, waiters: &RefCell<std::collections::VecDeque<u32>>) {
    let ids: Vec<u32> = waiters.borrow_mut().drain(..).collect();
    for id in ids {
        interp.wake(id);
    }
}

fn channel_send(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let c = chan(interp, recv)?;
    let value = args.arg(0).clone();
    loop {
        if c.closed.get() {
            return Err(interp.raise(interp.exc.channel_closed, "channel is closed"));
        }
        if c.can_send() {
            c.buffer.borrow_mut().push_back(value);
            let ticket = c.pushed.get() + 1;
            c.pushed.set(ticket);
            wake_one(interp, &c.recv_waiters);
            if c.capacity == 0 {
                // Rendezvous: wait until a receiver has taken the value.
                while c.taken.get() < ticket {
                    if c.closed.get() && c.taken.get() < ticket {
                        return Err(interp.raise(interp.exc.channel_closed, "channel is closed"));
                    }
                    let me = interp.current_task().id;
                    c.send_waiters.borrow_mut().push_back(me);
                    interp.park()?;
                }
            }
            return Ok(Value::Nil);
        }
        let me = interp.current_task().id;
        c.send_waiters.borrow_mut().push_back(me);
        interp.park()?;
    }
}

fn channel_try_send(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let c = chan(interp, recv)?;
    if c.closed.get() {
        return Err(interp.raise(interp.exc.channel_closed, "channel is closed"));
    }
    // Only buffered channels can accept without a waiting receiver.
    if c.capacity > 0 && c.can_send() {
        c.buffer.borrow_mut().push_back(args.arg(0).clone());
        c.pushed.set(c.pushed.get() + 1);
        wake_one(interp, &c.recv_waiters);
        return Ok(Value::Bool(true));
    }
    if c.capacity == 0 && c.can_send() && !c.recv_waiters.borrow().is_empty() {
        c.buffer.borrow_mut().push_back(args.arg(0).clone());
        c.pushed.set(c.pushed.get() + 1);
        c.taken.set(c.pushed.get());
        wake_one(interp, &c.recv_waiters);
        return Ok(Value::Bool(true));
    }
    Ok(Value::Bool(false))
}

fn take_value(interp: &Interp, c: &ChannelInner) -> Option<Value> {
    let v = c.buffer.borrow_mut().pop_front()?;
    c.taken.set(c.taken.get() + 1);
    wake_all(interp, &c.send_waiters);
    Some(v)
}

fn channel_receive(interp: &Interp, c: &Rc<ChannelInner>, raise_on_closed: bool) -> EvalResult {
    loop {
        if let Some(v) = take_value(interp, c) {
            return Ok(v);
        }
        if c.closed.get() {
            return if raise_on_closed {
                Err(interp.raise(interp.exc.channel_closed, "channel is closed"))
            } else {
                Ok(Value::Nil)
            };
        }
        let me = interp.current_task().id;
        c.recv_waiters.borrow_mut().push_back(me);
        interp.park()?;
    }
}

fn channel_close(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let c = chan(interp, recv)?;
    c.closed.set(true);
    wake_all(interp, &c.recv_waiters);
    wake_all(interp, &c.send_waiters);
    Ok(Value::Nil)
}

fn channel_each(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let c = chan(interp, recv)?.clone();
    let b = block(interp, &args)?;
    loop {
        let v = channel_receive(interp, &c, false)?;
        if v.is_nil() && c.closed.get() && c.buffer.borrow().is_empty() {
            return Ok(Value::Nil);
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
        if interp.sched.borrow().tasks.len() > 1 {
            interp.yield_now();
        }
    }
}

fn select_once(interp: &Interp, state: &Rc<RefCell<SelectorState>>) -> Result<(), Flow> {
    let me = interp.current_task().id;
    let timer_start = std::time::Instant::now();
    let after = state.borrow().after.clone();
    let mut timer_seq = None;
    if let Some((d, _)) = &after {
        timer_seq = Some(interp.sched.borrow_mut().add_timer(*d, me));
    }
    loop {
        // Receives.
        let receives: Vec<(Rc<ChannelInner>, Value)> = state.borrow().receives.clone();
        for (c, handler) in &receives {
            if let Some(v) = take_value(interp, c) {
                if let Some(seq) = timer_seq {
                    interp.sched.borrow_mut().cancel_timer(seq);
                }
                interp.call_block(handler, smallvec![v])?;
                return Ok(());
            }
            if c.closed.get() {
                if let Some(seq) = timer_seq {
                    interp.sched.borrow_mut().cancel_timer(seq);
                }
                return Err(interp.raise(interp.exc.channel_closed, "channel is closed"));
            }
        }
        // Sends.
        let sends: Vec<(Rc<ChannelInner>, Value, Value)> = state.borrow().sends.clone();
        for (c, value, handler) in &sends {
            if c.closed.get() {
                if let Some(seq) = timer_seq {
                    interp.sched.borrow_mut().cancel_timer(seq);
                }
                return Err(interp.raise(interp.exc.channel_closed, "channel is closed"));
            }
            let ready = (c.capacity > 0 && c.can_send())
                || (c.capacity == 0 && c.can_send() && !c.recv_waiters.borrow().is_empty());
            if ready {
                c.buffer.borrow_mut().push_back(value.clone());
                c.pushed.set(c.pushed.get() + 1);
                if c.capacity == 0 {
                    c.taken.set(c.pushed.get());
                }
                wake_one(interp, &c.recv_waiters);
                if let Some(seq) = timer_seq {
                    interp.sched.borrow_mut().cancel_timer(seq);
                }
                interp.call_block(handler, smallvec![])?;
                return Ok(());
            }
        }
        // Timeout.
        if let Some((d, handler)) = &after {
            if timer_start.elapsed() >= *d {
                interp.call_block(handler, smallvec![])?;
                return Ok(());
            }
        }
        // Default.
        let default = state.borrow().default.clone();
        if let Some(handler) = default {
            if let Some(seq) = timer_seq {
                interp.sched.borrow_mut().cancel_timer(seq);
            }
            interp.call_block(&handler, smallvec![])?;
            return Ok(());
        }
        if receives.is_empty() && sends.is_empty() && after.is_none() {
            return Err(interp.err_arg("select with no alternatives"));
        }
        // Register and wait.
        for (c, _) in &receives {
            c.recv_waiters.borrow_mut().push_back(me);
        }
        for (c, _, _) in &sends {
            c.send_waiters.borrow_mut().push_back(me);
        }
        interp.park()?;
    }
}

// ----- atoms --------------------------------------------------------------------------------

fn atom_update(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let cell = atom(interp, recv)?;
    loop {
        let current = cell.borrow().clone();
        let new = interp.call_block(&b, smallvec![current.clone()])?;
        // Single-threaded: the value can only have changed if the block
        // suspended and another task updated it.
        if cell.borrow().identical(&current) {
            *cell.borrow_mut() = new.clone();
            return Ok(new);
        }
    }
}
