//! `Enumerator#next` over the sources it can step one element at a time
//! without running their method: the built-in collections, integer
//! ranges, the counting methods of `Int`, a string's characters, and the
//! enumerators the `Enumerable` methods make over those (or over another
//! such enumerator). The source's elements come one by one from its own
//! state (`Stepper`), so an endless one gives them as well; a method
//! written in Quarz has no such state, and its enumerator no `next`.

use std::collections::VecDeque;

use crate::interp::{EvalResult, Flow, Interp};
use crate::value::*;

/// The state for the first element of `method` (with `args`) on `recv`,
/// or `None` when it cannot be stepped; a step the method refuses raises
/// as it does.
pub(super) fn start(
    interp: &Interp,
    recv: &Value,
    method: &str,
    args: &[Value],
) -> Result<Option<Stepper>, Flow> {
    let int_arg = |i: usize| match args.get(i) {
        Some(Value::Int(n)) => Some(*n),
        _ => None,
    };
    Ok(match (recv, method) {
        (
            Value::Array(_)
            | Value::ArrayBuilder(_)
            | Value::Hash(_)
            | Value::HashBuilder(_)
            | Value::Set(_)
            | Value::SetBuilder(_),
            "each",
        ) => Some(Stepper::Index(0)),
        (Value::Range(r), "each") if super::collections::string_steps(r).is_some() => {
            super::collections::string_steps(r).map(|s| Stepper::Strings(Box::new(s)))
        }
        (Value::Range(r), "each" | "step") => {
            let step = if method == "step" {
                int_arg(0)
            } else {
                Some(1)
            };
            match (&r.lo, &r.hi, step) {
                (_, _, Some(step)) if step <= 0 => {
                    return Err(interp.err_arg("step must be positive"));
                }
                (Value::Int(lo), hi, Some(step)) => {
                    let last = match hi {
                        // (Ruby's `step` there gives floats.)
                        Value::Float(f) if f.is_infinite() && *f > 0.0 && method == "each" => None,
                        Value::Int(hi) if r.exclusive => match hi.checked_sub(1) {
                            Some(last) => Some(last),
                            None => return Ok(Some(Stepper::Done)),
                        },
                        Value::Int(hi) => Some(*hi),
                        Value::Nil => None,
                        _ => return Err(not_integers(interp, method)),
                    };
                    Some(Stepper::Ints {
                        next: *lo,
                        step,
                        last,
                    })
                }
                _ => return Err(not_integers(interp, method)),
            }
        }
        (Value::Int(n), "times") if *n <= 0 => Some(Stepper::Done),
        (Value::Int(n), "times") => Some(Stepper::Ints {
            next: 0,
            step: 1,
            last: Some(n - 1),
        }),
        (Value::Int(n), "upto" | "downto") => int_arg(0).map(|limit| Stepper::Ints {
            next: *n,
            step: if method == "upto" { 1 } else { -1 },
            last: Some(limit),
        }),
        (Value::Int(n), "step") => match (int_arg(0), int_arg(1)) {
            (Some(_), Some(0)) => return Err(interp.err_arg("step cannot be 0")),
            (Some(limit), Some(step)) => Some(Stepper::Ints {
                next: *n,
                step,
                last: Some(limit),
            }),
            _ => None,
        },
        (Value::Str(_) | Value::Short(_), "each_char") => Some(Stepper::Chars(0)),
        (Value::Enumerator(inner), "each") => {
            start(interp, &inner.recv, &inner.method, &inner.args)?
                .map(|s| Stepper::Inner(Box::new(s)))
        }
        // A subclass of `Enumerator`: by its `next`.
        (Value::Object(_), "each")
            if interp
                .program
                .world
                .class_is_a(interp.class_of(recv), interp.program.rt.enumerator) =>
        {
            Some(Stepper::ByNext)
        }
        (_, "each_with_index_pairs") => {
            start(interp, recv, "each", &[])?.map(|s| Stepper::Pairs(Box::new(s), 0))
        }
        (_, "each_slice" | "each_cons") => match int_arg(0) {
            Some(n) if n <= 0 => return Err(interp.err_arg("invalid size")),
            Some(n) => start(interp, recv, "each", &[])?.map(|s| {
                if method == "each_slice" {
                    Stepper::Slices(Box::new(s), n as usize)
                } else {
                    Stepper::Windows(Box::new(s), n as usize, VecDeque::new())
                }
            }),
            _ => None,
        },
        _ => None,
    })
}

/// The next element of the source on `recv` that `st` steps, moving `st`
/// past it, or `None` past the end (`st` is then `Done`).
pub(super) fn step(interp: &Interp, st: &mut Stepper, recv: &Value) -> Result<Option<Value>, Flow> {
    let v = match st {
        Stepper::Index(i) => {
            let v = element_at(recv, *i);
            *i += 1;
            v
        }
        Stepper::Ints { next, step, last } => {
            let v = *next;
            let past = match *last {
                Some(l) => (*step > 0 && v > l) || (*step < 0 && v < l),
                None => false,
            };
            if past {
                None
            } else {
                match v.checked_add(*step) {
                    Some(n) => *next = n,
                    // The last that fits: nothing after it.
                    None => *st = Stepper::Done,
                }
                return Ok(Some(Value::Int(v)));
            }
        }
        Stepper::Chars(offset) => {
            let text = recv.as_str().unwrap_or("");
            match text[*offset..].chars().next() {
                Some(c) => {
                    *offset += c.len_utf8();
                    Some(Value::string(c.to_string()))
                }
                None => None,
            }
        }
        Stepper::Pairs(base, k) => match step(interp, base, recv)? {
            Some(x) => {
                let pair = Value::array(vec![x, Value::Int(*k)]);
                *k += 1;
                Some(pair)
            }
            None => None,
        },
        Stepper::Slices(base, n) => {
            let mut slice = Vec::with_capacity(*n);
            while slice.len() < *n {
                match step(interp, base, recv)? {
                    Some(x) => slice.push(x),
                    None => break,
                }
            }
            (!slice.is_empty()).then(|| Value::array(slice))
        }
        Stepper::Windows(base, n, window) => {
            let mut full = true;
            while window.len() < *n {
                match step(interp, base, recv)? {
                    Some(x) => window.push_back(x),
                    None => {
                        full = false;
                        break;
                    }
                }
            }
            if full {
                let v = Value::array(window.iter().cloned().collect());
                window.pop_front();
                Some(v)
            } else {
                None
            }
        }
        Stepper::Inner(base) => match recv {
            Value::Enumerator(inner) => step(interp, base, &inner.recv)?,
            _ => None,
        },
        Stepper::ByNext => match interp.send(recv, "next", smallvec::smallvec![], None) {
            Ok(x) => Some(x),
            Err(Flow::Raise(e)) if interp.exception_is_a(&e, interp.program.exc.stop_iteration) => {
                None
            }
            Err(e) => return Err(e),
        },
        Stepper::Strings(steps) => steps
            .downcast_mut::<super::text::StringSteps>()
            .and_then(|s| s.next())
            .map(Value::string),
        Stepper::Done | Stepper::Running => None,
    };
    if v.is_none() {
        *st = Stepper::Done;
    }
    Ok(v)
}

/// The element at index `i` of a collection, in iteration order (a
/// hash's as a `[key, value]` pair).
fn element_at(recv: &Value, i: usize) -> Option<Value> {
    match recv {
        Value::Array(a) => a.get(i),
        Value::ArrayBuilder(b) => b.borrow().get(i).cloned(),
        Value::Hash(h) => match &**h {
            HashData::Values(m) => m
                .get_index(i)
                .map(|(k, v)| Value::array(vec![k.clone(), v.clone()])),
            HashData::Ints(m) => m
                .get_index(i)
                .map(|(k, v)| Value::array(vec![Value::Int(*k), Value::Int(*v)])),
        },
        Value::HashBuilder(b) => b
            .borrow()
            .get_index(i)
            .map(|(k, v)| Value::array(vec![k.clone(), v.clone()])),
        Value::Set(s) => s.get_index(i).cloned(),
        Value::SetBuilder(b) => b.borrow().get_index(i).cloned(),
        _ => None,
    }
}

/// `Enumerator#next`: the element `peek` took, or the source's next.
pub(super) fn next(interp: &Interp, recv: &Value) -> EvalResult {
    next_for(interp, recv, "next")
}

/// `next`, for `method` (`next` or `peek`, which an error names).
fn next_for(interp: &Interp, recv: &Value, method: &str) -> EvalResult {
    let e = match recv {
        Value::Enumerator(e) => e,
        // A subclass that does not define it.
        _ => return Err(undefined(interp, recv, method)),
    };
    if let Some(v) = e.take_peeked() {
        return Ok(v);
    }
    // (A subclass's `next`, which a step may call, could come back here.)
    let Ok(taken) = e.begin_step() else {
        return Err(interp.raise(
            interp.program.exc.runtime_error,
            &format!("Enumerator#{method} called from its own iteration"),
        ));
    };
    let mut st = match taken {
        Some(st) => st,
        None => match start(interp, &e.recv, &e.method, &e.args) {
            Ok(Some(st)) => st,
            Ok(None) => {
                e.end_step(None);
                let method = e.method.strip_suffix("_pairs").unwrap_or(&e.method);
                return Err(interp.raise(
                    interp.program.exc.not_implemented,
                    &format!(
                        "{}#{method} gives no elements one at a time: `next` needs a built-in \
                         source, or a subclass of Enumerator that defines it",
                        interp.class_name(&e.recv)
                    ),
                ));
            }
            Err(flow) => {
                e.end_step(None);
                return Err(flow);
            }
        },
    };
    let v = step(interp, &mut st, &e.recv);
    e.end_step(Some(st));
    let v = v?;
    v.ok_or_else(|| {
        interp.raise(
            interp.program.exc.stop_iteration,
            "iteration reached an end",
        )
    })
}

/// `Enumerator#peek`: what `next` returns next, kept for it.
pub(super) fn peek(interp: &Interp, recv: &Value) -> EvalResult {
    let Value::Enumerator(e) = recv else {
        return Err(undefined(interp, recv, "peek"));
    };
    let v = next_for(interp, recv, "peek")?;
    e.set_peeked(v.clone());
    Ok(v)
}

/// `Enumerator#rewind`.
pub(super) fn rewind(interp: &Interp, recv: &Value) -> EvalResult {
    let Value::Enumerator(e) = recv else {
        return Err(undefined(interp, recv, "rewind"));
    };
    if !e.rewind() {
        return Err(interp.raise(
            interp.program.exc.runtime_error,
            "Enumerator#rewind called from its own iteration",
        ));
    }
    // A subclass this one is over rewinds too, when it can (as Ruby calls
    // the receiver's `rewind`).
    let mut source = &e.recv;
    while let Value::Enumerator(inner) = source {
        source = &inner.recv;
    }
    let own = interp
        .has_user_method(source, "rewind", 0)
        .is_some_and(|m| interp.program.method(m).owner != interp.program.rt.enumerator);
    if matches!(source, Value::Object(_)) && own {
        interp.send(source, "rewind", smallvec::smallvec![], None)?;
    }
    Ok(recv.clone())
}

/// `Enumerator#each` on a subclass: its `next` until `StopIteration`.
pub(super) fn each_by_next(interp: &Interp, recv: &Value, block: &Value) -> EvalResult {
    loop {
        let x = match interp.send(recv, "next", smallvec::smallvec![], None) {
            Ok(x) => x,
            Err(Flow::Raise(e)) if interp.exception_is_a(&e, interp.program.exc.stop_iteration) => {
                return Ok(Value::Nil)
            }
            Err(e) => return Err(e),
        };
        interp.call_block(block, smallvec::smallvec![x])?;
    }
}

/// A method of `Enumerator` that a subclass is to define.
pub(super) fn undefined(interp: &Interp, recv: &Value, method: &str) -> Flow {
    interp.raise(
        interp.program.exc.not_implemented,
        &format!("{}#{method} is not defined", interp.class_name(recv)),
    )
}

/// The error the block form of `Range#each` or `#step` raises for a range
/// it cannot iterate.
fn not_integers(interp: &Interp, method: &str) -> Flow {
    interp.err_type(if method == "step" {
        "step needs an integer range"
    } else {
        "cannot iterate over an endless or non-integer range"
    })
}
