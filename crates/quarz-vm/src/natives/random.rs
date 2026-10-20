//! `Random`, and the `Kernel#rand`/`srand` family over the default
//! generator.

use std::cell::RefCell;
use std::rc::Rc;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::{float, int};

thread_local! {
    /// The generator behind `rand`/`srand` and `Random.rand`.
    static DEFAULT: RefCell<Option<RandomState>> = const { RefCell::new(None) };
}

/// A seed from the clock and the address space.
pub fn new_seed() -> i64 {
    let t = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(1);
    let stack = &t as *const u64 as u64;
    (t ^ stack.rotate_left(32) ^ (std::process::id() as u64) << 48) as i64
}

fn with_default<R>(f: impl FnOnce(&mut RandomState) -> R) -> R {
    DEFAULT.with(|d| {
        let mut d = d.borrow_mut();
        let state = d.get_or_insert_with(|| RandomState::new(new_seed()));
        f(state)
    })
}

/// A random 64-bit word from the default generator (used by `shuffle`
/// and `sample`).
pub fn next_random() -> u64 {
    with_default(|s| s.next_u64())
}

pub fn register(m: &mut super::Registry<NativeFn>) {
    m.insert("Random.new", |_, _, a| {
        let seed = match a.pos.first() {
            Some(Value::Int(i)) => *i,
            Some(Value::BigInt(b)) => {
                use num_traits::ToPrimitive;
                b.to_i64()
                    .unwrap_or_else(|| (b.bits() as i64).wrapping_mul(0x9E3779B9))
            }
            _ => new_seed(),
        };
        Ok(Value::Random(Rc::new(RefCell::new(RandomState::new(seed)))))
    });
    m.insert("Random.new_seed", |_, _, _| Ok(Value::Int(new_seed())));
    m.insert("Random.rand", |i, _, a| with_default(|s| draw(i, s, &a)));
    m.insert("Random.bytes", |i, _, a| {
        let n = int(i, a.arg(0), "size")?.max(0) as usize;
        Ok(Value::bytes(with_default(|s| random_bytes(s, n))))
    });
    m.insert("Random#seed", |i, r, _| {
        Ok(Value::Int(rng(i, r)?.borrow().seed))
    });
    m.insert("Random#rand", |i, r, a| {
        draw(i, &mut rng(i, r)?.borrow_mut(), &a)
    });
    m.insert("Random#bytes", |i, r, a| {
        let n = int(i, a.arg(0), "size")?.max(0) as usize;
        Ok(Value::bytes(random_bytes(&mut rng(i, r)?.borrow_mut(), n)))
    });
    m.insert("Random#==", |i, r, a| {
        Ok(Value::Bool(match a.arg(0) {
            Value::Random(other) => Rc::ptr_eq(rng(i, r)?, other),
            _ => false,
        }))
    });
    m.insert("Kernel#rand", |i, _, a| with_default(|s| draw(i, s, &a)));
    m.insert("Kernel#srand", |i, _, a| {
        let seed = match a.pos.first() {
            Some(v) => int(i, v, "seed")?,
            None => new_seed(),
        };
        Ok(Value::Int(with_default(|s| {
            let previous = s.seed;
            *s = RandomState::new(seed);
            previous
        })))
    });
}

fn rng<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RefCell<RandomState>>, Flow> {
    match v {
        Value::Random(r) => Ok(r),
        _ => Err(interp.err_type("expected a Random")),
    }
}

fn random_bytes(state: &mut RandomState, n: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let word = state.next_u64().to_le_bytes();
        let take = (n - out.len()).min(8);
        out.extend_from_slice(&word[..take]);
    }
    out
}

/// `rand`, `rand(max)`, `rand(max_float)`, `rand(range)`.
fn draw(interp: &Interp, state: &mut RandomState, args: &Args) -> EvalResult {
    match args.pos.first() {
        None => Ok(Value::Float(state.next_f64())),
        Some(Value::Int(n)) => {
            if *n <= 0 {
                return Err(interp.err_arg(&format!("invalid argument: {n}")));
            }
            Ok(Value::Int(state.below(*n as u64) as i64))
        }
        Some(Value::Float(f)) => {
            if *f <= 0.0 {
                return Err(interp.err_arg(&format!("invalid argument: {f}")));
            }
            Ok(Value::Float(state.next_f64() * f))
        }
        Some(Value::Range(r)) => match (&r.lo, &r.hi) {
            (Value::Int(lo), Value::Int(hi)) => {
                let hi = if r.exclusive { hi - 1 } else { *hi };
                if hi < *lo {
                    return Err(interp.err_arg("invalid argument: empty range"));
                }
                let span = (hi - lo) as u64 + 1;
                Ok(Value::Int(lo + state.below(span) as i64))
            }
            (lo, hi) => {
                let lo = float(interp, lo, "range start")?;
                let hi = float(interp, hi, "range end")?;
                if hi < lo {
                    return Err(interp.err_arg("invalid argument: empty range"));
                }
                Ok(Value::Float(lo + state.next_f64() * (hi - lo)))
            }
        },
        Some(other) => Err(interp.err_type(&format!(
            "rand takes an Int, Float or Range, got {}",
            interp.class_name(other)
        ))),
    }
}
