//! The second batch of number natives: Integer.sqrt, rounding to digits,
//! bit queries, Float steps and neighbours, the rest of `Math`, and
//! `clamp` with a range.

use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use crate::interp::{Args, EvalResult, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::numeric::{arith, float_to_int, Num};
use super::{block, float, int};

pub fn register(m: &mut super::Registry<NativeFn>) {
    // Int
    native!(m, ["Int.sqrt", "Integer.sqrt"], |i, _, a| {
        let n = Num::of(i, a.arg(0))?.to_big();
        if n.is_negative() {
            return Err(i.raise(
                i.program.exc.argument_error,
                "Numerical argument is out of domain - \"isqrt\"",
            ));
        }
        // An Int's square root is one.
        Ok(match a.arg(0) {
            Value::BigInt(_) => integer(n.sqrt()),
            _ => i.int_of_big(&n.sqrt())?,
        })
    });
    native!(m, "Int#fdiv", |i, r, a| {
        let x = Num::of(i, r)?.to_f64();
        let y = Num::of(i, a.arg(0))?.to_f64();
        Ok(Value::Float(x / y))
    });
    native!(m, "Int#ceildiv", |i, r, a| {
        // -(-a / b) with floor division is the ceiling.
        let neg = arith(
            i,
            r,
            &Args {
                pos: smallvec![Value::Int(-1)],
                ..Args::default()
            },
            "*",
        )?;
        let q = arith(i, &neg, &a, "/")?;
        arith(
            i,
            &q,
            &Args {
                pos: smallvec![Value::Int(-1)],
                ..Args::default()
            },
            "*",
        )
    });
    native!(m, "Int#pow", |i, r, a| {
        if a.pos.len() == 1 {
            return arith(i, r, &a, "**");
        }
        super::numeric::int_pow_mod(i, r, a)
    });
    native!(m, "Int#digits", |i, r, a| {
        let base = match a.pos.first() {
            Some(b) => int(i, b, "base")?,
            None => 10,
        };
        if base < 2 {
            return Err(i.err_arg(&format!("invalid radix {base}")));
        }
        let mut n = Num::of(i, r)?.to_big();
        if n.is_negative() {
            return Err(i.raise(i.program.exc.argument_error, "out of domain"));
        }
        let base = BigInt::from(base);
        let mut out = Vec::new();
        if n.is_zero() {
            out.push(Value::Int(0));
        }
        while !n.is_zero() {
            let (q, rem) = num_integer::Integer::div_rem(&n, &base);
            out.push(i.int_of_big(&rem)?);
            n = q;
        }
        Ok(Value::array(out))
    });
    native!(m, "Int#floor", |i, r, a| {
        int_round_digits(i, r, a, Rounding::Floor)
    });
    native!(m, "Int#ceil", |i, r, a| {
        int_round_digits(i, r, a, Rounding::Ceil)
    });
    native!(m, "Int#round", |i, r, a| {
        int_round_digits(i, r, a, Rounding::Round)
    });
    native!(m, "Int#truncate", |i, r, a| {
        int_round_digits(i, r, a, Rounding::Truncate)
    });
    native!(m, "Int#[]", |i, r, a| {
        let bit = int(i, a.arg(0), "bit")?;
        if bit < 0 {
            return Ok(Value::Int(0));
        }
        let n = Num::of(i, r)?.to_big();
        Ok(Value::Int(
            if (n >> bit as usize) & BigInt::from(1) == BigInt::from(1) {
                1
            } else {
                0
            },
        ))
    });
    native!(m, "Int#allbits?", |i, r, a| {
        let n = Num::of(i, r)?.to_big();
        let mask = Num::of(i, a.arg(0))?.to_big();
        Ok(Value::Bool((&n & &mask) == mask))
    });
    native!(m, "Int#anybits?", |i, r, a| {
        let n = Num::of(i, r)?.to_big();
        let mask = Num::of(i, a.arg(0))?.to_big();
        Ok(Value::Bool(!(n & mask).is_zero()))
    });
    native!(m, "Int#nobits?", |i, r, a| {
        let n = Num::of(i, r)?.to_big();
        let mask = Num::of(i, a.arg(0))?.to_big();
        Ok(Value::Bool((n & mask).is_zero()))
    });
    native!(m, "Int#bit_set?", |i, r, a| {
        let bit = int(i, a.arg(0), "bit")?;
        let n = Num::of(i, r)?.to_big();
        Ok(Value::Bool(
            bit >= 0 && !((n >> bit as usize) & BigInt::from(1)).is_zero(),
        ))
    });

    // Float
    native!(m, "Float#divmod", |i, r, a| {
        let x = float(i, r, "Float")?;
        let y = Num::of(i, a.arg(0))?.to_f64();
        if y == 0.0 {
            return Err(i.raise(i.program.exc.zero_division, "divided by 0"));
        }
        let q = (x / y).floor();
        let rem = x - q * y;
        Ok(Value::array(vec![float_to_int(i, q)?, Value::Float(rem)]))
    });
    native!(m, "Float#fdiv", |i, r, a| {
        let x = float(i, r, "Float")?;
        let y = Num::of(i, a.arg(0))?.to_f64();
        Ok(Value::Float(x / y))
    });
    native!(m, "Float#floor", |i, r, a| {
        float_round_digits(i, r, a, Rounding::Floor)
    });
    native!(m, "Float#ceil", |i, r, a| {
        float_round_digits(i, r, a, Rounding::Ceil)
    });
    native!(m, "Float#truncate", |i, r, a| {
        float_round_digits(i, r, a, Rounding::Truncate)
    });
    native!(m, "Float#next_float", |i, r, _| {
        Ok(Value::Float(float(i, r, "Float")?.next_up()))
    });
    native!(m, "Float#prev_float", |i, r, _| {
        Ok(Value::Float(float(i, r, "Float")?.next_down()))
    });
    native!(m, "Float#step", |i, r, a| {
        let from = float(i, r, "Float")?;
        let limit = Num::of(i, a.arg(0))?.to_f64();
        let step = Num::of(i, a.arg(1))?.to_f64();
        if step == 0.0 {
            return Err(i.err_arg("step cannot be 0"));
        }
        let b = block(i, &a)?;
        // Count the steps up front so that rounding errors do not lose
        // the last one, as Ruby does.
        let n = ((limit - from) / step + 1e-9).floor();
        if n < 0.0 {
            return Ok(Value::Nil);
        }
        let mut k = 0.0;
        while k <= n {
            i.call_block(&b, smallvec![Value::Float(from + k * step)])?;
            k += 1.0;
        }
        Ok(Value::Nil)
    });

    // Math
    native!(m, "Math.asin", |i, _, a| unary(i, &a, f64::asin));
    native!(m, "Math.acos", |i, _, a| unary(i, &a, f64::acos));
    native!(m, "Math.sinh", |i, _, a| unary(i, &a, f64::sinh));
    native!(m, "Math.cosh", |i, _, a| unary(i, &a, f64::cosh));
    native!(m, "Math.tanh", |i, _, a| unary(i, &a, f64::tanh));
    native!(m, "Math.asinh", |i, _, a| unary(i, &a, f64::asinh));
    native!(m, "Math.acosh", |i, _, a| unary(i, &a, f64::acosh));
    native!(m, "Math.atanh", |i, _, a| unary(i, &a, f64::atanh));
    native!(m, "Math.log1p", |i, _, a| unary(i, &a, f64::ln_1p));
    native!(m, "Math.expm1", |i, _, a| unary(i, &a, f64::exp_m1));

    // Comparable#clamp with a range.
    native!(m, "Comparable#clamp", |i, r, a| {
        use std::cmp::Ordering;
        let (min, max) = match a.arg(0) {
            Value::Range(rg) if a.pos.len() == 1 => {
                if rg.exclusive && !rg.hi.is_nil() {
                    return Err(i.err_arg("cannot clamp with an exclusive range"));
                }
                (rg.lo.clone(), rg.hi.clone())
            }
            _ => (a.arg(0).clone(), a.arg(1).clone()),
        };
        if !min.is_nil() && i.compare(r, &min)? == Ordering::Less {
            return Ok(min);
        }
        if !max.is_nil() && i.compare(r, &max)? == Ordering::Greater {
            return Ok(max);
        }
        Ok(r.clone())
    });
}

#[derive(Clone, Copy)]
enum Rounding {
    Floor,
    Ceil,
    Round,
    Truncate,
}

fn unary(interp: &Interp, args: &Args, f: fn(f64) -> f64) -> EvalResult {
    Ok(Value::Float(f(float(interp, args.arg(0), "x")?)))
}

/// `Int#floor(digits)` and friends: a negative count of digits rounds to
/// a power of ten; otherwise the integer is unchanged.
fn int_round_digits(interp: &Interp, recv: &Value, args: Args, how: Rounding) -> EvalResult {
    let Some(d) = args.pos.first() else {
        return Ok(recv.clone());
    };
    let digits = int(interp, d, "digits")?;
    if digits >= 0 {
        return Ok(recv.clone());
    }
    let n = Num::of(interp, recv)?.to_big();
    let unit = num_traits::pow(BigInt::from(10), (-digits) as usize);
    let (q, rem) = num_integer::Integer::div_mod_floor(&n, &unit);
    let rounded = match how {
        Rounding::Floor => q * &unit,
        Rounding::Ceil => {
            if rem.is_zero() {
                q * &unit
            } else {
                (q + 1) * &unit
            }
        }
        Rounding::Truncate => {
            if n.is_negative() && !rem.is_zero() {
                (q + 1) * &unit
            } else {
                q * &unit
            }
        }
        Rounding::Round => {
            // Half away from zero.
            let twice = &rem * 2;
            let up = if n.is_negative() {
                twice > unit
            } else {
                twice >= unit
            };
            if up {
                (q + 1) * &unit
            } else {
                q * &unit
            }
        }
    };
    interp.int_of_big(&rounded)
}

fn float_round_digits(interp: &Interp, recv: &Value, args: Args, how: Rounding) -> EvalResult {
    let f = float(interp, recv, "Float")?;
    let apply = |x: f64| -> f64 {
        match how {
            Rounding::Floor => x.floor(),
            Rounding::Ceil => x.ceil(),
            Rounding::Truncate => x.trunc(),
            Rounding::Round => x.round(),
        }
    };
    match args.pos.first() {
        None => float_to_int(interp, apply(f)),
        Some(d) => {
            let digits = int(interp, d, "digits")?;
            if digits <= 0 {
                let factor = 10f64.powi((-digits) as i32);
                return float_to_int(interp, apply(f / factor) * factor);
            }
            let factor = 10f64.powi(digits as i32);
            Ok(Value::Float(apply(f * factor) / factor))
        }
    }
}
