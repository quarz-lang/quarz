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
pub(super) enum Rounding {
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
    // Every Int is below 10**19 in magnitude: to 10**20 or more, 0, or an
    // overflow away from zero (without computing a huge power).
    if digits <= -20 {
        let n = int(interp, recv, "Int")?;
        let away = match how {
            Rounding::Floor => n < 0,
            Rounding::Ceil => n > 0,
            Rounding::Truncate | Rounding::Round => false,
        };
        return if away {
            Err(interp.err_overflow())
        } else {
            Ok(Value::Int(0))
        };
    }
    let n = Num::of(interp, recv)?.to_big();
    let rounded = round_big(&n, digits.unsigned_abs() as usize, how);
    interp.int_of_big(&rounded)
}

/// `n` rounded to a multiple of `10**k`.
fn round_big(n: &BigInt, k: usize, how: Rounding) -> BigInt {
    let unit = num_traits::pow(BigInt::from(10), k);
    let (q, rem) = num_integer::Integer::div_mod_floor(n, &unit);
    let up = match how {
        Rounding::Floor => false,
        Rounding::Ceil => !rem.is_zero(),
        Rounding::Truncate => n.is_negative() && !rem.is_zero(),
        Rounding::Round => {
            // Half away from zero.
            let twice = &rem * 2;
            if n.is_negative() {
                twice > unit
            } else {
                twice >= unit
            }
        }
    };
    if up {
        (q + 1) * &unit
    } else {
        q * &unit
    }
}

pub(super) fn float_round_digits(
    interp: &Interp,
    recv: &Value,
    args: Args,
    how: Rounding,
) -> EvalResult {
    let f = float(interp, recv, "Float")?;
    let apply = |x: f64| -> f64 {
        match how {
            Rounding::Floor => x.floor(),
            Rounding::Ceil => x.ceil(),
            Rounding::Truncate => x.trunc(),
            Rounding::Round => x.round(),
        }
    };
    let Some(d) = args.pos.first() else {
        return float_to_int(interp, apply(f));
    };
    // A Float, as declared, whatever the digits (`round` too).
    let digits = int(interp, d, "digits")?;
    if !f.is_finite() || f == 0.0 || digits == 0 {
        return Ok(Value::Float(apply(f)));
    }
    if digits > 0 {
        return Ok(Value::Float(round_fraction(f, digits, how)));
    }
    // To a power of ten, as Ruby does: the integer part rounded exactly.
    let k = digits.unsigned_abs();
    let rounded = if k > 400 {
        // Every finite Float is below 10**309 in magnitude: 0, or for
        // `floor` of a negative one and `ceil` of a positive one, 10**k,
        // an infinity as a Float.
        let away = match how {
            Rounding::Floor => f < 0.0,
            Rounding::Ceil => f > 0.0,
            Rounding::Truncate | Rounding::Round => false,
        };
        if away {
            f64::INFINITY.copysign(f)
        } else {
            0.0
        }
    } else {
        let whole = match how {
            Rounding::Round => f.trunc(),
            _ => apply(f),
        };
        let n: BigInt = format!("{whole:.0}").parse().unwrap_or_default();
        let r = round_big(&n, k as usize, how);
        format!("{r}").parse::<f64>().unwrap_or(f64::NAN)
    };
    // A zero keeps the sign, as `apply` gives one.
    Ok(Value::Float(if rounded == 0.0 {
        rounded.copysign(f)
    } else {
        rounded
    }))
}

/// `f` (finite, not zero) rounded to `digits` (> 0) places after the point,
/// on its shortest decimal form, the one `inspect` shows: `1.005.round(2)`
/// is 1.01 and `0.29.floor(2)` is 0.29, as in Ruby, though neither number
/// is exactly what it shows. The result is never on the wrong side of `f`,
/// and `f` itself once `digits` reaches past its last shown digit.
fn round_fraction(f: f64, digits: i64, how: Rounding) -> f64 {
    let text = format!("{:e}", f.abs());
    let (mantissa, exp) = text.split_once('e').unwrap_or((&text, "0"));
    let exp: i64 = exp.parse().unwrap_or(0);
    let shown: Vec<u8> = mantissa.bytes().filter(|b| *b != b'.').collect();
    // The value is 0.<shown> * 10**(exp + 1): keep `n` of its digits.
    let n = exp.saturating_add(1).saturating_add(digits);
    if n >= shown.len() as i64 {
        return f;
    }
    let negative = f < 0.0;
    let first_dropped = if n < 0 { b'0' } else { shown[n as usize] };
    // The dropped digits are not all zero: the shortest form ends in one
    // that is not.
    let up = match how {
        Rounding::Floor => negative,
        Rounding::Ceil => !negative,
        Rounding::Truncate => false,
        Rounding::Round => first_dropped >= b'5',
    };
    let mut kept = String::from_utf8(shown[..n.max(0) as usize].to_vec()).unwrap_or_default();
    if kept.is_empty() {
        kept.push('0');
    }
    if up {
        super::text::increment_decimal(&mut kept);
    }
    let sign = if negative { "-" } else { "" };
    format!("{sign}{kept}e-{digits}").parse().unwrap_or(f)
}
