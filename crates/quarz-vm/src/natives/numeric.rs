//! Int, Float, Duration and Math.

use crate::rc::Rc;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::{block, float, int};

/// The numeric tower used for arithmetic.
#[derive(Clone, Debug)]
pub(super) enum Num {
    I(i64),
    B(BigInt),
    F(f64),
}

impl Num {
    pub(super) fn of(interp: &Interp, v: &Value) -> Result<Num, Flow> {
        match v {
            Value::Int(i) => Ok(Num::I(*i)),
            Value::BigInt(b) => Ok(Num::B((**b).clone())),
            Value::Float(f) => Ok(Num::F(*f)),
            _ => Err(interp.err_type(&format!("expected a number, got {}", interp.class_name(v)))),
        }
    }

    pub(super) fn to_big(&self) -> BigInt {
        match self {
            Num::I(i) => BigInt::from(*i),
            Num::B(b) => b.clone(),
            Num::F(f) => BigInt::from(*f as i64),
        }
    }

    pub(super) fn to_f64(&self) -> f64 {
        match self {
            Num::I(i) => *i as f64,
            Num::B(b) => b.to_f64().unwrap_or(f64::INFINITY),
            Num::F(f) => *f,
        }
    }

    fn is_float(&self) -> bool {
        matches!(self, Num::F(_))
    }
}

pub(super) fn arith(interp: &Interp, recv: &Value, args: &Args, op: &str) -> EvalResult {
    let a = Num::of(interp, recv)?;
    let b = Num::of(interp, args.arg(0))?;
    if a.is_float() || b.is_float() {
        let (x, y) = (a.to_f64(), b.to_f64());
        return Ok(Value::Float(match op {
            "+" => x + y,
            "-" => x - y,
            "*" => x * y,
            "/" => x / y,
            "%" => {
                let r = x % y;
                if r != 0.0 && (r < 0.0) != (y < 0.0) {
                    r + y
                } else {
                    r
                }
            }
            "**" => x.powf(y),
            _ => unreachable!(),
        }));
    }
    if let (Num::I(x), Num::I(y)) = (&a, &b) {
        let (x, y) = (*x, *y);
        let r = match op {
            "+" => x.checked_add(y),
            "-" => x.checked_sub(y),
            "*" => x.checked_mul(y),
            "/" => {
                if y == 0 {
                    return Err(interp.raise(interp.program.exc.zero_division, "divided by 0"));
                }
                x.checked_div_euclid(y).map(|_| Integer::div_floor(&x, &y))
            }
            "%" => {
                if y == 0 {
                    return Err(interp.raise(interp.program.exc.zero_division, "divided by 0"));
                }
                // (`MIN % -1` would overflow the machine's remainder.)
                Some(if y == -1 {
                    0
                } else {
                    Integer::mod_floor(&x, &y)
                })
            }
            "**" => {
                if y < 0 {
                    return Err(
                        interp.err_arg("negative exponent of an Int (use a Float: 2.0 ** -1)")
                    );
                }
                if y <= u32::MAX as i64 {
                    x.checked_pow(y as u32)
                } else {
                    None
                }
            }
            _ => unreachable!(),
        };
        // Two Ints give an Int, or nothing.
        return match r {
            Some(r) => Ok(Value::Int(r)),
            None => Err(interp.err_overflow()),
        };
    }
    // An Integer on either side: an Integer.
    let (x, y) = (a.to_big(), b.to_big());
    Ok(integer(match op {
        "+" => x + y,
        "-" => x - y,
        "*" => x * y,
        "/" => {
            if y.is_zero() {
                return Err(interp.raise(interp.program.exc.zero_division, "divided by 0"));
            }
            x.div_floor(&y)
        }
        "%" => {
            if y.is_zero() {
                return Err(interp.raise(interp.program.exc.zero_division, "divided by 0"));
            }
            x.mod_floor(&y)
        }
        "**" => {
            if y.is_negative() {
                return Err(
                    interp.err_arg("negative exponent of an Integer (use a Float: 2.0 ** -1)")
                );
            }
            let e = y
                .to_u32()
                .ok_or_else(|| interp.err_arg("exponent too large"))?;
            num_traits::pow(x, e as usize)
        }
        _ => unreachable!(),
    }))
}

fn has_nan(a: &Value, b: &Value) -> bool {
    matches!(a, Value::Float(f) if f.is_nan()) || matches!(b, Value::Float(f) if f.is_nan())
}

fn cmp_num(interp: &Interp, recv: &Value, args: &Args) -> Result<std::cmp::Ordering, Flow> {
    use std::cmp::Ordering;
    let other = args.arg(0);
    // A BigInt on either side: compare in the numeric tower (the
    // generic `compare` would come back here through `<=>`).
    if matches!(recv, Value::BigInt(_)) || matches!(other, Value::BigInt(_)) {
        let a = Num::of(interp, recv)?;
        let b = Num::of(interp, other)?;
        return Ok(match (&a, &b) {
            (Num::F(_), _) | (_, Num::F(_)) => a
                .to_f64()
                .partial_cmp(&b.to_f64())
                .unwrap_or(Ordering::Equal),
            _ => a.to_big().cmp(&b.to_big()),
        });
    }
    // Not a number: failed, not the generic `compare` (which would send
    // `<=>` back here without end).
    if !matches!(other, Value::Int(_) | Value::Float(_)) {
        return Err(interp.err_arg(&format!(
            "comparison of {} with {} failed",
            interp.class_name(recv),
            interp.class_name(other)
        )));
    }
    interp.compare(recv, other)
}

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, ["Int#+", "Float#+", "Integer#+"], |i, r, a| arith(
        i, r, &a, "+"
    ));
    native!(m, ["Int#-", "Float#-", "Integer#-"], |i, r, a| arith(
        i, r, &a, "-"
    ));
    native!(m, ["Int#*", "Float#*", "Integer#*"], |i, r, a| arith(
        i, r, &a, "*"
    ));
    native!(m, ["Int#/", "Float#/", "Integer#/"], |i, r, a| arith(
        i, r, &a, "/"
    ));
    native!(m, ["Int#%", "Float#%", "Integer#%"], |i, r, a| arith(
        i, r, &a, "%"
    ));
    native!(m, ["Int#**", "Float#**", "Integer#**"], |i, r, a| arith(
        i, r, &a, "**"
    ));
    native!(m, ["Int#==", "Float#==", "Integer#=="], |i, r, a| {
        Ok(Value::Bool(i.values_equal(r, a.arg(0))?))
    });
    native!(m, ["Int#!=", "Float#!=", "Integer#!="], |i, r, a| {
        Ok(Value::Bool(!i.values_equal(r, a.arg(0))?))
    });
    native!(m, ["Int#<=>", "Float#<=>", "Integer#<=>"], |i, r, a| {
        // NaN sorts after every number (`<` and the others stay false).
        let nan = |v: &Value| matches!(v, Value::Float(f) if f.is_nan());
        if nan(r) || nan(a.arg(0)) {
            let x = Num::of(i, r)?.to_f64();
            let y = Num::of(i, a.arg(0))?.to_f64();
            return Ok(Value::Int(crate::interp::float_order(x, y) as i64));
        }
        Ok(Value::Int(cmp_num(i, r, &a)? as i64))
    });
    native!(m, ["Int#<", "Float#<", "Integer#<"], |i, r, a| {
        // False with a NaN, as IEEE 754 says (`<=>` orders it last).
        if has_nan(r, a.arg(0)) {
            return Ok(Value::Bool(false));
        }
        Ok(Value::Bool(cmp_num(i, r, &a)?.is_lt()))
    });
    native!(m, ["Int#<=", "Float#<=", "Integer#<="], |i, r, a| {
        // False with a NaN, as IEEE 754 says (`<=>` orders it last).
        if has_nan(r, a.arg(0)) {
            return Ok(Value::Bool(false));
        }
        Ok(Value::Bool(cmp_num(i, r, &a)?.is_le()))
    });
    native!(m, ["Int#>", "Float#>", "Integer#>"], |i, r, a| {
        // False with a NaN, as IEEE 754 says (`<=>` orders it last).
        if has_nan(r, a.arg(0)) {
            return Ok(Value::Bool(false));
        }
        Ok(Value::Bool(cmp_num(i, r, &a)?.is_gt()))
    });
    native!(m, ["Int#>=", "Float#>=", "Integer#>="], |i, r, a| {
        // False with a NaN, as IEEE 754 says (`<=>` orders it last).
        if has_nan(r, a.arg(0)) {
            return Ok(Value::Bool(false));
        }
        Ok(Value::Bool(cmp_num(i, r, &a)?.is_ge()))
    });
    native!(m, ["Int#+@", "Float#+@", "Integer#+@"], |_, r, _| Ok(
        r.clone()
    ));
    native!(
        m,
        ["Int#negative?", "Float#negative?", "Integer#negative?"],
        |i, r, _| { Ok(Value::Bool(float(i, r, "number")? < 0.0)) }
    );
    native!(
        m,
        ["Int#positive?", "Float#positive?", "Integer#positive?"],
        |i, r, _| { Ok(Value::Bool(float(i, r, "number")? > 0.0)) }
    );
    native!(
        m,
        ["Int#zero?", "Float#zero?", "Integer#zero?"],
        |i, r, _| { Ok(Value::Bool(float(i, r, "number")? == 0.0)) }
    );
    native!(m, ["Int#to_f", "Float#to_f", "Integer#to_f"], |i, r, _| {
        Ok(Value::Float(float(i, r, "number")?))
    });
    native!(m, ["Int#ms", "Float#ms", "Integer#ms"], |i, r, _| duration(
        i,
        r,
        1_000_000.0
    ));
    native!(
        m,
        [
            "Int#milliseconds",
            "Float#milliseconds",
            "Integer#milliseconds"
        ],
        |i, r, _| duration(i, r, 1_000_000.0)
    );
    native!(
        m,
        ["Int#second", "Float#second", "Integer#second"],
        |i, r, _| duration(i, r, 1_000_000_000.0)
    );
    native!(
        m,
        ["Int#seconds", "Float#seconds", "Integer#seconds"],
        |i, r, _| duration(i, r, 1_000_000_000.0)
    );
    native!(
        m,
        ["Int#minute", "Float#minute", "Integer#minute"],
        |i, r, _| duration(i, r, 60_000_000_000.0)
    );
    native!(
        m,
        ["Int#minutes", "Float#minutes", "Integer#minutes"],
        |i, r, _| duration(i, r, 60_000_000_000.0)
    );
    native!(m, ["Int#hour", "Float#hour", "Integer#hour"], |i, r, _| {
        duration(i, r, 3_600_000_000_000.0)
    });
    native!(
        m,
        ["Int#hours", "Float#hours", "Integer#hours"],
        |i, r, _| duration(i, r, 3_600_000_000_000.0)
    );
    native!(m, ["Int#day", "Float#day", "Integer#day"], |i, r, _| {
        duration(i, r, 86_400_000_000_000.0)
    });
    native!(m, ["Int#days", "Float#days", "Integer#days"], |i, r, _| {
        duration(i, r, 86_400_000_000_000.0)
    });
    native!(m, "Int#-@", int_neg);
    native!(m, "Int#to_integer", |i, r, _| {
        Ok(integer(Num::of(i, r)?.to_big()))
    });
    register_integer(m);
    native!(m, "Int#~", |i, r, _| Ok(Value::Int(!int(i, r, "Int")?)));
    native!(m, "Int#&", |i, r, a| {
        Ok(Value::Int(int(i, r, "Int")? & int(i, a.arg(0), "Int")?))
    });
    native!(m, "Int#|", |i, r, a| {
        Ok(Value::Int(int(i, r, "Int")? | int(i, a.arg(0), "Int")?))
    });
    native!(m, "Int#^", |i, r, a| {
        Ok(Value::Int(int(i, r, "Int")? ^ int(i, a.arg(0), "Int")?))
    });
    native!(m, "Int#<<", int_shl);
    native!(m, "Int#>>", |i, r, a| {
        let n = int(i, a.arg(0), "Int")?;
        if n < 0 {
            // A negative count shifts left, as in Ruby (by 64 or more,
            // `int_shl` overflows without building the number).
            let left = Args {
                pos: smallvec![Value::Int(n.checked_neg().unwrap_or(i64::MAX))],
                ..Args::default()
            };
            return int_shl(i, r, left);
        }
        Ok(Value::Int(int(i, r, "Int")? >> n.min(63)))
    });
    native!(m, "Int#abs", int_abs);
    native!(m, "Int#even?", |i, r, _| {
        Ok(Value::Bool(int(i, r, "Int")? % 2 == 0))
    });
    native!(m, "Int#odd?", |i, r, _| {
        Ok(Value::Bool(int(i, r, "Int")? % 2 != 0))
    });
    native!(m, "Int#succ", |i, r, a| {
        arith(
            i,
            r,
            &Args {
                pos: smallvec![Value::Int(1)],
                kw: a.kw,
                block: None,
            },
            "+",
        )
    });
    native!(m, "Int#pred", |i, r, a| {
        arith(
            i,
            r,
            &Args {
                pos: smallvec![Value::Int(1)],
                kw: a.kw,
                block: None,
            },
            "-",
        )
    });
    native!(m, "Int#to_i", |_, r, _| Ok(r.clone()));
    native!(m, "Int#to_s", int_to_s);
    native!(m, "Int#chr", int_chr);
    native!(m, "Int#divmod", int_divmod);
    // In the numeric tower: a result past the `Int` range (the gcd of
    // the smallest Int and 0, a large lcm) raises `OverflowError`.
    native!(m, "Int#gcd", |i, r, a| {
        let (x, y) = (int(i, r, "Int")?, int(i, a.arg(0), "Int")?);
        // In u64: only the gcd of the smallest Int and 0 or itself, 2**63,
        // does not fit back.
        let g = x.unsigned_abs().gcd(&y.unsigned_abs());
        i64::try_from(g)
            .map(Value::Int)
            .map_err(|_| i.err_overflow())
    });
    native!(m, "Int#lcm", |i, r, a| {
        let (x, y) = (int(i, r, "Int")?, int(i, a.arg(0), "Int")?);
        if x == 0 || y == 0 {
            return Ok(Value::Int(0));
        }
        let g = x.unsigned_abs().gcd(&y.unsigned_abs());
        (x.unsigned_abs() / g)
            .checked_mul(y.unsigned_abs())
            .and_then(|l| i64::try_from(l).ok())
            .map(Value::Int)
            .ok_or_else(|| i.err_overflow())
    });
    // The bits of the number past its sign, as in Ruby: `~n`'s for a
    // negative one (so -1 has none, -256 has 8).
    native!(m, "Int#bit_length", |i, r, _| match r {
        Value::BigInt(b) => {
            let n = if b.sign() == num_bigint::Sign::Minus {
                -(**b).clone() - 1
            } else {
                (**b).clone()
            };
            Ok(Value::Int(n.bits() as i64))
        }
        _ => {
            let n = int(i, r, "Int")?;
            let n = if n < 0 { !n } else { n };
            Ok(Value::Int(64 - n.leading_zeros() as i64))
        }
    });
    native!(m, "Int#times", int_times);
    native!(m, "Int#upto", int_upto);
    native!(m, "Int#downto", int_downto);
    native!(m, "Int#step", int_step);
    native!(m, "Float#-@", |i, r, _| {
        Ok(Value::Float(-float(i, r, "Float")?))
    });
    native!(m, "Float#abs", |i, r, _| {
        Ok(Value::Float(float(i, r, "Float")?.abs()))
    });
    native!(m, "Float#nan?", |i, r, _| {
        Ok(Value::Bool(float(i, r, "Float")?.is_nan()))
    });
    native!(m, "Float#infinite?", |i, r, _| {
        Ok(Value::Bool(float(i, r, "Float")?.is_infinite()))
    });
    native!(m, "Float#finite?", |i, r, _| {
        Ok(Value::Bool(float(i, r, "Float")?.is_finite()))
    });
    native!(m, "Float#round", float_round);
    native!(m, "Float#to_i", |i, r, _| {
        float_to_int(i, float(i, r, "Float")?.trunc())
    });
    native!(m, "Float#to_s", |i, r, _| {
        Ok(Value::string(crate::interp::format_float(float(
            i, r, "Float",
        )?)))
    });
    native!(m, "Duration#+", |i, r, a| {
        match dur(i, r)?.checked_add(dur(i, a.arg(0))?) {
            Some(d) => Ok(Value::Duration(d)),
            None => Err(i.err_overflow()),
        }
    });
    native!(m, "Duration#-", |i, r, a| {
        match dur(i, r)?.checked_sub(dur(i, a.arg(0))?) {
            Some(d) => Ok(Value::Duration(d)),
            None => Err(i.err_overflow()),
        }
    });
    native!(m, "Duration#*", |i, r, a| {
        // An Int factor exactly; a Float one through a Float.
        if let Value::Int(n) = a.arg(0) {
            return dur(i, r)?
                .checked_mul(*n)
                .map(Value::Duration)
                .ok_or_else(|| i.err_overflow());
        }
        let ns = dur(i, r)? as f64 * float(i, a.arg(0), "factor")?;
        // As `+` and `-`: past the range, `OverflowError` (not the nearest
        // Duration).
        if !ns.is_finite() || ns >= i64::MAX as f64 || ns < i64::MIN as f64 {
            return Err(i.err_overflow());
        }
        Ok(Value::Duration(ns as i64))
    });
    native!(m, "Duration#<=>", |i, r, a| {
        Ok(Value::Int(dur(i, r)?.cmp(&dur(i, a.arg(0))?) as i64))
    });
    native!(m, "Duration#to_f", |i, r, _| {
        Ok(Value::Float(dur(i, r)? as f64 / 1e9))
    });
    native!(m, "Duration#to_ms", |i, r, _| {
        Ok(Value::Int(dur(i, r)? / 1_000_000))
    });
    native!(m, "Duration#to_s", |i, r, _| {
        Ok(Value::string(crate::interp::format_duration(dur(i, r)?)))
    });
    native!(m, "Math.sqrt", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "sqrt")?.sqrt()))
    });
    native!(m, "Math.cbrt", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "cbrt")?.cbrt()))
    });
    native!(m, "Math.sin", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "sin")?.sin()))
    });
    native!(m, "Math.cos", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "cos")?.cos()))
    });
    native!(m, "Math.tan", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "tan")?.tan()))
    });
    native!(m, "Math.atan", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "atan")?.atan()))
    });
    native!(m, "Math.atan2", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "atan2")?.atan2(float(
            i,
            a.arg(1),
            "atan2",
        )?)))
    });
    native!(m, "Math.exp", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "exp")?.exp()))
    });
    native!(m, "Math.log", math_log);
    native!(m, "Math.log2", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "log2")?.log2()))
    });
    native!(m, "Math.log10", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "log10")?.log10()))
    });
    native!(m, "Math.pow", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "pow")?.powf(float(
            i,
            a.arg(1),
            "pow",
        )?)))
    });
    native!(m, "Math.hypot", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "hypot")?.hypot(float(
            i,
            a.arg(1),
            "hypot",
        )?)))
    });
    native!(m, "Math.floor", |i, _, a| {
        float_to_int(i, float(i, a.arg(0), "floor")?.floor())
    });
    native!(m, "Math.ceil", |i, _, a| {
        float_to_int(i, float(i, a.arg(0), "ceil")?.ceil())
    });
}

/// `Integer`'s own methods (its arithmetic and comparisons are Int's and
/// Float's, above).
fn register_integer(m: &mut super::Registry<NativeFn>) {
    fn big(interp: &Interp, v: &Value) -> Result<BigInt, Flow> {
        Ok(Num::of(interp, v)?.to_big())
    }
    native!(m, "Integer#-@", int_neg);
    native!(m, "Integer#abs", int_abs);
    native!(m, "Integer#even?", |i, r, _| {
        Ok(Value::Bool(big(i, r)?.is_even()))
    });
    native!(m, "Integer#odd?", |i, r, _| {
        Ok(Value::Bool(big(i, r)?.is_odd()))
    });
    native!(m, "Integer#succ", |i, r, _| Ok(integer(big(i, r)? + 1)));
    native!(m, "Integer#pred", |i, r, _| Ok(integer(big(i, r)? - 1)));
    native!(m, "Integer#to_i", |i, r, _| i.int_of_big(&big(i, r)?));
    native!(m, "Integer#to_integer", |_, r, _| Ok(r.clone()));
    native!(m, "Integer#to_s", int_to_s);
    native!(m, "Integer#divmod", int_divmod);
    native!(m, "Integer#pow", int_pow_mod);
    native!(m, "Integer#gcd", |i, r, a| {
        Ok(integer(big(i, r)?.gcd(&big(i, a.arg(0))?)))
    });
    native!(m, "Integer#lcm", |i, r, a| {
        Ok(integer(big(i, r)?.lcm(&big(i, a.arg(0))?)))
    });
    native!(m, "Integer#bit_length", |i, r, _| {
        let b = big(i, r)?;
        let n = if b.sign() == num_bigint::Sign::Minus {
            -b - 1
        } else {
            b
        };
        Ok(Value::Int(n.bits() as i64))
    });
    native!(m, "Integer.parse", |i, _, a| {
        use num_traits::Num as _;
        let text = super::string(i, a.arg(0), "text")?;
        let base = match a.pos.get(1) {
            Some(b) => int(i, b, "base")?,
            None => 10,
        };
        if !(2..=36).contains(&base) {
            return Err(i.err_arg(&format!("invalid radix {base}")));
        }
        let t = text.trim().replace('_', "");
        let digits = t.strip_prefix('+').unwrap_or(&t);
        BigInt::from_str_radix(digits, base as u32)
            .map(integer)
            .map_err(|_| i.err_arg(&format!("invalid value for Integer.parse: {text:?}")))
    });
}

fn dur(interp: &Interp, v: &Value) -> Result<i64, Flow> {
    match v {
        Value::Duration(d) => Ok(*d),
        _ => Err(interp.err_type("expected a Duration")),
    }
}

fn duration(interp: &Interp, v: &Value, unit_ns: f64) -> EvalResult {
    Ok(Value::Duration(
        (float(interp, v, "duration")? * unit_ns).round() as i64,
    ))
}

fn int_neg(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Int(i) => i
            .checked_neg()
            .map(Value::Int)
            .ok_or_else(|| interp.err_overflow()),
        Value::BigInt(b) => Ok(integer(-(**b).clone())),
        _ => Err(interp.err_type("expected an Int")),
    }
}

fn int_abs(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Int(i) => i
            .checked_abs()
            .map(Value::Int)
            .ok_or_else(|| interp.err_overflow()),
        Value::BigInt(b) => Ok(integer(b.abs())),
        _ => Err(interp.err_type("expected an Int")),
    }
}

fn int_shl(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let n = int(interp, args.arg(0), "shift")?;
    // Past 64 bits a shift is known without doing it: a nonzero Int
    // shifted left overflows, one shifted right is 0 or -1.
    if let Value::Int(x) = recv {
        if *x == 0 {
            return Ok(Value::Int(0));
        }
        if n >= 64 {
            return Err(interp.err_overflow());
        }
        if n <= -64 {
            return Ok(Value::Int(if *x < 0 { -1 } else { 0 }));
        }
    }
    let x = Num::of(interp, recv)?.to_big();
    let r = if n < 0 {
        x >> n.unsigned_abs() as usize
    } else {
        x << n as usize
    };
    interp.int_of_big(&r)
}

fn int_to_s(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let base = match args.pos.first() {
        Some(b) => int(interp, b, "base")?,
        None => 10,
    };
    if !(2..=36).contains(&base) {
        return Err(interp.err_arg(&format!("invalid radix {base}")));
    }
    let base = base as u32;
    let b = Num::of(interp, recv)?.to_big();
    Ok(Value::string(b.to_str_radix(base)))
}

fn int_chr(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let i = int(interp, recv, "Int")?;
    match char::from_u32(i as u32) {
        Some(c) if i >= 0 => Ok(Value::string(c.to_string())),
        _ => Err(interp.raise(
            interp.program.exc.range_error,
            &format!("{i} out of char range"),
        )),
    }
}

fn int_divmod(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let q = arith(interp, recv, &args, "/")?;
    let r = arith(interp, recv, &args, "%")?;
    Ok(Value::array(vec![q, r]))
}

pub(super) fn int_pow_mod(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let base = Num::of(interp, recv)?.to_big();
    let exp = Num::of(interp, args.arg(0))?.to_big();
    let m = Num::of(interp, args.arg(1))?.to_big();
    if m.is_zero() {
        return Err(interp.raise(interp.program.exc.zero_division, "divided by 0"));
    }
    if exp.is_negative() {
        return Err(interp.raise(
            interp.program.exc.range_error,
            "negative exponent with a modulus",
        ));
    }
    let r = base.modpow(&exp, &m);
    match recv {
        Value::BigInt(_) => Ok(integer(r)),
        _ => interp.int_of_big(&r),
    }
}

pub(super) fn enumerator(
    interp: &Interp,
    recv: &Value,
    method: &str,
    args: Vec<Value>,
) -> EvalResult {
    let _ = interp;
    Ok(Value::Enumerator(Rc::new(EnumeratorVal::new(
        recv.clone(),
        Rc::from(method),
        args,
    ))))
}

fn int_times(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let n = int(interp, recv, "Int")?;
    let Some(b) = args.block else {
        return enumerator(interp, recv, "times", vec![]);
    };
    super::each_value(interp, (0..n).map(Value::Int), &b)?;
    Ok(Value::Nil)
}

fn int_upto(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    if args.block.is_none() {
        return enumerator(interp, recv, "upto", args.pos.to_vec());
    }
    let from = int(interp, recv, "Int")?;
    let to = int(interp, args.arg(0), "limit")?;
    let b = block(interp, &args)?;
    let mut i = from;
    while i <= to {
        interp.call_block(&b, smallvec![Value::Int(i)])?;
        i += 1;
    }
    Ok(Value::Nil)
}

fn int_downto(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    if args.block.is_none() {
        return enumerator(interp, recv, "downto", args.pos.to_vec());
    }
    let from = int(interp, recv, "Int")?;
    let to = int(interp, args.arg(0), "limit")?;
    let b = block(interp, &args)?;
    let mut i = from;
    while i >= to {
        interp.call_block(&b, smallvec![Value::Int(i)])?;
        i -= 1;
    }
    Ok(Value::Nil)
}

fn int_step(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    if args.block.is_none() {
        return enumerator(interp, recv, "step", args.pos.to_vec());
    }
    let from = int(interp, recv, "Int")?;
    let limit = int(interp, args.arg(0), "limit")?;
    let step = int(interp, args.arg(1), "step")?;
    if step == 0 {
        return Err(interp.err_arg("step cannot be 0"));
    }
    let b = block(interp, &args)?;
    let mut i = from;
    while (step > 0 && i <= limit) || (step < 0 && i >= limit) {
        interp.call_block(&b, smallvec![Value::Int(i)])?;
        i += step;
    }
    Ok(Value::Nil)
}

pub(super) fn float_to_int(interp: &Interp, f: f64) -> EvalResult {
    if f.is_nan() || f.is_infinite() {
        return Err(interp.raise(
            interp.program.exc.range_error,
            "cannot convert NaN or Infinity to Int",
        ));
    }
    if f.abs() < 9.2e18 {
        Ok(Value::Int(f as i64))
    } else {
        Err(interp.err_overflow())
    }
}

fn float_round(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let f = float(interp, recv, "Float")?;
    match args.pos.first() {
        None => float_to_int(interp, f.round()),
        // As `floor`, `ceil` and `truncate` with digits.
        Some(_) => {
            super::math::float_round_digits(interp, recv, args, super::math::Rounding::Round)
        }
    }
}

fn math_log(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let x = float(interp, args.arg(0), "log")?;
    match args.pos.get(1) {
        Some(b) => Ok(Value::Float(x.ln() / float(interp, b, "base")?.ln())),
        None => Ok(Value::Float(x.ln())),
    }
}
