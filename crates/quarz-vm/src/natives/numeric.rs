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
                Some(Integer::mod_floor(&x, &y))
            }
            "**" => {
                if y < 0 {
                    return Ok(Value::Float((x as f64).powf(y as f64)));
                }
                if y <= u32::MAX as i64 {
                    x.checked_pow(y as u32)
                } else {
                    None
                }
            }
            _ => unreachable!(),
        };
        if let Some(r) = r {
            return Ok(Value::Int(r));
        }
    }
    // Big integers.
    let (x, y) = (a.to_big(), b.to_big());
    Ok(int_from_big(match op {
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
            let e = y
                .to_u32()
                .ok_or_else(|| interp.err_arg("exponent too large"))?;
            num_traits::pow(x, e as usize)
        }
        _ => unreachable!(),
    }))
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
    interp.compare(recv, other)
}

pub fn register(m: &mut super::Registry<NativeFn>) {
    for class in ["Int", "Float"] {
        let key =
            |name: &str| -> &'static str { Box::leak(format!("{class}#{name}").into_boxed_str()) };
        m.insert(key("+"), |i, r, a| arith(i, r, &a, "+"));
        m.insert(key("-"), |i, r, a| arith(i, r, &a, "-"));
        m.insert(key("*"), |i, r, a| arith(i, r, &a, "*"));
        m.insert(key("/"), |i, r, a| arith(i, r, &a, "/"));
        m.insert(key("%"), |i, r, a| arith(i, r, &a, "%"));
        m.insert(key("**"), |i, r, a| arith(i, r, &a, "**"));
        m.insert(key("=="), |i, r, a| {
            Ok(Value::Bool(i.values_equal(r, a.arg(0))?))
        });
        m.insert(key("!="), |i, r, a| {
            Ok(Value::Bool(!i.values_equal(r, a.arg(0))?))
        });
        m.insert(key("<=>"), |i, r, a| {
            Ok(Value::Int(cmp_num(i, r, &a)? as i64))
        });
        m.insert(key("<"), |i, r, a| {
            Ok(Value::Bool(cmp_num(i, r, &a)?.is_lt()))
        });
        m.insert(key("<="), |i, r, a| {
            Ok(Value::Bool(cmp_num(i, r, &a)?.is_le()))
        });
        m.insert(key(">"), |i, r, a| {
            Ok(Value::Bool(cmp_num(i, r, &a)?.is_gt()))
        });
        m.insert(key(">="), |i, r, a| {
            Ok(Value::Bool(cmp_num(i, r, &a)?.is_ge()))
        });
        m.insert(key("+@"), |_, r, _| Ok(r.clone()));
        m.insert(key("negative?"), |i, r, _| {
            Ok(Value::Bool(float(i, r, "number")? < 0.0))
        });
        m.insert(key("positive?"), |i, r, _| {
            Ok(Value::Bool(float(i, r, "number")? > 0.0))
        });
        m.insert(key("zero?"), |i, r, _| {
            Ok(Value::Bool(float(i, r, "number")? == 0.0))
        });
        m.insert(key("to_f"), |i, r, _| {
            Ok(Value::Float(float(i, r, "number")?))
        });
        m.insert(key("ms"), |i, r, _| duration(i, r, 1_000_000.0));
        m.insert(key("milliseconds"), |i, r, _| duration(i, r, 1_000_000.0));
        m.insert(key("second"), |i, r, _| duration(i, r, 1_000_000_000.0));
        m.insert(key("seconds"), |i, r, _| duration(i, r, 1_000_000_000.0));
        m.insert(key("minute"), |i, r, _| duration(i, r, 60_000_000_000.0));
        m.insert(key("minutes"), |i, r, _| duration(i, r, 60_000_000_000.0));
        m.insert(key("hour"), |i, r, _| duration(i, r, 3_600_000_000_000.0));
        m.insert(key("hours"), |i, r, _| duration(i, r, 3_600_000_000_000.0));
        m.insert(key("day"), |i, r, _| duration(i, r, 86_400_000_000_000.0));
        m.insert(key("days"), |i, r, _| duration(i, r, 86_400_000_000_000.0));
    }
    m.insert("Int#-@", int_neg);
    m.insert("Int#~", |i, r, _| Ok(Value::Int(!int(i, r, "Int")?)));
    m.insert("Int#&", |i, r, a| {
        Ok(Value::Int(int(i, r, "Int")? & int(i, a.arg(0), "Int")?))
    });
    m.insert("Int#|", |i, r, a| {
        Ok(Value::Int(int(i, r, "Int")? | int(i, a.arg(0), "Int")?))
    });
    m.insert("Int#^", |i, r, a| {
        Ok(Value::Int(int(i, r, "Int")? ^ int(i, a.arg(0), "Int")?))
    });
    m.insert("Int#<<", int_shl);
    m.insert("Int#>>", |i, r, a| {
        Ok(Value::Int(
            int(i, r, "Int")? >> int(i, a.arg(0), "Int")?.clamp(0, 63),
        ))
    });
    m.insert("Int#abs", int_abs);
    m.insert("Int#even?", |i, r, _| {
        Ok(Value::Bool(int(i, r, "Int")? % 2 == 0))
    });
    m.insert("Int#odd?", |i, r, _| {
        Ok(Value::Bool(int(i, r, "Int")? % 2 != 0))
    });
    m.insert("Int#succ", |i, r, a| {
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
    m.insert("Int#pred", |i, r, a| {
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
    m.insert("Int#to_i", |_, r, _| Ok(r.clone()));
    m.insert("Int#to_s", int_to_s);
    m.insert("Int#chr", int_chr);
    m.insert("Int#floor", |_, r, _| Ok(r.clone()));
    m.insert("Int#ceil", |_, r, _| Ok(r.clone()));
    m.insert("Int#round", |_, r, _| Ok(r.clone()));
    m.insert("Int#truncate", |_, r, _| Ok(r.clone()));
    m.insert("Int#divmod", int_divmod);
    m.insert("Int#pow", int_pow_mod);
    m.insert("Int#gcd", |i, r, a| {
        Ok(Value::Int(int(i, r, "Int")?.gcd(&int(i, a.arg(0), "Int")?)))
    });
    m.insert("Int#lcm", |i, r, a| {
        Ok(Value::Int(int(i, r, "Int")?.lcm(&int(i, a.arg(0), "Int")?)))
    });
    // The bits of the number past its sign, as in Ruby: `~n`'s for a
    // negative one (so -1 has none, -256 has 8).
    m.insert("Int#bit_length", |i, r, _| match r {
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
    m.insert("Int#digits", int_digits);
    m.insert("Int#times", int_times);
    m.insert("Int#upto", int_upto);
    m.insert("Int#downto", int_downto);
    m.insert("Int#step", int_step);
    m.insert("Float#-@", |i, r, _| {
        Ok(Value::Float(-float(i, r, "Float")?))
    });
    m.insert("Float#abs", |i, r, _| {
        Ok(Value::Float(float(i, r, "Float")?.abs()))
    });
    m.insert("Float#nan?", |i, r, _| {
        Ok(Value::Bool(float(i, r, "Float")?.is_nan()))
    });
    m.insert("Float#infinite?", |i, r, _| {
        Ok(Value::Bool(float(i, r, "Float")?.is_infinite()))
    });
    m.insert("Float#finite?", |i, r, _| {
        Ok(Value::Bool(float(i, r, "Float")?.is_finite()))
    });
    m.insert("Float#floor", |i, r, _| {
        float_to_int(i, float(i, r, "Float")?.floor())
    });
    m.insert("Float#ceil", |i, r, _| {
        float_to_int(i, float(i, r, "Float")?.ceil())
    });
    m.insert("Float#round", float_round);
    m.insert("Float#truncate", |i, r, _| {
        float_to_int(i, float(i, r, "Float")?.trunc())
    });
    m.insert("Float#to_i", |i, r, _| {
        float_to_int(i, float(i, r, "Float")?.trunc())
    });
    m.insert("Float#to_s", |i, r, _| {
        Ok(Value::string(crate::interp::format_float(float(
            i, r, "Float",
        )?)))
    });
    m.insert("Duration#+", |i, r, a| {
        Ok(Value::Duration(dur(i, r)? + dur(i, a.arg(0))?))
    });
    m.insert("Duration#-", |i, r, a| {
        Ok(Value::Duration(dur(i, r)? - dur(i, a.arg(0))?))
    });
    m.insert("Duration#*", |i, r, a| {
        Ok(Value::Duration(
            (dur(i, r)? as f64 * float(i, a.arg(0), "factor")?) as i64,
        ))
    });
    m.insert("Duration#<=>", |i, r, a| {
        Ok(Value::Int(dur(i, r)?.cmp(&dur(i, a.arg(0))?) as i64))
    });
    m.insert("Duration#to_f", |i, r, _| {
        Ok(Value::Float(dur(i, r)? as f64 / 1e9))
    });
    m.insert("Duration#to_ms", |i, r, _| {
        Ok(Value::Int(dur(i, r)? / 1_000_000))
    });
    m.insert("Duration#to_s", |i, r, _| {
        Ok(Value::string(crate::interp::format_duration(dur(i, r)?)))
    });
    m.insert("Math.sqrt", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "sqrt")?.sqrt()))
    });
    m.insert("Math.cbrt", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "cbrt")?.cbrt()))
    });
    m.insert("Math.sin", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "sin")?.sin()))
    });
    m.insert("Math.cos", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "cos")?.cos()))
    });
    m.insert("Math.tan", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "tan")?.tan()))
    });
    m.insert("Math.atan", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "atan")?.atan()))
    });
    m.insert("Math.atan2", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "atan2")?.atan2(float(
            i,
            a.arg(1),
            "atan2",
        )?)))
    });
    m.insert("Math.exp", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "exp")?.exp()))
    });
    m.insert("Math.log", math_log);
    m.insert("Math.log2", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "log2")?.log2()))
    });
    m.insert("Math.log10", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "log10")?.log10()))
    });
    m.insert("Math.pow", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "pow")?.powf(float(
            i,
            a.arg(1),
            "pow",
        )?)))
    });
    m.insert("Math.hypot", |i, _, a| {
        Ok(Value::Float(float(i, a.arg(0), "hypot")?.hypot(float(
            i,
            a.arg(1),
            "hypot",
        )?)))
    });
    m.insert("Math.floor", |i, _, a| {
        float_to_int(i, float(i, a.arg(0), "floor")?.floor())
    });
    m.insert("Math.ceil", |i, _, a| {
        float_to_int(i, float(i, a.arg(0), "ceil")?.ceil())
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
        Value::Int(i) => Ok(match i.checked_neg() {
            Some(n) => Value::Int(n),
            None => int_from_big(-BigInt::from(*i)),
        }),
        Value::BigInt(b) => Ok(int_from_big(-(**b).clone())),
        _ => Err(interp.err_type("expected an Int")),
    }
}

fn int_abs(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Int(i) => Ok(match i.checked_abs() {
            Some(n) => Value::Int(n),
            None => int_from_big(BigInt::from(*i).abs()),
        }),
        Value::BigInt(b) => Ok(int_from_big(b.abs())),
        _ => Err(interp.err_type("expected an Int")),
    }
}

fn int_shl(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let x = Num::of(interp, recv)?.to_big();
    let n = int(interp, args.arg(0), "shift")?;
    if n < 0 {
        return Ok(int_from_big(x >> (-n) as usize));
    }
    Ok(int_from_big(x << n as usize))
}

fn int_to_s(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let base = match args.pos.first() {
        Some(b) => int(interp, b, "base")? as u32,
        None => 10,
    };
    if !(2..=36).contains(&base) {
        return Err(interp.err_arg("invalid radix"));
    }
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
    Ok(int_from_big(base.modpow(&exp, &m)))
}

fn int_digits(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let mut n = int(interp, recv, "Int")?;
    if n < 0 {
        return Err(interp.err_arg("digits of a negative number"));
    }
    let mut out = Vec::new();
    if n == 0 {
        out.push(Value::Int(0));
    }
    while n > 0 {
        out.push(Value::Int(n % 10));
        n /= 10;
    }
    Ok(Value::array(out))
}

pub(super) fn enumerator(
    interp: &Interp,
    recv: &Value,
    method: &str,
    args: Vec<Value>,
) -> EvalResult {
    let _ = interp;
    Ok(Value::Enumerator(Rc::new(EnumeratorVal {
        recv: recv.clone(),
        method: Rc::from(method),
        args,
        buffer: std::cell::RefCell::new(None),
        position: std::cell::Cell::new(0),
    })))
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
        Ok(int_from_big(BigInt::from(f as i128)))
    }
}

fn float_round(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let f = float(interp, recv, "Float")?;
    match args.pos.first() {
        None => float_to_int(interp, f.round()),
        Some(d) => {
            let digits = int(interp, d, "digits")?;
            let factor = 10f64.powi(digits as i32);
            Ok(Value::Float((f * factor).round() / factor))
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
