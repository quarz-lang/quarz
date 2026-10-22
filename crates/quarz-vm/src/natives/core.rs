//! Object, Nil, Bool, Class, Kernel, Comparable and Exception.

use crate::rc::Rc;
use std::hash::{Hash, Hasher};

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::{int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    m.insert("Object#==", obj_eq);
    m.insert("Object#!=", obj_ne);
    m.insert("Object#equal?", obj_equal);
    m.insert("Object#hash", obj_hash);
    m.insert("Object#to_s", obj_to_s);
    m.insert("Object#inspect", obj_inspect);
    m.insert("Object#nil?", obj_nil);
    m.insert("Object#class", obj_class);
    m.insert("Object#frozen?", obj_frozen);
    m.insert("Object#dup", obj_dup);
    m.insert("Object#instance_exec", |i, r, a| {
        let b = super::block(i, &a)?;
        i.call_block_on(&b, Some(r.clone()), a.pos)
    });
    m.insert("Class#name", class_name);
    m.insert("Nil#to_a", |_, _, _| Ok(Value::array(vec![])));
    m.insert("Nil#&", |_, _, _| Ok(Value::Bool(false)));
    m.insert("Nil#|", |_, _, a| Ok(Value::Bool(a.arg(0).is_truthy())));
    m.insert("Bool#&", bool_and);
    m.insert("Bool#|", bool_or);
    m.insert("Bool#^", bool_xor);
    m.insert("Comparable#clamp", clamp);
    m.insert("Proc#arity", proc_arity);
    m.insert("Exception#backtrace", exc_backtrace);
    m.insert("Exception#full_message", exc_full_message);
    m.insert("Exception#cause", exc_cause);
    m.insert("Exception#inspect", obj_inspect);
    m.insert("Kernel#puts", kernel_puts);
    m.insert("Kernel#print", kernel_print);
    m.insert("Kernel#p", kernel_p);
    m.insert("Kernel#pp", kernel_p);
    m.insert("Kernel#warn", kernel_warn);
    m.insert("Kernel#exit", kernel_exit);
    m.insert("Kernel#abort", kernel_abort);
    m.insert("Kernel#at_exit", kernel_at_exit);
    m.insert("Kernel#gets", kernel_gets);
    m.insert("Kernel#gets?", kernel_gets_opt);
    m.insert("Kernel#readline", kernel_gets);
    m.insert("Kernel#readlines", |i, _, _| {
        let mut lines = Vec::new();
        loop {
            match super::core_gets(i, false)? {
                Value::Nil => break,
                line => lines.push(line),
            }
        }
        Ok(Value::array(lines))
    });
    m.insert("Kernel#printf", |i, _, a| {
        let fmt = string(i, a.arg(0), "format string")?;
        let text = format_values(i, fmt, &a.pos[1..])?;
        i.write_out(&text);
        Ok(Value::Nil)
    });
    m.insert("Kernel#format", kernel_format);
    m.insert("Kernel#sprintf", kernel_format);
    m.insert("Kernel#Integer", kernel_integer);
    m.insert("Kernel#Float", kernel_float);
    m.insert("Kernel#String", kernel_string);
}

fn obj_eq(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(interp.values_equal(recv, args.arg(0))?))
}

fn obj_ne(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(!interp.values_equal(recv, args.arg(0))?))
}

fn obj_equal(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(recv.identical(args.arg(0))))
}

fn obj_hash(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    recv.hash(&mut h);
    Ok(Value::Int((h.finish() >> 1) as i64))
}

fn obj_to_s(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Object(o) if !interp.program.world.is_exception_class(o.class) => {
            Ok(Value::string(interp.inspect(recv)?))
        }
        _ => Ok(Value::str(&interp.to_s(recv)?)),
    }
}

fn obj_inspect(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::string(interp.inspect(recv)?))
}

fn obj_nil(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::Bool(recv.is_nil()))
}

fn obj_class(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::Class(interp.class_of(recv)))
}

fn obj_frozen(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::Bool(!matches!(
        recv,
        Value::ArrayBuilder(_)
            | Value::HashBuilder(_)
            | Value::SetBuilder(_)
            | Value::StringBuilder(_)
    )))
}

fn obj_dup(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(match recv {
        Value::ArrayBuilder(a) => {
            Value::ArrayBuilder(Rc::new(std::cell::RefCell::new(a.borrow().clone())))
        }
        Value::HashBuilder(h) => {
            Value::HashBuilder(Rc::new(std::cell::RefCell::new(h.borrow().clone())))
        }
        Value::SetBuilder(s) => {
            Value::SetBuilder(Rc::new(std::cell::RefCell::new(s.borrow().clone())))
        }
        Value::StringBuilder(s) => {
            Value::StringBuilder(Rc::new(std::cell::RefCell::new(s.borrow().clone())))
        }
        Value::Object(o) => Value::Object(Object::new(o.class, o.fields())),
        other => other.clone(),
    })
}

fn class_name(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Class(c) => Ok(Value::str(&interp.program.world.class(*c).name)),
        _ => Ok(Value::str(&interp.class_name(recv))),
    }
}

fn bool_and(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(recv.is_truthy() && args.arg(0).is_truthy()))
}

fn bool_or(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(recv.is_truthy() || args.arg(0).is_truthy()))
}

fn bool_xor(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    Ok(Value::Bool(recv.is_truthy() != args.arg(0).is_truthy()))
}

fn clamp(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    use std::cmp::Ordering;
    let min = args.arg(0);
    let max = args.arg(1);
    if interp.compare(recv, min)? == Ordering::Less {
        return Ok(min.clone());
    }
    if interp.compare(recv, max)? == Ordering::Greater {
        return Ok(max.clone());
    }
    Ok(recv.clone())
}

fn proc_arity(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let Value::Proc(c) = recv else {
        return Err(interp.err_type("expected a Proc"));
    };
    Ok(Value::Int(match &c.body {
        ClosureBody::Func(fid) => interp.func(*fid).arity as i64,
        ClosureBody::MethodName(..) => 1,
        ClosureBody::BoundMethod { .. } | ClosureBody::Native(_) => -1,
    }))
}

fn exc_backtrace(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Object(o) => {
            let items: Vec<Value> = o
                .backtrace()
                .map(|b| b.iter().map(|s| Value::str(s)).collect())
                .unwrap_or_default();
            Ok(Value::array(items))
        }
        _ => Ok(Value::array(vec![])),
    }
}

fn exc_full_message(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let mut s = format!(
        "{}: {}",
        interp.class_name(recv),
        interp.exception_message(recv)
    );
    if let Value::Object(o) = recv {
        if let Some(bt) = o.backtrace() {
            for frame in bt.iter() {
                s.push_str(&format!("\n    from {frame}"));
            }
        }
    }
    Ok(Value::string(s))
}

fn exc_cause(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    match recv {
        Value::Object(o) => Ok(o.cause().unwrap_or(Value::Nil)),
        _ => Ok(Value::Nil),
    }
}

// ----- Kernel ---------------------------------------------------------------------

pub fn puts_to(interp: &Interp, args: &[Value], out: &mut String) -> Result<(), Flow> {
    if args.is_empty() {
        out.push('\n');
        return Ok(());
    }
    for a in args {
        match a {
            Value::Array(items) => {
                if items.is_empty() {
                    out.push('\n');
                }
                for x in items.iter() {
                    puts_to(interp, std::slice::from_ref(&x), out)?;
                }
            }
            _ => {
                let s = interp.to_s(a)?;
                out.push_str(&s);
                if !s.ends_with('\n') {
                    out.push('\n');
                }
            }
        }
    }
    Ok(())
}

fn kernel_puts(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    puts_to(interp, &args.pos, &mut out)?;
    interp.write_out(&out);
    Ok(Value::Nil)
}

fn kernel_print(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    for a in &args.pos {
        out.push_str(&interp.to_s(a)?);
    }
    interp.write_out(&out);
    Ok(Value::Nil)
}

fn kernel_p(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    for a in &args.pos {
        out.push_str(&interp.inspect(a)?);
        out.push('\n');
    }
    interp.write_out(&out);
    Ok(match args.pos.len() {
        0 => Value::Nil,
        1 => args.pos[0].clone(),
        _ => Value::array(args.pos.into_vec()),
    })
}

fn kernel_warn(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    puts_to(interp, &args.pos, &mut out)?;
    interp.flush();
    eprint!("{out}");
    Ok(Value::Nil)
}

fn kernel_exit(_: &Interp, _: &Value, args: Args) -> EvalResult {
    let code = match args.arg(0) {
        Value::Int(i) => *i as i32,
        _ => 0,
    };
    Err(Flow::Exit(code))
}

fn kernel_abort(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    interp.flush();
    if let Some(s) = args.arg(0).as_str() {
        eprintln!("{s}");
    }
    Err(Flow::Exit(1))
}

fn kernel_at_exit(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    if let Some(b) = args.block {
        interp.at_exit.borrow_mut().push(b);
    }
    Ok(Value::Nil)
}

fn read_line(interp: &Interp) -> Result<Option<String>, Flow> {
    super::io::stdin_line(interp)
}

fn kernel_gets(interp: &Interp, _: &Value, _: Args) -> EvalResult {
    match read_line(interp)? {
        Some(l) => Ok(Value::string(l)),
        None => Err(interp.raise(interp.program.exc.eof_error, "end of file reached")),
    }
}

fn kernel_gets_opt(interp: &Interp, _: &Value, _: Args) -> EvalResult {
    match read_line(interp)? {
        Some(l) => Ok(Value::string(l)),
        None => Ok(Value::Nil),
    }
}

fn kernel_format(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let fmt = string(interp, args.arg(0), "format string")?;
    let s = format_values(interp, fmt, &args.pos[1..])?;
    Ok(Value::string(s))
}

/// A subset of `sprintf`: `%d %i %s %f %e %g %x %o %b %c %%` with flags
/// `-`, `0`, `+`, space, width and precision.
pub fn format_values(interp: &Interp, fmt: &str, args: &[Value]) -> Result<String, Flow> {
    let mut out = String::new();
    let mut chars = fmt.chars().peekable();
    let mut next_arg = 0;
    while let Some(c) = chars.next() {
        if c != '%' {
            out.push(c);
            continue;
        }
        let mut left = false;
        let mut zero = false;
        let mut plus = false;
        let mut space = false;
        let mut width: Option<usize> = None;
        let mut precision: Option<usize> = None;
        loop {
            match chars.peek() {
                Some('-') => {
                    left = true;
                    chars.next();
                }
                Some('0') if width.is_none() => {
                    zero = true;
                    chars.next();
                }
                Some('+') => {
                    plus = true;
                    chars.next();
                }
                Some(' ') => {
                    space = true;
                    chars.next();
                }
                _ => break,
            }
        }
        while let Some(d) = chars.peek().and_then(|c| c.to_digit(10)) {
            width = Some(width.unwrap_or(0) * 10 + d as usize);
            chars.next();
        }
        if chars.peek() == Some(&'.') {
            chars.next();
            let mut p = 0;
            while let Some(d) = chars.peek().and_then(|c| c.to_digit(10)) {
                p = p * 10 + d as usize;
                chars.next();
            }
            precision = Some(p);
        }
        let Some(conv) = chars.next() else {
            return Err(interp.err_arg("incomplete format specifier"));
        };
        if conv == '%' {
            out.push('%');
            continue;
        }
        let arg = args.get(next_arg).cloned().unwrap_or(Value::Nil);
        next_arg += 1;
        let body = match conv {
            'd' | 'i' => {
                let v = match &arg {
                    Value::Float(f) => Value::Int(f.floor() as i64),
                    other => other.clone(),
                };
                let s = interp.to_s(&v)?.to_string();
                sign(s, plus, space)
            }
            's' => {
                let s = interp.to_s(&arg)?.to_string();
                match precision {
                    Some(p) => s.chars().take(p).collect(),
                    None => s,
                }
            }
            'f' => {
                let f = super::float(interp, &arg, "format argument")?;
                sign(format!("{:.*}", precision.unwrap_or(6), f), plus, space)
            }
            'e' => {
                let f = super::float(interp, &arg, "format argument")?;
                sign(format!("{:.*e}", precision.unwrap_or(6), f), plus, space)
            }
            'g' => {
                let f = super::float(interp, &arg, "format argument")?;
                sign(crate::interp::format_float(f), plus, space)
            }
            'x' => format!("{:x}", int(interp, &arg, "format argument")?),
            'X' => format!("{:X}", int(interp, &arg, "format argument")?),
            'o' => format!("{:o}", int(interp, &arg, "format argument")?),
            'b' => format!("{:b}", int(interp, &arg, "format argument")?),
            'c' => match &arg {
                Value::Int(i) => char::from_u32(*i as u32)
                    .map(|c| c.to_string())
                    .unwrap_or_default(),
                other => interp.to_s(other)?.chars().take(1).collect(),
            },
            other => return Err(interp.err_arg(&format!("unknown format specifier %{other}"))),
        };
        let padded = match width {
            Some(w) if body.chars().count() < w => {
                let pad = w - body.chars().count();
                if left {
                    format!("{body}{}", " ".repeat(pad))
                } else if zero && matches!(conv, 'd' | 'i' | 'f' | 'e' | 'x' | 'X' | 'o' | 'b') {
                    let (sign_part, digits) = match body.strip_prefix(['-', '+', ' ']) {
                        Some(rest) => (body[..1].to_string(), rest.to_string()),
                        None => (String::new(), body.clone()),
                    };
                    format!("{sign_part}{}{digits}", "0".repeat(pad))
                } else {
                    format!("{}{body}", " ".repeat(pad))
                }
            }
            _ => body,
        };
        out.push_str(&padded);
    }
    Ok(out)
}

fn sign(s: String, plus: bool, space: bool) -> String {
    if s.starts_with('-') {
        s
    } else if plus {
        format!("+{s}")
    } else if space {
        format!(" {s}")
    } else {
        s
    }
}

fn kernel_integer(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let s = string(interp, args.arg(0), "Integer()")?;
    let t = s.trim().replace('_', "");
    if let Some(base) = args.pos.get(1) {
        let base = int(interp, base, "base")?;
        if !(2..=36).contains(&base) {
            return Err(interp.err_arg(&format!("invalid radix {base}")));
        }
        let (neg, digits) = match t.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, t.strip_prefix('+').unwrap_or(&t)),
        };
        let parsed = num_bigint::BigInt::parse_bytes(digits.as_bytes(), base as u32)
            .filter(|_| !digits.is_empty());
        return match parsed {
            Some(n) => Ok(int_from_big(if neg { -n } else { n })),
            None => Err(interp.err_arg(&format!("invalid value for Integer(): {s:?}"))),
        };
    }
    let parsed = if let Some(h) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        i64::from_str_radix(h, 16).ok()
    } else if let Some(b) = t.strip_prefix("0b") {
        i64::from_str_radix(b, 2).ok()
    } else {
        t.parse::<i64>().ok()
    };
    match parsed {
        Some(i) => Ok(Value::Int(i)),
        None => Err(interp.err_arg(&format!("invalid value for Integer(): {s:?}"))),
    }
}

fn kernel_float(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let s = string(interp, args.arg(0), "Float()")?;
    match s.trim().replace('_', "").parse::<f64>() {
        Ok(f) => Ok(Value::Float(f)),
        Err(_) => Err(interp.err_arg(&format!("invalid value for Float(): {s:?}"))),
    }
}

fn kernel_string(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let v = args.arg(0);
    if v.is_str() {
        return Ok(v.clone());
    }
    Ok(Value::str(&interp.to_s(v)?))
}
