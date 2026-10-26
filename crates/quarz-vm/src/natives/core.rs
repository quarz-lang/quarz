//! Object, Nil, Bool, Class, Kernel, Comparable and Exception.

use crate::rc::Rc;
use std::hash::{Hash, Hasher};

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::{int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Object#==", obj_eq);
    native!(m, "Object#!=", obj_ne);
    native!(m, "Object#equal?", obj_equal);
    native!(m, "Object#hash", obj_hash);
    native!(m, "Object#to_s", obj_to_s);
    native!(m, "Object#inspect", obj_inspect);
    native!(m, "Object#nil?", obj_nil);
    native!(m, "Object#class", obj_class);
    native!(m, "Object#is_a?", |i, r, a| match a.arg(0) {
        Value::Class(cid) => Ok(Value::Bool(i.program.world.class_is_a(i.class_of(r), *cid))),
        _ => Err(i.err_type("is_a? takes a class")),
    });
    native!(m, "Object#frozen?", obj_frozen);
    native!(m, "Object#dup", obj_dup);
    native!(m, "Object#instance_exec", |i, r, a| {
        let b = super::block(i, &a)?;
        i.call_block_on(&b, Some(r.clone()), a.pos)
    });
    native!(m, "Class#name", class_name);
    native!(m, "Nil#to_a", |_, _, _| Ok(Value::array(vec![])));
    native!(m, "Nil#&", |_, _, _| Ok(Value::Bool(false)));
    native!(m, "Nil#|", |_, _, a| Ok(Value::Bool(a.arg(0).is_truthy())));
    native!(m, "Bool#&", bool_and);
    native!(m, "Bool#|", bool_or);
    native!(m, "Bool#^", bool_xor);
    native!(m, "Proc#arity", proc_arity);
    native!(m, "Exception#backtrace", exc_backtrace);
    native!(m, "Exception#full_message", exc_full_message);
    native!(m, "Exception#cause", exc_cause);
    native!(m, "Exception#__set_cause", exc_set_cause);
    native!(m, "Exception#inspect", obj_inspect);
    native!(m, "Kernel#puts", kernel_puts);
    native!(m, "Kernel#print", kernel_print);
    native!(m, "Kernel#p", kernel_p);
    native!(m, "Kernel#pp", kernel_p);
    native!(m, "Kernel#warn", kernel_warn);
    native!(m, "Kernel#exit", kernel_exit);
    native!(m, "Kernel#abort", kernel_abort);
    native!(m, "Kernel#exit!", kernel_exit_now);
    native!(m, "Kernel#at_exit", kernel_at_exit);
    native!(m, "Kernel#gets", kernel_gets);
    native!(m, "Kernel#gets?", kernel_gets_opt);
    native!(m, "Kernel#readline", kernel_gets);
    native!(m, "Kernel#readlines", |i, _, _| {
        let mut lines = Vec::new();
        loop {
            match super::core_gets(i, false)? {
                Value::Nil => break,
                line => lines.push(line),
            }
        }
        Ok(Value::array(lines))
    });
    native!(m, "Kernel#printf", |i, _, a| {
        let fmt = string(i, a.arg(0), "format string")?;
        let text = format_values(i, fmt, &a.pos[1..])?;
        i.write_out(&text);
        Ok(Value::Nil)
    });
    native!(m, "Kernel#format", kernel_format);
    native!(m, "Kernel#sprintf", kernel_format);
    native!(m, "Kernel#Integer", kernel_integer);
    native!(m, "Kernel#Float", kernel_float);
    native!(m, "Kernel#String", kernel_string);
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
        Value::Object(_) => Ok(Value::string(interp.object_to_s(recv)?)),
        _ => Ok(Value::str(&interp.to_s(recv)?)),
    }
}

/// The default `inspect` (of `Object` and `Exception`): the receiver
/// formatted, not looked up again, which would find this very method.
fn obj_inspect(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::string(interp.format_value(recv, true)?))
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
            | Value::BytesBuilder(_)
    )))
}

fn obj_dup(_: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(match recv {
        Value::ArrayBuilder(a) => Value::ArrayBuilder(Value::array_builder(a.borrow().clone())),
        Value::HashBuilder(h) => Value::HashBuilder(Value::hash_builder(h.borrow().clone())),
        Value::SetBuilder(s) => Value::SetBuilder(Value::set_builder(s.borrow().clone())),
        Value::StringBuilder(s) => {
            Value::StringBuilder(Rc::new(std::cell::RefCell::new(s.borrow().clone())))
        }
        Value::BytesBuilder(b) => {
            Value::BytesBuilder(Rc::new(std::cell::RefCell::new(b.borrow().clone())))
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

/// An exception raised (or caught) while `cause` was being rescued gets
/// it as its cause, as Ruby's `$!` does, unless it has one, is `cause`
/// itself (raised again), or `cause` comes from it (a cycle).
fn exc_set_cause(_: &Interp, recv: &Value, args: Args) -> EvalResult {
    let (Value::Object(o), Value::Object(c)) = (recv, args.arg(0)) else {
        return Ok(Value::Nil);
    };
    // Shared exceptions: the check and the setting at once, so that two
    // threads cannot each make the other's exception its cause.
    static SHARED: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _held = (Rc::is_shared(o) || Rc::is_shared(c))
        .then(|| SHARED.lock().unwrap_or_else(|e| e.into_inner()));
    let mut link = Some(Value::Object(c.clone()));
    while let Some(Value::Object(l)) = link {
        if Rc::ptr_eq(&l, o) {
            return Ok(Value::Nil);
        }
        link = l.cause();
    }
    o.set_cause(Value::Object(c.clone()), Rc::is_shared(o));
    Ok(Value::Nil)
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

/// `exit`: raises `SystemExit`, as Ruby's, so that `ensure` clauses run
/// and `rescue SystemExit` sees it; one nothing rescues ends the program
/// with its status (`task_exit`).
fn kernel_exit(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let code = match args.arg(0) {
        Value::Int(i) => *i,
        _ => 0,
    };
    Err(Flow::Raise(system_exit(interp, code, "exit")))
}

/// `abort`: the message on standard error, then `SystemExit` with status 1.
fn kernel_abort(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    interp.flush();
    let message = args.arg(0).as_str().unwrap_or("").to_string();
    eprintln!("{message}");
    Err(Flow::Raise(system_exit(interp, 1, &message)))
}

/// `exit!`: ends the program at once, running no `ensure` clause and no
/// `at_exit` block (the output written so far is flushed).
fn kernel_exit_now(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let code = match args.arg(0) {
        Value::Int(i) => *i as i32,
        _ => 1,
    };
    interp.flush();
    crate::transfer::write_worker_output();
    std::process::exit(code)
}

/// A raised `SystemExit` with `status`.
pub(crate) fn system_exit(interp: &Interp, status: i64, message: &str) -> Value {
    let class = interp.program.exc.system_exit;
    let e = interp.make_exception(class, message);
    if let (Value::Object(o), Some(i)) = (&e, interp.field_index(class, "status")) {
        o.set_field(i, Value::Int(status));
    }
    e
}

fn kernel_at_exit(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    if let Some(b) = args.block {
        interp.add_at_exit(b);
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

/// `Integer(text)` and `Integer(text, base)`, as Ruby's: `String#to_i`'s
/// reading (a prefix naming the base, base 0 by default taking it from the
/// prefix, octal for a bare leading `0`), but the whole text must be the
/// number, with blanks around it only and single `_`s between digits.
fn kernel_integer(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let s = string(interp, args.arg(0), "Integer()")?;
    let base = match args.pos.get(1) {
        Some(b) => int(interp, b, "base")?,
        None => 0,
    };
    if base != 0 && !(2..=36).contains(&base) {
        return Err(interp.err_arg(&format!("invalid radix {base}")));
    }
    let (negative, digits, base, end) = super::string::int_digits(s, base as u32, 10);
    let rest = &s.as_bytes()[end..];
    if digits.is_empty() || !rest.iter().all(|b| b.is_ascii_whitespace() || *b == 0x0b) {
        return Err(interp.err_arg(&format!("invalid value for Integer(): {s:?}")));
    }
    let digits = if negative {
        format!("-{digits}")
    } else {
        digits
    };
    match i64::from_str_radix(&digits, base) {
        Ok(v) => Ok(Value::Int(v)),
        Err(_) => {
            use num_traits::Num;
            match num_bigint::BigInt::from_str_radix(&digits, base) {
                Ok(n) => interp.int_of_big(&n),
                Err(_) => Err(interp.err_arg(&format!("invalid value for Integer(): {s:?}"))),
            }
        }
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
