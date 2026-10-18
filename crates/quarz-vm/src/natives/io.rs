//! IO, File and Process.

use std::collections::HashMap;
use std::rc::Rc;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::{block, string};

pub fn register(m: &mut HashMap<&'static str, NativeFn>) {
    m.insert("Process.argv", |i, _, _| {
        Ok(Value::array(i.argv.iter().map(|s| Value::str(s)).collect()))
    });
    m.insert("Process.env", |_, _, _| {
        let map: indexmap::IndexMap<Value, Value> = std::env::vars()
            .map(|(k, v)| (Value::string(k), Value::string(v)))
            .collect();
        Ok(Value::Hash(Rc::new(map)))
    });
    m.insert("Process.pid", |_, _, _| {
        Ok(Value::Int(std::process::id() as i64))
    });
    m.insert("Process.stdin", |_, _, _| Ok(io(IoKind::Stdin)));
    m.insert("Process.stdout", |_, _, _| Ok(io(IoKind::Stdout)));
    m.insert("Process.stderr", |_, _, _| Ok(io(IoKind::Stderr)));
    m.insert("Process.clock", |_, _, _| {
        thread_local! { static START: std::time::Instant = std::time::Instant::now(); }
        Ok(Value::Float(START.with(|s| s.elapsed().as_secs_f64())))
    });
    m.insert("IO#puts", io_puts);
    m.insert("IO#print", io_print);
    m.insert("IO#write", |i, r, a| {
        let s = string(i, a.arg(0), "text")?;
        io_write(i, r, &s)?;
        Ok(Value::Int(s.len() as i64))
    });
    m.insert("IO#gets", |i, _, _| super::core_gets(i, true));
    m.insert("IO#gets?", |i, _, _| super::core_gets(i, false));
    m.insert("IO#read", |i, _, _| {
        i.flush();
        let mut s = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut s)
            .map_err(|e| i.raise(i.exc.io_error, &e.to_string()))?;
        Ok(Value::string(s))
    });
    m.insert("IO#each_line", |i, _, a| {
        let b = block(i, &a)?;
        loop {
            match super::core_gets(i, false)? {
                Value::Nil => return Ok(Value::Nil),
                line => {
                    i.call_block(&b, vec![line])?;
                }
            }
        }
    });
    m.insert("IO#flush", |i, _, _| {
        i.flush();
        Ok(Value::Nil)
    });
    m.insert("IO#close", |_, _, _| Ok(Value::Nil));
    m.insert("IO#eof?", |_, _, _| Ok(Value::Bool(false)));
    m.insert("File.read", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        std::fs::read_to_string(&*p)
            .map(Value::string)
            .map_err(|e| i.raise(i.exc.io_error, &format!("{p}: {e}")))
    });
    m.insert("File.write", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let c = string(i, a.arg(1), "content")?;
        std::fs::write(&*p, c.as_bytes())
            .map(|_| Value::Int(c.len() as i64))
            .map_err(|e| i.raise(i.exc.io_error, &format!("{p}: {e}")))
    });
    m.insert("File.exist?", |i, _, a| {
        Ok(Value::Bool(
            std::path::Path::new(&*string(i, a.arg(0), "path")?).exists(),
        ))
    });
    m.insert("File.readlines", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let s = std::fs::read_to_string(&*p)
            .map_err(|e| i.raise(i.exc.io_error, &format!("{p}: {e}")))?;
        Ok(Value::array(
            s.split_inclusive('\n').map(Value::str).collect(),
        ))
    });
    m.insert("File.basename", |i, _, a| {
        Ok(Value::str(
            std::path::Path::new(&*string(i, a.arg(0), "path")?)
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or(""),
        ))
    });
    m.insert("File.dirname", |i, _, a| {
        Ok(Value::str(
            std::path::Path::new(&*string(i, a.arg(0), "path")?)
                .parent()
                .and_then(|s| s.to_str())
                .filter(|s| !s.is_empty())
                .unwrap_or("."),
        ))
    });
    m.insert("File.extname", |i, _, a| {
        Ok(Value::string(
            std::path::Path::new(&*string(i, a.arg(0), "path")?)
                .extension()
                .and_then(|s| s.to_str())
                .map(|e| format!(".{e}"))
                .unwrap_or_default(),
        ))
    });
    m.insert("File.join", |i, _, a| {
        let mut parts = Vec::new();
        for p in &a.pos {
            parts.push(string(i, p, "part")?.to_string());
        }
        Ok(Value::string(parts.join("/")))
    });
}

fn io(kind: IoKind) -> Value {
    Value::Io(Rc::new(IoVal { kind }))
}

fn io_write(interp: &Interp, recv: &Value, s: &str) -> Result<(), Flow> {
    match recv {
        Value::Io(io) => match io.kind {
            IoKind::Stdout => interp.write_out(s),
            IoKind::Stderr => {
                interp.flush();
                eprint!("{s}");
            }
            IoKind::Stdin => {
                return Err(interp.raise(interp.exc.io_error, "not opened for writing"))
            }
        },
        _ => return Err(interp.err_type("expected an IO")),
    }
    Ok(())
}

fn io_puts(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    super::core::puts_to(interp, &args.pos, &mut out)?;
    io_write(interp, recv, &out)?;
    Ok(Value::Nil)
}

fn io_print(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let mut out = String::new();
    for a in &args.pos {
        out.push_str(&interp.to_s(a)?);
    }
    io_write(interp, recv, &out)?;
    Ok(Value::Nil)
}
