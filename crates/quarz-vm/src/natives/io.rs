//! IO, File, Dir and Process.
//!
//! Whole-file operations and child processes run on a helper thread
//! through `Interp::block_on`, so only the calling task waits. Reads and
//! writes through an open file handle are buffered and synchronous.
//! Sockets (see `net.rs`) are non-blocking and wait on the reactor.

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{BufRead, Read, Seek, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::net;
use super::{block, string};

pub fn register(m: &mut HashMap<&'static str, NativeFn>) {
    m.insert("Process.argv", |i, _, _| {
        Ok(Value::array(i.argv.iter().map(|s| Value::str(s)).collect()))
    });
    m.insert("Process.env", |_, _, _| {
        let map: ValueMap = std::env::vars()
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
    m.insert("Process.run", |i, _, a| {
        if a.pos.is_empty() {
            return Err(i.err_arg("Process.run needs a command"));
        }
        let mut parts = Vec::with_capacity(a.pos.len());
        for p in &a.pos {
            parts.push(string(i, p, "command")?.to_string());
        }
        let mut command = std::process::Command::new(&parts[0]);
        command.args(&parts[1..]);
        run_command(i, command, &parts[0])
    });
    m.insert("Process.sh", |i, _, a| {
        let script = string(i, a.arg(0), "script")?;
        let mut command = std::process::Command::new("sh");
        command.arg("-c").arg(&*script);
        run_command(i, command, "sh")
    });
    m.insert("Process::Output#success?", |i, r, _| {
        let status = i.send(r, "status", smallvec![], None)?;
        Ok(Value::Bool(matches!(status, Value::Int(0))))
    });

    // IO
    m.insert("IO#puts", io_puts);
    m.insert("IO#print", io_print);
    m.insert("IO#printf", |i, r, a| {
        let fmt = string(i, a.arg(0), "format string")?;
        let text = super::core::format_values(i, &fmt, &a.pos[1..])?;
        io_write(i, r, &text)?;
        Ok(Value::Nil)
    });
    m.insert("IO#write", |i, r, a| {
        let mut total = 0;
        for v in &a.pos {
            let bytes = net::payload(i, v)?;
            io_write_bytes(i, r, &bytes)?;
            total += bytes.len();
        }
        Ok(Value::Int(total as i64))
    });
    m.insert("IO#<<", |i, r, a| {
        let bytes = net::payload(i, a.arg(0))?;
        io_write_bytes(i, r, &bytes)?;
        Ok(r.clone())
    });
    m.insert("IO#gets", |i, r, _| io_gets(i, r, true));
    m.insert("IO#gets?", |i, r, _| io_gets(i, r, false));
    m.insert("IO#readline", |i, r, _| io_gets(i, r, true));
    m.insert("IO#readlines", |i, r, _| {
        let mut lines = Vec::new();
        loop {
            match io_gets(i, r, false)? {
                Value::Nil => break,
                line => lines.push(line),
            }
        }
        Ok(Value::array(lines))
    });
    m.insert("IO#read", |i, r, a| {
        let text = io_read(i, r, a.pos.first())?;
        match text {
            Some(text) => Ok(Value::string(text)),
            None if a.pos.is_empty() => Ok(Value::str("")),
            None => Err(i.raise(i.exc.eof_error, "end of file reached")),
        }
    });
    m.insert("IO#read?", |i, r, a| {
        Ok(match io_read(i, r, a.pos.first())? {
            Some(text) => Value::string(text),
            None => Value::Nil,
        })
    });
    m.insert("IO#getc", |i, r, _| {
        let mut buf = [0u8; 4];
        let first = match read_byte(i, r)? {
            Some(b) => b,
            None => return Ok(Value::Nil),
        };
        buf[0] = first;
        let width = match first {
            0x00..=0x7f => 1,
            0xc0..=0xdf => 2,
            0xe0..=0xef => 3,
            _ => 4,
        };
        for slot in buf.iter_mut().take(width).skip(1) {
            match read_byte(i, r)? {
                Some(b) => *slot = b,
                None => break,
            }
        }
        Ok(Value::string(
            String::from_utf8_lossy(&buf[..width]).into_owned(),
        ))
    });
    m.insert("IO#each_line", |i, r, a| {
        let b = block(i, &a)?;
        loop {
            match io_gets(i, r, false)? {
                Value::Nil => return Ok(Value::Nil),
                line => {
                    i.call_block(&b, smallvec![line])?;
                }
            }
        }
    });
    m.insert("IO#flush", |i, r, _| {
        match &io_of(i, r)?.kind {
            IoKind::File(f) => {
                if let Some(w) = f.borrow_mut().writer.as_mut() {
                    w.flush().map_err(|e| os_error(i, e, "flush"))?;
                }
            }
            IoKind::Stdout | IoKind::Stderr | IoKind::Stdin => i.flush(),
            _ => {}
        }
        Ok(Value::Nil)
    });
    m.insert("IO#close", |i, r, _| {
        match &io_of(i, r)?.kind {
            IoKind::File(f) => {
                let mut f = f.borrow_mut();
                if let Some(mut w) = f.writer.take() {
                    w.flush().map_err(|e| os_error(i, e, "close"))?;
                }
                f.reader = None;
                f.closed = true;
            }
            IoKind::Socket(_) | IoKind::Listener(_) | IoKind::Udp(_) => net::close(i, r)?,
            _ => {}
        }
        Ok(Value::Nil)
    });
    m.insert("IO#closed?", |i, r, _| {
        Ok(Value::Bool(net::is_closed(io_of(i, r)?)))
    });
    m.insert("IO#eof?", |i, r, _| {
        Ok(Value::Bool(match &io_of(i, r)?.kind {
            IoKind::File(f) => {
                let mut f = f.borrow_mut();
                match f.reader.as_mut() {
                    Some(reader) => reader
                        .fill_buf()
                        .map(|buf| buf.is_empty())
                        .map_err(|e| os_error(i, e, "eof?"))?,
                    None => true,
                }
            }
            IoKind::Stdin => {
                i.flush();
                let stdin = std::io::stdin();
                let mut lock = stdin.lock();
                lock.fill_buf().map(|b| b.is_empty()).unwrap_or(true)
            }
            IoKind::Socket(st) => net::socket_eof(i, st)?,
            _ => false,
        }))
    });
    m.insert("IO#rewind", |i, r, _| {
        match &io_of(i, r)?.kind {
            IoKind::File(f) => {
                let mut f = f.borrow_mut();
                if let Some(reader) = f.reader.as_mut() {
                    reader
                        .seek(std::io::SeekFrom::Start(0))
                        .map_err(|e| os_error(i, e, "rewind"))?;
                }
                if let Some(writer) = f.writer.as_mut() {
                    writer
                        .seek(std::io::SeekFrom::Start(0))
                        .map_err(|e| os_error(i, e, "rewind"))?;
                }
            }
            IoKind::Socket(_) | IoKind::Listener(_) | IoKind::Udp(_) => {
                return Err(i.raise(i.exc.io_error, "cannot rewind a socket"))
            }
            _ => {}
        }
        Ok(Value::Nil)
    });
    m.insert("IO#tty?", |i, r, _| {
        use std::io::IsTerminal;
        Ok(Value::Bool(match &io_of(i, r)?.kind {
            IoKind::Stdin => std::io::stdin().is_terminal(),
            IoKind::Stdout => std::io::stdout().is_terminal(),
            IoKind::Stderr => std::io::stderr().is_terminal(),
            _ => false,
        }))
    });
    m.insert("IO#path", |i, r, _| {
        let io = io_of(i, r)?;
        Ok(match &io.kind {
            IoKind::File(f) => Value::str(&f.borrow().path),
            _ => match net::socket_path(io) {
                Some(p) => Value::string(p),
                None => Value::Nil,
            },
        })
    });
    m.insert("IO#to_s", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("IO#inspect", |i, r, _| Ok(Value::string(i.inspect(r)?)));

    // File
    m.insert("File.open", file_open);
    m.insert("File.read", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let path = p.to_string();
        i.block_on(move || std::fs::read_to_string(&path))?
            .map(Value::string)
            .map_err(|e| os_error(i, e, &p))
    });
    m.insert("File.read_bytes", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let path = p.to_string();
        i.block_on(move || std::fs::read(&path))?
            .map(Value::bytes)
            .map_err(|e| os_error(i, e, &p))
    });
    m.insert("File.write", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let content = content_bytes(i, a.arg(1))?;
        let len = content.len();
        let path = p.to_string();
        i.block_on(move || std::fs::write(&path, &content))?
            .map(|_| Value::Int(len as i64))
            .map_err(|e| os_error(i, e, &p))
    });
    m.insert("File.append", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let content = content_bytes(i, a.arg(1))?;
        let len = content.len();
        let path = p.to_string();
        i.block_on(move || {
            let mut f = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(&path)?;
            f.write_all(&content)
        })?
        .map(|_| Value::Int(len as i64))
        .map_err(|e| os_error(i, e, &p))
    });
    m.insert("File.exist?", |i, _, a| {
        Ok(Value::Bool(
            Path::new(&*string(i, a.arg(0), "path")?).exists(),
        ))
    });
    m.insert("File.file?", |i, _, a| {
        Ok(Value::Bool(
            Path::new(&*string(i, a.arg(0), "path")?).is_file(),
        ))
    });
    m.insert("File.directory?", |i, _, a| {
        Ok(Value::Bool(
            Path::new(&*string(i, a.arg(0), "path")?).is_dir(),
        ))
    });
    m.insert("File.symlink?", |i, _, a| {
        Ok(Value::Bool(
            std::fs::symlink_metadata(&*string(i, a.arg(0), "path")?)
                .map(|m| m.file_type().is_symlink())
                .unwrap_or(false),
        ))
    });
    m.insert("File.readable?", |i, _, a| {
        Ok(Value::Bool(
            std::fs::File::open(&*string(i, a.arg(0), "path")?).is_ok(),
        ))
    });
    m.insert("File.writable?", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        Ok(Value::Bool(
            std::fs::OpenOptions::new().append(true).open(&*p).is_ok()
                || std::fs::metadata(&*p).is_ok_and(|m| m.is_dir() && !m.permissions().readonly()),
        ))
    });
    m.insert("File.executable?", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        Ok(Value::Bool(std::fs::metadata(&*p).is_ok_and(|m| {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                m.is_file() && m.permissions().mode() & 0o111 != 0
            }
            #[cfg(not(unix))]
            {
                m.is_file()
            }
        })))
    });
    m.insert("File.size", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        std::fs::metadata(&*p)
            .map(|m| Value::Int(m.len() as i64))
            .map_err(|e| os_error(i, e, &p))
    });
    m.insert("File.mtime", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let modified = std::fs::metadata(&*p)
            .and_then(|m| m.modified())
            .map_err(|e| os_error(i, e, &p))?;
        let ns = match modified.duration_since(std::time::UNIX_EPOCH) {
            Ok(d) => d.as_nanos() as i64,
            Err(e) => -(e.duration().as_nanos() as i64),
        };
        Ok(super::time::at_local(ns))
    });
    m.insert("File.delete", |i, _, a| {
        for p in &a.pos {
            let p = string(i, p, "path")?;
            std::fs::remove_file(&*p).map_err(|e| os_error(i, e, &p))?;
        }
        Ok(Value::Int(a.pos.len() as i64))
    });
    m.insert("File.rename", |i, _, a| {
        let from = string(i, a.arg(0), "from")?;
        let to = string(i, a.arg(1), "to")?;
        std::fs::rename(&*from, &*to).map_err(|e| os_error(i, e, &from))?;
        Ok(Value::Int(0))
    });
    m.insert("File.copy", |i, _, a| {
        let from = string(i, a.arg(0), "from")?;
        let to = string(i, a.arg(1), "to")?;
        let (f, t) = (from.to_string(), to.to_string());
        i.block_on(move || std::fs::copy(&f, &t))?
            .map(|n| Value::Int(n as i64))
            .map_err(|e| os_error(i, e, &from))
    });
    m.insert("File.readlines", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let chomp = a.arg(1).is_truthy() || a.kw(i, "chomp").is_some_and(|v| v.is_truthy());
        let path = p.to_string();
        let s = i
            .block_on(move || std::fs::read_to_string(&path))?
            .map_err(|e| os_error(i, e, &p))?;
        Ok(Value::array(
            s.split_inclusive('\n')
                .map(|line| if chomp { chomp_line(line) } else { line })
                .map(Value::str)
                .collect(),
        ))
    });
    m.insert("File.each_line", file_each_line);
    m.insert("File.foreach", file_each_line);
    m.insert("File.basename", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let name = file_name(&p);
        let name = match a.pos.get(1) {
            Some(suffix) => {
                let suffix = string(i, suffix, "suffix")?;
                if &*suffix == ".*" {
                    match name.rfind('.') {
                        Some(0) | None => name.to_string(),
                        Some(at) => name[..at].to_string(),
                    }
                } else {
                    name.strip_suffix(&*suffix).unwrap_or(name).to_string()
                }
            }
            None => name.to_string(),
        };
        Ok(Value::string(name))
    });
    m.insert("File.dirname", |i, _, a| {
        Ok(Value::str(dir_name(&string(i, a.arg(0), "path")?)))
    });
    m.insert("File.extname", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let name = file_name(&p);
        Ok(Value::string(match name.rfind('.') {
            Some(0) | None => String::new(),
            Some(at) if at == name.len() - 1 => String::new(),
            Some(at) => name[at..].to_string(),
        }))
    });
    m.insert("File.split", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        Ok(Value::array(vec![
            Value::str(dir_name(&p)),
            Value::str(file_name(&p)),
        ]))
    });
    m.insert("File.join", |i, _, a| {
        let mut out = String::new();
        for p in &a.pos {
            let part = string(i, p, "part")?;
            if out.is_empty() {
                out.push_str(&part);
            } else {
                let trimmed = part.trim_start_matches('/');
                if !out.ends_with('/') {
                    out.push('/');
                }
                out.push_str(trimmed);
            }
        }
        Ok(Value::string(out))
    });
    m.insert("File.expand_path", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let base: Option<PathBuf> = match a.pos.get(1) {
            Some(Value::Nil) | None => None,
            Some(b) => Some(PathBuf::from(&*string(i, b, "directory")?)),
        };
        Ok(Value::string(expand_path(&p, base)))
    });
    m.insert("File.absolute_path", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        Ok(Value::string(expand_path(&p, None)))
    });

    // Dir
    m.insert("Dir.pwd", |i, _, _| current_dir(i));
    m.insert("Dir.getwd", |i, _, _| current_dir(i));
    m.insert("Dir.home", |i, _, _| {
        std::env::var("HOME")
            .map(Value::string)
            .map_err(|_| i.raise(i.exc.argument_error, "couldn't find HOME environment"))
    });
    m.insert("Dir.tmpdir", |_, _, _| {
        Ok(Value::string(
            std::env::temp_dir().to_string_lossy().into_owned(),
        ))
    });
    m.insert("Dir.chdir", |i, _, a| {
        let target = match a.pos.first() {
            Some(p) => string(i, p, "path")?.to_string(),
            None => std::env::var("HOME").unwrap_or_else(|_| "/".to_string()),
        };
        let Some(b) = &a.block else {
            std::env::set_current_dir(&target).map_err(|e| os_error(i, e, &target))?;
            return Ok(Value::Int(0));
        };
        let previous = std::env::current_dir().map_err(|e| os_error(i, e, "."))?;
        std::env::set_current_dir(&target).map_err(|e| os_error(i, e, &target))?;
        let result = i.call_block(b, smallvec![Value::string(target)]);
        let _ = std::env::set_current_dir(previous);
        result
    });
    m.insert("Dir.exist?", |i, _, a| {
        Ok(Value::Bool(
            Path::new(&*string(i, a.arg(0), "path")?).is_dir(),
        ))
    });
    m.insert("Dir.empty?", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        Ok(Value::Bool(
            std::fs::read_dir(&*p)
                .map(|mut d| d.next().is_none())
                .unwrap_or(false),
        ))
    });
    m.insert("Dir.mkdir", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        std::fs::create_dir(&*p).map_err(|e| os_error(i, e, &p))?;
        Ok(Value::Int(0))
    });
    m.insert("Dir.mkdir_p", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        std::fs::create_dir_all(&*p).map_err(|e| os_error(i, e, &p))?;
        Ok(Value::Int(0))
    });
    m.insert("Dir.rmdir", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        std::fs::remove_dir(&*p).map_err(|e| os_error(i, e, &p))?;
        Ok(Value::Int(0))
    });
    m.insert("Dir.rm_rf", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        match std::fs::remove_dir_all(&*p) {
            Ok(()) => Ok(Value::Int(0)),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(Value::Int(0)),
            Err(e) => Err(os_error(i, e, &p)),
        }
    });
    m.insert("Dir.children", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        Ok(Value::array(
            dir_children(i, &p)?
                .into_iter()
                .map(Value::string)
                .collect(),
        ))
    });
    m.insert("Dir.entries", |i, _, a| {
        let p = string(i, a.arg(0), "path")?;
        let mut names = vec![".".to_string(), "..".to_string()];
        names.extend(dir_children(i, &p)?);
        Ok(Value::array(names.into_iter().map(Value::string).collect()))
    });
    m.insert("Dir.each_child", |i, _, a| {
        let b = block(i, &a)?;
        let p = string(i, a.arg(0), "path")?;
        for name in dir_children(i, &p)? {
            i.call_block(&b, smallvec![Value::string(name)])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Dir.glob", |i, _, a| {
        let mut patterns = Vec::new();
        match a.arg(0) {
            Value::Array(items) => {
                for p in items.iter() {
                    patterns.push(string(i, p, "pattern")?.to_string());
                }
            }
            other => patterns.push(string(i, other, "pattern")?.to_string()),
        }
        let base = match a.pos.get(1) {
            Some(Value::Nil) | None => a
                .kw(i, "base")
                .map(|b| string(i, b, "base"))
                .transpose()?
                .map(|s| s.to_string()),
            Some(b) => Some(string(i, b, "base")?.to_string()),
        };
        let mut out = Vec::new();
        for pattern in patterns {
            for expanded in expand_braces(&pattern) {
                let full = match &base {
                    Some(b) if !expanded.starts_with('/') => {
                        format!("{}/{}", b.trim_end_matches('/'), expanded)
                    }
                    _ => expanded.clone(),
                };
                let paths = glob::glob(&full)
                    .map_err(|e| i.err_arg(&format!("invalid glob pattern: {e}")))?;
                for path in paths.flatten() {
                    let mut shown = path.to_string_lossy().into_owned();
                    if let Some(b) = &base {
                        if !expanded.starts_with('/') {
                            let prefix = format!("{}/", b.trim_end_matches('/'));
                            if let Some(rest) = shown.strip_prefix(&prefix) {
                                shown = rest.to_string();
                            }
                        }
                    }
                    out.push(shown);
                }
            }
        }
        out.sort();
        out.dedup();
        Ok(Value::array(out.into_iter().map(Value::string).collect()))
    });
}

// ----- helpers ---------------------------------------------------------------------

pub(super) fn io(kind: IoKind) -> Value {
    Value::Io(Rc::new(IoVal { kind }))
}

pub(super) fn io_of<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<IoVal>, Flow> {
    match v {
        Value::Io(io) => Ok(io),
        _ => Err(interp.err_type("expected an IO")),
    }
}

/// An operating-system failure as a `SystemCallError`.
pub(super) fn os_error(interp: &Interp, e: std::io::Error, what: &str) -> Flow {
    interp.raise(interp.exc.system_call_error, &format!("{what}: {e}"))
}

fn content_bytes(interp: &Interp, v: &Value) -> Result<Vec<u8>, Flow> {
    Ok(match v {
        Value::Bytes(b) => b.to_vec(),
        v => string(interp, v, "content")?.as_bytes().to_vec(),
    })
}

fn chomp_line(line: &str) -> &str {
    line.strip_suffix("\r\n")
        .or_else(|| line.strip_suffix('\n'))
        .unwrap_or(line)
}

fn file_name(path: &str) -> &str {
    let trimmed = path.trim_end_matches('/');
    if trimmed.is_empty() {
        return if path.is_empty() { "" } else { "/" };
    }
    trimmed.rsplit('/').next().unwrap_or(trimmed)
}

fn dir_name(path: &str) -> &str {
    let trimmed = path.trim_end_matches('/');
    if trimmed.is_empty() {
        return if path.is_empty() { "." } else { "/" };
    }
    match trimmed.rfind('/') {
        None => ".",
        Some(0) => "/",
        Some(at) => trimmed[..at].trim_end_matches('/'),
    }
}

/// `File.expand_path`: absolute, with `~`, `.` and `..` resolved
/// lexically (the path need not exist).
fn expand_path(path: &str, base: Option<PathBuf>) -> String {
    let home = std::env::var("HOME").unwrap_or_else(|_| "/".to_string());
    let expanded: PathBuf = if path == "~" {
        PathBuf::from(&home)
    } else if let Some(rest) = path.strip_prefix("~/") {
        Path::new(&home).join(rest)
    } else {
        PathBuf::from(path)
    };
    let absolute = if expanded.is_absolute() {
        expanded
    } else {
        let base = match base {
            Some(b) => PathBuf::from(expand_path(&b.to_string_lossy(), None)),
            None => std::env::current_dir().unwrap_or_else(|_| PathBuf::from("/")),
        };
        base.join(expanded)
    };
    let mut parts: Vec<String> = Vec::new();
    for component in absolute.components() {
        use std::path::Component;
        match component {
            Component::RootDir | Component::Prefix(_) => {}
            Component::CurDir => {}
            Component::ParentDir => {
                parts.pop();
            }
            Component::Normal(s) => parts.push(s.to_string_lossy().into_owned()),
        }
    }
    format!("/{}", parts.join("/"))
}

fn current_dir(interp: &Interp) -> EvalResult {
    std::env::current_dir()
        .map(|p| Value::string(p.to_string_lossy().into_owned()))
        .map_err(|e| os_error(interp, e, "."))
}

fn dir_children(interp: &Interp, path: &str) -> Result<Vec<String>, Flow> {
    let entries = std::fs::read_dir(path).map_err(|e| os_error(interp, e, path))?;
    let mut names = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|e| os_error(interp, e, path))?;
        names.push(entry.file_name().to_string_lossy().into_owned());
    }
    names.sort();
    Ok(names)
}

/// `{a,b}` alternatives in a glob pattern, expanded recursively.
fn expand_braces(pattern: &str) -> Vec<String> {
    let Some(open) = pattern.find('{') else {
        return vec![pattern.to_string()];
    };
    let mut depth = 0;
    let mut close = None;
    for (k, c) in pattern[open..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(open + k);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(close) = close else {
        return vec![pattern.to_string()];
    };
    let (head, rest) = (&pattern[..open], &pattern[close + 1..]);
    let inner = &pattern[open + 1..close];
    // Split on top-level commas.
    let mut alternatives = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (k, c) in inner.char_indices() {
        match c {
            '{' => depth += 1,
            '}' => depth -= 1,
            ',' if depth == 0 => {
                alternatives.push(&inner[start..k]);
                start = k + 1;
            }
            _ => {}
        }
    }
    alternatives.push(&inner[start..]);
    let mut out = Vec::new();
    for alt in alternatives {
        for tail in expand_braces(rest) {
            out.push(format!("{head}{alt}{tail}"));
        }
    }
    out
}

fn run_command(interp: &Interp, mut command: std::process::Command, name: &str) -> EvalResult {
    interp.flush();
    let output = interp
        .block_on(move || command.output())?
        .map_err(|e| os_error(interp, e, name))?;
    let status = output.status.code().unwrap_or(-1);
    let class = interp
        .world
        .class(interp.rt.process)
        .members
        .get("Output")
        .copied()
        .ok_or_else(|| interp.err_type("Process::Output is not defined"))?;
    // A `data` with no initializer of its own: fill the fields directly.
    let value = interp.construct(class, None, smallvec![], Vec::new(), None)?;
    if let Value::Object(obj) = &value {
        let mut fields = obj.fields.borrow_mut();
        fields[0] = Value::Int(status as i64);
        fields[1] = Value::string(String::from_utf8_lossy(&output.stdout).into_owned());
        fields[2] = Value::string(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(value)
}

fn file_open(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let path = string(interp, args.arg(0), "path")?;
    let mode = match args.pos.get(1) {
        Some(m) => string(interp, m, "mode")?.to_string(),
        None => "r".to_string(),
    };
    let mut options = std::fs::OpenOptions::new();
    let (read, write) = match mode.trim_end_matches('b') {
        "r" => {
            options.read(true);
            (true, false)
        }
        "r+" => {
            options.read(true).write(true);
            (true, true)
        }
        "w" => {
            options.write(true).create(true).truncate(true);
            (false, true)
        }
        "w+" => {
            options.read(true).write(true).create(true).truncate(true);
            (true, true)
        }
        "a" => {
            options.append(true).create(true);
            (false, true)
        }
        "a+" => {
            options.read(true).append(true).create(true);
            (true, true)
        }
        other => return Err(interp.err_arg(&format!("invalid access mode {other}"))),
    };
    let file = options
        .open(&*path)
        .map_err(|e| os_error(interp, e, &path))?;
    let handle = FileHandle {
        path: path.to_string(),
        reader: if read {
            Some(std::io::BufReader::new(
                file.try_clone().map_err(|e| os_error(interp, e, &path))?,
            ))
        } else {
            None
        },
        writer: if write {
            Some(std::io::BufWriter::new(file))
        } else {
            None
        },
        closed: false,
    };
    let value = io(IoKind::File(RefCell::new(handle)));
    let Some(b) = &args.block else {
        return Ok(value);
    };
    let result = interp.call_block(b, smallvec![value.clone()]);
    if let IoKind::File(f) = &io_of(interp, &value)?.kind {
        let mut f = f.borrow_mut();
        if let Some(mut w) = f.writer.take() {
            let _ = w.flush();
        }
        f.reader = None;
        f.closed = true;
    }
    result
}

fn file_each_line(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let path = string(interp, args.arg(0), "path")?;
    let p = path.to_string();
    let text = interp
        .block_on(move || std::fs::read_to_string(&p))?
        .map_err(|e| os_error(interp, e, &path))?;
    for line in text.split_inclusive('\n') {
        interp.call_block(&b, smallvec![Value::str(line)])?;
    }
    Ok(Value::Nil)
}

fn io_write(interp: &Interp, recv: &Value, s: &str) -> Result<(), Flow> {
    io_write_bytes(interp, recv, s.as_bytes())
}

fn io_write_bytes(interp: &Interp, recv: &Value, bytes: &[u8]) -> Result<(), Flow> {
    match &io_of(interp, recv)?.kind {
        IoKind::Stdout => interp.write_out_bytes(bytes),
        IoKind::Stderr => {
            interp.flush();
            let _ = std::io::stderr().write_all(bytes);
        }
        IoKind::Stdin => return Err(interp.raise(interp.exc.io_error, "not opened for writing")),
        IoKind::File(f) => {
            let mut f = f.borrow_mut();
            if f.closed {
                return Err(interp.raise(interp.exc.io_error, "closed stream"));
            }
            match f.writer.as_mut() {
                Some(w) => w
                    .write_all(bytes)
                    .map_err(|e| os_error(interp, e, "write"))?,
                None => return Err(interp.raise(interp.exc.io_error, "not opened for writing")),
            }
        }
        IoKind::Socket(st) => net::socket_write(interp, st, bytes)?,
        IoKind::Listener(_) | IoKind::Udp(_) => {
            return Err(interp.raise(interp.exc.io_error, "not opened for writing"))
        }
    }
    Ok(())
}

/// One line (with its newline), `nil` at the end of the stream, or an
/// `EOFError` when `raise_on_eof`.
fn io_gets(interp: &Interp, recv: &Value, raise_on_eof: bool) -> EvalResult {
    let line = match &io_of(interp, recv)?.kind {
        IoKind::Stdin => return super::core_gets(interp, raise_on_eof),
        IoKind::File(f) => {
            let mut f = f.borrow_mut();
            if f.closed {
                return Err(interp.raise(interp.exc.io_error, "closed stream"));
            }
            let Some(reader) = f.reader.as_mut() else {
                return Err(interp.raise(interp.exc.io_error, "not opened for reading"));
            };
            let mut buf = Vec::new();
            let n = reader
                .read_until(b'\n', &mut buf)
                .map_err(|e| os_error(interp, e, "read"))?;
            if n == 0 {
                None
            } else {
                Some(String::from_utf8_lossy(&buf).into_owned())
            }
        }
        IoKind::Socket(st) => net::socket_gets(interp, st)?,
        _ => return Err(interp.raise(interp.exc.io_error, "not opened for reading")),
    };
    match line {
        Some(line) => Ok(Value::string(line)),
        None if raise_on_eof => Err(interp.raise(interp.exc.eof_error, "end of file reached")),
        None => Ok(Value::Nil),
    }
}

/// The rest of the stream (or up to `limit` bytes); `None` at the end.
fn io_read(interp: &Interp, recv: &Value, limit: Option<&Value>) -> Result<Option<String>, Flow> {
    let limit = match limit {
        Some(v) => Some(super::int(interp, v, "length")?.max(0) as usize),
        None => None,
    };
    let buf = read_raw(interp, recv, limit)?;
    if buf.is_empty() && limit.is_some_and(|n| n > 0) {
        return Ok(None);
    }
    Ok(Some(String::from_utf8_lossy(&buf).into_owned()))
}

/// Up to `limit` bytes (all when `None`) from a stream of any kind.
fn read_raw(interp: &Interp, recv: &Value, limit: Option<usize>) -> Result<Vec<u8>, Flow> {
    let mut buf = Vec::new();
    match &io_of(interp, recv)?.kind {
        IoKind::Stdin => {
            interp.flush();
            let stdin = std::io::stdin();
            let mut lock = stdin.lock();
            read_up_to(&mut lock, &mut buf, limit).map_err(|e| os_error(interp, e, "read"))?;
        }
        IoKind::File(f) => {
            let mut f = f.borrow_mut();
            if f.closed {
                return Err(interp.raise(interp.exc.io_error, "closed stream"));
            }
            let Some(reader) = f.reader.as_mut() else {
                return Err(interp.raise(interp.exc.io_error, "not opened for reading"));
            };
            read_up_to(reader, &mut buf, limit).map_err(|e| os_error(interp, e, "read"))?;
        }
        IoKind::Socket(st) => buf = net::socket_read(interp, st, limit)?,
        _ => return Err(interp.raise(interp.exc.io_error, "not opened for reading")),
    }
    Ok(buf)
}

fn read_up_to(
    reader: &mut impl Read,
    buf: &mut Vec<u8>,
    limit: Option<usize>,
) -> std::io::Result<()> {
    match limit {
        Some(n) => {
            buf.resize(n, 0);
            let mut filled = 0;
            while filled < n {
                let got = reader.read(&mut buf[filled..])?;
                if got == 0 {
                    break;
                }
                filled += got;
            }
            buf.truncate(filled);
        }
        None => {
            reader.read_to_end(buf)?;
        }
    }
    Ok(())
}

/// `readpartial` on a file or standard input: up to `max` bytes, `None`
/// at the end.
pub(super) fn read_limited(
    interp: &Interp,
    recv: &Value,
    max: usize,
) -> Result<Option<String>, Flow> {
    let buf = read_raw(interp, recv, Some(max))?;
    if buf.is_empty() && max > 0 {
        return Ok(None);
    }
    Ok(Some(String::from_utf8_lossy(&buf).into_owned()))
}

fn read_byte(interp: &Interp, recv: &Value) -> Result<Option<u8>, Flow> {
    let buf = read_raw(interp, recv, Some(1))?;
    Ok(buf.first().copied())
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
