//! `Signal` (std/prelude.qz): a signal handler writes the signal's number
//! to one end of a socket pair, whose other end is a UNIXSocket that a
//! task reads to run the traps (the handler itself does nothing else,
//! which is all a signal handler may safely do).

use std::os::fd::IntoRawFd;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Mutex;

use crate::interp::{Interp, NativeFn};
use crate::value::*;

use super::io::os_error;
use super::net::make_socket;
use super::{int, string};

/// The end the handler writes to (-1 before the first trap).
static WRITE_END: AtomicI32 = AtomicI32::new(-1);
/// The other end, until `Signal.reader` takes it.
static READ_END: Mutex<Option<UnixStream>> = Mutex::new(None);

extern "C" fn on_signal(sig: libc::c_int) {
    let fd = WRITE_END.load(Ordering::Relaxed);
    if fd >= 0 {
        let b = sig as u8;
        // The interrupted code's errno is kept (a full buffer makes the
        // write fail, and drops the signal: traps are not counted).
        unsafe {
            let errno = libc::__errno_location();
            let saved = *errno;
            libc::write(fd, (&b as *const u8).cast(), 1);
            *errno = saved;
        }
    }
}

const NAMES: &[(&str, libc::c_int)] = &[
    ("HUP", libc::SIGHUP),
    ("INT", libc::SIGINT),
    ("QUIT", libc::SIGQUIT),
    ("USR1", libc::SIGUSR1),
    ("USR2", libc::SIGUSR2),
    ("PIPE", libc::SIGPIPE),
    ("TERM", libc::SIGTERM),
];

fn signo(interp: &Interp, v: &Value) -> Result<libc::c_int, crate::interp::Flow> {
    let n = int(interp, v, "signal")?;
    if NAMES.iter().any(|(_, s)| *s as i64 == n) {
        Ok(n as libc::c_int)
    } else {
        Err(interp.err_arg(&format!("unsupported signal {n}")))
    }
}

fn set_action(sig: libc::c_int, handler: libc::sighandler_t) {
    unsafe {
        let mut sa: libc::sigaction = std::mem::zeroed();
        sa.sa_sigaction = handler;
        sa.sa_flags = libc::SA_RESTART;
        libc::sigemptyset(&mut sa.sa_mask);
        libc::sigaction(sig, &sa, std::ptr::null_mut());
    }
}

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Signal.number", |i, _, a| {
        let name = string(i, a.arg(0), "name")?;
        let name = name.strip_prefix("SIG").unwrap_or(name);
        Ok(match NAMES.iter().find(|(n, _)| *n == name) {
            Some((_, s)) => Value::Int(*s as i64),
            None => Value::Nil,
        })
    });
    native!(m, "Signal.names", |_, _, _| {
        Ok(Value::array(
            NAMES.iter().map(|(n, _)| Value::str(n)).collect(),
        ))
    });
    // Route the signal to the socket pair (made on the first call).
    native!(m, "Signal.watch", |i, _, a| {
        let sig = signo(i, a.arg(0))?;
        // Made once, under the lock: two first traps on two workers.
        static MADE: Mutex<bool> = Mutex::new(false);
        let mut made = MADE.lock().unwrap();
        if !*made {
            let (r, w) = UnixStream::pair().map_err(|e| os_error(i, e, "socketpair"))?;
            w.set_nonblocking(true)
                .map_err(|e| os_error(i, e, "socketpair"))?;
            r.set_nonblocking(true)
                .map_err(|e| os_error(i, e, "socketpair"))?;
            *READ_END.lock().unwrap() = Some(r);
            WRITE_END.store(w.into_raw_fd(), Ordering::Release);
            *made = true;
        }
        drop(made);
        set_action(sig, on_signal as *const () as libc::sighandler_t);
        Ok(Value::Nil)
    });
    // `ignore`: SIG_IGN, else SIG_DFL.
    native!(m, "Signal.action", |i, _, a| {
        let sig = signo(i, a.arg(0))?;
        let ignore = a.arg(1).is_truthy();
        set_action(sig, if ignore { libc::SIG_IGN } else { libc::SIG_DFL });
        Ok(Value::Nil)
    });
    // The socket the signals arrive on, once (nil after).
    native!(m, "Signal.reader", |i, _, _| {
        Ok(match READ_END.lock().unwrap().take() {
            Some(r) => make_socket(i, Stream::Unix(r), None),
            None => Value::Nil,
        })
    });
}

/// Ignore SIGPIPE, so that writing to a closed socket fails with EPIPE
/// instead of ending the process (Rust's start-up does this for `quarz
/// run`; compiled programs start in `qz_main`).
pub fn ignore_sigpipe() {
    set_action(libc::SIGPIPE, libc::SIG_IGN);
}
