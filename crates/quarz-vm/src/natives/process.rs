//! `Process.spawn`, `Process::Child`, `Process::Status` and `Process.exec`
//! (std/prelude.qz).
//!
//! A child's pipes are non-blocking and wait on the reactor, as sockets
//! do (`Stream::Pipe`, an `IO` read and written through the socket
//! code). Waiting for the child's end takes no thread on Linux: a pidfd
//! (`pidfd_open`), readable once the child ended, is waited on through
//! the reactor, so `Task.timeout` and `cancel` interrupt the wait and
//! the child can be waited for again. Elsewhere (or on a kernel without
//! pidfds) a helper thread per child blocks in `waitpid` and leaves the
//! status in the shared state, and a waiting task waits for that on a
//! helper thread of its own (`Interp::block_on`); an interrupted wait
//! leaves the helper running, and the next wait finds the status there.

use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::process::ExitStatusExt;
use std::process::ExitStatus;
use std::sync::{Arc, Condvar, Mutex};

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::rc::Rc;
use crate::value::*;
use smallvec::smallvec;

use super::io::{io_of, os_error};
use super::net::make_socket;
use super::string;

/// What a helper thread's `waitpid` leaves (`ChildState::helper`): the
/// status, or the error number of a failed wait. The helper reaps the
/// child while holding the lock, which `signal` holds across its `kill`,
/// so that no signal goes to a pid the system has given to another
/// process.
type Reaped = Arc<(Mutex<Option<Result<ExitStatus, i32>>>, Condvar)>;

/// The state of a child process, shared by the tasks holding its
/// `Process::Child`.
pub struct ChildState {
    pub pid: u32,
    child: std::process::Child,
    /// Readable once the child ended (Linux), waited on by the reactor.
    pidfd: Option<OwnedFd>,
    /// The status, once the child was reaped: every `wait` and `status`
    /// reads it.
    status: Option<ExitStatus>,
    watch: IoWatch,
    /// Without a pidfd: the helper thread reaping the child, once a
    /// `wait` started it.
    helper: Option<Reaped>,
    /// The parent's ends of the pipes asked for (`:pipe`).
    stdin: Option<Rc<IoVal>>,
    stdout: Option<Rc<IoVal>>,
    stderr: Option<Rc<IoVal>>,
}

impl std::fmt::Debug for ChildState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ChildState({})", self.pid)
    }
}

impl Watched for ChildState {
    fn watch(&mut self) -> &mut IoWatch {
        &mut self.watch
    }
}

impl ChildState {
    /// The status if the child ended, reaping it (no waiting).
    fn poll(&mut self) -> std::io::Result<Option<ExitStatus>> {
        if self.status.is_none() {
            if let Some(h) = &self.helper {
                match *h.0.lock().unwrap_or_else(|e| e.into_inner()) {
                    Some(Ok(x)) => self.status = Some(x),
                    Some(Err(n)) => return Err(std::io::Error::from_raw_os_error(n)),
                    None => {}
                }
            } else {
                self.status = self.child.try_wait()?;
            }
        }
        Ok(self.status)
    }
}

impl Drop for ChildState {
    /// A child dropped without `wait` is not killed: it is reaped now if
    /// it has ended, else left running (a zombie once it ends, until the
    /// program exits).
    fn drop(&mut self) {
        if self.status.is_none() && self.helper.is_none() {
            let _ = self.child.try_wait();
        }
    }
}

/// The signals by name (without `SIG`), for a status's `signal`.
const SIGNAL_NAMES: &[(&str, libc::c_int)] = &[
    ("HUP", libc::SIGHUP),
    ("INT", libc::SIGINT),
    ("QUIT", libc::SIGQUIT),
    ("ILL", libc::SIGILL),
    ("TRAP", libc::SIGTRAP),
    ("ABRT", libc::SIGABRT),
    ("BUS", libc::SIGBUS),
    ("FPE", libc::SIGFPE),
    ("KILL", libc::SIGKILL),
    ("USR1", libc::SIGUSR1),
    ("SEGV", libc::SIGSEGV),
    ("USR2", libc::SIGUSR2),
    ("PIPE", libc::SIGPIPE),
    ("ALRM", libc::SIGALRM),
    ("TERM", libc::SIGTERM),
    ("CHLD", libc::SIGCHLD),
    ("CONT", libc::SIGCONT),
    ("STOP", libc::SIGSTOP),
    ("TSTP", libc::SIGTSTP),
    ("TTIN", libc::SIGTTIN),
    ("TTOU", libc::SIGTTOU),
    ("XCPU", libc::SIGXCPU),
    ("XFSZ", libc::SIGXFSZ),
    ("SYS", libc::SIGSYS),
];

fn signal_name(signo: libc::c_int) -> String {
    match SIGNAL_NAMES.iter().find(|(_, s)| *s == signo) {
        Some((n, _)) => n.to_string(),
        None => signo.to_string(),
    }
}

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Process.spawn", spawn);
    native!(m, "Process.exec", exec);
    native!(m, "Process::Child#pid", |i, r, _| {
        Ok(Value::Int(child(i, r)?.borrow().pid as i64))
    });
    native!(m, "Process::Child#wait", |i, r, _| {
        let status = wait(i, r)?;
        make_status(i, status)
    });
    native!(m, "Process::Child#status", |i, r, _| {
        let st = child(i, r)?;
        let status = st
            .borrow_mut()
            .poll()
            .map_err(|e| os_error(i, e, "waitpid"))?;
        match status {
            Some(s) => make_status(i, s),
            None => Ok(Value::Nil),
        }
    });
    native!(m, "Process::Child#running?", |i, r, _| {
        let st = child(i, r)?;
        let status = st
            .borrow_mut()
            .poll()
            .map_err(|e| os_error(i, e, "waitpid"))?;
        Ok(Value::Bool(status.is_none()))
    });
    native!(m, "Process::Child#signal", |i, r, a| {
        let name = match a.arg(0) {
            Value::Symbol(s) => i.symbol_name(*s).to_string(),
            v => string(i, v, "signal")?.to_string(),
        };
        let Some(signo) = super::signal::number(&name) else {
            return Err(i.err_arg(&format!("unsupported signal: {name}")));
        };
        let st = child(i, r)?;
        let mut s = st.borrow_mut();
        // (Not once reaped: the pid may be another process's by now. The
        // child is reaped under this lock, or the helper's, held here
        // across the `kill`.)
        if s.poll().map_err(|e| os_error(i, e, "waitpid"))?.is_some() {
            return Ok(Value::Nil);
        }
        let helper = s
            .helper
            .as_ref()
            .map(|h| h.0.lock().unwrap_or_else(|e| e.into_inner()));
        if helper.as_ref().is_some_and(|g| g.is_some()) {
            return Ok(Value::Nil);
        }
        let r = unsafe { libc::kill(s.pid as libc::pid_t, signo) };
        drop(helper);
        if r != 0 {
            let e = std::io::Error::last_os_error();
            if e.raw_os_error() != Some(libc::ESRCH) {
                return Err(os_error(i, e, "kill"));
            }
        }
        Ok(Value::Nil)
    });
    native!(m, "Process::Child#stdin", |i, r, _| stream(i, r, 0));
    native!(m, "Process::Child#stdout", |i, r, _| stream(i, r, 1));
    native!(m, "Process::Child#stderr", |i, r, _| stream(i, r, 2));
}

pub(crate) fn child<'a>(interp: &Interp, v: &'a Value) -> Result<&'a IoCell<ChildState>, Flow> {
    match &io_of(interp, v)?.kind {
        IoKind::Child(st) => Ok(st),
        _ => Err(interp.err_type("expected a Process::Child")),
    }
}

/// `#<Process::Child 1234 running>`, or with the status once reaped.
pub fn inspect_child(st: &IoCell<ChildState>) -> String {
    let mut s = st.borrow_mut();
    let pid = s.pid;
    match s.poll().ok().flatten() {
        None => format!("#<Process::Child {pid} running>"),
        Some(x) => match (x.code(), x.signal()) {
            (Some(c), _) => format!("#<Process::Child {pid} exited {c}>"),
            (None, Some(sig)) => format!("#<Process::Child {pid} SIG{}>", signal_name(sig)),
            _ => format!("#<Process::Child {pid} ended>"),
        },
    }
}

/// The command (`*command` strings), checked not empty.
fn command_of(interp: &Interp, args: &Args, what: &str) -> Result<Vec<String>, Flow> {
    if args.pos.is_empty() {
        return Err(interp.err_arg(&format!("{what} needs a command")));
    }
    let mut parts = Vec::with_capacity(args.pos.len());
    for p in &args.pos {
        parts.push(string(interp, p, "command")?.to_string());
    }
    Ok(parts)
}

/// `env:`, added to the parent's environment.
fn env_of(interp: &Interp, args: &Args) -> Result<Vec<(String, String)>, Flow> {
    let mut env = Vec::new();
    if let Some(Value::Hash(h)) = args.kw(interp, "env") {
        for (k, v) in h.as_map().iter() {
            env.push((
                string(interp, k, "env key")?.to_string(),
                string(interp, v, "env value")?.to_string(),
            ));
        }
    }
    Ok(env)
}

/// What a stream option asks for.
#[derive(Clone, Copy, PartialEq)]
enum Redirect {
    Inherit,
    Pipe,
    Null,
}

fn redirect_of(interp: &Interp, args: &Args, name: &str) -> Result<Redirect, Flow> {
    let Some(v) = args.kw(interp, name) else {
        return Ok(Redirect::Inherit);
    };
    let Value::Symbol(s) = v else {
        return Err(interp.err_arg(&format!("{name}: must be :inherit, :pipe or :null")));
    };
    match &*interp.symbol_name(*s) {
        "inherit" => Ok(Redirect::Inherit),
        "pipe" => Ok(Redirect::Pipe),
        "null" => Ok(Redirect::Null),
        other => Err(interp.err_arg(&format!(
            "{name}: must be :inherit, :pipe or :null, not :{other}"
        ))),
    }
}

fn stdio(r: Redirect) -> std::process::Stdio {
    match r {
        Redirect::Inherit => std::process::Stdio::inherit(),
        Redirect::Pipe => std::process::Stdio::piped(),
        Redirect::Null => std::process::Stdio::null(),
    }
}

/// The parent's end of a pipe, made non-blocking, as an `IO`.
fn pipe_io(interp: &Interp, fd: OwnedFd, end: PipeEnd) -> Result<Rc<IoVal>, Flow> {
    let raw = fd.as_raw_fd();
    let flags = unsafe { libc::fcntl(raw, libc::F_GETFL) };
    if flags < 0 || unsafe { libc::fcntl(raw, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(os_error(interp, std::io::Error::last_os_error(), "pipe"));
    }
    match make_socket(interp, Stream::Pipe(std::fs::File::from(fd)), None) {
        Value::Io(io) => {
            if let IoKind::Socket(st) = &io.kind {
                st.borrow_mut().pipe = Some(end);
            }
            Ok(io)
        }
        _ => unreachable!("make_socket makes an IO"),
    }
}

fn spawn(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let parts = command_of(interp, &args, "Process.spawn")?;
    let env = env_of(interp, &args)?;
    let streams = [
        redirect_of(interp, &args, "stdin")?,
        redirect_of(interp, &args, "stdout")?,
        redirect_of(interp, &args, "stderr")?,
    ];
    let chdir = match args.kw(interp, "chdir") {
        None | Some(Value::Nil) => None,
        Some(v) => Some(string(interp, v, "chdir")?.to_string()),
    };
    let mut command = std::process::Command::new(&parts[0]);
    command
        .args(&parts[1..])
        .envs(env)
        .stdin(stdio(streams[0]))
        .stdout(stdio(streams[1]))
        .stderr(stdio(streams[2]));
    if let Some(dir) = &chdir {
        command.current_dir(dir);
    }
    // (What the program printed comes before what the child prints on
    // an inherited stream.)
    interp.flush();
    let mut child = command.spawn().map_err(|e| {
        let what = match &chdir {
            Some(dir) if !std::path::Path::new(dir).is_dir() => dir.as_str(),
            _ => parts[0].as_str(),
        };
        os_error(interp, e, what)
    })?;
    let pid = child.id();
    let stdin = match child.stdin.take() {
        Some(p) => Some(pipe_io(interp, OwnedFd::from(p), PipeEnd::Write)?),
        None => None,
    };
    let stdout = match child.stdout.take() {
        Some(p) => Some(pipe_io(interp, OwnedFd::from(p), PipeEnd::Read)?),
        None => None,
    };
    let stderr = match child.stderr.take() {
        Some(p) => Some(pipe_io(interp, OwnedFd::from(p), PipeEnd::Read)?),
        None => None,
    };
    Ok(Value::Io(Rc::new_shared(IoVal {
        kind: IoKind::Child(IoCell::new(ChildState {
            pid,
            child,
            pidfd: pidfd_open(pid),
            status: None,
            watch: IoWatch::new(),
            helper: None,
            stdin,
            stdout,
            stderr,
        })),
    })))
}

/// A pidfd for `pid` (close-on-exec, as `pidfd_open` makes it); `None`
/// where the system has none, or with `QUARZ_NO_PIDFD=1` (which the
/// tests set to run the other way).
#[cfg(target_os = "linux")]
fn pidfd_open(pid: u32) -> Option<OwnedFd> {
    static OFF: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *OFF.get_or_init(|| std::env::var_os("QUARZ_NO_PIDFD").is_some_and(|v| v == "1")) {
        return None;
    }
    let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid as libc::pid_t, 0) };
    (fd >= 0).then(|| unsafe { OwnedFd::from_raw_fd(fd as libc::c_int) })
}

#[cfg(not(target_os = "linux"))]
fn pidfd_open(_: u32) -> Option<OwnedFd> {
    None
}

/// Wait for the child's end, parking only the calling task.
fn wait(interp: &Interp, recv: &Value) -> Result<ExitStatus, Flow> {
    let st = child(interp, recv)?;
    loop {
        let mut s = st.borrow_mut();
        if let Some(x) = s.poll().map_err(|e| os_error(interp, e, "waitpid"))? {
            return Ok(x);
        }
        if let Some(fd) = s.pidfd.as_ref().map(|f| f.as_raw_fd()) {
            interp.wait_io_held(st, s, fd, false)?;
            continue;
        }
        // No pidfd: a helper thread reaps the child, once.
        let reaped = match &s.helper {
            Some(h) => h.clone(),
            None => {
                let h: Reaped = Arc::new((Mutex::new(None), Condvar::new()));
                let pid = s.pid as libc::pid_t;
                let theirs = h.clone();
                std::thread::Builder::new()
                    .name("quarz-waitpid".into())
                    .spawn(move || {
                        let errno = || std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
                        // Wait for the end without reaping, then reap
                        // under the lock (see `Reaped`).
                        let ended = loop {
                            let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
                            let r = unsafe {
                                libc::waitid(
                                    libc::P_PID,
                                    pid as libc::id_t,
                                    &mut info,
                                    libc::WEXITED | libc::WNOWAIT,
                                )
                            };
                            if r == 0 {
                                break Ok(());
                            }
                            if errno() != libc::EINTR {
                                break Err(errno());
                            }
                        };
                        let mut g = theirs.0.lock().unwrap_or_else(|e| e.into_inner());
                        *g = Some(ended.and_then(|()| {
                            let mut raw = 0;
                            loop {
                                if unsafe { libc::waitpid(pid, &mut raw, 0) } >= 0 {
                                    break Ok(ExitStatus::from_raw(raw));
                                }
                                if errno() != libc::EINTR {
                                    break Err(errno());
                                }
                            }
                        }));
                        drop(g);
                        theirs.1.notify_all();
                    })
                    .map_err(|e| os_error(interp, e, "waitpid"))?;
                s.helper = Some(h.clone());
                h
            }
        };
        drop(s);
        let x = interp.block_on(move || {
            let (m, c) = &*reaped;
            let mut g = m.lock().unwrap_or_else(|e| e.into_inner());
            while g.is_none() {
                g = c.wait(g).unwrap_or_else(|e| e.into_inner());
            }
            g.expect("set above")
        })?;
        let x = x.map_err(|n| os_error(interp, std::io::Error::from_raw_os_error(n), "waitpid"))?;
        st.borrow_mut().status = Some(x);
        return Ok(x);
    }
}

/// A `Process::Status` for `status`.
fn make_status(interp: &Interp, status: ExitStatus) -> EvalResult {
    let class = interp.program.rt.process_status;
    // A `data` with no initializer of its own: fill the fields directly.
    let value = interp.construct(class, None, smallvec![], Vec::new(), None)?;
    if let Value::Object(obj) = &value {
        obj.set_field(
            0,
            match status.code() {
                Some(c) => Value::Int(c as i64),
                None => Value::Nil,
            },
        );
        obj.set_field(
            1,
            match status.signal() {
                Some(s) => Value::string(signal_name(s)),
                None => Value::Nil,
            },
        );
    }
    Ok(value)
}

/// `stdin`, `stdout` or `stderr` (0, 1, 2), when it was `:pipe`.
fn stream(interp: &Interp, recv: &Value, which: usize) -> EvalResult {
    let st = child(interp, recv)?;
    let s = st.borrow();
    let (io, name) = match which {
        0 => (&s.stdin, "stdin"),
        1 => (&s.stdout, "stdout"),
        _ => (&s.stderr, "stderr"),
    };
    match io {
        Some(io) => Ok(Value::Io(io.clone())),
        None => Err(interp.err_arg(&format!(
            "the child's {name} is not a pipe: spawn it with `{name}: :pipe`"
        ))),
    }
}

fn exec(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    use std::os::unix::process::CommandExt;
    let parts = command_of(interp, &args, "Process.exec")?;
    let env = env_of(interp, &args)?;
    let mut command = std::process::Command::new(&parts[0]);
    command.args(&parts[1..]).envs(env);
    interp.flush();
    let _ = std::io::Write::flush(&mut std::io::stderr());
    // The standard library sets SIGPIPE's action to the default and
    // empties the thread's signal mask before `execvp`, in this process:
    // restored when it fails (the runtime ignores SIGPIPE, or a trap
    // handles it).
    let mut pipe_action: libc::sigaction = unsafe { std::mem::zeroed() };
    let mut mask: libc::sigset_t = unsafe { std::mem::zeroed() };
    unsafe {
        libc::sigaction(libc::SIGPIPE, std::ptr::null(), &mut pipe_action);
        libc::pthread_sigmask(libc::SIG_SETMASK, std::ptr::null(), &mut mask);
    }
    // Returns only when it fails.
    let e = command.exec();
    unsafe {
        libc::sigaction(libc::SIGPIPE, &pipe_action, std::ptr::null_mut());
        libc::pthread_sigmask(libc::SIG_SETMASK, &mask, std::ptr::null_mut());
    }
    Err(os_error(interp, e, &parts[0]))
}
