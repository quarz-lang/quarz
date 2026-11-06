//! TLS connections as a kind of IO (`IoKind::Tls`, `TLSSocket` in
//! `std/tls.qz`): the state of a stream socket taken over, and a TLS
//! session pumped through it the way a socket is read and written.
//!
//! The session is reached through `TlsSession`, a trait object made only
//! by `TLSSocket.connect`'s native (`tls.rs`, behind the `tls` feature):
//! the IO natives' `Tls` arms call it without naming rustls, so a program
//! that never connects keeps none of its code.
//!
//! Sharing (docs/04 §4): the session is touched only under the handle's
//! lock, which is released only to wait for the descriptor, and is
//! consistent whenever it is; a write keeps the stream's write turn
//! through its whole pump (its plaintext into records, then the records
//! out), so two tasks' plaintext never shares a record; a read takes its
//! unit from the plaintext buffer under the lock, as a socket's does.

use std::io::Read;

use crate::interp::{EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::io::{io_of, os_error};
use super::net::{
    close_stream, closed_stream, shutdown_stream, stream_error, with_write_turn, Fill, Readable,
    StreamError, WriteTurn,
};

/// A TLS session (rustls's client or server connection): the calls the
/// pump makes.
pub trait TlsSession: Send {
    /// Read TLS records from `rd` into the session.
    fn read_tls(&mut self, rd: &mut dyn Read) -> std::io::Result<usize>;
    /// Write the records the session has to send to `wr`.
    fn write_tls(&mut self, wr: &mut dyn std::io::Write) -> std::io::Result<usize>;
    /// Process the records read; a failure leaves an alert to send.
    fn process_new_packets(&mut self) -> Result<(), TlsFailure>;
    /// Plaintext received: `WouldBlock` when none yet, `Ok(0)` after the
    /// peer's close_notify, `UnexpectedEof` when the stream ended without.
    fn read_plain(&mut self, buf: &mut [u8]) -> std::io::Result<usize>;
    /// Plaintext to send, made into records at once (no limit).
    fn write_plain(&mut self, data: &[u8]);
    fn wants_write(&self) -> bool;
    fn is_handshaking(&self) -> bool;
    fn send_close_notify(&mut self);
    /// The protocol ALPN agreed on.
    fn alpn(&self) -> Option<Vec<u8>>;
    /// The peer's end-entity certificate (DER).
    fn peer_certificate(&self) -> Option<Vec<u8>>;
}

/// A TLS failure, made into a `TLS::Error` (a `TLS::CertificateError`
/// when `certificate`).
#[derive(Debug)]
pub struct TlsFailure {
    pub message: String,
    pub certificate: bool,
}

pub(crate) fn tls_error(interp: &Interp, f: TlsFailure) -> Flow {
    let exc = &interp.program.exc;
    let class = if f.certificate {
        exc.tls_certificate_error
    } else {
        exc.tls_error
    };
    interp.raise(class, &f.message)
}

pub struct TlsState {
    /// The socket taken over (its descriptor, addresses, write turn and
    /// waiters); its `rbuf` holds the bytes it had read before (TLS
    /// records, fed to the session first), its `eof` that the plaintext
    /// stream has ended.
    pub sock: SocketState,
    pub session: Box<dyn TlsSession>,
    /// Plaintext received but not yet taken.
    pub plain: Vec<u8>,
    pub server_name: String,
    /// Whether the peer's certificate was verified (`verify: false` in
    /// the config: not).
    pub verified: bool,
    /// close_notify is queued: nothing more is written.
    pub notified: bool,
}

impl std::fmt::Debug for TlsState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TlsState({})", self.server_name)
    }
}

impl Watched for TlsState {
    fn watch(&mut self) -> &mut IoWatch {
        &mut self.sock.watch
    }
}

impl WriteTurn for TlsState {
    fn turn(
        &mut self,
    ) -> (
        &mut bool,
        &mut std::collections::VecDeque<crate::sched::TaskRef>,
    ) {
        self.sock.turn()
    }
}

/// What the session reads records from: the bytes the socket had
/// buffered, then the socket.
struct Source<'a> {
    rbuf: &'a mut Vec<u8>,
    stream: &'a mut Stream,
}

impl Read for Source<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        if self.rbuf.is_empty() {
            return self.stream.read(buf);
        }
        let n = buf.len().min(self.rbuf.len());
        buf[..n].copy_from_slice(&self.rbuf[..n]);
        self.rbuf.drain(..n);
        Ok(n)
    }
}

impl TlsState {
    /// Read records from the socket into the session and process them,
    /// without waiting: `Ok(None)` when it would block.
    fn receive(&mut self) -> Result<Option<usize>, StreamError> {
        let Some(stream) = self.sock.stream.as_mut() else {
            return Ok(Some(0));
        };
        let mut src = Source {
            rbuf: &mut self.sock.rbuf,
            stream,
        };
        match self.session.read_tls(&mut src) {
            Ok(n) => {
                let r = self.session.process_new_packets();
                // An alert for a failure, a reply the peer asked for (a
                // key update): sent now if the socket takes it.
                self.send_pending();
                r.map_err(StreamError::Tls)?;
                Ok(Some(n))
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => Ok(None),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => Ok(Some(1)),
            Err(e) => Err(StreamError::Os(e, "read")),
        }
    }

    /// Write what the session has to send while the socket takes it,
    /// without waiting (the rest goes with the next write or close).
    fn send_pending(&mut self) {
        let Some(stream) = self.sock.stream.as_mut() else {
            return;
        };
        while self.session.wants_write() {
            match self.session.write_tls(stream) {
                Ok(0) | Err(_) => break,
                Ok(_) => {}
            }
        }
    }
}

impl Readable for TlsState {
    fn buffer(&mut self) -> (&mut Vec<u8>, bool) {
        (&mut self.plain, self.sock.eof)
    }

    fn fill(&mut self, chunk: &mut [u8]) -> Fill {
        let Some(fd) = self.sock.stream.as_ref().map(|s| s.fd()) else {
            return Fill::Closed;
        };
        // The plaintext the session holds first.
        match self.session.read_plain(chunk) {
            Ok(0) => {
                self.sock.eof = true;
                return Fill::More;
            }
            Ok(n) => {
                self.plain.extend_from_slice(&chunk[..n]);
                return Fill::More;
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
            // The peer closed without close_notify: the end, as for a
            // socket (`strict_close` would make it an error).
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                self.sock.eof = true;
                return Fill::More;
            }
            Err(e) => return Fill::Failed(StreamError::Os(e, "read")),
        }
        match self.receive() {
            Ok(Some(_)) => Fill::More,
            Ok(None) => Fill::Wait(fd),
            Err(e) => Fill::Failed(e),
        }
    }
}

/// What a step of the handshake or of a write's pump left to do.
enum Step {
    Done,
    Wait(std::os::fd::RawFd, bool),
    /// The socket is closed (raised once the lock is released).
    Closed,
}

/// Run the handshake to its end: write what the session has to send,
/// read what it waits for, waiting for the socket as a socket's
/// operations do (so `Task.timeout` and `cancel` interrupt it).
#[cfg_attr(not(feature = "tls"), allow(dead_code))]
pub(crate) fn handshake(interp: &Interp, st: &IoCell<TlsState>) -> Result<(), Flow> {
    loop {
        let step = {
            let mut g = st.borrow_mut();
            let s = &mut *g;
            loop {
                let Some(stream) = s.sock.stream.as_mut() else {
                    break Step::Closed;
                };
                let fd = stream.fd();
                if s.session.wants_write() {
                    match s.session.write_tls(stream) {
                        Ok(0) => {
                            drop(g);
                            return Err(
                                interp.raise(interp.program.exc.io_error, "connection closed")
                            );
                        }
                        Ok(_) => continue,
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                            break Step::Wait(fd, true)
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                        Err(e) => {
                            drop(g);
                            return Err(os_error(interp, e, "TLS handshake"));
                        }
                    }
                }
                if !s.session.is_handshaking() {
                    break Step::Done;
                }
                match s.receive() {
                    Ok(Some(0)) => {
                        drop(g);
                        return Err(tls_error(
                            interp,
                            TlsFailure {
                                message: "connection closed during the TLS handshake".to_string(),
                                certificate: false,
                            },
                        ));
                    }
                    Ok(Some(_)) => {}
                    Ok(None) => break Step::Wait(fd, false),
                    Err(e) => {
                        drop(g);
                        return Err(stream_error(interp, e));
                    }
                }
            }
        };
        match step {
            Step::Done => return Ok(()),
            Step::Wait(fd, writable) => interp.wait_io(st, fd, writable)?,
            Step::Closed => return Err(closed_stream(interp)),
        }
    }
}

/// Write what the session has to send, waiting for the socket.
fn pump(interp: &Interp, st: &IoCell<TlsState>) -> Result<(), Flow> {
    loop {
        let step = {
            let mut g = st.borrow_mut();
            let s = &mut *g;
            loop {
                let Some(stream) = s.sock.stream.as_mut() else {
                    break Step::Closed;
                };
                if !s.session.wants_write() {
                    break Step::Done;
                }
                match s.session.write_tls(stream) {
                    Ok(0) => {
                        drop(g);
                        return Err(interp.raise(interp.program.exc.io_error, "connection closed"));
                    }
                    Ok(_) => {}
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        break Step::Wait(stream.fd(), true)
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                    Err(e) => {
                        drop(g);
                        return Err(os_error(interp, e, "write"));
                    }
                }
            }
        };
        match step {
            Step::Done => return Ok(()),
            Step::Wait(fd, writable) => interp.wait_io(st, fd, writable)?,
            Step::Closed => return Err(closed_stream(interp)),
        }
    }
}

/// Write all of `data`: in this task's write turn, its records made at
/// once and sent before the turn passes.
pub(crate) fn write(interp: &Interp, st: &IoCell<TlsState>, data: &[u8]) -> Result<(), Flow> {
    with_write_turn(interp, st, || {
        {
            let mut s = st.borrow_mut();
            if s.sock.stream.is_none() {
                drop(s);
                return Err(closed_stream(interp));
            }
            if s.notified {
                drop(s);
                return Err(interp.raise(interp.program.exc.io_error, "not opened for writing"));
            }
            s.session.write_plain(data);
        }
        pump(interp, st)
    })
}

/// Send what is pending (`flush`).
pub(crate) fn flush(interp: &Interp, st: &IoCell<TlsState>) -> Result<(), Flow> {
    with_write_turn(interp, st, || pump(interp, st))
}

/// `close_write`: send close_notify, then shut the socket's write side.
pub(crate) fn close_write(interp: &Interp, st: &IoCell<TlsState>) -> Result<(), Flow> {
    with_write_turn(interp, st, || {
        {
            let mut s = st.borrow_mut();
            if s.sock.stream.is_none() {
                drop(s);
                return Err(closed_stream(interp));
            }
            if !s.notified {
                s.session.send_close_notify();
                s.notified = true;
            }
        }
        pump(interp, st)?;
        let r = shutdown_stream(&st.borrow().sock, std::net::Shutdown::Write);
        match r {
            Some(r) => r.map_err(|e| os_error(interp, e, "shutdown")),
            None => Err(closed_stream(interp)),
        }
    })
}

/// `close`: send close_notify if the socket takes it now, then close the
/// socket. The tasks waiting on it, returned, are to be woken.
pub(crate) fn close(interp: &Interp, st: &IoCell<TlsState>) -> Vec<crate::sched::TaskRef> {
    let mut s = st.borrow_mut();
    if s.sock.stream.is_some() && !s.notified {
        s.session.send_close_notify();
        s.notified = true;
        s.send_pending();
    }
    close_stream(interp, &mut s.sock)
}

fn tls_state<'a>(interp: &Interp, v: &'a Value) -> Result<&'a IoCell<TlsState>, Flow> {
    match &io_of(interp, v)?.kind {
        IoKind::Tls(st) => Ok(st),
        _ => Err(interp.err_type("not a TLS socket")),
    }
}

/// The natives that read a connection's state (the ones that make one
/// are in `tls.rs`).
pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "TLSSocket#alpn", |i, r, _| -> EvalResult {
        let alpn = tls_state(i, r)?.borrow().session.alpn();
        Ok(match alpn {
            Some(p) => Value::string(String::from_utf8_lossy(&p).into_owned()),
            None => Value::Nil,
        })
    });
    native!(m, "TLSSocket#peer_certificate", |i, r, _| -> EvalResult {
        let der = tls_state(i, r)?.borrow().session.peer_certificate();
        Ok(der.map(Value::bytes).unwrap_or(Value::Nil))
    });
    native!(m, "TLSSocket#verified?", |i, r, _| -> EvalResult {
        Ok(Value::Bool(tls_state(i, r)?.borrow().verified))
    });
}
