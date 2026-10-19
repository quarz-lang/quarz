//! Sockets: TCPSocket, TCPServer, UDPSocket, UNIXSocket and UNIXServer.
//!
//! Every socket is non-blocking. An operation that would block parks the
//! task on the scheduler's reactor until the descriptor is ready, so
//! only the calling task waits. Name resolution and `connect` run on a
//! helper thread for the same reason. `close` releases the descriptor at
//! once rather than when the value is dropped.

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::os::fd::{AsRawFd, RawFd};
use std::os::unix::net::{UnixListener, UnixStream};
use std::rc::Rc;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::io::{io, io_of, os_error};
use super::{int, string};

pub fn register(m: &mut HashMap<&'static str, NativeFn>) {
    // TCPSocket
    m.insert("TCPSocket.new", |i, _, a| tcp_connect(i, &a));
    m.insert("TCPSocket.open", |i, _, a| {
        let sock = tcp_connect(i, &a)?;
        with_closing(i, sock, &a)
    });
    // TCPServer
    m.insert("TCPServer.new", |i, _, a| {
        let (host, port) = match a.pos.len() {
            1 => ("0.0.0.0".to_string(), int(i, a.arg(0), "port")?),
            _ => (
                string(i, a.arg(0), "host")?.to_string(),
                int(i, a.arg(1), "port")?,
            ),
        };
        let label = format!("{host}:{port}");
        let addr = label.clone();
        let listener = i
            .block_on(move || TcpListener::bind(addr.as_str()))?
            .map_err(|e| os_error(i, e, &label))?;
        listener
            .set_nonblocking(true)
            .map_err(|e| os_error(i, e, "listen"))?;
        Ok(make_listener(i, Listener::Tcp(listener), None))
    });
    m.insert("TCPServer#accept", listener_accept);
    m.insert("UNIXServer#accept", listener_accept);
    // UNIXSocket / UNIXServer
    m.insert("UNIXSocket.new", |i, _, a| unix_connect(i, &a));
    m.insert("UNIXSocket.open", |i, _, a| {
        let sock = unix_connect(i, &a)?;
        with_closing(i, sock, &a)
    });
    m.insert("UNIXServer.new", |i, _, a| {
        let path = string(i, a.arg(0), "path")?;
        let listener = UnixListener::bind(path).map_err(|e| os_error(i, e, path))?;
        listener
            .set_nonblocking(true)
            .map_err(|e| os_error(i, e, path))?;
        Ok(make_listener(
            i,
            Listener::Unix(listener),
            Some(path.to_string()),
        ))
    });
    // UDPSocket
    m.insert("UDPSocket.new", |i, _, _| {
        let socket = udp_bind(i, "0.0.0.0:0")?;
        i.sched.borrow().register(socket.as_raw_fd());
        Ok(io(IoKind::Udp(RefCell::new(UdpState {
            socket: Some(socket),
            closed: false,
        }))))
    });
    m.insert("UDPSocket#bind", |i, r, a| {
        // Binding after creation replaces the descriptor.
        let host = string(i, a.arg(0), "host")?;
        let port = int(i, a.arg(1), "port")?;
        let st = udp(i, r)?;
        let socket = udp_bind(i, &format!("{host}:{port}"))?;
        let old_fd = udp_fd(i, st)?;
        i.sched.borrow_mut().deregister(old_fd);
        st.borrow_mut().socket = Some(socket);
        let new_fd = udp_fd(i, st)?;
        i.sched.borrow().register(new_fd);
        Ok(Value::Nil)
    });
    m.insert("UDPSocket#connect", |i, r, a| {
        let host = string(i, a.arg(0), "host")?.to_string();
        let port = int(i, a.arg(1), "port")?;
        let addr = resolve(i, &host, port)?;
        let st = udp(i, r)?;
        let r = match &st.borrow().socket {
            Some(s) => s.connect(addr),
            None => return Err(i.raise(i.exc.io_error, "closed stream")),
        };
        r.map_err(|e| os_error(i, e, &format!("{host}:{port}")))?;
        Ok(Value::Nil)
    });
    m.insert("UDPSocket#send", |i, r, a| {
        let data = payload(i, a.arg(0))?;
        let st = udp(i, r)?;
        let fd = udp_fd(i, st)?;
        let target = match a.pos.len() {
            3 => {
                let host = string(i, a.arg(1), "host")?.to_string();
                let port = int(i, a.arg(2), "port")?;
                Some(resolve(i, &host, port)?)
            }
            _ => None,
        };
        loop {
            let r = {
                let s = st.borrow();
                let Some(socket) = s.socket.as_ref() else {
                    return Err(i.raise(i.exc.io_error, "closed stream"));
                };
                match target {
                    Some(addr) => socket.send_to(&data, addr),
                    None => socket.send(&data),
                }
            };
            match r {
                Ok(n) => return Ok(Value::Int(n as i64)),
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => i.wait_fd(fd, true)?,
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(os_error(i, e, "send")),
            }
        }
    });
    m.insert("UDPSocket#recvfrom", |i, r, a| {
        udp_recv(i, r, &a, true, false)
    });
    m.insert("UDPSocket#recvfrom_bytes", |i, r, a| {
        udp_recv(i, r, &a, true, true)
    });
    m.insert("UDPSocket#recv", |i, r, a| udp_recv(i, r, &a, false, false));
    m.insert("UDPSocket#recv_bytes", |i, r, a| {
        udp_recv(i, r, &a, false, true)
    });
    // Addresses.
    for key in [
        "TCPSocket#local_address",
        "TCPServer#local_address",
        "UDPSocket#local_address",
    ] {
        m.insert(key, |i, r, _| {
            let addr = match &io_of(i, r)?.kind {
                IoKind::Socket(st) => st.borrow().local,
                IoKind::Listener(st) => match &st.borrow().listener {
                    Some(Listener::Tcp(l)) => l.local_addr().ok(),
                    _ => None,
                },
                IoKind::Udp(st) => st
                    .borrow()
                    .socket
                    .as_ref()
                    .and_then(|s| s.local_addr().ok()),
                _ => return Err(i.err_type("not a socket")),
            };
            Ok(addr.map(addr_value).unwrap_or(Value::Nil))
        });
    }
    m.insert("TCPSocket#remote_address", |i, r, _| {
        match &io_of(i, r)?.kind {
            IoKind::Socket(st) => Ok(st.borrow().peer.map(addr_value).unwrap_or(Value::Nil)),
            _ => Err(i.err_type("not a socket")),
        }
    });
    // Streams in general (sockets and files).
    m.insert("IO#readpartial", |i, r, a| {
        let max = int(i, a.arg(0), "length")?.max(0) as usize;
        match read_partial(i, r, max)? {
            Some(bytes) => Ok(Value::string(String::from_utf8_lossy(&bytes).into_owned())),
            None => Err(i.raise(i.exc.eof_error, "end of file reached")),
        }
    });
    m.insert("IO#readpartial?", |i, r, a| {
        let max = int(i, a.arg(0), "length")?.max(0) as usize;
        Ok(match read_partial(i, r, max)? {
            Some(bytes) => Value::string(String::from_utf8_lossy(&bytes).into_owned()),
            None => Value::Nil,
        })
    });
    m.insert("IO#read_bytes", |i, r, a| {
        let max = int(i, a.arg(0), "length")?.max(0) as usize;
        Ok(Value::bytes(read_partial(i, r, max)?.unwrap_or_default()))
    });
    m.insert("IO#close_write", |i, r, _| {
        shutdown(i, r, std::net::Shutdown::Write)?;
        Ok(Value::Nil)
    });
    m.insert("IO#close_read", |i, r, _| {
        shutdown(i, r, std::net::Shutdown::Read)?;
        Ok(Value::Nil)
    });
}

// ----- construction ----------------------------------------------------------------

fn tcp_connect(interp: &Interp, args: &Args) -> EvalResult {
    let host = string(interp, args.arg(0), "host")?.to_string();
    let port = int(interp, args.arg(1), "port")?;
    let label = format!("{host}:{port}");
    let stream = interp
        .block_on(move || TcpStream::connect((host.as_str(), port as u16)))?
        .map_err(|e| os_error(interp, e, &label))?;
    stream
        .set_nonblocking(true)
        .map_err(|e| os_error(interp, e, &label))?;
    let _ = stream.set_nodelay(true);
    Ok(make_socket(interp, Stream::Tcp(stream), None))
}

fn unix_connect(interp: &Interp, args: &Args) -> EvalResult {
    let path = string(interp, args.arg(0), "path")?;
    let stream = UnixStream::connect(path).map_err(|e| os_error(interp, e, path))?;
    stream
        .set_nonblocking(true)
        .map_err(|e| os_error(interp, e, path))?;
    Ok(make_socket(
        interp,
        Stream::Unix(stream),
        Some(path.to_string()),
    ))
}

fn udp_bind(interp: &Interp, addr: &str) -> Result<UdpSocket, Flow> {
    let socket = UdpSocket::bind(addr).map_err(|e| os_error(interp, e, addr))?;
    socket
        .set_nonblocking(true)
        .map_err(|e| os_error(interp, e, addr))?;
    Ok(socket)
}

fn make_socket(interp: &Interp, stream: Stream, path: Option<String>) -> Value {
    interp.sched.borrow().register(stream.fd());
    let (local, peer, unix) = match &stream {
        Stream::Tcp(s) => (s.local_addr().ok(), s.peer_addr().ok(), false),
        Stream::Unix(_) => (None, None, true),
    };
    io(IoKind::Socket(RefCell::new(SocketState {
        stream: Some(stream),
        unix,
        rbuf: Vec::new(),
        eof: false,
        closed: false,
        path,
        local,
        peer,
    })))
}

fn make_listener(interp: &Interp, listener: Listener, path: Option<String>) -> Value {
    interp.sched.borrow().register(listener.fd());
    let unix = matches!(listener, Listener::Unix(_));
    io(IoKind::Listener(RefCell::new(ListenerState {
        listener: Some(listener),
        unix,
        closed: false,
        path,
    })))
}

/// `open` with a block: yield the socket and close it afterwards.
fn with_closing(interp: &Interp, sock: Value, args: &Args) -> EvalResult {
    let Some(b) = &args.block else {
        return Ok(sock);
    };
    let result = interp.call_block(b, smallvec![sock.clone()]);
    let _ = close(interp, &sock);
    result
}

/// Resolve `host:port` on a helper thread.
fn resolve(interp: &Interp, host: &str, port: i64) -> Result<SocketAddr, Flow> {
    use std::net::ToSocketAddrs;
    let label = format!("{host}:{port}");
    let host = host.to_string();
    let addrs = interp
        .block_on(move || {
            (host.as_str(), port as u16)
                .to_socket_addrs()
                .map(|a| a.collect::<Vec<_>>())
        })?
        .map_err(|e| os_error(interp, e, &label))?;
    addrs.into_iter().next().ok_or_else(|| {
        interp.raise(
            interp.exc.system_call_error,
            &format!("{label}: no address"),
        )
    })
}

fn listener_accept(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let IoKind::Listener(st) = &io_of(interp, recv)?.kind else {
        return Err(interp.err_type("not a server socket"));
    };
    loop {
        let accepted = {
            let s = st.borrow();
            let Some(listener) = s.listener.as_ref() else {
                return Err(interp.raise(interp.exc.io_error, "closed stream"));
            };
            match listener {
                Listener::Tcp(l) => l.accept().map(|(s, _)| Stream::Tcp(s)),
                Listener::Unix(l) => l.accept().map(|(s, _)| Stream::Unix(s)),
            }
        };
        match accepted {
            Ok(stream) => {
                let path = st.borrow().path.clone();
                let label = path.clone().unwrap_or_else(|| "accept".to_string());
                match &stream {
                    Stream::Tcp(s) => {
                        s.set_nonblocking(true)
                            .map_err(|e| os_error(interp, e, &label))?;
                        let _ = s.set_nodelay(true);
                    }
                    Stream::Unix(s) => s
                        .set_nonblocking(true)
                        .map_err(|e| os_error(interp, e, &label))?,
                }
                return Ok(make_socket(interp, stream, path));
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                let fd = listener_fd(interp, st)?;
                interp.wait_fd(fd, false)?
            }
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(os_error(interp, e, "accept")),
        }
    }
}

// ----- stream operations (used by the IO natives) ---------------------------------

fn socket<'a>(interp: &Interp, v: &'a Value) -> Result<&'a RefCell<SocketState>, Flow> {
    match &io_of(interp, v)?.kind {
        IoKind::Socket(st) => Ok(st),
        _ => Err(interp.err_type("not a stream socket")),
    }
}

fn udp<'a>(interp: &Interp, v: &'a Value) -> Result<&'a RefCell<UdpState>, Flow> {
    match &io_of(interp, v)?.kind {
        IoKind::Udp(st) => Ok(st),
        _ => Err(interp.err_type("not a UDP socket")),
    }
}

fn socket_fd(interp: &Interp, st: &RefCell<SocketState>) -> Result<RawFd, Flow> {
    match &st.borrow().stream {
        Some(s) => Ok(s.fd()),
        None => Err(interp.raise(interp.exc.io_error, "closed stream")),
    }
}

fn listener_fd(interp: &Interp, st: &RefCell<ListenerState>) -> Result<RawFd, Flow> {
    match &st.borrow().listener {
        Some(l) => Ok(l.fd()),
        None => Err(interp.raise(interp.exc.io_error, "closed stream")),
    }
}

fn udp_fd(interp: &Interp, st: &RefCell<UdpState>) -> Result<RawFd, Flow> {
    match &st.borrow().socket {
        Some(s) => Ok(s.as_raw_fd()),
        None => Err(interp.raise(interp.exc.io_error, "closed stream")),
    }
}

/// Read more bytes into the buffer; `false` at the end of the stream.
fn fill(interp: &Interp, st: &RefCell<SocketState>) -> Result<bool, Flow> {
    let fd = socket_fd(interp, st)?;
    let mut chunk = [0u8; 8192];
    loop {
        if st.borrow().eof {
            return Ok(false);
        }
        let r = {
            let mut s = st.borrow_mut();
            let Some(stream) = s.stream.as_mut() else {
                return Err(interp.raise(interp.exc.io_error, "closed stream"));
            };
            stream.read(&mut chunk)
        };
        match r {
            Ok(0) => {
                st.borrow_mut().eof = true;
                return Ok(false);
            }
            Ok(n) => {
                st.borrow_mut().rbuf.extend_from_slice(&chunk[..n]);
                return Ok(true);
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => interp.wait_fd(fd, false)?,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(os_error(interp, e, "read")),
        }
    }
}

/// One line including its newline; `None` at the end of the stream.
pub fn socket_gets(interp: &Interp, st: &RefCell<SocketState>) -> Result<Option<String>, Flow> {
    loop {
        {
            let mut s = st.borrow_mut();
            if let Some(pos) = s.rbuf.iter().position(|b| *b == b'\n') {
                let line: Vec<u8> = s.rbuf.drain(..=pos).collect();
                return Ok(Some(String::from_utf8_lossy(&line).into_owned()));
            }
        }
        if !fill(interp, st)? {
            let mut s = st.borrow_mut();
            if s.rbuf.is_empty() {
                return Ok(None);
            }
            let rest = std::mem::take(&mut s.rbuf);
            return Ok(Some(String::from_utf8_lossy(&rest).into_owned()));
        }
    }
}

/// Everything up to the end of the stream, or up to `limit` bytes.
pub fn socket_read(
    interp: &Interp,
    st: &RefCell<SocketState>,
    limit: Option<usize>,
) -> Result<Vec<u8>, Flow> {
    loop {
        if let Some(n) = limit {
            if st.borrow().rbuf.len() >= n {
                return Ok(st.borrow_mut().rbuf.drain(..n).collect());
            }
        }
        if !fill(interp, st)? {
            return Ok(std::mem::take(&mut st.borrow_mut().rbuf));
        }
    }
}

/// Whatever is available, up to `max` bytes (one read when the buffer is
/// empty); `None` at the end of the stream.
pub fn socket_read_partial(
    interp: &Interp,
    st: &RefCell<SocketState>,
    max: usize,
) -> Result<Option<Vec<u8>>, Flow> {
    if st.borrow().rbuf.is_empty() && !fill(interp, st)? {
        return Ok(None);
    }
    let mut s = st.borrow_mut();
    let n = max.min(s.rbuf.len());
    Ok(Some(s.rbuf.drain(..n).collect()))
}

pub fn socket_write(interp: &Interp, st: &RefCell<SocketState>, data: &[u8]) -> Result<(), Flow> {
    let fd = socket_fd(interp, st)?;
    let mut written = 0;
    while written < data.len() {
        let r = {
            let mut s = st.borrow_mut();
            let Some(stream) = s.stream.as_mut() else {
                return Err(interp.raise(interp.exc.io_error, "closed stream"));
            };
            stream.write(&data[written..])
        };
        match r {
            Ok(0) => return Err(interp.raise(interp.exc.io_error, "connection closed")),
            Ok(n) => written += n,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => interp.wait_fd(fd, true)?,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(os_error(interp, e, "write")),
        }
    }
    Ok(())
}

pub fn socket_eof(interp: &Interp, st: &RefCell<SocketState>) -> Result<bool, Flow> {
    if !st.borrow().rbuf.is_empty() {
        return Ok(false);
    }
    Ok(!fill(interp, st)?)
}

/// `readpartial` / `read_bytes` for any stream kind.
fn read_partial(interp: &Interp, recv: &Value, max: usize) -> Result<Option<Vec<u8>>, Flow> {
    match &io_of(interp, recv)?.kind {
        IoKind::Socket(st) => socket_read_partial(interp, st, max),
        _ => {
            let text = super::io::read_limited(interp, recv, max)?;
            Ok(text.map(|t| t.into_bytes()))
        }
    }
}

fn shutdown(interp: &Interp, recv: &Value, how: std::net::Shutdown) -> Result<(), Flow> {
    let st = socket(interp, recv)?;
    let s = st.borrow();
    let r = match &s.stream {
        Some(Stream::Tcp(t)) => t.shutdown(how),
        Some(Stream::Unix(u)) => u.shutdown(how),
        None => return Err(interp.raise(interp.exc.io_error, "closed stream")),
    };
    r.map_err(|e| os_error(interp, e, "shutdown"))
}

/// Close any socket kind: deregister from the reactor, then release the
/// descriptor.
pub fn close(interp: &Interp, recv: &Value) -> Result<(), Flow> {
    match &io_of(interp, recv)?.kind {
        IoKind::Socket(st) => {
            let mut s = st.borrow_mut();
            if let Some(stream) = s.stream.take() {
                interp.sched.borrow_mut().deregister(stream.fd());
                let _ = match &stream {
                    Stream::Tcp(t) => t.shutdown(std::net::Shutdown::Both),
                    Stream::Unix(u) => u.shutdown(std::net::Shutdown::Both),
                };
            }
            s.closed = true;
        }
        IoKind::Listener(st) => {
            let mut s = st.borrow_mut();
            if let Some(listener) = s.listener.take() {
                interp.sched.borrow_mut().deregister(listener.fd());
                if let (Listener::Unix(_), Some(path)) = (&listener, &s.path) {
                    let _ = std::fs::remove_file(path);
                }
            }
            s.closed = true;
        }
        IoKind::Udp(st) => {
            let mut s = st.borrow_mut();
            if let Some(socket) = s.socket.take() {
                interp.sched.borrow_mut().deregister(socket.as_raw_fd());
            }
            s.closed = true;
        }
        _ => {}
    }
    Ok(())
}

pub fn is_closed(io: &IoVal) -> bool {
    match &io.kind {
        IoKind::Socket(st) => st.borrow().closed,
        IoKind::Listener(st) => st.borrow().closed,
        IoKind::Udp(st) => st.borrow().closed,
        IoKind::File(f) => f.borrow().closed,
        _ => false,
    }
}

pub fn socket_path(io: &IoVal) -> Option<String> {
    match &io.kind {
        IoKind::Socket(st) => st.borrow().path.clone(),
        IoKind::Listener(st) => st.borrow().path.clone(),
        _ => None,
    }
}

// ----- UDP ---------------------------------------------------------------------------

fn udp_recv(
    interp: &Interp,
    recv: &Value,
    args: &Args,
    with_addr: bool,
    binary: bool,
) -> EvalResult {
    let max = int(interp, args.arg(0), "length")?.max(0) as usize;
    let st = udp(interp, recv)?;
    let fd = udp_fd(interp, st)?;
    let mut buf = vec![0u8; max.max(1)];
    loop {
        let r = {
            let s = st.borrow();
            let Some(socket) = s.socket.as_ref() else {
                return Err(interp.raise(interp.exc.io_error, "closed stream"));
            };
            socket.recv_from(&mut buf)
        };
        match r {
            Ok((n, from)) => {
                buf.truncate(n);
                let data = if binary {
                    Value::bytes(buf)
                } else {
                    Value::string(String::from_utf8_lossy(&buf).into_owned())
                };
                return Ok(if with_addr {
                    Value::array(vec![data, addr_value(from)])
                } else {
                    data
                });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => interp.wait_fd(fd, false)?,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(os_error(interp, e, "recv")),
        }
    }
}

// ----- helpers ---------------------------------------------------------------------

/// The bytes of a String or Bytes argument.
pub fn payload(interp: &Interp, v: &Value) -> Result<Vec<u8>, Flow> {
    Ok(match v {
        Value::Bytes(b) => b.to_vec(),
        other => interp.to_s(other)?.as_bytes().to_vec(),
    })
}

fn addr_value(addr: SocketAddr) -> Value {
    Value::array(vec![
        Value::string(addr.ip().to_string()),
        Value::Int(addr.port() as i64),
    ])
}

pub fn inspect_socket(interp: &Interp, io: &Rc<IoVal>) -> String {
    let closed = if is_closed(io) { " (closed)" } else { "" };
    match &io.kind {
        IoKind::Socket(st) => {
            let s = st.borrow();
            if s.unix {
                format!(
                    "#<UNIXSocket {}{closed}>",
                    s.path.clone().unwrap_or_default()
                )
            } else {
                format!(
                    "#<TCPSocket {}{closed}>",
                    s.peer.map(|a| a.to_string()).unwrap_or_default()
                )
            }
        }
        IoKind::Listener(st) => {
            let s = st.borrow();
            if s.unix {
                format!(
                    "#<UNIXServer {}{closed}>",
                    s.path.clone().unwrap_or_default()
                )
            } else {
                let addr = match &s.listener {
                    Some(Listener::Tcp(l)) => l.local_addr().map(|a| a.to_string()).ok(),
                    _ => None,
                };
                format!("#<TCPServer {}{closed}>", addr.unwrap_or_default())
            }
        }
        IoKind::Udp(st) => format!(
            "#<UDPSocket {}{closed}>",
            st.borrow()
                .socket
                .as_ref()
                .and_then(|s| s.local_addr().ok())
                .map(|a| a.to_string())
                .unwrap_or_default()
        ),
        _ => interp.class_name(&Value::Io(io.clone())),
    }
}
