//! Sockets: TCPSocket, TCPServer, UDPSocket, UNIXSocket and UNIXServer,
//! and the primitives of the `Socket` module (whose `tcp`, written in
//! the prelude, races connections to a host's addresses).
//!
//! Every socket is non-blocking. An operation that would block parks the
//! task on the scheduler's reactor until the descriptor is ready, so
//! only the calling task waits: a TCP `connect` too, which waits for the
//! socket to become writable. Name resolution runs on a helper thread
//! for the same reason. `close` releases the descriptor at once rather
//! than when the value is dropped.

use crate::rc::Rc;
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::os::fd::{AsRawFd, RawFd};
use std::os::unix::net::{UnixListener, UnixStream};

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::io::{io, io_of, os_error};
use super::{int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    // Socket
    native!(m, "Socket.getaddrinfo", |i, _, a| {
        let host = string(i, a.arg(0), "host")?.to_string();
        let port = port_number(i, a.arg(1))?;
        let family = match a.pos.get(2) {
            None | Some(Value::Nil) => libc::AF_UNSPEC,
            Some(v) => match int(i, v, "family")? {
                4 => libc::AF_INET,
                6 => libc::AF_INET6,
                _ => return Err(i.err_arg("family: 4, 6 or nil")),
            },
        };
        let addrs = getaddrinfo(i, host, port, family)?;
        Ok(Value::array(
            addrs
                .into_iter()
                .map(|a| address_value(i, a))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    });
    // TCPSocket
    native!(m, "TCPSocket.connect", |i, _, a| {
        let addr = address_of(i, a.arg(0))?;
        tcp_connect(i, addr)
    });
    // TCPServer
    native!(m, "TCPServer.new", |i, _, a| {
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
    native!(m, "TCPServer#accept", listener_accept);
    native!(m, "UNIXServer#accept", listener_accept);
    // UNIXSocket / UNIXServer
    native!(m, "UNIXSocket.new", |i, _, a| unix_connect(i, &a));
    native!(m, "UNIXSocket.open", |i, _, a| {
        let sock = unix_connect(i, &a)?;
        with_closing(i, sock, &a)
    });
    native!(m, "UNIXServer.new", |i, _, a| {
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
    native!(m, "UDPSocket.new", |i, _, _| {
        let socket = udp_bind(i, "0.0.0.0:0")?;
        Ok(io(IoKind::Udp(IoCell::new(UdpState {
            socket: Some(socket),
            closed: false,
            watch: IoWatch::new(),
        }))))
    });
    native!(m, "UDPSocket#bind", |i, r, a| {
        // Binding after creation replaces the descriptor.
        let host = string(i, a.arg(0), "host")?;
        let port = int(i, a.arg(1), "port")?;
        let st = udp(i, r)?;
        let socket = udp_bind(i, &format!("{host}:{port}"))?;
        let old_fd = udp_fd(i, st)?;
        let waiters = {
            let mut s = st.borrow_mut();
            i.sched.borrow_mut().deregister(old_fd);
            s.socket = Some(socket);
            // A new descriptor: it is registered anew where waited on.
            std::mem::take(&mut s.watch).waiters
        };
        for w in waiters {
            i.wake_ref(w);
        }
        Ok(Value::Nil)
    });
    native!(m, "UDPSocket#connect", |i, r, a| {
        let host = string(i, a.arg(0), "host")?.to_string();
        let port = int(i, a.arg(1), "port")?;
        let addr = resolve(i, &host, port)?;
        let st = udp(i, r)?;
        let r = match &st.borrow().socket {
            Some(s) => s.connect(addr),
            None => return Err(i.raise(i.program.exc.io_error, "closed stream")),
        };
        r.map_err(|e| os_error(i, e, &format!("{host}:{port}")))?;
        Ok(Value::Nil)
    });
    native!(m, "UDPSocket#send", |i, r, a| {
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
                    return Err(i.raise(i.program.exc.io_error, "closed stream"));
                };
                match target {
                    Some(addr) => socket.send_to(&data, addr),
                    None => socket.send(&data),
                }
            };
            match r {
                Ok(n) => return Ok(Value::Int(n as i64)),
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => i.wait_io(st, fd, true)?,
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(os_error(i, e, "send")),
            }
        }
    });
    native!(m, "UDPSocket#recvfrom", |i, r, a| {
        udp_recv(i, r, &a, true, false)
    });
    native!(m, "UDPSocket#recvfrom_bytes", |i, r, a| {
        udp_recv(i, r, &a, true, true)
    });
    native!(m, "UDPSocket#recv", |i, r, a| udp_recv(
        i, r, &a, false, false
    ));
    native!(m, "UDPSocket#recv_bytes", |i, r, a| {
        udp_recv(i, r, &a, false, true)
    });
    // Addresses.
    native!(
        m,
        [
            "TCPSocket#local_address",
            "TCPServer#local_address",
            "UDPSocket#local_address"
        ],
        |i, r, _| {
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
            match addr {
                Some(a) => address_value(i, a),
                None => Ok(Value::Nil),
            }
        }
    );
    native!(m, "TCPSocket#remote_address", |i, r, _| {
        match &io_of(i, r)?.kind {
            IoKind::Socket(st) => {
                let peer = st.borrow().peer;
                match peer {
                    Some(a) => address_value(i, a),
                    None => Ok(Value::Nil),
                }
            }
            _ => Err(i.err_type("not a socket")),
        }
    });
    // Streams in general (sockets and files).
    native!(m, "IO#readpartial", |i, r, a| {
        let max = int(i, a.arg(0), "length")?.max(0) as usize;
        match read_partial(i, r, max)? {
            Some(bytes) => Ok(Value::string(String::from_utf8_lossy(&bytes).into_owned())),
            None => Err(i.raise(i.program.exc.eof_error, "end of file reached")),
        }
    });
    native!(m, "IO#readpartial?", |i, r, a| {
        let max = int(i, a.arg(0), "length")?.max(0) as usize;
        Ok(match read_partial(i, r, max)? {
            Some(bytes) => Value::string(String::from_utf8_lossy(&bytes).into_owned()),
            None => Value::Nil,
        })
    });
    native!(m, "IO#read_bytes", |i, r, a| {
        let max = int(i, a.arg(0), "length")?.max(0) as usize;
        Ok(Value::bytes(read_partial(i, r, max)?.unwrap_or_default()))
    });
    native!(m, "IO#close_write", |i, r, _| {
        shutdown(i, r, std::net::Shutdown::Write)?;
        Ok(Value::Nil)
    });
    native!(m, "IO#close_read", |i, r, _| {
        shutdown(i, r, std::net::Shutdown::Read)?;
        Ok(Value::Nil)
    });
}

// ----- construction ----------------------------------------------------------------

/// Connect to one address without blocking the thread: start the
/// connection, wait for the socket to become writable (only this task
/// waits; `Task.timeout` and `cancel` interrupt it, closing the socket),
/// then read the outcome.
fn tcp_connect(interp: &Interp, addr: SocketAddr) -> EvalResult {
    use std::os::fd::FromRawFd;
    let label = addr.to_string();
    let domain = if addr.is_ipv6() {
        libc::AF_INET6
    } else {
        libc::AF_INET
    };
    // SAFETY: plain system calls; the descriptor is owned by the stream
    // from here on (closed when it is dropped, on every error path).
    let fd = unsafe {
        libc::socket(
            domain,
            libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
            0,
        )
    };
    if fd < 0 {
        return Err(os_error(interp, std::io::Error::last_os_error(), &label));
    }
    let stream = unsafe { TcpStream::from_raw_fd(fd) };
    let (storage, len) = sockaddr_of(addr);
    let r = unsafe {
        libc::connect(
            fd,
            &storage as *const libc::sockaddr_storage as *const libc::sockaddr,
            len,
        )
    };
    if r < 0 {
        let e = std::io::Error::last_os_error();
        if e.raw_os_error() != Some(libc::EINPROGRESS) {
            return Err(os_error(interp, e, &label));
        }
    }
    let sock = make_socket(interp, Stream::Tcp(stream), None);
    if r < 0 {
        let st = socket(interp, &sock)?;
        // Until the connection is made or fails: a wake that is not the
        // socket's (a cancellation, in `Task.uncancellable`) finds it still
        // in progress.
        let waited = loop {
            if let Err(e) = interp.wait_io(st, fd, true) {
                break Err(e);
            }
            let mut err: libc::c_int = 0;
            let mut n = std::mem::size_of::<libc::c_int>() as libc::socklen_t;
            // SAFETY: reads an int option into `err`.
            let r = unsafe {
                libc::getsockopt(
                    fd,
                    libc::SOL_SOCKET,
                    libc::SO_ERROR,
                    &mut err as *mut libc::c_int as *mut libc::c_void,
                    &mut n,
                )
            };
            if r < 0 {
                break Err(os_error(interp, std::io::Error::last_os_error(), &label));
            }
            if err != 0 {
                break Err(os_error(
                    interp,
                    std::io::Error::from_raw_os_error(err),
                    &label,
                ));
            }
            // SAFETY: writes at most `len` bytes of a peer address.
            let mut peer: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
            let mut len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
            let r = unsafe {
                libc::getpeername(
                    fd,
                    &mut peer as *mut libc::sockaddr_storage as *mut libc::sockaddr,
                    &mut len,
                )
            };
            if r == 0 {
                break Ok(());
            }
            let e = std::io::Error::last_os_error();
            if e.raw_os_error() != Some(libc::ENOTCONN) {
                break Err(os_error(interp, e, &label));
            }
        };
        if let Err(e) = waited {
            let _ = close(interp, &sock);
            return Err(e);
        }
        // The addresses, now that there is a connection.
        let mut s = st.borrow_mut();
        if let Some(Stream::Tcp(t)) = &s.stream {
            let (local, peer) = (t.local_addr().ok(), t.peer_addr().ok());
            s.local = local;
            s.peer = peer;
        }
    }
    if let Some(Stream::Tcp(t)) = &socket(interp, &sock)?.borrow().stream {
        let _ = t.set_nodelay(true);
    }
    Ok(sock)
}

/// `addr` as a C socket address.
fn sockaddr_of(addr: SocketAddr) -> (libc::sockaddr_storage, libc::socklen_t) {
    // SAFETY: an all-zero sockaddr_storage is valid, and each arm writes a
    // sockaddr that fits in it.
    let mut storage: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
    let len = match addr {
        SocketAddr::V4(a) => {
            let sin = libc::sockaddr_in {
                sin_family: libc::AF_INET as libc::sa_family_t,
                sin_port: a.port().to_be(),
                sin_addr: libc::in_addr {
                    s_addr: u32::from_ne_bytes(a.ip().octets()),
                },
                sin_zero: [0; 8],
            };
            unsafe { std::ptr::write(&mut storage as *mut _ as *mut libc::sockaddr_in, sin) };
            std::mem::size_of::<libc::sockaddr_in>()
        }
        SocketAddr::V6(a) => {
            let sin6 = libc::sockaddr_in6 {
                sin6_family: libc::AF_INET6 as libc::sa_family_t,
                sin6_port: a.port().to_be(),
                sin6_flowinfo: a.flowinfo(),
                sin6_addr: libc::in6_addr {
                    s6_addr: a.ip().octets(),
                },
                sin6_scope_id: a.scope_id(),
            };
            unsafe { std::ptr::write(&mut storage as *mut _ as *mut libc::sockaddr_in6, sin6) };
            std::mem::size_of::<libc::sockaddr_in6>()
        }
    };
    (storage, len as libc::socklen_t)
}

/// The addresses of `host` for `port` in `family` (`AF_INET`, `AF_INET6`
/// or `AF_UNSPEC`), in the resolver's order: at once for a numeric
/// address, else on a helper thread. A failure is a `SocketError` (as
/// for a family the host has no address in).
fn getaddrinfo(
    interp: &Interp,
    host: String,
    port: u16,
    family: libc::c_int,
) -> Result<Vec<SocketAddr>, Flow> {
    if let Ok(ip) = host.parse::<std::net::IpAddr>() {
        let fits = match family {
            libc::AF_INET => ip.is_ipv4(),
            libc::AF_INET6 => ip.is_ipv6(),
            _ => true,
        };
        return Ok(if fits {
            vec![SocketAddr::new(ip, port)]
        } else {
            Vec::new()
        });
    }
    let label = host.clone();
    let found = interp.block_on(move || lookup(&host, port, family))?;
    found.map_err(|e| {
        interp.raise(
            interp.program.exc.socket_error,
            &format!("getaddrinfo: {label}: {e}"),
        )
    })
}

/// `getaddrinfo(3)` for stream sockets.
fn lookup(host: &str, port: u16, family: libc::c_int) -> Result<Vec<SocketAddr>, String> {
    let c_host = std::ffi::CString::new(host).map_err(|_| "a NUL in the host name".to_string())?;
    // SAFETY: the hints are zeroed but for what is set; the result list is
    // read, then freed once.
    unsafe {
        let mut hints: libc::addrinfo = std::mem::zeroed();
        hints.ai_family = family;
        // No `AI_ADDRCONFIG`: on a host whose only IPv6 address is the
        // loopback's, it would hide `::1` for `localhost` (an attempt to
        // an unreachable family fails at once anyway).
        hints.ai_socktype = libc::SOCK_STREAM;
        let mut res: *mut libc::addrinfo = std::ptr::null_mut();
        let rc = libc::getaddrinfo(c_host.as_ptr(), std::ptr::null(), &hints, &mut res);
        if rc != 0 {
            let msg = std::ffi::CStr::from_ptr(libc::gai_strerror(rc));
            return Err(msg.to_string_lossy().into_owned());
        }
        let mut out = Vec::new();
        let mut p = res;
        while !p.is_null() {
            let ai = &*p;
            if !ai.ai_addr.is_null() {
                match ai.ai_family {
                    libc::AF_INET => {
                        let sin = &*(ai.ai_addr as *const libc::sockaddr_in);
                        let ip = std::net::Ipv4Addr::from(sin.sin_addr.s_addr.to_ne_bytes());
                        out.push(SocketAddr::new(ip.into(), port));
                    }
                    libc::AF_INET6 => {
                        let sin6 = &*(ai.ai_addr as *const libc::sockaddr_in6);
                        let ip = std::net::Ipv6Addr::from(sin6.sin6_addr.s6_addr);
                        out.push(SocketAddr::V6(std::net::SocketAddrV6::new(
                            ip,
                            port,
                            sin6.sin6_flowinfo,
                            sin6.sin6_scope_id,
                        )));
                    }
                    _ => {}
                }
            }
            p = ai.ai_next;
        }
        libc::freeaddrinfo(res);
        out.dedup();
        Ok(out)
    }
}

fn port_number(interp: &Interp, v: &Value) -> Result<u16, Flow> {
    let port = int(interp, v, "port")?;
    u16::try_from(port).map_err(|_| interp.err_arg(&format!("port {port} out of range")))
}

/// A `Socket::Address` as a socket address (its host is numeric).
fn address_of(interp: &Interp, v: &Value) -> Result<SocketAddr, Flow> {
    let Value::Object(obj) = v else {
        return Err(interp.err_type("expected a Socket::Address"));
    };
    let host = obj.field(0).unwrap_or(Value::Nil);
    let host = string(interp, &host, "host")?;
    let port = port_number(interp, &obj.field(1).unwrap_or(Value::Nil))?;
    let ip: std::net::IpAddr = host
        .parse()
        .map_err(|_| interp.err_arg(&format!("not a numeric address: {host}")))?;
    Ok(SocketAddr::new(ip, port))
}

/// `addr` as a `Socket::Address`.
fn address_value(interp: &Interp, addr: SocketAddr) -> EvalResult {
    let value = interp.construct(
        interp.program.rt.socket_address,
        None,
        smallvec![],
        Vec::new(),
        None,
    )?;
    if let Value::Object(obj) = &value {
        obj.set_field(0, Value::string(addr.ip().to_string()));
        obj.set_field(1, Value::Int(addr.port() as i64));
    }
    Ok(value)
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

pub(crate) fn make_socket(_: &Interp, stream: Stream, path: Option<String>) -> Value {
    let (local, peer, unix) = match &stream {
        Stream::Tcp(s) => (s.local_addr().ok(), s.peer_addr().ok(), false),
        Stream::Unix(_) => (None, None, true),
    };
    io(IoKind::Socket(IoCell::new(SocketState {
        stream: Some(stream),
        unix,
        rbuf: Vec::new(),
        eof: false,
        closed: false,
        path,
        local,
        peer,
        writing: false,
        write_waiters: std::collections::VecDeque::new(),
        watch: IoWatch::new(),
    })))
}

fn make_listener(_: &Interp, listener: Listener, path: Option<String>) -> Value {
    let unix = matches!(listener, Listener::Unix(_));
    io(IoKind::Listener(IoCell::new(ListenerState {
        listener: Some(listener),
        unix,
        closed: false,
        path,
        watch: IoWatch::new(),
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
            interp.program.exc.system_call_error,
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
                return Err(interp.raise(interp.program.exc.io_error, "closed stream"));
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
                interp.wait_io(st, fd, false)?
            }
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(os_error(interp, e, "accept")),
        }
    }
}

// ----- stream operations (used by the IO natives) ---------------------------------

fn socket<'a>(interp: &Interp, v: &'a Value) -> Result<&'a IoCell<SocketState>, Flow> {
    match &io_of(interp, v)?.kind {
        IoKind::Socket(st) => Ok(st),
        _ => Err(interp.err_type("not a stream socket")),
    }
}

fn udp<'a>(interp: &Interp, v: &'a Value) -> Result<&'a IoCell<UdpState>, Flow> {
    match &io_of(interp, v)?.kind {
        IoKind::Udp(st) => Ok(st),
        _ => Err(interp.err_type("not a UDP socket")),
    }
}

fn socket_fd(interp: &Interp, st: &IoCell<SocketState>) -> Result<RawFd, Flow> {
    match &st.borrow().stream {
        Some(s) => Ok(s.fd()),
        None => Err(interp.raise(interp.program.exc.io_error, "closed stream")),
    }
}

fn listener_fd(interp: &Interp, st: &IoCell<ListenerState>) -> Result<RawFd, Flow> {
    match &st.borrow().listener {
        Some(l) => Ok(l.fd()),
        None => Err(interp.raise(interp.program.exc.io_error, "closed stream")),
    }
}

fn udp_fd(interp: &Interp, st: &IoCell<UdpState>) -> Result<RawFd, Flow> {
    match &st.borrow().socket {
        Some(s) => Ok(s.as_raw_fd()),
        None => Err(interp.raise(interp.program.exc.io_error, "closed stream")),
    }
}

/// Read from the socket until `take` can take what it wants from the
/// buffer (it sees `eof` once the stream has ended). Taking, and reading
/// more when it cannot, happen under the state's lock, released only to
/// wait for the socket: with tasks on several threads, a read call takes
/// a whole unit (a line, all of the rest) however they interleave.
fn read_with<R>(
    interp: &Interp,
    st: &IoCell<SocketState>,
    mut take: impl FnMut(&mut SocketState) -> Option<R>,
) -> Result<R, Flow> {
    let mut chunk = [0u8; 8192];
    loop {
        let fd = {
            let mut s = st.borrow_mut();
            loop {
                if let Some(r) = take(&mut s) {
                    return Ok(r);
                }
                let Some(stream) = s.stream.as_mut() else {
                    return Err(interp.raise(interp.program.exc.io_error, "closed stream"));
                };
                match stream.read(&mut chunk) {
                    Ok(0) => s.eof = true,
                    Ok(n) => s.rbuf.extend_from_slice(&chunk[..n]),
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break stream.fd(),
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                    Err(e) => {
                        drop(s);
                        return Err(os_error(interp, e, "read"));
                    }
                }
            }
        };
        interp.wait_io(st, fd, false)?;
    }
}

/// One line including its newline; `None` at the end of the stream.
pub fn socket_gets(interp: &Interp, st: &IoCell<SocketState>) -> Result<Option<String>, Flow> {
    read_with(interp, st, |s| {
        if let Some(pos) = s.rbuf.iter().position(|b| *b == b'\n') {
            let line: Vec<u8> = s.rbuf.drain(..=pos).collect();
            return Some(Some(String::from_utf8_lossy(&line).into_owned()));
        }
        if !s.eof {
            return None;
        }
        if s.rbuf.is_empty() {
            return Some(None);
        }
        let rest = std::mem::take(&mut s.rbuf);
        Some(Some(String::from_utf8_lossy(&rest).into_owned()))
    })
}

/// Everything up to the end of the stream, or up to `limit` bytes.
pub fn socket_read(
    interp: &Interp,
    st: &IoCell<SocketState>,
    limit: Option<usize>,
) -> Result<Vec<u8>, Flow> {
    read_with(interp, st, |s| {
        if let Some(n) = limit {
            if s.rbuf.len() >= n {
                return Some(s.rbuf.drain(..n).collect());
            }
        }
        s.eof.then(|| std::mem::take(&mut s.rbuf))
    })
}

/// Whatever is available, up to `max` bytes (one read when the buffer is
/// empty); `None` at the end of the stream.
pub fn socket_read_partial(
    interp: &Interp,
    st: &IoCell<SocketState>,
    max: usize,
) -> Result<Option<Vec<u8>>, Flow> {
    read_with(interp, st, |s| {
        if !s.rbuf.is_empty() {
            let n = max.min(s.rbuf.len());
            return Some(Some(s.rbuf.drain(..n).collect()));
        }
        s.eof.then_some(None)
    })
}

/// Write all of `data`. A write that has to wait for the socket keeps
/// its turn: another task's write waits until this one is done, so the
/// bytes of one call are never interleaved with another's.
pub fn socket_write(interp: &Interp, st: &IoCell<SocketState>, data: &[u8]) -> Result<(), Flow> {
    let me = interp.sched.borrow().current_ref();
    loop {
        {
            let mut s = st.borrow_mut();
            if !s.writing {
                s.writing = true;
                break;
            }
            // Woken by something else (a cancellation, uncancellable),
            // it may be listed already.
            if !s.write_waiters.contains(&me) {
                s.write_waiters.push_back(me);
            }
        }
        if let Err(flow) = interp.park() {
            // Leaving: a turn this task was woken for (the socket free)
            // goes to the next writer, or nobody would wake it.
            let next = {
                let mut s = st.borrow_mut();
                s.write_waiters.retain(|t| *t != me);
                if s.writing {
                    None
                } else {
                    s.write_waiters.pop_front()
                }
            };
            if let Some(next) = next {
                interp.wake_ref(next);
            }
            return Err(flow);
        }
    }
    let r = socket_write_all(interp, st, data);
    let next = {
        let mut s = st.borrow_mut();
        s.writing = false;
        s.write_waiters.pop_front()
    };
    if let Some(next) = next {
        interp.wake_ref(next);
    }
    r
}

fn socket_write_all(interp: &Interp, st: &IoCell<SocketState>, data: &[u8]) -> Result<(), Flow> {
    let fd = socket_fd(interp, st)?;
    let mut written = 0;
    while written < data.len() {
        let r = {
            let mut s = st.borrow_mut();
            let Some(stream) = s.stream.as_mut() else {
                return Err(interp.raise(interp.program.exc.io_error, "closed stream"));
            };
            stream.write(&data[written..])
        };
        match r {
            Ok(0) => return Err(interp.raise(interp.program.exc.io_error, "connection closed")),
            Ok(n) => written += n,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => interp.wait_io(st, fd, true)?,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(os_error(interp, e, "write")),
        }
    }
    Ok(())
}

pub fn socket_eof(interp: &Interp, st: &IoCell<SocketState>) -> Result<bool, Flow> {
    read_with(interp, st, |s| {
        if !s.rbuf.is_empty() {
            return Some(false);
        }
        s.eof.then_some(true)
    })
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
        None => return Err(interp.raise(interp.program.exc.io_error, "closed stream")),
    };
    r.map_err(|e| os_error(interp, e, "shutdown"))
}

/// Close any socket kind: deregister from the reactor, then release the
/// descriptor.
pub fn close(interp: &Interp, recv: &Value) -> Result<(), Flow> {
    // The tasks waiting on the descriptor, on whatever worker: woken, they
    // find it closed.
    let waiters = match &io_of(interp, recv)?.kind {
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
            let mut w = std::mem::take(&mut s.watch.waiters);
            w.extend(s.write_waiters.drain(..));
            w
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
            std::mem::take(&mut s.watch.waiters)
        }
        IoKind::Udp(st) => {
            let mut s = st.borrow_mut();
            if let Some(socket) = s.socket.take() {
                interp.sched.borrow_mut().deregister(socket.as_raw_fd());
            }
            s.closed = true;
            std::mem::take(&mut s.watch.waiters)
        }
        _ => Vec::new(),
    };
    for w in waiters {
        interp.wake_ref(w);
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
                return Err(interp.raise(interp.program.exc.io_error, "closed stream"));
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
                    Value::array(vec![data, address_value(interp, from)?])
                } else {
                    data
                });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                interp.wait_io(st, fd, false)?
            }
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
