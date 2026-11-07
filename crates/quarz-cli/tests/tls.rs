//! `std/tls.qz` against a rustls server run here: the programs in
//! `tls/` connect to it (its port and the certificates' directory are
//! their arguments) and print their `.out`, interpreted and compiled.
//!
//! The server echoes each line it reads. A line starting with `!` is a
//! command instead: `!big N` writes N bytes (a pattern) and a newline,
//! `!notify` writes `bye` then close_notify, `!abrupt` writes `bye` then
//! closes the TCP connection without close_notify.
//!
//! `QUARZ_TLS_PUBLIC_HOST=example.com` also runs `tls/public.qz` against
//! that host's port 443 with the system's roots (not in CI).
//!
//! The server side: `server*.qz` and `https.qz` listen on port 0, print
//! `port N` and serve a rustls client driven here, then print the rest
//! of their `.out`; `loopback.qz` is a Quarz client and a Quarz server
//! in one program.

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

use rustls::pki_types::pem::PemObject;
use rustls::pki_types::{CertificateDer, PrivateKeyDer};

fn certs_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/tls")
}

fn program(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/tls")
        .join(name)
}

/// Start the server; its port.
fn serve() -> u16 {
    let dir = certs_dir();
    let certs: Vec<CertificateDer<'static>> = CertificateDer::pem_file_iter(dir.join("server.pem"))
        .unwrap()
        .map(|c| c.unwrap())
        .collect();
    let key = PrivateKeyDer::from_pem_file(dir.join("server.key")).unwrap();
    let mut config = rustls::ServerConfig::builder_with_provider(Arc::new(
        rustls::crypto::ring::default_provider(),
    ))
    .with_safe_default_protocol_versions()
    .unwrap()
    .with_no_client_auth()
    .with_single_cert(certs, key)
    .unwrap();
    config.alpn_protocols = vec![b"http/1.1".to_vec()];
    let config = Arc::new(config);
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    std::thread::spawn(move || {
        for conn in listener.incoming() {
            let Ok(conn) = conn else { continue };
            let config = config.clone();
            std::thread::spawn(move || {
                let _ = session(conn, config);
            });
        }
    });
    port
}

/// One connection: echo lines, or run a command (see the module's
/// comment).
fn session(sock: TcpStream, config: Arc<rustls::ServerConfig>) -> std::io::Result<()> {
    let conn = rustls::ServerConnection::new(config).map_err(std::io::Error::other)?;
    let mut tls = rustls::StreamOwned::new(conn, sock);
    let mut line = Vec::new();
    loop {
        line.clear();
        // Byte by byte: what follows a command must stay unread.
        let mut byte = [0u8; 1];
        loop {
            match tls.read(&mut byte) {
                Ok(0) => return Ok(()),
                Ok(_) => {
                    line.push(byte[0]);
                    if byte[0] == b'\n' {
                        break;
                    }
                }
                // The client went without close_notify, or failed the
                // handshake.
                Err(_) => return Ok(()),
            }
        }
        let text = String::from_utf8_lossy(&line).into_owned();
        let cmd = text.trim_end();
        if let Some(n) = cmd.strip_prefix("!big ") {
            let n: usize = n.parse().unwrap();
            let data: Vec<u8> = (0..n).map(|i| b'a' + (i % 26) as u8).collect();
            tls.write_all(&data)?;
            tls.write_all(b"\n")?;
        } else if cmd == "!notify" {
            tls.write_all(b"bye\n")?;
            tls.conn.send_close_notify();
            tls.flush()?;
            // Until the client closes.
            let mut rest = Vec::new();
            let _ = tls.read_to_end(&mut rest);
            return Ok(());
        } else if cmd == "!abrupt" {
            tls.write_all(b"bye\n")?;
            tls.flush()?;
            tls.sock.shutdown(std::net::Shutdown::Both)?;
            return Ok(());
        } else {
            tls.write_all(&line)?;
        }
        tls.flush()?;
    }
}

fn compile(path: &Path) -> (PathBuf, PathBuf) {
    let dir = std::env::temp_dir().join(format!(
        "quarz-tls-test-{}-{}",
        std::process::id(),
        path.file_stem().unwrap().to_string_lossy()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let exe = dir.join(path.file_stem().unwrap());
    let built = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("build")
        .arg(path)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("run quarz build");
    assert!(
        built.status.success(),
        "quarz build {}: {}",
        path.display(),
        String::from_utf8_lossy(&built.stderr)
    );
    (dir, exe)
}

fn check(out: &Output, want: &str, what: &str) {
    assert!(
        out.status.success(),
        "{what} failed: {}\n{}",
        String::from_utf8_lossy(&out.stderr),
        String::from_utf8_lossy(&out.stdout)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), want, "{what}");
}

/// Run `name` with the server's port and the certificates' directory as
/// its arguments, on the VM and compiled, with `threads` workers.
fn prints_its_out(name: &str, threads: &str) {
    let port = serve().to_string();
    let path = program(name);
    let dir = certs_dir();
    let want = std::fs::read_to_string(path.with_extension("out")).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(&path)
        .arg(&port)
        .arg(&dir)
        .env("QUARZ_THREADS", threads)
        .output()
        .expect("run quarz");
    check(&out, &want, &format!("{name} on the VM"));
    let (tmp, exe) = compile(&path);
    let out = Command::new(&exe)
        .arg(&port)
        .arg(&dir)
        .env("QUARZ_THREADS", threads)
        .output()
        .expect("run the executable");
    check(&out, &want, &format!("{name} compiled"));
    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn connects_reads_and_writes() {
    prints_its_out("basic.qz", "1");
}

#[test]
fn refuses_and_fails() {
    prints_its_out("errors.qz", "1");
}

#[test]
fn shared_between_tasks() {
    prints_its_out("shared.qz", "1");
    prints_its_out("shared.qz", "4");
}

#[test]
fn public_host() {
    let Ok(host) = std::env::var("QUARZ_TLS_PUBLIC_HOST") else {
        return;
    };
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(program("public.qz"))
        .arg(&host)
        .output()
        .expect("run quarz");
    check(&out, "HTTP/1.1\ntrue\n", "public.qz");
}

// ----- the server side --------------------------------------------------------------

type Client = rustls::StreamOwned<rustls::ClientConnection, TcpStream>;

/// A rustls client to `port`, trusting `ca` (a file of the certificates'
/// directory), as `name` (an address sends no SNI), offering `alpn`; the
/// handshake is done when it returns.
fn client(port: u16, ca: &str, name: &str, alpn: &[&str]) -> Result<Client, rustls::Error> {
    let mut roots = rustls::RootCertStore::empty();
    for c in CertificateDer::pem_file_iter(certs_dir().join(ca)).unwrap() {
        roots.add(c.unwrap()).unwrap();
    }
    let mut config = rustls::ClientConfig::builder_with_provider(Arc::new(
        rustls::crypto::ring::default_provider(),
    ))
    .with_safe_default_protocol_versions()
    .unwrap()
    .with_root_certificates(roots)
    .with_no_client_auth();
    config.alpn_protocols = alpn.iter().map(|p| p.as_bytes().to_vec()).collect();
    let name = rustls::pki_types::ServerName::try_from(name.to_string()).unwrap();
    let conn = rustls::ClientConnection::new(Arc::new(config), name).unwrap();
    let mut tls = rustls::StreamOwned::new(conn, TcpStream::connect(("127.0.0.1", port)).unwrap());
    while tls.conn.is_handshaking() {
        tls.conn.complete_io(&mut tls.sock).map_err(|e| {
            match e.into_inner().map(|e| e.downcast::<rustls::Error>()) {
                Some(Ok(e)) => *e,
                _ => rustls::Error::General("handshake".to_string()),
            }
        })?;
    }
    Ok(tls)
}

/// A line from `r`, with its newline.
fn line(r: &mut impl Read) -> String {
    let mut out = Vec::new();
    let mut byte = [0u8; 1];
    while r.read(&mut byte).unwrap() == 1 {
        out.push(byte[0]);
        if byte[0] == b'\n' {
            break;
        }
    }
    String::from_utf8(out).unwrap()
}

/// Send close_notify.
fn notify(tls: &mut Client) {
    tls.conn.send_close_notify();
    tls.flush().unwrap();
}

/// Run `name` (with the certificates' directory as its argument) on the
/// VM and compiled: read its port, run `drive` against it, and check that
/// it prints its `.out` after the port line.
fn serves(name: &str, drive: fn(u16)) {
    let path = program(name);
    let want = std::fs::read_to_string(path.with_extension("out")).unwrap();
    let (tmp, exe) = compile(&path);
    let vm = {
        let mut c = Command::new(env!("CARGO_BIN_EXE_quarz"));
        c.arg("run").arg(&path);
        c
    };
    for (what, mut cmd) in [("on the VM", vm), ("compiled", Command::new(&exe))] {
        let mut child = cmd
            .arg(certs_dir())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run the program");
        let mut out = BufReader::new(child.stdout.take().unwrap());
        // What it prints before its port, then the port.
        let mut first = String::new();
        let port: u16 = loop {
            let mut l = String::new();
            if out.read_line(&mut l).unwrap() == 0 {
                let mut err = String::new();
                child
                    .stderr
                    .take()
                    .unwrap()
                    .read_to_string(&mut err)
                    .unwrap();
                panic!("{name} {what}: no port: {first}\n{err}");
            }
            first.push_str(&l);
            if let Some(p) = l.trim_end().strip_prefix("port ") {
                break p.parse().unwrap();
            }
        };
        drive(port);
        let mut rest = String::new();
        out.read_to_string(&mut rest).unwrap();
        let output = child.wait_with_output().unwrap();
        let printed = format!("{}{rest}", first.replace(&format!("{port}"), "N"));
        assert!(
            output.status.success(),
            "{name} {what} failed: {}\n{printed}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(printed, want, "{name} {what}");
    }
    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn serves_reads_and_writes() {
    serves("server.qz", |port| {
        // Echo, 16 KB+ both ways, close_notify from the client.
        let mut tls = client(port, "ca.pem", "localhost", &["h2", "http/1.1"]).unwrap();
        assert_eq!(tls.conn.alpn_protocol(), Some(&b"http/1.1"[..]));
        tls.write_all(b"hello\n").unwrap();
        assert_eq!(line(&mut tls), "hello\n");
        let big = format!("{}\n", "y".repeat(20_000));
        tls.write_all(big.as_bytes()).unwrap();
        assert_eq!(line(&mut tls), big);
        tls.write_all(b"!big 40000\n").unwrap();
        let got = line(&mut tls);
        assert_eq!(got.len(), 40_001);
        assert!(got.starts_with("abcdefghijklmnopqrstuvwxyzabc"));
        notify(&mut tls);
        let mut rest = Vec::new();
        tls.read_to_end(&mut rest).unwrap();
        assert!(rest.is_empty());

        // close_notify from the server: a clean end.
        let mut tls = client(port, "ca.pem", "localhost", &["http/1.1"]).unwrap();
        tls.write_all(b"!notify\n").unwrap();
        assert_eq!(line(&mut tls), "bye\n");
        let mut rest = Vec::new();
        tls.read_to_end(&mut rest).unwrap();
        assert!(rest.is_empty());
        notify(&mut tls);

        // The TCP connection closed without close_notify.
        let mut tls = client(port, "ca.pem", "localhost", &["http/1.1"]).unwrap();
        tls.write_all(b"x\n").unwrap();
        assert_eq!(line(&mut tls), "x\n");
        tls.sock.shutdown(std::net::Shutdown::Both).unwrap();

        // An address: no SNI; no ALPN.
        let mut tls = client(port, "ca.pem", "127.0.0.1", &[]).unwrap();
        assert_eq!(tls.conn.alpn_protocol(), None);
        tls.write_all(b"y\n").unwrap();
        assert_eq!(line(&mut tls), "y\n");
        notify(&mut tls);
        let mut rest = Vec::new();
        tls.read_to_end(&mut rest).unwrap();
    });
}

/// Read `sock` until the server closes it (an error counts: a reset).
fn until_closed(mut sock: TcpStream) -> Vec<u8> {
    let mut got = Vec::new();
    let _ = sock.read_to_end(&mut got);
    got
}

#[test]
fn server_refuses_and_fails() {
    serves("server_errors.qz", |port| {
        // A client that does not trust the certificate.
        assert!(client(port, "other-ca.pem", "localhost", &[]).is_err());
        // Plain text.
        let mut sock = TcpStream::connect(("127.0.0.1", port)).unwrap();
        sock.write_all(b"GET / HTTP/1.0\r\n\r\n").unwrap();
        assert!(!until_closed(sock).starts_with(b"HTTP/"));
        // Nothing sent: the program's `Task.timeout` closes it.
        let start = Instant::now();
        until_closed(TcpStream::connect(("127.0.0.1", port)).unwrap());
        assert!(start.elapsed() >= Duration::from_millis(400));
        // Still accepting.
        let mut tls = client(port, "ca.pem", "localhost", &[]).unwrap();
        assert_eq!(line(&mut tls), "ok\n");
    });
}

#[test]
fn loopback() {
    let path = program("loopback.qz");
    let want = std::fs::read_to_string(path.with_extension("out")).unwrap();
    for threads in ["1", "4"] {
        let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
            .arg("run")
            .arg(&path)
            .arg(certs_dir())
            .env("QUARZ_THREADS", threads)
            .output()
            .expect("run quarz");
        check(
            &out,
            &want,
            &format!("loopback.qz on the VM, {threads} workers"),
        );
    }
    let (tmp, exe) = compile(&path);
    let out = Command::new(&exe).arg(certs_dir()).output().unwrap();
    check(&out, &want, "loopback.qz compiled");
    let _ = std::fs::remove_dir_all(&tmp);
}

/// Two tasks reading one `TLSSocket` on four workers (#345): no reader
/// stays parked with its line in the plaintext buffer.
#[test]
fn shared_readers() {
    let path = program("shared_readers.qz");
    let want = std::fs::read_to_string(path.with_extension("out")).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("run")
        .arg(&path)
        .arg(certs_dir())
        .env("QUARZ_THREADS", "4")
        .output()
        .expect("run quarz");
    check(&out, &want, "shared_readers.qz on the VM");
    let (tmp, exe) = compile(&path);
    let out = Command::new(&exe)
        .arg(certs_dir())
        .env("QUARZ_THREADS", "4")
        .output()
        .unwrap();
    check(&out, &want, "shared_readers.qz compiled");
    let _ = std::fs::remove_dir_all(&tmp);
}

/// An HTTPS request on `tls`; the response's body.
fn get(tls: &mut Client, target: &str, headers: &str) -> String {
    write!(
        tls,
        "GET {target} HTTP/1.1\r\nHost: localhost\r\n{headers}Connection: close\r\n\r\n"
    )
    .unwrap();
    let mut res = Vec::new();
    // The server closes after the response (with or without
    // close_notify, either is the end here).
    let _ = tls.read_to_end(&mut res);
    let res = String::from_utf8(res).unwrap();
    assert!(res.starts_with("HTTP/1.1 200"), "{res}");
    res.split("\r\n\r\n").nth(1).unwrap().to_string()
}

#[test]
fn https_server() {
    serves("https.qz", |port| {
        let mut tls = client(port, "ca.pem", "localhost", &["http/1.1"]).unwrap();
        assert_eq!(get(&mut tls, "/", ""), "https");
        // A trusted proxy says what the client used.
        let mut tls = client(port, "ca.pem", "localhost", &["http/1.1"]).unwrap();
        assert_eq!(get(&mut tls, "/", "X-Forwarded-Proto: http\r\n"), "http");
        // Plain HTTP to the TLS port: closed, no response.
        let mut sock = TcpStream::connect(("127.0.0.1", port)).unwrap();
        sock.write_all(b"GET / HTTP/1.1\r\nHost: x\r\n\r\n")
            .unwrap();
        assert!(!until_closed(sock).starts_with(b"HTTP/"));
        // No handshake: closed after `read_header_timeout` (300 ms).
        let start = Instant::now();
        until_closed(TcpStream::connect(("127.0.0.1", port)).unwrap());
        let took = start.elapsed();
        assert!(took >= Duration::from_millis(250), "{took:?}");
        assert!(took < Duration::from_secs(5), "{took:?}");
        // Still serving.
        let mut tls = client(port, "ca.pem", "localhost", &["http/1.1"]).unwrap();
        assert_eq!(get(&mut tls, "/quit", ""), "https");
    });
}
