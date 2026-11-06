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

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::Arc;

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
