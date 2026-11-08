//! TLS through rustls (`std/tls.qz`, the `tls` feature): the natives
//! that make a connection (`TLSSocket.connect`, `TLS::ServerConfig#accept`),
//! the `TlsSession` over a rustls connection, and the configurations
//! built from `TLS::Config`s and `TLS::ServerConfig`s.
//!
//! The crypto provider is ring. `TLS::Roots.system` is the system's
//! store, read once at its first use (rustls-native-certs, which honours
//! `SSL_CERT_FILE` and `SSL_CERT_DIR`). A `TLS::Config` is a `data` value:
//! the configuration built from it is kept by its contents, so that
//! connecting again does not parse the root store again; a
//! `TLS::ServerConfig`'s likewise (built when it is made, to check it).
//!
//! A private key never goes into a message: errors about one name the
//! part, not its bytes.

use std::sync::{Arc, Mutex, OnceLock};

use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::crypto::CryptoProvider;
use rustls::pki_types::pem::PemObject;
use rustls::pki_types::{CertificateDer, PrivateKeyDer, ServerName, UnixTime};
use rustls::{ClientConfig, DigitallySignedStruct, RootCertStore, ServerConfig, SignatureScheme};

use crate::interp::{Flow, Interp, NativeFn};
use crate::value::*;

use super::io::io;
use super::net;
use super::string;
use super::tls_io::{handshake, tls_error, TlsFailure, TlsSession, TlsState};

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "TLSSocket.handshake", |i, _, a| {
        let name = string(i, a.arg(1), "server_name")?.to_string();
        let key = config_key(i, a.arg(2))?;
        let server_name = ServerName::try_from(name.clone())
            .map_err(|_| i.err_arg(&format!("not a server name: {name}")))?;
        let config = client_config(i, key.clone())?;
        let conn = rustls::ClientConnection::new(config, server_name)
            .map_err(|e| tls_error(i, failure(e)))?;
        let tls = connection(
            i,
            rustls::Connection::Client(conn),
            a.arg(0),
            Some(name),
            key.verify,
        )?;
        Ok(tls)
    });
    native!(m, "TLS::ServerConfig#accept", |i, r, a| {
        let config = server_config(i, server_key(i, r)?)?;
        let conn = rustls::ServerConnection::new(config).map_err(|e| tls_error(i, failure(e)))?;
        connection(i, rustls::Connection::Server(conn), a.arg(0), None, false)
    });
    native!(m, "TLS::ServerConfig#check", |i, r, _| {
        server_config(i, server_key(i, r)?)?;
        Ok(Value::Nil)
    });
    native!(m, "TLS::Roots.check", |i, _, a| {
        let Value::Bytes(pem) = a.arg(0) else {
            return Err(i.err_type("pem must be Bytes"));
        };
        roots_from_pem(pem).map_err(|f| tls_error(i, f))?;
        Ok(a.arg(0).clone())
    });
}

/// A `TLSSocket` over `conn`, taking `socket` over, once the handshake
/// is done; on a failure, the connection is closed.
fn connection(
    interp: &Interp,
    mut conn: rustls::Connection,
    socket: &Value,
    server_name: Option<String>,
    verified: bool,
) -> Result<Value, Flow> {
    // A write's plaintext goes into records at once, whatever its size
    // (the bytes are in memory already).
    conn.set_buffer_limit(None);
    let sock = take_over(interp, socket)?;
    let tls = io(IoKind::Tls(IoCell::new(TlsState {
        sock,
        session: Box::new(Rustls(conn)),
        plain: Vec::new(),
        server_name,
        verified,
        notified: false,
    })));
    let Value::Io(v) = &tls else { unreachable!() };
    let IoKind::Tls(st) = &v.kind else {
        unreachable!()
    };
    if let Err(e) = handshake(interp, st) {
        let _ = net::close(interp, &tls);
        return Err(e);
    }
    Ok(tls)
}

/// The state of a connected `TCPSocket`, moved out of it: the socket is
/// closed for the program from here on (its waiters are woken and find
/// it so), and its descriptor belongs to the caller.
fn take_over(interp: &Interp, v: &Value) -> Result<SocketState, Flow> {
    let st = net::socket(interp, v)?;
    let (state, waiters) = {
        let mut s = st.borrow_mut();
        if s.stream.is_none() {
            drop(s);
            return Err(net::closed_stream(interp));
        }
        // Another task's write has part of its bytes on the wire already:
        // the handshake would follow them.
        if s.writing {
            drop(s);
            return Err(interp.raise(
                interp.program.exc.io_error,
                "a write is in progress on the socket",
            ));
        }
        let stream = s.stream.take().expect("checked above");
        // A new watch: the descriptor is registered anew where waited on.
        interp.sched.borrow_mut().deregister(stream.fd());
        s.closed = true;
        let mut waiters = std::mem::take(&mut s.watch.waiters);
        waiters.extend(s.write_waiters.drain(..));
        let state = SocketState {
            stream: Some(stream),
            unix: s.unix,
            pipe: s.pipe,
            rbuf: std::mem::take(&mut s.rbuf),
            eof: false,
            closed: false,
            path: s.path.clone(),
            local: s.local,
            peer: s.peer,
            writing: false,
            write_waiters: std::collections::VecDeque::new(),
            watch: IoWatch::new(),
        };
        (state, waiters)
    };
    for w in waiters {
        interp.wake_ref(w);
    }
    Ok(state)
}

/// A rustls connection as the pump sees it.
struct Rustls(rustls::Connection);

impl TlsSession for Rustls {
    fn read_tls(&mut self, rd: &mut dyn std::io::Read) -> std::io::Result<usize> {
        self.0.read_tls(rd)
    }

    fn write_tls(&mut self, wr: &mut dyn std::io::Write) -> std::io::Result<usize> {
        self.0.write_tls(wr)
    }

    fn process_new_packets(&mut self) -> Result<(), TlsFailure> {
        self.0.process_new_packets().map(|_| ()).map_err(failure)
    }

    fn read_plain(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        use std::io::Read;
        self.0.reader().read(buf)
    }

    fn write_plain(&mut self, data: &[u8]) {
        use std::io::Write;
        // Unlimited buffer (`set_buffer_limit(None)`): takes it all.
        let _ = self.0.writer().write_all(data);
    }

    fn wants_write(&self) -> bool {
        self.0.wants_write()
    }

    fn is_handshaking(&self) -> bool {
        self.0.is_handshaking()
    }

    fn send_close_notify(&mut self) {
        self.0.send_close_notify();
    }

    fn alpn(&self) -> Option<Vec<u8>> {
        self.0.alpn_protocol().map(|p| p.to_vec())
    }

    fn peer_certificate(&self) -> Option<Vec<u8>> {
        self.0
            .peer_certificates()
            .and_then(|c| c.first())
            .map(|c| c.as_ref().to_vec())
    }

    fn sni(&self) -> Option<String> {
        match &self.0 {
            rustls::Connection::Server(c) => c.server_name().map(str::to_string),
            rustls::Connection::Client(_) => None,
        }
    }
}

/// A rustls error as a `TLS::Error`, a certificate one naming the reason.
fn failure(e: rustls::Error) -> TlsFailure {
    use rustls::CertificateError as C;
    let rustls::Error::InvalidCertificate(c) = &e else {
        return TlsFailure {
            message: e.to_string(),
            certificate: false,
        };
    };
    let reason = match c {
        C::UnknownIssuer => "unknown issuer",
        C::NotValidForName | C::NotValidForNameContext { .. } => "name mismatch",
        C::Expired | C::ExpiredContext { .. } => "expired",
        C::NotValidYet | C::NotValidYetContext { .. } => "not yet valid",
        C::Revoked => "revoked",
        C::BadSignature => "bad signature",
        _ => "invalid certificate",
    };
    TlsFailure {
        message: format!("certificate verify failed ({reason}): {e}"),
        certificate: true,
    }
}

// ----- configurations ------------------------------------------------------------

/// What a client configuration is built from: a `TLS::Config`'s contents.
#[derive(Clone, PartialEq, Eq, Hash)]
struct ConfigKey {
    /// The roots' PEM, `None` for the system's.
    pem: Option<Vec<u8>>,
    alpn: Vec<Vec<u8>>,
    tls13_only: bool,
    verify: bool,
}

/// A `TLS::Config` (`data Config(roots, alpn, min_version, verify)`, its
/// roots `data Roots(pem: Bytes?)`).
fn config_key(interp: &Interp, v: &Value) -> Result<ConfigKey, Flow> {
    let bad = || interp.err_type("expected a TLS::Config");
    let Value::Object(cfg) = v else {
        return Err(bad());
    };
    let Some(Value::Object(roots)) = cfg.field(0) else {
        return Err(bad());
    };
    let pem = match roots.field(0) {
        Some(Value::Bytes(b)) => Some(b.to_vec()),
        Some(Value::Nil) => None,
        _ => return Err(bad()),
    };
    let alpn = alpn(interp, cfg.field(1)).ok_or_else(bad)??;
    let tls13_only = tls13_only(interp, cfg.field(2)).ok_or_else(bad)??;
    let verify = !matches!(cfg.field(3), Some(Value::Bool(false)));
    Ok(ConfigKey {
        pem,
        alpn,
        tls13_only,
        verify,
    })
}

/// What a server configuration is built from: a `TLS::ServerConfig`'s
/// contents. (No `Debug`: it holds the private key.)
#[derive(Clone, PartialEq, Eq, Hash)]
struct ServerKey {
    certificate: Vec<u8>,
    private_key: Vec<u8>,
    alpn: Vec<Vec<u8>>,
    tls13_only: bool,
}

/// A `TLS::ServerConfig` (`data ServerConfig(certificate, private_key,
/// alpn, min_version)`).
fn server_key(interp: &Interp, v: &Value) -> Result<ServerKey, Flow> {
    let bad = || interp.err_type("expected a TLS::ServerConfig");
    let Value::Object(cfg) = v else {
        return Err(bad());
    };
    let (Some(Value::Bytes(certificate)), Some(Value::Bytes(private_key))) =
        (cfg.field(0), cfg.field(1))
    else {
        return Err(bad());
    };
    Ok(ServerKey {
        certificate: certificate.to_vec(),
        private_key: private_key.to_vec(),
        alpn: alpn(interp, cfg.field(2)).ok_or_else(bad)??,
        tls13_only: tls13_only(interp, cfg.field(3)).ok_or_else(bad)??,
    })
}

/// A config's `alpn` field; `None` when it is not an array.
fn alpn(interp: &Interp, v: Option<Value>) -> Option<Result<Vec<Vec<u8>>, Flow>> {
    let Some(Value::Array(a)) = v else {
        return None;
    };
    Some(
        a.iter()
            .map(|p| Ok(string(interp, &p, "an ALPN protocol")?.as_bytes().to_vec()))
            .collect(),
    )
}

/// Whether a config's `min_version` field is `:tls13`; `None` when it is
/// not a symbol.
fn tls13_only(interp: &Interp, v: Option<Value>) -> Option<Result<bool, Flow>> {
    let Some(Value::Symbol(s)) = v else {
        return None;
    };
    Some(match &*interp.symbol_name(s) {
        "tls12" => Ok(false),
        "tls13" => Ok(true),
        other => Err(interp.err_arg(&format!("min_version: :tls12 or :tls13, not :{other}"))),
    })
}

/// The configurations built, by what they were built from (a program
/// uses a few; past `CACHED`, the cache starts again).
const CACHED: usize = 64;

type Cache<K, V> = OnceLock<Mutex<quarz_ir::HashMap<K, Arc<V>>>>;

/// The configuration built from `key`, from `cache` or by `build`: on a
/// helper thread, as file IO is (reading the system's store, parsing
/// certificates and keys).
fn cached<K, V>(
    interp: &Interp,
    cache: &'static Cache<K, V>,
    key: K,
    build: fn(&K) -> Result<Arc<V>, TlsFailure>,
) -> Result<Arc<V>, Flow>
where
    K: Clone + Eq + std::hash::Hash + Send + 'static,
    V: Send + Sync + 'static,
{
    let cache = cache.get_or_init(Default::default);
    if let Some(c) = crate::sched::lock(cache).get(&key) {
        return Ok(c.clone());
    }
    let k = key.clone();
    let built = interp
        .block_on(move || build(&k))?
        .map_err(|f| tls_error(interp, f))?;
    let mut c = crate::sched::lock(cache);
    if c.len() >= CACHED {
        c.clear();
    }
    c.insert(key, built.clone());
    Ok(built)
}

fn client_config(interp: &Interp, key: ConfigKey) -> Result<Arc<ClientConfig>, Flow> {
    static CACHE: Cache<ConfigKey, ClientConfig> = OnceLock::new();
    cached(interp, &CACHE, key, build_config)
}

fn server_config(interp: &Interp, key: ServerKey) -> Result<Arc<ServerConfig>, Flow> {
    static CACHE: Cache<ServerKey, ServerConfig> = OnceLock::new();
    cached(interp, &CACHE, key, build_server_config)
}

fn provider() -> Arc<CryptoProvider> {
    static PROVIDER: OnceLock<Arc<CryptoProvider>> = OnceLock::new();
    PROVIDER
        .get_or_init(|| Arc::new(rustls::crypto::ring::default_provider()))
        .clone()
}

fn build_config(key: &ConfigKey) -> Result<Arc<ClientConfig>, TlsFailure> {
    let versions: &[&rustls::SupportedProtocolVersion] = if key.tls13_only {
        &[&rustls::version::TLS13]
    } else {
        rustls::DEFAULT_VERSIONS
    };
    let builder = ClientConfig::builder_with_provider(provider())
        .with_protocol_versions(versions)
        .map_err(failure)?;
    let mut config = if key.verify {
        let roots = match &key.pem {
            Some(pem) => Arc::new(roots_from_pem(pem)?),
            None => system_roots()?,
        };
        builder.with_root_certificates(roots).with_no_client_auth()
    } else {
        builder
            .dangerous()
            .with_custom_certificate_verifier(Arc::new(NoVerify(provider())))
            .with_no_client_auth()
    };
    config.alpn_protocols = key.alpn.clone();
    Ok(Arc::new(config))
}

fn build_server_config(key: &ServerKey) -> Result<Arc<ServerConfig>, TlsFailure> {
    let fail = |message: &str| TlsFailure {
        message: message.to_string(),
        certificate: false,
    };
    let mut chain = Vec::new();
    for cert in CertificateDer::pem_slice_iter(&key.certificate) {
        chain.push(cert.map_err(|e| fail(&format!("certificate: bad PEM: {e}")))?);
    }
    if chain.is_empty() {
        return Err(fail("certificate: no certificate in the PEM"));
    }
    // Not the PEM parser's message: it may quote a line of the key.
    let private_key = PrivateKeyDer::from_pem_slice(&key.private_key).map_err(|e| match e {
        rustls::pki_types::pem::Error::NoItemsFound => {
            fail("private_key: no private key in the PEM (PKCS#8, PKCS#1 or SEC1)")
        }
        _ => fail("private_key: bad PEM"),
    })?;
    let versions: &[&rustls::SupportedProtocolVersion] = if key.tls13_only {
        &[&rustls::version::TLS13]
    } else {
        rustls::DEFAULT_VERSIONS
    };
    let mut config = ServerConfig::builder_with_provider(provider())
        .with_protocol_versions(versions)
        .map_err(failure)?
        .with_no_client_auth()
        .with_single_cert(chain, private_key)
        .map_err(|e| match e {
            rustls::Error::InconsistentKeys(_) => {
                fail("private_key: does not match the certificate")
            }
            // ring's key loader.
            rustls::Error::General(_) => {
                fail("private_key: not a key that can sign (RSA, ECDSA P-256 or P-384, Ed25519)")
            }
            rustls::Error::InvalidCertificate(_) => {
                fail("certificate: the first certificate does not parse")
            }
            e => fail(&format!("certificate: {e}")),
        })?;
    config.alpn_protocols = key.alpn.clone();
    Ok(Arc::new(config))
}

fn roots_from_pem(pem: &[u8]) -> Result<RootCertStore, TlsFailure> {
    let fail = |message: String| TlsFailure {
        message,
        certificate: false,
    };
    let mut store = RootCertStore::empty();
    for cert in CertificateDer::pem_slice_iter(pem) {
        let cert = cert.map_err(|e| fail(format!("bad PEM: {e}")))?;
        store
            .add(cert)
            .map_err(|e| fail(format!("bad root certificate: {e}")))?;
    }
    if store.is_empty() {
        return Err(fail("no certificate in the PEM".to_string()));
    }
    Ok(store)
}

/// The system's root certificates, read once.
fn system_roots() -> Result<Arc<RootCertStore>, TlsFailure> {
    static SYSTEM: OnceLock<Result<Arc<RootCertStore>, String>> = OnceLock::new();
    SYSTEM
        .get_or_init(|| {
            let found = rustls_native_certs::load_native_certs();
            let mut store = RootCertStore::empty();
            store.add_parsable_certificates(found.certs);
            if !store.is_empty() {
                return Ok(Arc::new(store));
            }
            let mut message = format!("no system root certificates ({})", places_tried());
            for e in &found.errors {
                message.push_str(&format!("; {e}"));
            }
            Err(message)
        })
        .clone()
        .map_err(|message| TlsFailure {
            message,
            certificate: false,
        })
}

/// Where the system's store was looked for.
fn places_tried() -> String {
    let var =
        |name: &str| std::env::var_os(name).map(|v| format!("{name}={}", v.to_string_lossy()));
    let set: Vec<String> = ["SSL_CERT_FILE", "SSL_CERT_DIR"]
        .iter()
        .filter_map(|n| var(n))
        .collect();
    if !set.is_empty() {
        return format!("tried {}", set.join(", "));
    }
    #[cfg(all(unix, not(target_os = "macos")))]
    {
        let dirs: Vec<String> = openssl_probe::candidate_cert_dirs()
            .map(|p| p.display().to_string())
            .collect();
        format!(
            "SSL_CERT_FILE and SSL_CERT_DIR unset; tried the usual bundle files and {}",
            dirs.join(", ")
        )
    }
    #[cfg(not(all(unix, not(target_os = "macos"))))]
    {
        "SSL_CERT_FILE and SSL_CERT_DIR unset; tried the system's keychain".to_string()
    }
}

/// `verify: false`: any certificate is accepted (the handshake's
/// signatures are still checked, so the connection is encrypted, but its
/// peer is not authenticated).
#[derive(Debug)]
struct NoVerify(Arc<CryptoProvider>);

impl ServerCertVerifier for NoVerify {
    fn verify_server_cert(
        &self,
        _: &CertificateDer<'_>,
        _: &[CertificateDer<'_>],
        _: &ServerName<'_>,
        _: &[u8],
        _: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        Ok(ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls12_signature(
            message,
            cert,
            dss,
            &self.0.signature_verification_algorithms,
        )
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(
            message,
            cert,
            dss,
            &self.0.signature_verification_algorithms,
        )
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.0.signature_verification_algorithms.supported_schemes()
    }
}
