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
//! part, not its bytes. A `TLS::ServerConfig` holds it as a
//! `Bytes::Secret`; its configuration is kept by a digest of the key, not
//! the key, and the key is read into buffers cleared when dropped:
//! what stays is the signing key ring made of it, inside the
//! configuration (ring does not clear it when dropped).

use std::sync::{Arc, Mutex, OnceLock};

use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::crypto::CryptoProvider;
use rustls::pki_types::pem::PemObject;
use rustls::pki_types::{
    CertificateDer, PrivateKeyDer, PrivatePkcs1KeyDer, PrivatePkcs8KeyDer, PrivateSec1KeyDer,
    ServerName, UnixTime,
};
use rustls::{ClientConfig, DigitallySignedStruct, RootCertStore, ServerConfig, SignatureScheme};
use sha2::{Digest, Sha256};

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
        let config = server_config(i, r)?;
        let conn = rustls::ServerConnection::new(config).map_err(|e| tls_error(i, failure(e)))?;
        connection(i, rustls::Connection::Server(conn), a.arg(0), None, false)
    });
    native!(m, "TLS::ServerConfig#check", |i, r, _| {
        server_config(i, r)?;
        Ok(Value::Nil)
    });
    native!(m, "TLS::Testing.generate", |i, _, a| {
        let strings = |v: &Value, what: &str| -> Result<Vec<String>, Flow> {
            let Value::Array(xs) = v else {
                return Err(i.err_type(&format!("{what} must be an Array")));
            };
            xs.iter()
                .map(|x| Ok(string(i, &x, what)?.to_string()))
                .collect()
        };
        let dns = strings(a.arg(0), "a DNS name")?;
        let ips = strings(a.arg(1), "an IP address")?;
        let not_before = super::int(i, a.arg(2), "not_before")?;
        let not_after = super::int(i, a.arg(3), "not_after")?;
        let (cert, key) = self_signed(&dns, &ips, not_before, not_after)
            .map_err(|e| i.err_arg(&format!("cannot make the certificate: {e}")))?;
        Ok(Value::array(vec![Value::string(cert), Value::string(key)]))
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

/// What a server configuration is kept by: a `TLS::ServerConfig`'s
/// contents, its private key as the SHA-256 of its PEM, so that the cache
/// holds no copy of the key.
#[derive(Clone, PartialEq, Eq, Hash)]
struct ServerKey {
    certificate: Vec<u8>,
    key_digest: [u8; 32],
    alpn: Vec<Vec<u8>>,
    tls13_only: bool,
}

/// A `TLS::ServerConfig` (`data ServerConfig(certificate, private_key,
/// alpn, min_version)`), and its private key (a `Bytes::Secret`).
fn server_key(interp: &Interp, v: &Value) -> Result<(ServerKey, Value), Flow> {
    let bad = || interp.err_type("expected a TLS::ServerConfig");
    let Value::Object(cfg) = v else {
        return Err(bad());
    };
    let (Some(Value::Bytes(certificate)), Some(private_key @ Value::Secret(_))) =
        (cfg.field(0), cfg.field(1))
    else {
        return Err(bad());
    };
    // Read in place, under the secret's lock: a wiped key raises.
    let key_digest = super::bytes::secret_of(interp, &private_key)?
        .with(|pem| <[u8; 32]>::from(Sha256::digest(pem)))
        .ok_or_else(|| super::bytes::wiped(interp))?;
    Ok((
        ServerKey {
            certificate: certificate.to_vec(),
            key_digest,
            alpn: alpn(interp, cfg.field(2)).ok_or_else(bad)??,
            tls13_only: tls13_only(interp, cfg.field(3)).ok_or_else(bad)??,
        },
        private_key,
    ))
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

/// The configuration kept for `key` in `cache`, if any.
fn kept<K, V>(cache: &'static Cache<K, V>, key: &K) -> Option<Arc<V>>
where
    K: Eq + std::hash::Hash,
{
    let cache = cache.get_or_init(Default::default);
    crate::sched::lock(cache).get(key).cloned()
}

/// The configuration built from `key`, from `cache` or by `build`: on a
/// helper thread, as file IO is (reading the system's store, parsing
/// certificates and keys).
fn cached<K, V>(
    interp: &Interp,
    cache: &'static Cache<K, V>,
    key: K,
    build: impl FnOnce(&K) -> Result<Arc<V>, TlsFailure> + Send + 'static,
) -> Result<Arc<V>, Flow>
where
    K: Clone + Eq + std::hash::Hash + Send + 'static,
    V: Send + Sync + 'static,
{
    if let Some(c) = kept(cache, &key) {
        return Ok(c);
    }
    let cache = cache.get_or_init(Default::default);
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

/// The server configuration of the `TLS::ServerConfig` `v`. Its key is
/// copied (into a buffer cleared when dropped, for the helper thread)
/// only when the configuration is not kept yet.
fn server_config(interp: &Interp, v: &Value) -> Result<Arc<ServerConfig>, Flow> {
    static CACHE: Cache<ServerKey, ServerConfig> = OnceLock::new();
    let (key, private_key) = server_key(interp, v)?;
    if let Some(c) = kept(&CACHE, &key) {
        return Ok(c);
    }
    let pem = super::bytes::secret_input(interp, &private_key, "private_key")?.into_owned();
    cached(interp, &CACHE, key, move |k| build_server_config(k, &pem))
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

fn build_server_config(key: &ServerKey, pem: &[u8]) -> Result<Arc<ServerConfig>, TlsFailure> {
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
    // Not a parser's message: it may quote a line of the key.
    let der = private_key_der(pem).map_err(|e| match e {
        KeyPem::None => fail("private_key: no private key in the PEM (PKCS#8, PKCS#1 or SEC1)"),
        KeyPem::Bad => fail("private_key: bad PEM"),
    })?;
    // What `with_single_cert` does, from a key borrowed from `der` (which
    // is cleared when dropped) rather than one rustls takes: ring's
    // signing key, then the check that it is the certificate's.
    let private_key = match &der {
        Der::Pkcs8(d) => PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(&d[..])),
        Der::Pkcs1(d) => PrivateKeyDer::Pkcs1(PrivatePkcs1KeyDer::from(&d[..])),
        Der::Sec1(d) => PrivateKeyDer::Sec1(PrivateSec1KeyDer::from(&d[..])),
    };
    let signing = rustls::crypto::ring::sign::any_supported_type(&private_key);
    drop(private_key);
    drop(der);
    let certified = rustls::sign::CertifiedKey::new(chain, signing.map_err(map_key_error)?);
    match certified.keys_match() {
        // (As `with_single_cert`: a key whose public half is unknown is
        // not refused.)
        Ok(()) | Err(rustls::Error::InconsistentKeys(rustls::InconsistentKeys::Unknown)) => {}
        Err(e) => return Err(map_key_error(e)),
    }
    let versions: &[&rustls::SupportedProtocolVersion] = if key.tls13_only {
        &[&rustls::version::TLS13]
    } else {
        rustls::DEFAULT_VERSIONS
    };
    let mut config = ServerConfig::builder_with_provider(provider())
        .with_protocol_versions(versions)
        .map_err(failure)?
        .with_no_client_auth()
        .with_cert_resolver(Arc::new(rustls::sign::SingleCertAndKey::from(certified)));
    config.alpn_protocols = key.alpn.clone();
    Ok(Arc::new(config))
}

/// A server key's failure, as `with_single_cert` would have reported it.
fn map_key_error(e: rustls::Error) -> TlsFailure {
    let message = match e {
        rustls::Error::InconsistentKeys(_) => {
            "private_key: does not match the certificate".to_string()
        }
        // ring's key loader.
        rustls::Error::General(_) => {
            "private_key: not a key that can sign (RSA, ECDSA P-256 or P-384, Ed25519)".to_string()
        }
        rustls::Error::InvalidCertificate(_) => {
            "certificate: the first certificate does not parse".to_string()
        }
        e => format!("certificate: {e}"),
    };
    TlsFailure {
        message,
        certificate: false,
    }
}

/// A private key's DER, by its PEM label, in a buffer cleared when
/// dropped.
enum Der {
    Pkcs8(super::bytes::Cleared),
    Pkcs1(super::bytes::Cleared),
    Sec1(super::bytes::Cleared),
}

/// Why a PEM gave no private key.
enum KeyPem {
    /// No `PRIVATE KEY`, `RSA PRIVATE KEY` or `EC PRIVATE KEY` section.
    None,
    /// A section that does not end, or whose base64 does not decode.
    Bad,
}

/// The first private key of `pem`, as rustls-pki-types' `PrivateKeyDer`
/// reads it (sections of other labels skipped), but with every copy of
/// the key, base64 or DER, in a buffer of its final size that is cleared
/// when dropped (that parser's base64 buffer grows, and is not cleared).
fn private_key_der(pem: &[u8]) -> Result<Der, KeyPem> {
    let mut section: Option<&[u8]> = None;
    let mut b64 = super::bytes::Cleared(Vec::with_capacity(pem.len()));
    for line in pem.split(|&b| b == b'\n') {
        let line = line.trim_ascii();
        let Some(label) = section else {
            if let Some(rest) = line.strip_prefix(b"-----BEGIN ") {
                section = Some(rest.strip_suffix(b"-----").ok_or(KeyPem::Bad)?);
            }
            continue;
        };
        let Some(rest) = line.strip_prefix(b"-----END ") else {
            b64.0
                .extend(line.iter().filter(|b| !b.is_ascii_whitespace()));
            continue;
        };
        if rest.strip_suffix(b"-----") != Some(label) {
            return Err(KeyPem::Bad);
        }
        section = None;
        let make: fn(super::bytes::Cleared) -> Der = match label {
            b"PRIVATE KEY" => Der::Pkcs8,
            b"RSA PRIVATE KEY" => Der::Pkcs1,
            b"EC PRIVATE KEY" => Der::Sec1,
            _ => {
                clear_bytes(&mut b64.0);
                b64.0.clear();
                continue;
            }
        };
        use base64::Engine;
        let mut der = super::bytes::Cleared(vec![0u8; base64::decoded_len_estimate(b64.0.len())]);
        let n = base64::engine::general_purpose::STANDARD
            .decode_slice(&b64.0, &mut der.0)
            .map_err(|_| KeyPem::Bad)?;
        clear_bytes(&mut der.0[n..]);
        der.0.truncate(n);
        return Ok(make(der));
    }
    Err(if section.is_some() {
        KeyPem::Bad
    } else {
        KeyPem::None
    })
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

/// A self-signed end-entity certificate (no basicConstraints: webpki
/// refuses a CA as the server's own certificate) for the DNS names and IP
/// addresses given, with a new ECDSA P-256 key: its PEM and the key's
/// (PKCS#8). The first name is also the subject's common name. The times
/// are Unix seconds. `TLS::Testing.self_signed` (std/tls.qz) decides which
/// name is an address (`Socket::IP.parse`) and checks the names; the
/// addresses come in its canonical form.
fn self_signed(
    dns: &[String],
    ips: &[String],
    not_before: i64,
    not_after: i64,
) -> Result<(String, String), String> {
    use rcgen::{CertificateParams, DistinguishedName, DnType, KeyPair, SanType};
    let time = |t: i64| {
        time::OffsetDateTime::from_unix_timestamp(t).map_err(|_| "a time out of range".to_string())
    };
    let mut params = CertificateParams::default();
    for d in dns {
        let name = d.clone().try_into().map_err(|e| format!("{d}: {e}"))?;
        params.subject_alt_names.push(SanType::DnsName(name));
    }
    for ip in ips {
        let addr: std::net::IpAddr = ip.parse().map_err(|_| format!("not an IP address: {ip}"))?;
        params.subject_alt_names.push(SanType::IpAddress(addr));
    }
    let mut subject = DistinguishedName::new();
    if let Some(first) = dns.first().or(ips.first()) {
        subject.push(DnType::CommonName, first.as_str());
    }
    params.distinguished_name = subject;
    params.not_before = time(not_before)?;
    params.not_after = time(not_after)?;
    let key = KeyPair::generate().map_err(|e| e.to_string())?;
    let cert = params.self_signed(&key).map_err(|e| e.to_string())?;
    Ok((cert.pem(), key.serialize_pem()))
}
