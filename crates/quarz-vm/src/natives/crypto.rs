//! `std/crypto.qz` (the `crypto` feature): RSA keys and signatures
//! through RustCrypto's `rsa`.
//!
//! A key is a `data` value holding its DER (PKCS#8 for a private key,
//! SPKI for a public one, whatever it was read from): the natives parse
//! it per call, through a cache of the keys parsed by contents, so that
//! signing again with one key does not parse it again. A message never
//! holds key material.

use std::sync::{Arc, Mutex, OnceLock};

use rsa::pkcs1::{DecodeRsaPrivateKey, DecodeRsaPublicKey, EncodeRsaPrivateKey};
use rsa::pkcs8::{
    DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey, LineEnding,
};
use rsa::signature::{RandomizedSigner, SignatureEncoding, Verifier};
use rsa::traits::PublicKeyParts;
use rsa::{RsaPrivateKey, RsaPublicKey};
use sha2::{Digest, Sha256, Sha384, Sha512};

use crate::interp::{Flow, Interp, NativeFn};
use crate::value::*;

use super::string;

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Crypto::RSA.private_der", |i, _, a| {
        let key = private_from_der(bytes(i, a.arg(0), "der")?).map_err(|e| error(i, e))?;
        Ok(Value::bytes(private_pkcs8(i, &key)?))
    });
    native!(m, "Crypto::RSA.private_pem", |i, _, a| {
        let (label, der) = one_block(bytes(i, a.arg(0), "pem")?).map_err(|e| error(i, e))?;
        let key = match label.as_str() {
            "PRIVATE KEY" => private_from_pkcs8(&der),
            "RSA PRIVATE KEY" => private_from_pkcs1(&der),
            "ENCRYPTED PRIVATE KEY" => Err(ENCRYPTED.to_string()),
            other => Err(format!("not a private key: {other}")),
        }
        .map_err(|e| error(i, e))?;
        Ok(Value::bytes(private_pkcs8(i, &key)?))
    });
    native!(m, "Crypto::RSA.public_der", |i, _, a| {
        let key = public_from_der(bytes(i, a.arg(0), "der")?).map_err(|e| error(i, e))?;
        Ok(Value::bytes(public_spki(i, &key)?))
    });
    native!(m, "Crypto::RSA.public_pem", |i, _, a| {
        let (label, der) = one_block(bytes(i, a.arg(0), "pem")?).map_err(|e| error(i, e))?;
        let key = match label.as_str() {
            "PUBLIC KEY" => public_from_spki(&der),
            "RSA PUBLIC KEY" => public_from_pkcs1(&der),
            other => Err(format!("not a public key: {other}")),
        }
        .map_err(|e| error(i, e))?;
        Ok(Value::bytes(public_spki(i, &key)?))
    });
    native!(m, "Crypto::RSA.generate_der", |i, _, a| {
        let bits = super::int(i, a.arg(0), "bits")?;
        if ![2048, 3072, 4096].contains(&bits) {
            return Err(i.err_arg(&format!(
                "an RSA key has 2048, 3072 or 4096 bits, not {bits}"
            )));
        }
        // Hundreds of milliseconds for 4096 bits: on a helper thread.
        let der = i
            .block_on(move || {
                let key = RsaPrivateKey::new(&mut rand::rng(), bits as usize)
                    .map_err(|e| e.to_string())?;
                key.to_pkcs8_der()
                    .map(|d| d.as_bytes().to_vec())
                    .map_err(|e| e.to_string())
            })?
            .map_err(|e| error(i, format!("generating a key failed: {e}")))?;
        Ok(Value::bytes(der))
    });
    native!(m, "Crypto::RSA::PrivateKey#to_pem", |i, r, a| {
        let key = private_key(i, r)?;
        let format = a.pos.first().map(|v| symbol(i, v, "format")).transpose()?;
        let pem = match format.as_deref().unwrap_or("pkcs8") {
            "pkcs8" => key
                .to_pkcs8_pem(LineEnding::LF)
                .map(|p| p.to_string())
                .map_err(|e| e.to_string()),
            "pkcs1" => key
                .to_pkcs1_pem(LineEnding::LF)
                .map(|p| p.to_string())
                .map_err(|e| e.to_string()),
            other => return Err(i.err_arg(&format!("format: :pkcs8 or :pkcs1, not :{other}"))),
        }
        .map_err(|e| error(i, format!("encoding the key failed: {e}")))?;
        Ok(Value::string(pem))
    });
    native!(m, "Crypto::RSA.public_of", |i, _, a| {
        let key = cached(
            i,
            &PRIVATE,
            bytes(i, a.arg(0), "der")?.to_vec(),
            private_from_pkcs8,
        )?;
        Ok(Value::bytes(public_spki(i, &key.to_public_key())?))
    });
    native!(m, "Crypto::RSA::PrivateKey#bits", |i, r, _| {
        Ok(Value::Int(bits(&private_key(i, r)?.to_public_key())))
    });
    native!(m, "Crypto::RSA::PublicKey#bits", |i, r, _| {
        Ok(Value::Int(bits(&*public_key(i, r)?)))
    });
    native!(m, "Crypto::RSA::PrivateKey#sign", |i, r, a| {
        let key = private_key(i, r)?;
        usable(i, &key.to_public_key())?;
        let data = message(i, a.arg(0))?;
        // The same (deterministic) signature, computed blinded.
        let mut rng = rand::rng();
        let sig = match hash(i, a.arg(1))? {
            Hash::Sha256 => rsa::pkcs1v15::SigningKey::<Sha256>::new((*key).clone())
                .try_sign_with_rng(&mut rng, data)
                .map(|s| s.to_vec()),
            Hash::Sha384 => rsa::pkcs1v15::SigningKey::<Sha384>::new((*key).clone())
                .try_sign_with_rng(&mut rng, data)
                .map(|s| s.to_vec()),
            Hash::Sha512 => rsa::pkcs1v15::SigningKey::<Sha512>::new((*key).clone())
                .try_sign_with_rng(&mut rng, data)
                .map(|s| s.to_vec()),
        }
        .map_err(|e| error(i, format!("signing failed: {e}")))?;
        Ok(Value::bytes(sig))
    });
    native!(m, "Crypto::RSA::PrivateKey#sign_pss", |i, r, a| {
        let key = private_key(i, r)?;
        usable(i, &key.to_public_key())?;
        let data = message(i, a.arg(0))?;
        let mut rng = rand::rng();
        let h = hash(i, a.arg(1))?;
        // EMSA-PSS needs the hash twice (the salt is as long) and 2 bytes
        // in the modulus.
        let need = 2 * h.size() + 2;
        if key.size() < need {
            return Err(error(
                i,
                format!(
                    "a {}-bit key is too small for PSS with this hash ({} bits at least)",
                    bits(&key.to_public_key()),
                    need * 8
                ),
            ));
        }
        // The salt as long as the hash (`SigningKey::new`'s default).
        let sig = match h {
            Hash::Sha256 => rsa::pss::SigningKey::<Sha256>::new((*key).clone())
                .try_sign_with_rng(&mut rng, data)
                .map(|s| s.to_vec()),
            Hash::Sha384 => rsa::pss::SigningKey::<Sha384>::new((*key).clone())
                .try_sign_with_rng(&mut rng, data)
                .map(|s| s.to_vec()),
            Hash::Sha512 => rsa::pss::SigningKey::<Sha512>::new((*key).clone())
                .try_sign_with_rng(&mut rng, data)
                .map(|s| s.to_vec()),
        }
        .map_err(|e| error(i, format!("signing failed: {e}")))?;
        Ok(Value::bytes(sig))
    });
    native!(m, "Crypto::RSA::PublicKey#verify", |i, r, a| {
        let key = public_key(i, r)?;
        usable(i, &key)?;
        let data = message(i, a.arg(0))?;
        let sig = bytes(i, a.arg(1), "signature")?;
        let h = hash(i, a.arg(2))?;
        let Ok(sig) = rsa::pkcs1v15::Signature::try_from(sig) else {
            return Ok(Value::Bool(false));
        };
        let ok = match h {
            Hash::Sha256 => {
                rsa::pkcs1v15::VerifyingKey::<Sha256>::new((*key).clone()).verify(data, &sig)
            }
            Hash::Sha384 => {
                rsa::pkcs1v15::VerifyingKey::<Sha384>::new((*key).clone()).verify(data, &sig)
            }
            Hash::Sha512 => {
                rsa::pkcs1v15::VerifyingKey::<Sha512>::new((*key).clone()).verify(data, &sig)
            }
        };
        Ok(Value::Bool(ok.is_ok()))
    });
    native!(m, "Crypto::RSA::PublicKey#verify_pss", |i, r, a| {
        let key = public_key(i, r)?;
        usable(i, &key)?;
        let data = message(i, a.arg(0))?;
        let sig = bytes(i, a.arg(1), "signature")?;
        let h = hash(i, a.arg(2))?;
        let Ok(sig) = rsa::pss::Signature::try_from(sig) else {
            return Ok(Value::Bool(false));
        };
        let ok = match h {
            Hash::Sha256 => {
                rsa::pss::VerifyingKey::<Sha256>::new((*key).clone()).verify(data, &sig)
            }
            Hash::Sha384 => {
                rsa::pss::VerifyingKey::<Sha384>::new((*key).clone()).verify(data, &sig)
            }
            Hash::Sha512 => {
                rsa::pss::VerifyingKey::<Sha512>::new((*key).clone()).verify(data, &sig)
            }
        };
        Ok(Value::Bool(ok.is_ok()))
    });
    native!(m, "Crypto::RSA::PublicKey#to_pem", |i, r, _| {
        let key = public_key(i, r)?;
        let pem = key
            .to_public_key_pem(LineEnding::LF)
            .map_err(|e| error(i, format!("encoding the key failed: {e}")))?;
        Ok(Value::string(pem))
    });
    native!(m, "Crypto::RSA::PublicKey#fingerprint", |i, r, _| {
        Ok(Value::bytes(Sha256::digest(der_field(i, r)?).to_vec()))
    });
}

const ENCRYPTED: &str =
    "an encrypted private key: decrypt it first (openssl pkcs8 -topk8 -nocrypt)";

/// A `Crypto::Error` (its message names no key material).
fn error(interp: &Interp, message: impl AsRef<str>) -> Flow {
    interp.raise(interp.program.exc.crypto_error, message.as_ref())
}

fn bytes<'a>(interp: &Interp, v: &'a Value, what: &str) -> Result<&'a [u8], Flow> {
    match v {
        Value::Bytes(b) => Ok(b),
        v => Err(interp.err_type(&format!(
            "{what} must be Bytes, got {}",
            interp.class_name(v)
        ))),
    }
}

/// The data signed: `Bytes`, or a `String`'s UTF-8 bytes.
fn message<'a>(interp: &Interp, v: &'a Value) -> Result<&'a [u8], Flow> {
    match v {
        Value::Bytes(b) => Ok(b),
        v => Ok(string(interp, v, "data")?.as_bytes()),
    }
}

fn symbol(interp: &Interp, v: &Value, what: &str) -> Result<String, Flow> {
    match v {
        Value::Symbol(s) => Ok(interp.symbol_name(*s).to_string()),
        v => Err(interp.err_type(&format!(
            "{what} must be a Symbol, got {}",
            interp.class_name(v)
        ))),
    }
}

#[derive(Clone, Copy)]
enum Hash {
    Sha256,
    Sha384,
    Sha512,
}

impl Hash {
    /// The digest's size in bytes.
    fn size(self) -> usize {
        match self {
            Hash::Sha256 => 32,
            Hash::Sha384 => 48,
            Hash::Sha512 => 64,
        }
    }
}

fn hash(interp: &Interp, v: &Value) -> Result<Hash, Flow> {
    match symbol(interp, v, "hash")?.as_str() {
        "sha256" => Ok(Hash::Sha256),
        "sha384" => Ok(Hash::Sha384),
        "sha512" => Ok(Hash::Sha512),
        other => Err(interp.err_arg(&format!("hash: :sha256, :sha384 or :sha512, not :{other}"))),
    }
}

/// The modulus's size in bits.
fn bits(key: &RsaPublicKey) -> i64 {
    key.n().bits() as i64
}

/// A key of at least 1024 bits signs and verifies.
fn usable(interp: &Interp, key: &RsaPublicKey) -> Result<(), Flow> {
    let n = bits(key);
    if n < 1024 {
        return Err(error(
            interp,
            format!("a {n}-bit key is too small to sign or verify with (1024 at least)"),
        ));
    }
    Ok(())
}

/// The one PEM block of `text` (whitespace around it allowed): its label
/// and DER.
fn one_block(text: &[u8]) -> Result<(String, Vec<u8>), String> {
    let text = std::str::from_utf8(text).map_err(|_| "a PEM text is ASCII".to_string())?;
    let text = text.trim();
    if text.contains("Proc-Type: 4,ENCRYPTED") {
        return Err(ENCRYPTED.to_string());
    }
    if text.contains("-----BEGIN ")
        && (!text.starts_with("-----BEGIN ") || !text.ends_with("-----"))
    {
        return Err("text before or after the PEM block: give the key alone".to_string());
    }
    if text.matches("-----BEGIN ").count() != 1 {
        return Err(if text.contains("-----BEGIN ") {
            "more than one PEM block: give one key".to_string()
        } else {
            "not a PEM text".to_string()
        });
    }
    let (label, der) =
        pem_rfc7468::decode_vec(text.as_bytes()).map_err(|e| format!("bad PEM: {e}"))?;
    Ok((label.to_string(), der))
}

/// The algorithm of a PKCS#8 or SPKI envelope that is not RSA, by name
/// when known.
fn algorithm_name(oid: &str) -> String {
    match oid {
        "1.2.840.10045.2.1" => "an EC key (1.2.840.10045.2.1)".to_string(),
        "1.3.101.112" => "an Ed25519 key (1.3.101.112)".to_string(),
        "1.3.101.113" => "an Ed448 key (1.3.101.113)".to_string(),
        "1.3.101.110" => "an X25519 key (1.3.101.110)".to_string(),
        "1.2.840.10040.4.1" => "a DSA key (1.2.840.10040.4.1)".to_string(),
        "1.2.840.113549.1.1.10" => {
            "an RSASSA-PSS-only key (1.2.840.113549.1.1.10), which is not supported".to_string()
        }
        other => format!("a key of algorithm {other}"),
    }
}

const RSA_OID: &str = "1.2.840.113549.1.1.1";

/// The sizes of the keys read: what `rsa` takes for a public key
/// (`RsaPublicKey::MIN_SIZE..=MAX_SIZE`), for private ones too.
const MIN_BITS: usize = 1024;
const MAX_BITS: usize = 8192;

fn size_error(bits: usize) -> String {
    format!("a {bits}-bit RSA key: keys of {MIN_BITS} to {MAX_BITS} bits only")
}

/// The modulus's size of a PKCS#1 `RSAPublicKey`, if it decodes.
fn pkcs1_modulus_bits(der: &[u8]) -> Option<usize> {
    use rsa::pkcs1::der::Decode;
    let key = rsa::pkcs1::RsaPublicKey::<rsa::pkcs1::der::asn1::UintRef<'_>>::from_der(der).ok()?;
    let n = key.modulus.as_bytes();
    let first = *n.first()?;
    Some(n.len() * 8 - first.leading_zeros() as usize)
}

/// The size error for a public key `rsa` would refuse, when that is why.
fn public_size_error(pkcs1: &[u8]) -> Option<String> {
    let bits = pkcs1_modulus_bits(pkcs1)?;
    (!(MIN_BITS..=MAX_BITS).contains(&bits)).then(|| size_error(bits))
}

fn checked_private(key: RsaPrivateKey) -> Result<RsaPrivateKey, String> {
    let n = key.n().bits() as usize;
    if !(MIN_BITS..=MAX_BITS).contains(&n) {
        return Err(size_error(n));
    }
    Ok(key)
}

/// Whether a parse failed for a reason other than the encoding (the
/// algorithm, the size): no other encoding is tried then.
fn decisive(e: &str) -> bool {
    !e.starts_with("not an RSA private key") && !e.starts_with("not an RSA public key")
}

fn private_from_pkcs8(der: &[u8]) -> Result<RsaPrivateKey, String> {
    if let Ok(info) = rsa::pkcs8::PrivateKeyInfoRef::try_from(der) {
        let oid = info.algorithm.oid.to_string();
        if oid != RSA_OID {
            return Err(format!("not an RSA key: {}", algorithm_name(&oid)));
        }
    }
    checked_private(
        RsaPrivateKey::from_pkcs8_der(der).map_err(|e| format!("not an RSA private key: {e}"))?,
    )
}

fn private_from_pkcs1(der: &[u8]) -> Result<RsaPrivateKey, String> {
    checked_private(
        RsaPrivateKey::from_pkcs1_der(der).map_err(|e| format!("not an RSA private key: {e}"))?,
    )
}

fn public_from_spki(der: &[u8]) -> Result<RsaPublicKey, String> {
    if let Ok(info) = rsa::pkcs8::spki::SubjectPublicKeyInfoRef::try_from(der) {
        let oid = info.algorithm.oid.to_string();
        if oid != RSA_OID {
            return Err(format!("not an RSA key: {}", algorithm_name(&oid)));
        }
        if let Some(e) = info
            .subject_public_key
            .as_bytes()
            .and_then(public_size_error)
        {
            return Err(e);
        }
    }
    RsaPublicKey::from_public_key_der(der).map_err(|e| format!("not an RSA public key: {e}"))
}

fn public_from_pkcs1(der: &[u8]) -> Result<RsaPublicKey, String> {
    if let Some(e) = public_size_error(der) {
        return Err(e);
    }
    RsaPublicKey::from_pkcs1_der(der).map_err(|e| format!("not an RSA public key: {e}"))
}

/// A private key from PKCS#8 or PKCS#1 DER.
fn private_from_der(der: &[u8]) -> Result<RsaPrivateKey, String> {
    match private_from_pkcs8(der) {
        Ok(k) => Ok(k),
        Err(e) if decisive(&e) => Err(e),
        Err(e) => match private_from_pkcs1(der) {
            Err(e1) if decisive(&e1) => Err(e1),
            r => r.map_err(|_| e),
        },
    }
}

/// A public key from SPKI or PKCS#1 DER.
fn public_from_der(der: &[u8]) -> Result<RsaPublicKey, String> {
    match public_from_spki(der) {
        Ok(k) => Ok(k),
        Err(e) if decisive(&e) => Err(e),
        Err(e) => match public_from_pkcs1(der) {
            Err(e1) if decisive(&e1) => Err(e1),
            r => r.map_err(|_| e),
        },
    }
}

fn private_pkcs8(interp: &Interp, key: &RsaPrivateKey) -> Result<Vec<u8>, Flow> {
    key.to_pkcs8_der()
        .map(|d| d.as_bytes().to_vec())
        .map_err(|e| error(interp, format!("encoding the key failed: {e}")))
}

fn public_spki(interp: &Interp, key: &RsaPublicKey) -> Result<Vec<u8>, Flow> {
    key.to_public_key_der()
        .map(|d| d.as_bytes().to_vec())
        .map_err(|e| error(interp, format!("encoding the key failed: {e}")))
}

/// The DER field of a key (`data PrivateKey(der: Bytes)`).
fn der_field(interp: &Interp, v: &Value) -> Result<Vec<u8>, Flow> {
    let Value::Object(o) = v else {
        return Err(interp.err_type("expected a Crypto::RSA key"));
    };
    match o.field(0) {
        Some(Value::Bytes(b)) => Ok(b.to_vec()),
        _ => Err(interp.err_type("expected a Crypto::RSA key")),
    }
}

/// The keys parsed, by DER (a program uses a few; past `CACHED`, the
/// cache starts again).
const CACHED: usize = 64;

type Cache<K> = OnceLock<Mutex<quarz_ir::HashMap<Vec<u8>, Arc<K>>>>;

fn cached<K>(
    interp: &Interp,
    cache: &'static Cache<K>,
    der: Vec<u8>,
    parse: fn(&[u8]) -> Result<K, String>,
) -> Result<Arc<K>, Flow> {
    let cache = cache.get_or_init(Default::default);
    if let Some(k) = crate::sched::lock(cache).get(&der) {
        return Ok(k.clone());
    }
    let key = Arc::new(parse(&der).map_err(|e| error(interp, e))?);
    let mut c = crate::sched::lock(cache);
    if c.len() >= CACHED {
        c.clear();
    }
    c.insert(der, key.clone());
    Ok(key)
}

static PRIVATE: Cache<RsaPrivateKey> = OnceLock::new();

fn private_key(interp: &Interp, v: &Value) -> Result<Arc<RsaPrivateKey>, Flow> {
    cached(interp, &PRIVATE, der_field(interp, v)?, private_from_pkcs8)
}

fn public_key(interp: &Interp, v: &Value) -> Result<Arc<RsaPublicKey>, Flow> {
    static CACHE: Cache<RsaPublicKey> = OnceLock::new();
    cached(interp, &CACHE, der_field(interp, v)?, public_from_spki)
}
