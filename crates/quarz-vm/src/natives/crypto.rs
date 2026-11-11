//! `std/crypto.qz` (the `crypto` feature): RSA keys and signatures
//! through RustCrypto's `rsa`, AES-GCM through `aes-gcm`, argon2id
//! password hashes through `argon2`, and the system's random bytes
//! through `getrandom`.
//!
//! A key is a `data` value holding its DER (PKCS#8 for a private key,
//! SPKI for a public one, whatever it was read from): the natives parse
//! it per call, through a cache of the keys parsed by contents, so that
//! signing again with one key does not parse it again. A message never
//! holds key material.

use std::sync::{Arc, Mutex, OnceLock};

use aes_gcm::aead::Aead;
use rsa::pkcs1::{DecodeRsaPrivateKey, DecodeRsaPublicKey, EncodeRsaPrivateKey};
use rsa::pkcs8::{
    DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey, LineEnding,
};
use rsa::signature::{RandomizedSigner, SignatureEncoding, Verifier};
use rsa::traits::PublicKeyParts;
use rsa::{PrivateKey, PublicKey};
use sha2::{Digest, Sha256, Sha384, Sha512};
use zeroize::Zeroizing;

use crate::interp::{Flow, Interp, NativeFn};
use crate::value::*;

use super::string;

pub fn register(m: &mut super::Registry<NativeFn>) {
    register_argon2(m);
    native!(m, "Crypto.random_bytes", |i, _, a| {
        let n = super::int(i, a.arg(0), "n")?;
        if !(0..=RANDOM_MAX).contains(&n) {
            return Err(i.err_arg(&format!("random_bytes: 0 to {RANDOM_MAX} bytes, not {n}")));
        }
        let mut buf = vec![0u8; n as usize];
        getrandom::fill(&mut buf)
            .map_err(|e| error(i, format!("the system's random source failed: {e}")))?;
        Ok(Value::bytes(buf))
    });
    native!(m, "Crypto::AES.seal_with", |i, _, a| {
        let key = bytes(i, a.arg(0), "key")?;
        let nonce = gcm_nonce(i, a.arg(1))?;
        let plaintext = message(i, a.arg(2))?;
        let aad = message(i, a.arg(3))?;
        let payload = aes_gcm::aead::Payload {
            msg: plaintext,
            aad,
        };
        let sealed = match key.len() {
            16 => gcm::<aes_gcm::Aes128Gcm>(key).encrypt(&nonce, payload),
            24 => gcm::<Aes192Gcm>(key).encrypt(&nonce, payload),
            32 => gcm::<aes_gcm::Aes256Gcm>(key).encrypt(&nonce, payload),
            n => return Err(key_size_error(i, n)),
        }
        .map_err(|_| error(i, "the data is too long for AES-GCM"))?;
        Ok(Value::bytes(sealed))
    });
    // nil when the data does not authenticate (nothing of it is returned).
    native!(m, "Crypto::AES.open_with", |i, _, a| {
        let key = bytes(i, a.arg(0), "key")?;
        let nonce = gcm_nonce(i, a.arg(1))?;
        let sealed = bytes(i, a.arg(2), "sealed")?;
        let aad = message(i, a.arg(3))?;
        let payload = aes_gcm::aead::Payload { msg: sealed, aad };
        let opened = match key.len() {
            16 => gcm::<aes_gcm::Aes128Gcm>(key).decrypt(&nonce, payload),
            24 => gcm::<Aes192Gcm>(key).decrypt(&nonce, payload),
            32 => gcm::<aes_gcm::Aes256Gcm>(key).decrypt(&nonce, payload),
            n => return Err(key_size_error(i, n)),
        };
        Ok(opened.map(Value::bytes).unwrap_or(Value::Nil))
    });
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
                let key =
                    PrivateKey::new(&mut rand::rng(), bits as usize).map_err(|e| e.to_string())?;
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
                rsa::pss::VerifyingKey::<Sha256>::new_with_auto_salt_len((*key).clone())
                    .verify(data, &sig)
            }
            Hash::Sha384 => {
                rsa::pss::VerifyingKey::<Sha384>::new_with_auto_salt_len((*key).clone())
                    .verify(data, &sig)
            }
            Hash::Sha512 => {
                rsa::pss::VerifyingKey::<Sha512>::new_with_auto_salt_len((*key).clone())
                    .verify(data, &sig)
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

fn register_argon2(m: &mut super::Registry<NativeFn>) {
    // The PHC string of `password` hashed with `salt` and the parameters
    // (all checked by `Crypto::Argon2.hash`, and again here).
    native!(m, "Crypto::Argon2.hash_with", |i, _, a| {
        let password = Zeroizing::new(message(i, a.arg(0))?.to_vec());
        let salt = bytes(i, a.arg(1), "salt")?.to_vec();
        let params = argon2_params(
            i,
            super::int(i, a.arg(2), "memory_kib")?,
            super::int(i, a.arg(3), "iterations")?,
            super::int(i, a.arg(4), "parallelism")?,
        )?;
        if !(SALT_MIN..=SALT_MAX).contains(&salt.len()) {
            return Err(i.err_arg(&format!(
                "an argon2 salt has {SALT_MIN} to {SALT_MAX} bytes, not {}",
                salt.len()
            )));
        }
        // Tens of milliseconds and `memory_kib` of memory: on a helper
        // thread.
        let phc = i
            .block_on(move || {
                use argon2::PasswordHasher;
                argon2_id(params)
                    .hash_password_with_salt(&password, &salt)
                    .map(|h| h.to_string())
                    .map_err(|e| e.to_string())
            })?
            .map_err(|e| error(i, format!("hashing failed: {e}")))?;
        Ok(Value::string(phc))
    });
    // Whether `password` matches the argon2id PHC string `hash`;
    // `Crypto::Error` for a string that is not one.
    native!(m, "Crypto::Argon2.verify_with", |i, _, a| {
        let password = Zeroizing::new(message(i, a.arg(0))?.to_vec());
        let (phc, params) = parse_argon2(string(i, a.arg(1), "hash")?).map_err(|e| error(i, e))?;
        let ok = i
            .block_on(move || {
                use argon2::PasswordVerifier;
                match argon2_id(params).verify_password(&password, &phc) {
                    Ok(()) => Ok(true),
                    Err(argon2::password_hash::Error::PasswordInvalid) => Ok(false),
                    Err(e) => Err(e.to_string()),
                }
            })?
            .map_err(|e| error(i, format!("verifying failed: {e}")))?;
        Ok(Value::Bool(ok))
    });
    // `[memory_kib, iterations, parallelism]` of an argon2id PHC string;
    // nil for a string of another scheme (one that does not begin with
    // `$argon2id$`); `Crypto::Error` for an argon2id one that does not
    // parse.
    native!(m, "Crypto::Argon2.params_with", |i, _, a| {
        let hash = string(i, a.arg(0), "hash")?;
        if !hash.starts_with("$argon2id$") {
            return Ok(Value::Nil);
        }
        let (_, p) = parse_argon2(hash).map_err(|e| error(i, e))?;
        Ok(Value::array(vec![
            Value::Int(p.m_cost() as i64),
            Value::Int(p.t_cost() as i64),
            Value::Int(p.p_cost() as i64),
        ]))
    });
}

/// The salt sizes `Crypto::Argon2.hash` takes: PHC's `Salt` holds 8 to
/// 48 bytes; 16 at least, as RFC 9106 recommends.
const SALT_MIN: usize = 16;
const SALT_MAX: usize = argon2::password_hash::phc::Salt::MAX_LENGTH;

/// The schemes a stored password hash may be of, named in `verify?`'s
/// error.
const KNOWN_SCHEMES: &[&str] = &[
    "argon2i",
    "argon2d",
    "pbkdf2",
    "pbkdf2-sha1",
    "pbkdf2-sha256",
    "pbkdf2-sha512",
    "scrypt",
    "bcrypt",
    "yescrypt",
    "y",
    "gy",
    "7",
    "2",
    "2a",
    "2b",
    "2x",
    "2y",
    "1",
    "5",
    "6",
    "md5",
    "sha1",
];

/// The bounds of `Crypto::Argon2::Params` (`std/crypto.qz`).
const MEMORY_MAX: i64 = 4 * 1024 * 1024;
const PARALLELISM_MAX: i64 = 255;

/// The parameters' bounds, as a message (None when they are within).
fn argon2_bounds(m: i64, t: i64, p: i64) -> Option<String> {
    if !(8..=MEMORY_MAX).contains(&m) {
        Some(format!("memory_kib: 8 to {MEMORY_MAX}, not {m}"))
    } else if !(1..=u32::MAX as i64).contains(&t) {
        Some(format!("iterations: 1 to {}, not {t}", u32::MAX))
    } else if !(1..=PARALLELISM_MAX).contains(&p) {
        Some(format!("parallelism: 1 to {PARALLELISM_MAX}, not {p}"))
    } else if m < 8 * p {
        Some(format!(
            "memory_kib must be at least 8 * parallelism ({}), not {m}",
            8 * p
        ))
    } else {
        None
    }
}

fn argon2_params(interp: &Interp, m: i64, t: i64, p: i64) -> Result<argon2::Params, Flow> {
    if let Some(e) = argon2_bounds(m, t, p) {
        return Err(interp.err_arg(&e));
    }
    argon2::Params::new(m as u32, t as u32, p as u32, Some(32))
        .map_err(|e| interp.err_arg(&format!("argon2 parameters: {e}")))
}

fn argon2_id(params: argon2::Params) -> argon2::Argon2<'static> {
    argon2::Argon2::new(argon2::Algorithm::Argon2id, argon2::Version::V0x13, params)
}

/// An argon2id `v=19` PHC string with `m`, `t` and `p` only, within the
/// bounds, with a salt and a hash, and its parameters. The message names
/// what is wrong (never the password, which is not here).
fn parse_argon2(
    hash: &str,
) -> Result<(argon2::password_hash::phc::PasswordHash, argon2::Params), String> {
    use argon2::password_hash::phc::PasswordHash;
    // The scheme first, whatever the rest is: named when it is one of the
    // usual password hash schemes, so that a password given in place of
    // the hash is never echoed.
    let ident = hash
        .strip_prefix('$')
        .and_then(|rest| rest.split('$').next())
        .filter(|id| {
            !id.is_empty()
                && id.len() <= 32
                && id
                    .bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
        });
    match ident {
        Some("argon2id") => {}
        Some(id) if KNOWN_SCHEMES.contains(&id) => {
            return Err(format!("a ${id}$ hash: only argon2id hashes are read"));
        }
        Some(_) => return Err("not an argon2id hash: another scheme".to_string()),
        None => return Err("not a PHC hash string".to_string()),
    }
    let phc = PasswordHash::new(hash).map_err(|e| format!("not a PHC hash string: {e}"))?;
    match phc.version {
        Some(0x13) => {}
        Some(v) => return Err(format!("argon2id version v={v}: only v=19 is read")),
        None => return Err("an argon2id hash without its version (v=19)".to_string()),
    }
    // m, t and p once each, as decimals (`ParamsString` keeps a repeated
    // name, and the crate would hash with the last one).
    let mut mtp: [Option<i64>; 3] = [None; 3];
    for (name, value) in phc.params.iter() {
        let Some(slot) = ["m", "t", "p"].iter().position(|n| *n == name.as_str()) else {
            return Err(format!(
                "an argon2id hash with the parameter {}: only m, t and p are read",
                name.as_str()
            ));
        };
        if mtp[slot].is_some() {
            return Err(format!(
                "an argon2id hash with the parameter {} twice",
                name.as_str()
            ));
        }
        let text = value.as_str();
        // Digits, without a leading zero; at most 18 of them (the bounds
        // then refuse what is too large).
        let decimal = !text.is_empty()
            && text.len() <= 18
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text == "0" || !text.starts_with('0'));
        let n = decimal
            .then(|| text.parse::<i64>().ok())
            .flatten()
            .ok_or_else(|| {
                format!(
                    "an argon2id hash whose parameter {} is not a decimal",
                    name.as_str()
                )
            })?;
        mtp[slot] = Some(n);
    }
    let get = |slot: usize| {
        mtp[slot].ok_or_else(|| {
            format!(
                "an argon2id hash without its parameter {}",
                ["m", "t", "p"][slot]
            )
        })
    };
    let (m, t, p) = (get(0)?, get(1)?, get(2)?);
    if let Some(e) = argon2_bounds(m, t, p) {
        return Err(format!("an argon2id hash with {e}"));
    }
    if phc.salt.is_none() {
        return Err("an argon2id hash without its salt".to_string());
    }
    let Some(out) = &phc.hash else {
        return Err("an argon2id hash without its hash".to_string());
    };
    let params = argon2::Params::new(m as u32, t as u32, p as u32, Some(out.len()))
        .map_err(|e| format!("an argon2id hash with bad parameters: {e}"))?;
    Ok((phc, params))
}

/// The most `Crypto.random_bytes` gives at once.
const RANDOM_MAX: i64 = 1 << 20;

type Aes192Gcm = aes_gcm::AesGcm<aes_gcm::aes::Aes192, aes_gcm::aead::consts::U12>;

/// An AES-GCM cipher for `key` (its length checked by the caller).
fn gcm<C: aes_gcm::KeyInit>(key: &[u8]) -> C {
    C::new_from_slice(key).expect("the key's length was checked")
}

fn key_size_error(interp: &Interp, n: usize) -> Flow {
    interp.err_arg(&format!("an AES key has 16, 24 or 32 bytes, not {n}"))
}

/// A GCM nonce: exactly 12 bytes.
fn gcm_nonce(
    interp: &Interp,
    v: &Value,
) -> Result<aes_gcm::Nonce<aes_gcm::aead::consts::U12>, Flow> {
    let nonce = bytes(interp, v, "nonce")?;
    aes_gcm::Nonce::<aes_gcm::aead::consts::U12>::try_from(nonce).map_err(|_| {
        interp.err_arg(&format!(
            "an AES-GCM nonce has 12 bytes, not {}",
            nonce.len()
        ))
    })
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
fn bits(key: &PublicKey) -> i64 {
    key.n().bits() as i64
}

/// A key of at least 1024 bits signs and verifies.
fn usable(interp: &Interp, key: &PublicKey) -> Result<(), Flow> {
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
/// (`PublicKey::MIN_SIZE..=MAX_SIZE`), for private ones too.
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

fn checked_private(key: PrivateKey) -> Result<PrivateKey, String> {
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

fn private_from_pkcs8(der: &[u8]) -> Result<PrivateKey, String> {
    if let Ok(info) = rsa::pkcs8::PrivateKeyInfoRef::try_from(der) {
        let oid = info.algorithm.oid.to_string();
        if oid != RSA_OID {
            return Err(format!("not an RSA key: {}", algorithm_name(&oid)));
        }
    }
    checked_private(
        PrivateKey::from_pkcs8_der(der).map_err(|e| format!("not an RSA private key: {e}"))?,
    )
}

fn private_from_pkcs1(der: &[u8]) -> Result<PrivateKey, String> {
    checked_private(
        PrivateKey::from_pkcs1_der(der).map_err(|e| format!("not an RSA private key: {e}"))?,
    )
}

fn public_from_spki(der: &[u8]) -> Result<PublicKey, String> {
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
    PublicKey::from_public_key_der(der).map_err(|e| format!("not an RSA public key: {e}"))
}

fn public_from_pkcs1(der: &[u8]) -> Result<PublicKey, String> {
    if let Some(e) = public_size_error(der) {
        return Err(e);
    }
    PublicKey::from_pkcs1_der(der).map_err(|e| format!("not an RSA public key: {e}"))
}

/// A private key from PKCS#8 or PKCS#1 DER.
fn private_from_der(der: &[u8]) -> Result<PrivateKey, String> {
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
fn public_from_der(der: &[u8]) -> Result<PublicKey, String> {
    match public_from_spki(der) {
        Ok(k) => Ok(k),
        Err(e) if decisive(&e) => Err(e),
        Err(e) => match public_from_pkcs1(der) {
            Err(e1) if decisive(&e1) => Err(e1),
            r => r.map_err(|_| e),
        },
    }
}

fn private_pkcs8(interp: &Interp, key: &PrivateKey) -> Result<Vec<u8>, Flow> {
    key.to_pkcs8_der()
        .map(|d| d.as_bytes().to_vec())
        .map_err(|e| error(interp, format!("encoding the key failed: {e}")))
}

fn public_spki(interp: &Interp, key: &PublicKey) -> Result<Vec<u8>, Flow> {
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

static PRIVATE: Cache<PrivateKey> = OnceLock::new();

fn private_key(interp: &Interp, v: &Value) -> Result<Arc<PrivateKey>, Flow> {
    cached(interp, &PRIVATE, der_field(interp, v)?, private_from_pkcs8)
}

fn public_key(interp: &Interp, v: &Value) -> Result<Arc<PublicKey>, Flow> {
    static CACHE: Cache<PublicKey> = OnceLock::new();
    cached(interp, &CACHE, der_field(interp, v)?, public_from_spki)
}
