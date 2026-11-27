//! `std/crypto.qz` (the `crypto` feature): RSA keys and signatures
//! through RustCrypto's `rsa`, AES-GCM through `aes-gcm`, argon2id
//! password hashes through `argon2`, the system's random bytes
//! through `getrandom`, and comparison in constant time through
//! `subtle`.
//!
//! A private RSA key and an AES key are held natively (#963): a
//! `Value::Secret` whose `KeyCell` holds the parsed key (`RsaKey`) or the
//! key and its cipher (`AesKey`), parsed once, cleared when the last
//! reference goes or wiped. A public key is a `data` value holding its
//! SPKI DER, parsed per call through a cache by its digest. A message
//! never holds key material.

use std::sync::{Arc, Mutex, OnceLock};

use aes_gcm::aead::Aead;
use rsa::pkcs1::{DecodeRsaPrivateKey, DecodeRsaPublicKey, EncodeRsaPrivateKey};
use rsa::pkcs8::{
    DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey, LineEnding,
};
use rsa::signature::Verifier;
use rsa::traits::PublicKeyParts;
use rsa::{PrivateKey, PublicKey};
use sha2::{Digest, Sha256, Sha384, Sha512};
use zeroize::Zeroizing;

use crate::interp::{Flow, Interp, NativeFn};
use crate::value::*;

use super::string;

pub fn register(m: &mut super::Registry<NativeFn>) {
    register_argon2(m);
    register_secret(m);
    register_keys(m);
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
    native!(m, "Crypto.secure_compare", |i, _, a| {
        use subtle::ConstantTimeEq;
        // Either may be a `Bytes::Secret` (quarz#1015): read through a
        // copy cleared when dropped; a wiped one raises `WipedError`.
        let x = compared(i, a.arg(0))?;
        let y = compared(i, a.arg(1))?;
        // `ct_eq` on slices answers false at once for different lengths.
        Ok(Value::Bool((*x).ct_eq(&*y).into()))
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
    native!(m, "Crypto::RSA::PublicKey#bits", |i, r, _| {
        Ok(Value::Int(bits(&*public_key(i, r)?)))
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
        Ok(Value::bytes(Sha256::digest(&*der_field(i, r)?).to_vec()))
    });
}

/// An RSA private key held natively (`KeyKind::RsaPrivate`): `rsa`'s
/// key clears itself when dropped (`ZeroizeOnDrop`).
struct RsaKey(PrivateKey);

impl KeyMaterial for RsaKey {
    /// The public parts compared as they are, the secret ones (`d`, the
    /// primes) in constant time and all of them, without stopping at the
    /// first difference (`rsa`'s own `==` stops between parts).
    fn same_key(&self, other: &dyn KeyMaterial) -> bool {
        use rsa::traits::PrivateKeyParts;
        let Some(o) = other.as_any().downcast_ref::<RsaKey>() else {
            return false;
        };
        let (a, b) = (&self.0, &o.0);
        if a.n() != b.n() || a.e() != b.e() || a.primes().len() != b.primes().len() {
            return false;
        }
        // The secret parts as big-endian bytes, each pair compared in
        // constant time and every pair compared; the copies cleared.
        let mut same = true;
        let mut pair = |x: &rsa::BoxedUint, y: &rsa::BoxedUint| {
            let (mut x, mut y) = (x.to_be_bytes(), y.to_be_bytes());
            same &= constant_time_eq(&x, &y);
            clear_bytes(&mut x);
            clear_bytes(&mut y);
        };
        pair(a.d(), b.d());
        for (p, q) in a.primes().iter().zip(b.primes()) {
            pair(p.as_ref(), q.as_ref());
        }
        same
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

/// An AES key held natively (`KeyKind::Aes`): the key itself (for
/// `export_key` and `==`), cleared when dropped, and its cipher with the
/// key schedule built once (`aes-gcm`'s `zeroize`: cleared when dropped).
struct AesKey {
    raw: Zeroizing<Vec<u8>>,
    cipher: AesCipher,
}

enum AesCipher {
    A128(aes_gcm::Aes128Gcm),
    A192(Aes192Gcm),
    A256(aes_gcm::Aes256Gcm),
}

impl KeyMaterial for AesKey {
    fn same_key(&self, other: &dyn KeyMaterial) -> bool {
        other
            .as_any()
            .downcast_ref::<AesKey>()
            .is_some_and(|o| constant_time_eq(&self.raw, &o.raw))
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

impl AesKey {
    fn new(interp: &Interp, raw: Zeroizing<Vec<u8>>) -> Result<AesKey, Flow> {
        use aes_gcm::KeyInit;
        let cipher = match raw.len() {
            16 => AesCipher::A128(aes_gcm::Aes128Gcm::new_from_slice(&raw).expect("16 bytes")),
            24 => AesCipher::A192(Aes192Gcm::new_from_slice(&raw).expect("24 bytes")),
            32 => AesCipher::A256(aes_gcm::Aes256Gcm::new_from_slice(&raw).expect("32 bytes")),
            n => return Err(key_size_error(interp, n)),
        };
        Ok(AesKey { raw, cipher })
    }

    fn seal(
        &self,
        nonce: &aes_gcm::Nonce<aes_gcm::aead::consts::U12>,
        p: aes_gcm::aead::Payload,
    ) -> Option<Vec<u8>> {
        match &self.cipher {
            AesCipher::A128(c) => c.encrypt(nonce, p),
            AesCipher::A192(c) => c.encrypt(nonce, p),
            AesCipher::A256(c) => c.encrypt(nonce, p),
        }
        .ok()
    }

    fn open(
        &self,
        nonce: &aes_gcm::Nonce<aes_gcm::aead::consts::U12>,
        p: aes_gcm::aead::Payload,
    ) -> Option<Vec<u8>> {
        match &self.cipher {
            AesCipher::A128(c) => c.decrypt(nonce, p),
            AesCipher::A192(c) => c.decrypt(nonce, p),
            AesCipher::A256(c) => c.decrypt(nonce, p),
        }
        .ok()
    }
}

/// A new key value of `kind` holding `key`.
fn key_value(kind: KeyKind, bits: usize, key: Arc<dyn KeyMaterial>) -> Value {
    Value::Secret(crate::rc::Rc::new(SecretVal::Key(KeyCell::new(
        kind, bits, key,
    ))))
}

/// The `KeyCell` of a key receiver of `kind`.
fn key_cell<'a>(interp: &Interp, v: &'a Value, kind: KeyKind) -> Result<&'a KeyCell, Flow> {
    match v {
        Value::Secret(s) => match &**s {
            SecretVal::Key(k) if k.kind() == kind => Ok(k),
            _ => Err(interp.err_type("a Crypto key was expected")),
        },
        _ => Err(interp.err_type("a Crypto key was expected")),
    }
}

/// The material of a key receiver for one operation (a snapshot: the
/// operation runs on its own reference, `KeyCell`); a wiped key raises.
fn key_material(interp: &Interp, v: &Value, kind: KeyKind) -> Result<Arc<dyn KeyMaterial>, Flow> {
    key_cell(interp, v, kind)?
        .get()
        .ok_or_else(|| super::bytes::wiped(interp))
}

fn rsa_key(interp: &Interp, v: &Value) -> Result<Arc<dyn KeyMaterial>, Flow> {
    key_material(interp, v, KeyKind::RsaPrivate)
}

fn as_rsa(m: &Arc<dyn KeyMaterial>) -> &PrivateKey {
    &m.as_any().downcast_ref::<RsaKey>().expect("an RSA key").0
}

fn as_aes(m: &Arc<dyn KeyMaterial>) -> &AesKey {
    m.as_any().downcast_ref::<AesKey>().expect("an AES key")
}

/// A private key read and checked: a key value.
fn private_value(_interp: &Interp, key: PrivateKey) -> Result<Value, Flow> {
    let bits = bits(&key.to_public_key());
    Ok(key_value(
        KeyKind::RsaPrivate,
        bits as usize,
        Arc::new(RsaKey(key)),
    ))
}

/// The keys held natively (#963): `Crypto::RSA::PrivateKey` and
/// `Crypto::AES::GCM`, their `wipe`, `==` and exports.
fn register_keys(m: &mut super::Registry<NativeFn>) {
    native!(m, "Crypto::RSA::PrivateKey.new", |i, _, a| {
        let der = super::bytes::secret_input(i, a.arg(0), "der")?;
        let key = private_from_der(&der).map_err(|e| error(i, e))?;
        private_value(i, key)
    });
    native!(m, "Crypto::RSA::PrivateKey.from_pem", |i, _, a| {
        let pem = super::bytes::secret_input(i, a.arg(0), "pem")?;
        let (label, der) = one_block(&pem).map_err(|e| error(i, e))?;
        let key = match label.as_str() {
            "PRIVATE KEY" => private_from_pkcs8(&der),
            "RSA PRIVATE KEY" => private_from_pkcs1(&der),
            "ENCRYPTED PRIVATE KEY" => Err(ENCRYPTED.to_string()),
            other => Err(format!("not a private key: {other}")),
        }
        .map_err(|e| error(i, e))?;
        private_value(i, key)
    });
    native!(m, "Crypto::RSA::PrivateKey.generate_with", |i, _, a| {
        let bits = super::int(i, a.arg(0), "bits")?;
        // Hundreds of milliseconds for 4096 bits: on a helper thread.
        let key = i
            .block_on(move || {
                PrivateKey::new(&mut rand::rng(), bits as usize).map_err(|e| e.to_string())
            })?
            .map_err(|e| error(i, format!("generating a key failed: {e}")))?;
        private_value(i, key)
    });
    native!(m, "Crypto::RSA::PrivateKey#export_der", |i, r, _| {
        let key = rsa_key(i, r)?;
        Ok(into_secret(private_pkcs8(i, as_rsa(&key))?))
    });
    native!(m, "Crypto::RSA::PrivateKey#export_pem", |i, r, a| {
        let key = rsa_key(i, r)?;
        let key = as_rsa(&key);
        let format = a.pos.first().map(|v| symbol(i, v, "format")).transpose()?;
        let pem = match format.as_deref().unwrap_or("pkcs8") {
            "pkcs8" => key.to_pkcs8_pem(LineEnding::LF).map_err(|e| e.to_string()),
            "pkcs1" => key.to_pkcs1_pem(LineEnding::LF).map_err(|e| e.to_string()),
            other => return Err(i.err_arg(&format!("format: :pkcs8 or :pkcs1, not :{other}"))),
        }
        .map_err(|e| error(i, format!("encoding the key failed: {e}")))?;
        Ok(into_secret(Zeroizing::new(pem.as_bytes().to_vec())))
    });
    native!(m, "Crypto::RSA::PrivateKey#public_der", |i, r, _| {
        let key = rsa_key(i, r)?;
        Ok(Value::bytes(public_spki(i, &as_rsa(&key).to_public_key())?))
    });
    native!(m, "Crypto::RSA::PrivateKey#bits", |i, r, _| {
        Ok(Value::Int(
            key_cell(i, r, KeyKind::RsaPrivate)?.bits() as i64
        ))
    });
    native!(m, "Crypto::RSA::PrivateKey#sign", |i, r, a| {
        let held = rsa_key(i, r)?;
        let key = as_rsa(&held);
        usable(i, &key.to_public_key())?;
        let data = message(i, a.arg(0))?;
        // The same (deterministic) signature, computed blinded, from the
        // key as it is held: no copy of it.
        let mut rng = rand::rng();
        let sig = match hash(i, a.arg(1))? {
            Hash::Sha256 => key.sign_with_rng(
                &mut rng,
                rsa::Pkcs1v15Sign::new::<Sha256>(),
                &Sha256::digest(data),
            ),
            Hash::Sha384 => key.sign_with_rng(
                &mut rng,
                rsa::Pkcs1v15Sign::new::<Sha384>(),
                &Sha384::digest(data),
            ),
            Hash::Sha512 => key.sign_with_rng(
                &mut rng,
                rsa::Pkcs1v15Sign::new::<Sha512>(),
                &Sha512::digest(data),
            ),
        }
        .map_err(|e| error(i, format!("signing failed: {e}")))?;
        Ok(Value::bytes(sig))
    });
    native!(m, "Crypto::RSA::PrivateKey#sign_pss", |i, r, a| {
        let held = rsa_key(i, r)?;
        let key = as_rsa(&held);
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
        // The salt as long as the hash (`Pss::new`'s default).
        let sig = match h {
            Hash::Sha256 => key.sign_with_rng(
                &mut rng,
                rsa::pss::Pss::<Sha256>::new(),
                &Sha256::digest(data),
            ),
            Hash::Sha384 => key.sign_with_rng(
                &mut rng,
                rsa::pss::Pss::<Sha384>::new(),
                &Sha384::digest(data),
            ),
            Hash::Sha512 => key.sign_with_rng(
                &mut rng,
                rsa::pss::Pss::<Sha512>::new(),
                &Sha512::digest(data),
            ),
        }
        .map_err(|e| error(i, format!("signing failed: {e}")))?;
        Ok(Value::bytes(sig))
    });
    native!(m, "Crypto::AES::GCM.new", |i, _, a| {
        let raw = super::bytes::secret_input(i, a.arg(0), "key")?;
        let key = AesKey::new(i, Zeroizing::new(raw.to_vec()))?;
        let bits = key.raw.len() * 8;
        Ok(key_value(KeyKind::Aes, bits, Arc::new(key)))
    });
    native!(m, "Crypto::AES::GCM#bits", |i, r, _| {
        Ok(Value::Int(key_cell(i, r, KeyKind::Aes)?.bits() as i64))
    });
    native!(m, "Crypto::AES::GCM#seal", |i, r, a| {
        let held = key_material(i, r, KeyKind::Aes)?;
        let nonce = gcm_nonce(i, a.arg(0))?;
        let plaintext = message(i, a.arg(1))?;
        let aad = aad(i, &a)?;
        let payload = aes_gcm::aead::Payload {
            msg: plaintext,
            aad,
        };
        let sealed = as_aes(&held)
            .seal(&nonce, payload)
            .ok_or_else(|| error(i, "the data is too long for AES-GCM"))?;
        Ok(Value::bytes(sealed))
    });
    // nil when the data does not authenticate (nothing of it is returned).
    native!(m, "Crypto::AES::GCM#open?", |i, r, a| {
        Ok(gcm_open(i, r, &a)?.map(Value::bytes).unwrap_or(Value::Nil))
    });
    native!(m, "Crypto::AES::GCM#open_secret?", |i, r, a| {
        // The plaintext's buffer becomes the secret's: no copy is made.
        Ok(gcm_open(i, r, &a)?
            .map(super::bytes::secret)
            .unwrap_or(Value::Nil))
    });
    native!(m, "Crypto::AES::GCM#export_key", |i, r, _| {
        let held = key_material(i, r, KeyKind::Aes)?;
        Ok(super::bytes::secret(as_aes(&held).raw.to_vec()))
    });
    native!(
        m,
        ["Crypto::RSA::PrivateKey#wipe", "Crypto::AES::GCM#wipe"],
        |i, r, _| {
            any_key(i, r)?.wipe();
            Ok(Value::Nil)
        }
    );
    native!(
        m,
        ["Crypto::RSA::PrivateKey#wiped?", "Crypto::AES::GCM#wiped?"],
        |i, r, _| Ok(Value::Bool(any_key(i, r)?.wiped()))
    );
    native!(
        m,
        ["Crypto::RSA::PrivateKey#==", "Crypto::AES::GCM#=="],
        |i, r, a| {
            let x = any_key(i, r)?;
            // A key of the same class; anything else (a `Bytes::Secret`,
            // the other kind of key, any other value) is not equal, and
            // raises only when the receiver is wiped.
            let other = match a.arg(0) {
                Value::Secret(s) => match &**s {
                    SecretVal::Key(k) if k.kind() == x.kind() => Some(k),
                    _ => None,
                },
                _ => None,
            };
            // Raises for a wiped key of the same class, itself included
            // (`Value`'s `==`, which cannot raise, differs there).
            match other {
                Some(y) => Ok(Value::Bool(
                    KeyCell::equal(x, y).ok_or_else(|| super::bytes::wiped(i))?,
                )),
                None if x.wiped() => Err(super::bytes::wiped(i)),
                None => Ok(Value::Bool(false)),
            }
        }
    );
}

/// The `KeyCell` of either kind of key.
fn any_key<'a>(interp: &Interp, v: &'a Value) -> Result<&'a KeyCell, Flow> {
    match v {
        Value::Secret(s) => match &**s {
            SecretVal::Key(k) => Ok(k),
            _ => Err(interp.err_type("a Crypto key was expected")),
        },
        _ => Err(interp.err_type("a Crypto key was expected")),
    }
}

/// The `aad:` keyword of `seal`/`open?` (`""` when absent).
fn aad<'a>(interp: &Interp, a: &'a crate::interp::Args) -> Result<&'a [u8], Flow> {
    match a.kw(interp, "aad") {
        Some(v) => message(interp, v),
        None => Ok(b""),
    }
}

/// `open?`'s arguments opened with the receiver's key: the plaintext,
/// `None` when it does not authenticate (then nothing of it is kept).
fn gcm_open(i: &Interp, r: &Value, a: &crate::interp::Args) -> Result<Option<Vec<u8>>, Flow> {
    let held = key_material(i, r, KeyKind::Aes)?;
    let nonce = gcm_nonce(i, a.arg(0))?;
    let sealed = bytes(i, a.arg(1), "sealed")?;
    let aad = aad(i, a)?;
    let payload = aes_gcm::aead::Payload { msg: sealed, aad };
    Ok(as_aes(&held).open(&nonce, payload))
}

/// `Crypto.random_secret` (#963): random bytes straight into a
/// `Bytes::Secret`.
fn register_secret(m: &mut super::Registry<NativeFn>) {
    native!(m, "Crypto.random_secret", |i, _, a| {
        let n = super::int(i, a.arg(0), "n")?;
        if !(0..=RANDOM_MAX).contains(&n) {
            return Err(i.err_arg(&format!("random_secret: 0 to {RANDOM_MAX} bytes, not {n}")));
        }
        let mut buf = vec![0u8; n as usize];
        if let Err(e) = getrandom::fill(&mut buf) {
            clear_bytes(&mut buf);
            return Err(error(i, format!("the system's random source failed: {e}")));
        }
        Ok(super::bytes::secret(buf))
    });
}

fn register_argon2(m: &mut super::Registry<NativeFn>) {
    // The PHC string of `password` hashed with `salt` and the parameters
    // (all checked by `Crypto::Argon2.hash`, and again here).
    native!(m, "Crypto::Argon2.hash_with", |i, _, a| {
        // A `Bytes::Secret` too; the copy, cleared when dropped, goes to
        // the helper thread.
        let password = super::bytes::secret_input(i, a.arg(0), "password")?.into_owned();
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
        // A `Bytes::Secret` too; the copy, cleared when dropped, goes to
        // the helper thread.
        let password = super::bytes::secret_input(i, a.arg(0), "password")?.into_owned();
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

/// What `Crypto.secure_compare` compares: `Bytes`, a `String`'s UTF-8
/// bytes, or a `Bytes::Secret`'s.
fn compared<'a>(interp: &Interp, v: &'a Value) -> Result<super::bytes::SecretInput<'a>, Flow> {
    super::bytes::secret_input(interp, v, "secure_compare")
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
    key.n().bit_width() as i64
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
fn one_block(text: &[u8]) -> Result<(String, Zeroizing<Vec<u8>>), String> {
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
    Ok((label.to_string(), Zeroizing::new(der)))
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
    let n = key.n().bit_width() as usize;
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

/// A private key's PKCS#8 DER, in a buffer cleared when dropped.
fn private_pkcs8(interp: &Interp, key: &PrivateKey) -> Result<Zeroizing<Vec<u8>>, Flow> {
    key.to_pkcs8_der()
        .map(|d| Zeroizing::new(d.as_bytes().to_vec()))
        .map_err(|e| error(interp, format!("encoding the key failed: {e}")))
}

/// A `Bytes::Secret` of `buf`'s contents, `buf` cleared.
fn into_secret(mut buf: Zeroizing<Vec<u8>>) -> Value {
    super::bytes::secret(std::mem::take(&mut *buf))
}

fn public_spki(interp: &Interp, key: &PublicKey) -> Result<Vec<u8>, Flow> {
    key.to_public_key_der()
        .map(|d| d.as_bytes().to_vec())
        .map_err(|e| error(interp, format!("encoding the key failed: {e}")))
}

/// The DER field of a key (`data PrivateKey(der: Bytes)`), shared, not
/// copied.
fn der_field(interp: &Interp, v: &Value) -> Result<crate::rc::Rc<[u8]>, Flow> {
    let Value::Object(o) = v else {
        return Err(interp.err_type("expected a Crypto::RSA key"));
    };
    match o.field(0) {
        Some(Value::Bytes(b)) => Ok(b.clone()),
        _ => Err(interp.err_type("expected a Crypto::RSA key")),
    }
}

/// The keys parsed, by the SHA-256 of their DER (a program uses a few;
/// past `CACHED`, the cache starts again). By digest rather than by the
/// DER itself, so that the cache holds no copy of a private key's DER
/// (#963); the parsed keys clear themselves when dropped (`rsa`'s
/// `ZeroizeOnDrop`). The DER is not compared again on a hit: two DERs
/// with one SHA-256 would take one key for the other, and finding such
/// a pair is SHA-256's collision resistance (about 2^128 work, which
/// nobody has done); a digest found is the same DER, as Git's object
/// names and certificate pinning take it.
const CACHED: usize = 64;

type Cache<K> = OnceLock<Mutex<quarz_ir::HashMap<[u8; 32], Arc<K>>>>;

fn cached<K>(
    interp: &Interp,
    cache: &'static Cache<K>,
    der: &[u8],
    parse: fn(&[u8]) -> Result<K, String>,
) -> Result<Arc<K>, Flow> {
    let cache = cache.get_or_init(Default::default);
    let id: [u8; 32] = Sha256::digest(der).into();
    if let Some(k) = crate::sched::lock(cache).get(&id) {
        return Ok(k.clone());
    }
    let key = Arc::new(parse(der).map_err(|e| error(interp, e))?);
    let mut c = crate::sched::lock(cache);
    if c.len() >= CACHED {
        c.clear();
    }
    c.insert(id, key.clone());
    Ok(key)
}

fn public_key(interp: &Interp, v: &Value) -> Result<Arc<PublicKey>, Flow> {
    static CACHE: Cache<PublicKey> = OnceLock::new();
    cached(interp, &CACHE, &der_field(interp, v)?, public_from_spki)
}
