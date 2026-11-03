//! `std/digest.qz` (SHA-256, MD5, HMAC-SHA-256, PBKDF2) and
//! `std/base64.qz`, with the RustCrypto crates and `base64`.

use base64::alphabet;
use base64::engine::general_purpose::{GeneralPurpose, GeneralPurposeConfig};
use base64::engine::DecodePaddingMode;
use base64::Engine;
use hmac::{Hmac, Mac};
use md5::Md5;
use sha2::{Digest, Sha256};

use crate::interp::{Flow, Interp, NativeFn};
use crate::value::*;

use super::{int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Digest::SHA256.digest", |i, _, a| {
        Ok(Value::bytes(
            Sha256::digest(data(i, a.arg(0), "data")?).to_vec(),
        ))
    });
    native!(m, "Digest::SHA256.hexdigest", |i, _, a| {
        Ok(Value::string(hex(&Sha256::digest(data(
            i,
            a.arg(0),
            "data",
        )?))))
    });
    native!(m, "Digest::MD5.digest", |i, _, a| {
        Ok(Value::bytes(
            Md5::digest(data(i, a.arg(0), "data")?).to_vec(),
        ))
    });
    native!(m, "Digest::MD5.hexdigest", |i, _, a| {
        Ok(Value::string(hex(&Md5::digest(data(i, a.arg(0), "data")?))))
    });
    native!(m, "Digest::HMAC.sha256", |i, _, a| {
        // HMAC takes a key of any length.
        let mut mac = Hmac::<Sha256>::new_from_slice(data(i, a.arg(0), "key")?).unwrap();
        mac.update(data(i, a.arg(1), "data")?);
        Ok(Value::bytes(mac.finalize().into_bytes().to_vec()))
    });
    native!(m, "Digest::PBKDF2.sha256", |i, _, a| {
        let password = data(i, a.arg(0), "password")?;
        let salt = data(i, a.arg(1), "salt")?;
        let iterations = int(i, a.arg(2), "iterations")?;
        let length = int(i, a.arg(3), "length")?;
        let Ok(rounds) = u32::try_from(iterations) else {
            return Err(i.err_arg(&format!("iterations out of range: {iterations}")));
        };
        if rounds == 0 {
            return Err(i.err_arg("iterations must be positive"));
        }
        if length < 0 {
            return Err(i.err_arg(&format!("negative length: {length}")));
        }
        // RFC 8018 §5.2: at most (2^32 - 1) blocks of the hash's size.
        if length > PBKDF2_MAX_LENGTH {
            return Err(i.err_arg(&format!("length too large: {length}")));
        }
        // A length the RFC allows may still not fit in memory: raise
        // rather than abort the process.
        let mut out = Vec::new();
        if out.try_reserve_exact(length as usize).is_err() {
            return Err(i.err_arg(&format!("length too large: {length}")));
        }
        out.resize(length as usize, 0u8);
        pbkdf2::pbkdf2_hmac::<Sha256>(password, salt, rounds, &mut out);
        Ok(Value::bytes(out))
    });

    native!(m, "Base64.encode", |i, _, a| {
        Ok(Value::string(STANDARD.encode(data(i, a.arg(0), "data")?)))
    });
    native!(m, "Base64.decode", |i, _, a| {
        decode(i, &alphabet::STANDARD, string(i, a.arg(0), "text")?)
    });
    native!(m, "Base64.urlsafe_encode", |i, _, a| {
        let bytes = data(i, a.arg(0), "data")?;
        let padding = !matches!(a.kw(i, "padding"), Some(Value::Bool(false)));
        Ok(Value::string(if padding {
            URL_SAFE.encode(bytes)
        } else {
            URL_SAFE_NO_PAD.encode(bytes)
        }))
    });
    native!(m, "Base64.urlsafe_decode", |i, _, a| {
        decode(i, &alphabet::URL_SAFE, string(i, a.arg(0), "text")?)
    });
}

/// The longest key PBKDF2 derives with HMAC-SHA-256.
const PBKDF2_MAX_LENGTH: i64 = (u32::MAX as i64) * 32;

/// Encoders pad unless told otherwise.
const STANDARD: GeneralPurpose = GeneralPurpose::new(&alphabet::STANDARD, PADDED);
const URL_SAFE: GeneralPurpose = GeneralPurpose::new(&alphabet::URL_SAFE, PADDED);
const URL_SAFE_NO_PAD: GeneralPurpose =
    GeneralPurpose::new(&alphabet::URL_SAFE, PADDED.with_encode_padding(false));
const PADDED: GeneralPurposeConfig = GeneralPurposeConfig::new();

/// Decoders take the text padded as the encoder pads it, or without any
/// padding: a partial padding (`Zg=`) is refused.
fn decode(interp: &Interp, alphabet: &alphabet::Alphabet, text: &str) -> Result<Value, Flow> {
    let padding = if text.ends_with('=') {
        DecodePaddingMode::RequireCanonical
    } else {
        DecodePaddingMode::RequireNone
    };
    let engine = GeneralPurpose::new(
        alphabet,
        GeneralPurposeConfig::new().with_decode_padding_mode(padding),
    );
    match engine.decode(text) {
        Ok(bytes) => Ok(Value::bytes(bytes)),
        Err(e) => Err(interp.err_arg(&format!("invalid base64: {e}"))),
    }
}

/// The bytes of a `Bytes | String` argument (a string's UTF-8).
fn data<'a>(interp: &Interp, v: &'a Value, what: &str) -> Result<&'a [u8], Flow> {
    match v {
        Value::Bytes(b) => Ok(b),
        v => match v.as_str() {
            Some(s) => Ok(s.as_bytes()),
            None => Err(interp.err_type(&format!(
                "{what} must be Bytes or a String, got {}",
                interp.class_name(v)
            ))),
        },
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
