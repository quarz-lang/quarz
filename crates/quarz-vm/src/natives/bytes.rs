//! Bytes and Bytes::Builder.

use crate::rc::Rc;
use std::cell::RefCell;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::{block, int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Bytes.new", |_, _, _| Ok(Value::bytes(Vec::new())));
    native!(m, "Bytes.[]", |i, _, a| {
        let mut out = Vec::with_capacity(a.pos.len());
        for v in a.pos.iter() {
            out.push(byte(i, v)?);
        }
        Ok(Value::bytes(out))
    });
    native!(m, "Bytes.from", |i, _, a| match a.arg(0) {
        Value::Array(items) => {
            let mut out = Vec::with_capacity(items.len());
            for v in items.iter() {
                out.push(byte(i, &v)?);
            }
            Ok(Value::bytes(out))
        }
        other => Err(i.err_type(&format!(
            "Bytes.from takes an Array[Int], got {}",
            i.class_name(other)
        ))),
    });
    native!(m, "Bytes.from_hex", |i, _, a| {
        let text = string(i, a.arg(0), "hex")?;
        let digits: Vec<u8> = text.bytes().filter(|b| !b.is_ascii_whitespace()).collect();
        if !digits.len().is_multiple_of(2) || !digits.iter().all(u8::is_ascii_hexdigit) {
            return Err(i.err_arg(&format!("invalid hex string {:?}", text)));
        }
        let out = digits
            .chunks(2)
            .map(|pair| {
                let hi = (pair[0] as char).to_digit(16).unwrap() as u8;
                let lo = (pair[1] as char).to_digit(16).unwrap() as u8;
                hi << 4 | lo
            })
            .collect();
        Ok(Value::bytes(out))
    });
    native!(m, "Bytes.build", |i, _, a| {
        let b = block(i, &a)?;
        let builder = Rc::new(RefCell::new(Vec::new()));
        i.call_block(&b, smallvec![Value::BytesBuilder(builder.clone())])?;
        let out = std::mem::take(&mut *builder.borrow_mut());
        Ok(Value::bytes(out))
    });

    native!(m, "Bytes#each", bytes_each);
    native!(m, "Bytes#each_byte", bytes_each);
    native!(m, "Bytes#size", |i, r, _| {
        Ok(Value::Int(bs(i, r)?.len() as i64))
    });
    native!(m, "Bytes#length", |i, r, _| {
        Ok(Value::Int(bs(i, r)?.len() as i64))
    });
    native!(m, "Bytes#bytesize", |i, r, _| {
        Ok(Value::Int(bs(i, r)?.len() as i64))
    });
    native!(m, "Bytes#empty?", |i, r, _| {
        Ok(Value::Bool(bs(i, r)?.is_empty()))
    });
    native!(m, "Bytes#[]", |i, r, a| {
        let data = bs(i, r)?;
        match a.arg(0) {
            Value::Int(idx) => match offset(&data, *idx) {
                Some(k) => Ok(Value::Int(data[k] as i64)),
                None => Err(i.err_index(&format!("index {idx} out of bounds"))),
            },
            Value::Range(range) => {
                let (lo, hi) = super::string::range_bounds(i, range, data.len())?
                    .unwrap_or((data.len(), data.len()));
                Ok(Value::bytes(data[lo..hi].to_vec()))
            }
            other => Err(i.err_type(&format!(
                "Bytes#[] takes an Int or Range, got {}",
                i.class_name(other)
            ))),
        }
    });
    native!(m, "Bytes#[]?", |i, r, a| {
        let data = bs(i, r)?;
        let idx = int(i, a.arg(0), "index")?;
        Ok(match offset(&data, idx) {
            Some(k) => Value::Int(data[k] as i64),
            None => Value::Nil,
        })
    });
    native!(m, "Bytes#slice", |i, r, a| {
        let data = bs(i, r)?;
        let start = int(i, a.arg(0), "start")?;
        let len = int(i, a.arg(1), "length")?.max(0) as usize;
        let start = match offset(&data, start) {
            Some(k) => k,
            None if start == data.len() as i64 => data.len(),
            None => return Err(i.err_index(&format!("index {start} out of bounds"))),
        };
        let end = (start + len).min(data.len());
        Ok(Value::bytes(data[start..end].to_vec()))
    });
    native!(m, "Bytes#+", |i, r, a| {
        let mut out = bs(i, r)?.to_vec();
        out.extend_from_slice(&bs(i, a.arg(0))?);
        Ok(Value::bytes(out))
    });
    native!(m, "Bytes#==", |i, r, a| {
        Ok(Value::Bool(
            matches!(a.arg(0), Value::Bytes(o) if *o == bs(i, r)?),
        ))
    });
    native!(m, "Bytes#<=>", |i, r, a| {
        Ok(Value::Int(bs(i, r)?.cmp(&bs(i, a.arg(0))?) as i64))
    });
    native!(m, "Bytes#hash", |i, r, _| {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        bs(i, r)?.hash(&mut h);
        Ok(Value::Int((h.finish() >> 1) as i64))
    });
    native!(m, "Bytes#reverse", |i, r, _| {
        let mut out = bs(i, r)?.to_vec();
        out.reverse();
        Ok(Value::bytes(out))
    });
    native!(m, "Bytes#to_a", |i, r, _| {
        Ok(Value::array(
            bs(i, r)?.iter().map(|b| Value::Int(*b as i64)).collect(),
        ))
    });
    native!(m, "Bytes#decode", |i, r, a| {
        let data = bs(i, r)?;
        let encoding = match a.pos.first() {
            Some(v) => string(i, v, "encoding")?,
            None => "UTF-8",
        };
        match decode(&data, encoding) {
            Some(Ok(s)) => Ok(Value::string(s)),
            Some(Err(at)) => Err(i.err_arg(&format!(
                "invalid {} byte sequence at offset {at}",
                encoding.to_uppercase()
            ))),
            None => Err(i.err_arg(&format!("unknown encoding {:?}", encoding))),
        }
    });
    native!(m, "Bytes#decode?", |i, r, _| {
        Ok(match std::str::from_utf8(&bs(i, r)?) {
            Ok(s) => Value::str(s),
            Err(_) => Value::Nil,
        })
    });
    native!(m, "Bytes#hex", |i, r, _| {
        Ok(Value::string(
            bs(i, r)?.iter().map(|b| format!("{b:02x}")).collect(),
        ))
    });
    native!(m, "Bytes#to_s", |i, r, _| {
        Ok(Value::string(inspect_bytes(&bs(i, r)?)))
    });
    native!(m, "Bytes#inspect", |i, r, _| {
        Ok(Value::string(inspect_bytes(&bs(i, r)?)))
    });

    native!(m, "Bytes::Builder.new", |_, _, _| {
        Ok(Value::BytesBuilder(Rc::new(RefCell::new(Vec::new()))))
    });
    native!(m, "Bytes::Builder#<<", builder_push);
    native!(m, "Bytes::Builder#push", builder_push);
    native!(m, "Bytes::Builder#size", |i, r, _| {
        Ok(Value::Int(bb(i, r)?.borrow().len() as i64))
    });
    native!(m, "Bytes::Builder#empty?", |i, r, _| {
        Ok(Value::Bool(bb(i, r)?.borrow().is_empty()))
    });
    native!(m, "Bytes::Builder#clear", |i, r, _| {
        bb(i, r)?.borrow_mut().clear();
        Ok(r.clone())
    });
    native!(m, "Bytes::Builder#to_bytes", |i, r, _| {
        Ok(Value::bytes(bb(i, r)?.borrow().clone()))
    });
    native!(m, "Bytes::Builder#snapshot", |i, r, _| {
        Ok(Value::bytes(bb(i, r)?.borrow().clone()))
    });
    native!(m, "Bytes::Builder#to_s", |i, r, _| {
        Ok(Value::string(inspect_bytes(&bb(i, r)?.borrow())))
    });
    native!(m, "Bytes::Builder#inspect", |i, r, _| {
        Ok(Value::string(inspect_bytes(&bb(i, r)?.borrow())))
    });

    native!(m, "String#to_bytes", string_to_bytes);
    native!(m, "String#b", string_to_bytes);
    native!(m, "String#encode", |i, r, a| {
        let text = string(i, r, "receiver")?;
        let encoding = match a.pos.first() {
            Some(v) => string(i, v, "encoding")?,
            None => "UTF-8",
        };
        match encode(text, encoding) {
            Some(Ok(bytes)) => Ok(Value::bytes(bytes)),
            Some(Err(c)) => Err(i.err_arg(&format!(
                "{c:?} cannot be encoded in {}",
                encoding.to_uppercase()
            ))),
            None => Err(i.err_arg(&format!("unknown encoding {:?}", encoding))),
        }
    });
}

/// `String#to_bytes` and `String#b`: the UTF-8 bytes.
fn string_to_bytes(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::bytes(
        string(interp, recv, "receiver")?.as_bytes().to_vec(),
    ))
}

fn bs(interp: &Interp, v: &Value) -> Result<Rc<[u8]>, Flow> {
    match v {
        Value::Bytes(b) => Ok(b.clone()),
        _ => Err(interp.err_type(&format!("expected Bytes, got {}", interp.class_name(v)))),
    }
}

fn bb<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RefCell<Vec<u8>>>, Flow> {
    match v {
        Value::BytesBuilder(b) => Ok(b),
        _ => Err(interp.err_type("expected a Bytes::Builder")),
    }
}

fn byte(interp: &Interp, v: &Value) -> Result<u8, Flow> {
    let n = int(interp, v, "byte")?;
    u8::try_from(n).map_err(|_| {
        interp.raise(
            interp.program.exc.range_error,
            &format!("{n} is not a byte (0..255)"),
        )
    })
}

fn offset(data: &[u8], idx: i64) -> Option<usize> {
    let n = data.len() as i64;
    let k = if idx < 0 { n + idx } else { idx };
    (0..n).contains(&k).then_some(k as usize)
}

fn bytes_each(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let data = bs(interp, recv)?;
    let b = block(interp, &args)?;
    for byte in data.iter() {
        interp.call_block(&b, smallvec![Value::Int(*byte as i64)])?;
    }
    Ok(Value::Nil)
}

fn builder_push(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let builder = bb(interp, recv)?;
    match args.arg(0) {
        Value::Bytes(b) => builder.borrow_mut().extend_from_slice(b),
        v if v.is_str() => builder
            .borrow_mut()
            .extend_from_slice(v.as_str().unwrap_or("").as_bytes()),
        v => {
            let b = byte(interp, v)?;
            builder.borrow_mut().push(b);
        }
    }
    Ok(recv.clone())
}

/// Decode `data` in `encoding`; `None` for an unknown encoding, `Err(at)`
/// for an invalid sequence at byte `at`.
fn decode(data: &[u8], encoding: &str) -> Option<Result<String, usize>> {
    match encoding.to_ascii_uppercase().as_str() {
        "UTF-8" | "UTF8" => Some(
            std::str::from_utf8(data)
                .map(str::to_string)
                .map_err(|e| e.valid_up_to()),
        ),
        "ASCII" | "US-ASCII" => Some(match data.iter().position(|b| !b.is_ascii()) {
            Some(at) => Err(at),
            None => Ok(data.iter().map(|b| *b as char).collect()),
        }),
        "ISO-8859-1" | "LATIN1" | "LATIN-1" => Some(Ok(data.iter().map(|b| *b as char).collect())),
        _ => None,
    }
}

fn encode(text: &str, encoding: &str) -> Option<Result<Vec<u8>, char>> {
    match encoding.to_ascii_uppercase().as_str() {
        "UTF-8" | "UTF8" => Some(Ok(text.as_bytes().to_vec())),
        "ASCII" | "US-ASCII" => Some(match text.chars().find(|c| !c.is_ascii()) {
            Some(c) => Err(c),
            None => Ok(text.as_bytes().to_vec()),
        }),
        "ISO-8859-1" | "LATIN1" | "LATIN-1" => {
            let mut out = Vec::with_capacity(text.len());
            for c in text.chars() {
                match u8::try_from(c as u32) {
                    Ok(b) => out.push(b),
                    Err(_) => return Some(Err(c)),
                }
            }
            Some(Ok(out))
        }
        _ => None,
    }
}

/// `b"..."` with printable ASCII kept and everything else escaped.
pub fn inspect_bytes(data: &[u8]) -> String {
    let mut out = String::with_capacity(data.len() + 3);
    out.push_str("b\"");
    for &b in data {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\t' => out.push_str("\\t"),
            b'\r' => out.push_str("\\r"),
            0x20..=0x7e => out.push(b as char),
            _ => out.push_str(&format!("\\x{b:02x}")),
        }
    }
    out.push('"');
    out
}
