//! By-reference versions of common natives: the receiver and the
//! arguments are borrowed from the registers, so a call builds no
//! argument list and copies nothing it does not keep. Each returns
//! `None` for what it does not handle (the generic native then runs,
//! and raises where it must).

use std::collections::HashMap;

use crate::interp::FastNativeFn;
use crate::value::Value;

use super::collections::index_data;

pub fn register(m: &mut HashMap<&'static str, FastNativeFn>) {
    // ----- String -----
    m.insert("String#size", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Ok(Value::Int(s.chars().count() as i64))),
        _ => None,
    });
    m.insert("String#length", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Ok(Value::Int(s.chars().count() as i64))),
        _ => None,
    });
    m.insert("String#bytesize", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Ok(Value::Int(s.len() as i64))),
        _ => None,
    });
    m.insert("String#empty?", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Ok(Value::Bool(s.is_empty()))),
        _ => None,
    });
    m.insert("String#==", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => Some(Ok(Value::Bool(o.as_str() == Some(s)))),
        _ => None,
    });
    m.insert("String#!=", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => Some(Ok(Value::Bool(o.as_str() != Some(s)))),
        _ => None,
    });
    m.insert("String#end_with?", |_, r, a| match (r.as_str(), a) {
        (Some(s), [p]) => p.as_str().map(|p| Ok(Value::Bool(s.ends_with(p)))),
        _ => None,
    });
    m.insert("String#start_with?", |_, r, a| match (r.as_str(), a) {
        (Some(s), [p]) => p.as_str().map(|p| Ok(Value::Bool(s.starts_with(p)))),
        _ => None,
    });
    m.insert("String#include?", |_, r, a| match (r.as_str(), a) {
        (Some(s), [p]) => p.as_str().map(|p| Ok(Value::Bool(s.contains(p)))),
        _ => None,
    });
    m.insert("String#upcase", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Ok(Value::build_string(|out| {
            if s.is_ascii() {
                out.push_str(s);
                out.make_ascii_uppercase();
            } else {
                out.push_str(&s.to_uppercase());
            }
        }))),
        _ => None,
    });
    m.insert("String#downcase", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Ok(Value::build_string(|out| {
            if s.is_ascii() {
                out.push_str(s);
                out.make_ascii_lowercase();
            } else {
                out.push_str(&s.to_lowercase());
            }
        }))),
        _ => None,
    });
    m.insert("String#+", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => o.as_str().map(|o| {
            Ok(Value::build_string(|out| {
                out.push_str(s);
                out.push_str(o);
            }))
        }),
        _ => None,
    });
    m.insert("String#to_s", |_, r, a| match (r.as_str(), a) {
        (Some(_), []) => Some(Ok(r.clone())),
        _ => None,
    });
    m.insert("Int#to_s", |_, r, a| match (r, a) {
        (Value::Int(i), []) => Some(Ok(Value::build_string(|out| {
            use std::fmt::Write as _;
            let _ = write!(out, "{i}");
        }))),
        _ => None,
    });
    // ----- String::Builder -----
    for key in [
        "String::Builder#<<",
        "String::Builder#push",
        "String::Builder#append",
    ] {
        m.insert(key, |_, r, a| match (r, a) {
            (Value::StringBuilder(b), [p]) => {
                b.borrow_mut().push_str(p.as_str()?);
                Some(Ok(r.clone()))
            }
            _ => None,
        });
    }
    // ----- Array -----
    m.insert("Array#size", |_, r, a| match (r, a) {
        (Value::Array(x), []) => Some(Ok(Value::Int(x.len() as i64))),
        _ => None,
    });
    m.insert("Array#length", |_, r, a| match (r, a) {
        (Value::Array(x), []) => Some(Ok(Value::Int(x.len() as i64))),
        _ => None,
    });
    m.insert("Array#empty?", |_, r, a| match (r, a) {
        (Value::Array(x), []) => Some(Ok(Value::Bool(x.is_empty()))),
        _ => None,
    });
    m.insert("Array#[]", |_, r, a| match (r, a) {
        (Value::Array(x), [Value::Int(i)]) => {
            let n = x.len() as i64;
            let k = if *i < 0 { n + i } else { *i };
            if k < 0 || k >= n {
                return None;
            }
            x.get(k as usize).map(Ok)
        }
        _ => None,
    });
    m.insert("Array#[]?", |_, r, a| match (r, a) {
        (Value::Array(x), [Value::Int(i)]) => Some(Ok(index_data(x, *i))),
        _ => None,
    });
    // ----- Hash / Set -----
    m.insert("Hash#[]", |_, r, a| match (r, a) {
        (Value::Hash(h), [k]) => h.get(*k).map(|v| Ok(v.clone())),
        _ => None,
    });
    m.insert("Hash#[]?", |_, r, a| match (r, a) {
        (Value::Hash(h), [k]) => Some(Ok(h.get(*k).cloned().unwrap_or(Value::Nil))),
        _ => None,
    });
    for key in ["Hash#key?", "Hash#has_key?", "Hash#include?"] {
        m.insert(key, |_, r, a| match (r, a) {
            (Value::Hash(h), [k]) => Some(Ok(Value::Bool(h.contains_key(*k)))),
            _ => None,
        });
    }
    m.insert("Hash#size", |_, r, a| match (r, a) {
        (Value::Hash(h), []) => Some(Ok(Value::Int(h.len() as i64))),
        _ => None,
    });
    m.insert("Hash#length", |_, r, a| match (r, a) {
        (Value::Hash(h), []) => Some(Ok(Value::Int(h.len() as i64))),
        _ => None,
    });
    m.insert("Hash#empty?", |_, r, a| match (r, a) {
        (Value::Hash(h), []) => Some(Ok(Value::Bool(h.is_empty()))),
        _ => None,
    });
    m.insert("Set#include?", |_, r, a| match (r, a) {
        (Value::Set(s), [k]) => Some(Ok(Value::Bool(s.contains(*k)))),
        _ => None,
    });
}
