//! By-reference versions of common natives: the receiver and the
//! arguments are borrowed from the registers, so a call builds no
//! argument list and copies nothing it does not keep. Each returns
//! `None` for what it does not handle (the generic native then runs,
//! and raises where it must).

use crate::value::Value;

use super::collections::{arr_data, hash, index_data, set};
use super::string::s;
use super::{int, string};

/// A twin declined a call of the kinds it answers (its generic form's
/// checks passed): the twin answers every such call (#1035).
fn declined(key: &str) -> crate::interp::Flow {
    unreachable!("internal error: `{key}`'s twin declined a call it answers (#1035)")
}

/// The natives with a by-reference twin, each written once: `fast!`
/// registers its generic form (into the plain registry) and its twin (into
/// the fast one) from the same line (#1035).
pub fn register(m: &mut impl super::Sink) {
    // ----- String -----
    fast!(m, "String#size", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Value::Int(super::string::char_count(r, s) as i64)),
        _ => None,
    },
        generic: |i, r, _| {
        super::string::s(i, r)?;
        Err(declined("String#size"))
    }
    );
    fast!(m, "String#length", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Value::Int(super::string::char_count(r, s) as i64)),
        _ => None,
    },
        generic: |i, r, _| {
        super::string::s(i, r)?;
        Err(declined("String#length"))
    }
    );
    fast!(m, "String#bytesize", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Value::Int(s.len() as i64)),
        _ => None,
    },
        generic: |i, r, _| {
        super::string::s(i, r)?;
        Err(declined("String#bytesize"))
    }
    );
    fast!(m, "String#empty?", |_, r, a| match (r.as_str(), a) {
        (Some(s), []) => Some(Value::Bool(s.is_empty())),
        _ => None,
    },
        generic: |i, r, _| {
        super::string::s(i, r)?;
        Err(declined("String#empty?"))
    }
    );
    fast!(m, "String#==", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => Some(Value::Bool(super::string::equal(s, o))),
        _ => None,
    },
        generic: |i, r, _| {
        super::string::s(i, r)?;
        Err(declined("String#=="))
    }
    );
    // (Comparable's would call `<=>` through dispatch for each, #836.)
    fast!(m, "String#<", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => o
            .as_str()
            .map(|o| Value::Bool(super::string::order(s, o).is_lt())),
        _ => None,
    },
        generic: |i, r, a| {
        super::string::s(i, r)?;
        super::string(i, a.arg(0), "other")?;
        Err(declined("String#<"))
    }
    );
    fast!(m, "String#<=", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => o
            .as_str()
            .map(|o| Value::Bool(super::string::order(s, o).is_le())),
        _ => None,
    },
        generic: |i, r, a| {
        super::string::s(i, r)?;
        super::string(i, a.arg(0), "other")?;
        Err(declined("String#<="))
    }
    );
    fast!(m, "String#>", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => o
            .as_str()
            .map(|o| Value::Bool(super::string::order(s, o).is_gt())),
        _ => None,
    },
        generic: |i, r, a| {
        super::string::s(i, r)?;
        super::string(i, a.arg(0), "other")?;
        Err(declined("String#>"))
    }
    );
    fast!(m, "String#>=", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => o
            .as_str()
            .map(|o| Value::Bool(super::string::order(s, o).is_ge())),
        _ => None,
    },
        generic: |i, r, a| {
        super::string::s(i, r)?;
        super::string(i, a.arg(0), "other")?;
        Err(declined("String#>="))
    }
    );
    fast!(m, "String#end_with?", |_, r, a| match (r.as_str(), a) {
        (Some(s), [p]) => p.as_str().map(|p| Value::Bool(s.ends_with(p))),
        _ => None,
    },
        generic: |i, r, a| {
        let text = s(i, r)?;
        for p in &a.pos {
            if text.ends_with(string(i, p, "suffix")?) {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    }
    );
    fast!(m, "String#start_with?", |_, r, a| match (r.as_str(), a) {
        (Some(s), [p]) => p.as_str().map(|p| Value::Bool(s.starts_with(p))),
        _ => None,
    },
        generic: |i, r, a| {
        let text = s(i, r)?;
        for p in &a.pos {
            let hit = match p {
                Value::Regexp(rx) => rx.regex.find(text.as_bytes()).is_some_and(|m| m.0 == 0),
                other => text.starts_with(string(i, other, "prefix")?),
            };
            if hit {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    }
    );
    fast!(m, "String#include?", |_, r, a| match (r.as_str(), a) {
        (Some(s), [p]) => p.as_str().map(|p| Value::Bool(s.contains(p))),
        _ => None,
    },
        generic: |i, r, a| {
        super::string::s(i, r)?;
        super::string(i, a.arg(0), "other")?;
        Err(declined("String#include?"))
    }
    );
    fast!(m, "String#upcase", |_, r, a| match (r, a) {
        // A short ASCII string is converted in a copy of the value.
        (Value::Short(s), []) if s.is_ascii() => {
            let mut t = *s;
            t.make_ascii_uppercase();
            Some(Value::Short(t))
        }
        (_, []) => r.as_str().map(|s| {
            Value::build_string(|out| {
                if s.is_ascii() {
                    out.push_str(s);
                    out.make_ascii_uppercase();
                } else {
                    out.push_str(&s.to_uppercase());
                }
            })
        }),
        _ => None,
    },
        generic: |i, r, _| {
        super::string::s(i, r)?;
        Err(declined("String#upcase"))
    }
    );
    fast!(m, "String#downcase", |_, r, a| match (r, a) {
        (Value::Short(s), []) if s.is_ascii() => {
            let mut t = *s;
            t.make_ascii_lowercase();
            Some(Value::Short(t))
        }
        (_, []) => r.as_str().map(|s| {
            Value::build_string(|out| {
                if s.is_ascii() {
                    out.push_str(s);
                    out.make_ascii_lowercase();
                } else {
                    out.push_str(&s.to_lowercase());
                }
            })
        }),
        _ => None,
    },
        generic: |i, r, _| {
        super::string::s(i, r)?;
        Err(declined("String#downcase"))
    }
    );
    fast!(m, "String#+", |_, r, a| match (r.as_str(), a) {
        (Some(s), [o]) => o.as_str().map(|o| {
            Value::build_string(|out| {
                out.push_str(s);
                out.push_str(o);
            })
        }),
        _ => None,
    },
        generic: |i, r, a| {
        super::string::s(i, r)?;
        super::string(i, a.arg(0), "other")?;
        Err(declined("String#+"))
    }
    );
    fast!(m, "String#to_s", |_, r, a| match (r.as_str(), a) {
        (Some(_), []) => Some(r.clone()),
        _ => None,
    },
        generic: |_, r, _| Ok(r.clone())
    );
    fast!(m, "Int#to_s", |_, r, a| match (r, a) {
        (Value::Int(i), []) => {
            let mut digits = [0u8; 20];
            Some(Value::str(crate::value::format_int(&mut digits, *i)))
        }
        _ => None,
    },
        generic: super::numeric::int_to_s
    );
    // ----- String::Builder -----
    fast!(
        m,
        [
            "String::Builder#<<",
            "String::Builder#push",
            "String::Builder#append"
        ],
        |_, r, a| match (r, a) {
            (Value::StringBuilder(b), [p]) => {
                b.borrow_mut().push_str(p.as_str()?);
                Some(r.clone())
            }
            _ => None,
        },
        generic: super::string::sb_push
    );
    // ----- Array -----
    fast!(m, "Array#size", |_, r, a| match (r, a) {
        (Value::Array(x), []) => Some(Value::Int(x.len() as i64)),
        _ => None,
    },
        generic: |i, r, _| {
        super::collections::arr_data(i, r)?;
        Err(declined("Array#size"))
    }
    );
    fast!(m, "Array#length", |_, r, a| match (r, a) {
        (Value::Array(x), []) => Some(Value::Int(x.len() as i64)),
        _ => None,
    },
        generic: |i, r, _| {
        super::collections::arr_data(i, r)?;
        Err(declined("Array#length"))
    }
    );
    fast!(m, "Array#empty?", |_, r, a| match (r, a) {
        (Value::Array(x), []) => Some(Value::Bool(x.is_empty())),
        _ => None,
    },
        generic: |i, r, _| {
        super::collections::arr_data(i, r)?;
        Err(declined("Array#empty?"))
    }
    );
    fast!(m, "Array#[]", |_, r, a| match (r, a) {
        (Value::Array(x), [Value::Int(i)]) => {
            let n = x.len() as i64;
            let k = if *i < 0 { n + i } else { *i };
            if k < 0 || k >= n {
                return None;
            }
            x.get(k as usize)
        }
        _ => None,
    },
        generic: super::collections::array_index
    );
    fast!(m, "Array#[]?", |_, r, a| match (r, a) {
        (Value::Array(x), [Value::Int(i)]) => Some(index_data(x, *i)),
        _ => None,
    },
        generic: |i, r, a| {
        Ok(index_data(arr_data(i, r)?, int(i, a.arg(0), "index")?))
    }
    );
    // ----- Hash / Set -----
    // A key with its own `==` or `hash` goes to the native, which raises
    // what they raise (`crate::keys`); a built-in key runs no Quarz code
    // (the key looked up is the receiver of `==`).
    fast!(m, "Hash#[]", |_, r, a| match (r, a) {
        (Value::Hash(_), [k]) if crate::keys::is_custom(k) => None,
        (Value::Hash(h), [k]) => h.get(k),
        _ => None,
    },
        generic: |i, r, a| match hash(i, r)?.get(a.arg(0)) {
        Some(v) => Ok(v.clone()),
        None => Err(i.raise(
            i.program.exc.key_error,
            &format!("key not found: {}", i.inspect(a.arg(0))?),
        )),
    }
    );
    fast!(m, "Hash#[]?", |_, r, a| match (r, a) {
        (Value::Hash(_), [k]) if crate::keys::is_custom(k) => None,
        (Value::Hash(h), [k]) => Some(h.get(k).unwrap_or(Value::Nil)),
        _ => None,
    },
        generic: |i, r, a| {
        Ok(hash(i, r)?.get(a.arg(0)).unwrap_or(Value::Nil))
    }
    );
    fast!(m, ["Hash#key?", "Hash#has_key?"], |_, r, a| match (r, a) {
        (Value::Hash(_), [k]) if crate::keys::is_custom(k) => None,
        (Value::Hash(h), [k]) => Some(Value::Bool(h.contains_key(k))),
        _ => None,
    },
        generic: |i, r, a| {
        Ok(Value::Bool(hash(i, r)?.contains_key(a.arg(0))))
    }
    );
    fast!(m, "Hash#size", |_, r, a| match (r, a) {
        (Value::Hash(h), []) => Some(Value::Int(h.len() as i64)),
        _ => None,
    },
        generic: |i, r, _| {
        super::collections::hash(i, r)?;
        Err(declined("Hash#size"))
    }
    );
    fast!(m, "Hash#length", |_, r, a| match (r, a) {
        (Value::Hash(h), []) => Some(Value::Int(h.len() as i64)),
        _ => None,
    },
        generic: |i, r, _| {
        super::collections::hash(i, r)?;
        Err(declined("Hash#length"))
    }
    );
    fast!(m, "Hash#empty?", |_, r, a| match (r, a) {
        (Value::Hash(h), []) => Some(Value::Bool(h.is_empty())),
        _ => None,
    },
        generic: |i, r, _| {
        super::collections::hash(i, r)?;
        Err(declined("Hash#empty?"))
    }
    );
    fast!(m, "Set#include?", |_, r, a| match (r, a) {
        (Value::Set(_), [k]) if crate::keys::is_custom(k) => None,
        (Value::Set(s), [k]) => Some(Value::Bool(s.contains(k))),
        _ => None,
    },
        generic: |i, r, a| {
        Ok(Value::Bool(set(i, r)?.contains(a.arg(0))))
    }
    );
}
