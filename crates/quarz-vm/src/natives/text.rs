//! The second batch of text natives: the String, String::Builder, Symbol,
//! Regexp and MatchData methods the first batch left out.

use crate::rc::Rc;

use unicode_segmentation::UnicodeSegmentation;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::numeric::enumerator;
use super::string::{char_offset, md, re, s, sb, slice_range, string_sub};
use super::{block, int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    // String
    m.insert("String#slice", string_slice);
    m.insert("String#codepoints", |i, r, _| {
        Ok(Value::array(
            s(i, r)?.chars().map(|c| Value::Int(c as i64)).collect(),
        ))
    });
    m.insert("String#getbyte", |i, r, a| {
        let text = s(i, r)?;
        let idx = int(i, a.arg(0), "index")?;
        let n = text.len() as i64;
        let idx = if idx < 0 { n + idx } else { idx };
        Ok(if idx < 0 || idx >= n {
            Value::Nil
        } else {
            Value::Int(text.as_bytes()[idx as usize] as i64)
        })
    });
    m.insert("String#each_byte", |i, r, a| {
        let b = block(i, &a)?;
        for byte in s(i, r)?.bytes() {
            i.call_block(&b, smallvec![Value::Int(byte as i64)])?;
        }
        Ok(Value::Nil)
    });
    m.insert("String#graphemes", |i, r, _| {
        Ok(Value::array(
            s(i, r)?.graphemes(true).map(Value::str).collect(),
        ))
    });
    m.insert("String#each_grapheme", |i, r, a| {
        let b = block(i, &a)?;
        let text = s(i, r)?;
        for g in text.graphemes(true) {
            i.call_block(&b, smallvec![Value::str(g)])?;
        }
        Ok(Value::Nil)
    });
    m.insert("String#partition", |i, r, a| {
        string_partition(i, r, a, false)
    });
    m.insert("String#rpartition", |i, r, a| {
        string_partition(i, r, a, true)
    });
    m.insert("String#delete_prefix", |i, r, a| {
        let text = s(i, r)?;
        let prefix = string(i, a.arg(0), "prefix")?;
        Ok(Value::str(text.strip_prefix(prefix).unwrap_or(text)))
    });
    m.insert("String#delete_suffix", |i, r, a| {
        let text = s(i, r)?;
        let suffix = string(i, a.arg(0), "suffix")?;
        Ok(Value::str(text.strip_suffix(suffix).unwrap_or(text)))
    });
    m.insert("String#casecmp?", |i, r, a| {
        let other = string(i, a.arg(0), "other")?;
        Ok(Value::Bool(s(i, r)?.to_lowercase() == other.to_lowercase()))
    });
    m.insert("String#casecmp", |i, r, a| {
        let other = string(i, a.arg(0), "other")?;
        Ok(Value::Int(
            s(i, r)?.to_lowercase().cmp(&other.to_lowercase()) as i64,
        ))
    });
    m.insert("String#insert", |i, r, a| {
        let text = s(i, r)?;
        let idx = int(i, a.arg(0), "index")?;
        let piece = string(i, a.arg(1), "other")?;
        let n = text.chars().count() as i64;
        // As in Ruby, a negative index inserts after that character.
        let at = if idx < 0 { n + idx + 1 } else { idx };
        if at < 0 || at > n {
            return Err(i.err_index(&format!("index {idx} out of string")));
        }
        let byte = text
            .char_indices()
            .nth(at as usize)
            .map(|(b, _)| b)
            .unwrap_or(text.len());
        let mut out = String::with_capacity(text.len() + piece.len());
        out.push_str(&text[..byte]);
        out.push_str(piece);
        out.push_str(&text[byte..]);
        Ok(Value::string(out))
    });
    m.insert("String#prepend", |i, r, a| {
        Ok(Value::string(format!(
            "{}{}",
            string(i, a.arg(0), "other")?,
            s(i, r)?
        )))
    });
    m.insert("String#ascii_only?", |i, r, _| {
        Ok(Value::Bool(s(i, r)?.is_ascii()))
    });
    m.insert("String#next", super::string::string_succ);
    m.insert("String#upto", |i, r, a| {
        let b = block(i, &a)?;
        let last = string(i, a.arg(0), "last")?;
        let last_len = last.chars().count();
        let mut current = r.clone();
        if s(i, &current)?.chars().count() > last_len {
            return Ok(Value::Nil);
        }
        loop {
            i.call_block(&b, smallvec![current.clone()])?;
            if s(i, &current)? == last {
                break;
            }
            current = super::string::string_succ(i, &current, Args::default())?;
            if s(i, &current)?.chars().count() > last_len {
                break;
            }
        }
        Ok(Value::Nil)
    });
    m.insert("String#each_char", |i, r, a| {
        if a.block.is_none() {
            return enumerator(i, r, "each_char", vec![]);
        }
        super::string::string_each_char(i, r, a)
    });
    m.insert("String#squeeze", |i, r, a| {
        let text = s(i, r)?;
        let set: Option<Vec<char>> = match a.pos.first() {
            Some(v) => Some(string(i, v, "chars")?.chars().collect()),
            None => None,
        };
        let mut out = String::with_capacity(text.len());
        let mut last: Option<char> = None;
        for c in text.chars() {
            let squeezable = set.as_ref().is_none_or(|set| set.contains(&c));
            if squeezable && last == Some(c) {
                continue;
            }
            out.push(c);
            last = Some(c);
        }
        Ok(Value::string(out))
    });
    m.insert("String#chomp", |i, r, a| {
        let text = s(i, r)?;
        if let Some(suffix) = a.pos.first() {
            let suffix = string(i, suffix, "suffix")?;
            return Ok(Value::str(text.strip_suffix(suffix).unwrap_or(text)));
        }
        Ok(Value::str(
            text.strip_suffix("\r\n")
                .or_else(|| text.strip_suffix('\n'))
                .or_else(|| text.strip_suffix('\r'))
                .unwrap_or(text),
        ))
    });
    m.insert("String#start_with?", |i, r, a| {
        let text = s(i, r)?;
        for p in &a.pos {
            let hit = match p {
                Value::Regexp(rx) => rx.regex.find(text).is_some_and(|m| m.start() == 0),
                other => text.starts_with(string(i, other, "prefix")?),
            };
            if hit {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    });
    m.insert("String#end_with?", |i, r, a| {
        let text = s(i, r)?;
        for p in &a.pos {
            if text.ends_with(string(i, p, "suffix")?) {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    });
    m.insert("String#index", |i, r, a| string_find(i, r, a, false));
    m.insert("String#rindex", |i, r, a| string_find(i, r, a, true));
    m.insert("String#lines", |i, r, a| {
        let chomp = a.arg(0).is_truthy() || a.kw(i, "chomp").is_some_and(|v| v.is_truthy());
        Ok(Value::array(
            s(i, r)?
                .split_inclusive('\n')
                .map(|line| {
                    if chomp {
                        line.strip_suffix("\r\n")
                            .or_else(|| line.strip_suffix('\n'))
                            .unwrap_or(line)
                    } else {
                        line
                    }
                })
                .map(Value::str)
                .collect(),
        ))
    });
    m.insert("String#split", string_split_limit);
    m.insert("String#sub", |i, r, a| string_sub_block(i, r, a, false));
    m.insert("String#gsub", |i, r, a| string_sub_block(i, r, a, true));
    m.insert("String#scan", |i, r, a| {
        let Some(b) = a.block.clone() else {
            return super::string::string_scan(i, r, a);
        };
        let matches = super::string::string_scan(i, r, Args { block: None, ..a })?;
        let Value::Array(items) = matches else {
            return Ok(Value::Nil);
        };
        for x in items.iter() {
            i.call_block(&b, smallvec![x.clone()])?;
        }
        Ok(Value::Nil)
    });
    m.insert("String#[]", |i, r, a| match (a.arg(0), a.pos.len()) {
        (Value::Regexp(rx), 1) => {
            let text = s(i, r)?;
            Ok(match rx.regex.find(text) {
                Some(m) => Value::str(m.as_str()),
                None => Value::Nil,
            })
        }
        (Value::Int(_), 2) => string_slice(i, r, a),
        _ => super::string::string_index(i, r, a),
    });
    m.insert("String#%", |i, r, a| {
        let fmt = s(i, r)?;
        let values: Vec<Value> = match a.arg(0) {
            Value::Array(items) => items.to_values(),
            other => vec![other.clone()],
        };
        Ok(Value::string(super::core::format_values(i, fmt, &values)?))
    });

    // String::Builder
    m.insert("String::Builder#append", super::string::sb_push);
    m.insert("String::Builder#prepend", |i, r, a| {
        let piece = string(i, a.arg(0), "piece")?;
        sb(i, r)?.borrow_mut().insert_str(0, piece);
        Ok(r.clone())
    });
    m.insert("String::Builder#insert", |i, r, a| {
        let b = sb(i, r)?;
        let idx = int(i, a.arg(0), "index")?;
        let piece = string(i, a.arg(1), "piece")?;
        let mut text = b.borrow_mut();
        let n = text.chars().count() as i64;
        let at = if idx < 0 { n + idx + 1 } else { idx };
        if at < 0 || at > n {
            return Err(i.err_index(&format!("index {idx} out of string")));
        }
        let byte = text
            .char_indices()
            .nth(at as usize)
            .map(|(b, _)| b)
            .unwrap_or(text.len());
        text.insert_str(byte, piece);
        drop(text);
        Ok(r.clone())
    });
    m.insert("String::Builder#delete_at", |i, r, a| {
        let b = sb(i, r)?;
        let idx = int(i, a.arg(0), "index")?;
        let mut text = b.borrow_mut();
        Ok(match char_offset(&text, idx) {
            Some((st, en)) => {
                let removed: String = text.drain(st..en).collect();
                Value::string(removed)
            }
            None => Value::Nil,
        })
    });
    m.insert("String::Builder#replace", |i, r, a| {
        let text = string(i, a.arg(0), "text")?;
        *sb(i, r)?.borrow_mut() = text.to_string();
        Ok(r.clone())
    });
    m.insert("String::Builder#reverse!", |i, r, _| {
        let b = sb(i, r)?;
        let reversed: String = b.borrow().chars().rev().collect();
        *b.borrow_mut() = reversed;
        Ok(r.clone())
    });
    m.insert("String::Builder#snapshot", |i, r, _| {
        Ok(Value::string(sb(i, r)?.borrow().clone()))
    });
    m.insert("String::Builder#bytesize", |i, r, _| {
        Ok(Value::Int(sb(i, r)?.borrow().len() as i64))
    });

    // Symbol
    m.insert("Symbol#length", |i, r, _| {
        Ok(Value::Int(symbol_text(i, r)?.chars().count() as i64))
    });
    m.insert("Symbol#empty?", |i, r, _| {
        Ok(Value::Bool(symbol_text(i, r)?.is_empty()))
    });
    m.insert("Symbol#upcase", |i, r, _| {
        Ok(Value::Symbol(i.intern(&symbol_text(i, r)?.to_uppercase())))
    });
    m.insert("Symbol#downcase", |i, r, _| {
        Ok(Value::Symbol(i.intern(&symbol_text(i, r)?.to_lowercase())))
    });
    m.insert("Symbol#capitalize", |i, r, _| {
        let text = symbol_text(i, r)?;
        let mut chars = text.chars();
        let cap = match chars.next() {
            Some(c) => c.to_uppercase().collect::<String>() + &chars.as_str().to_lowercase(),
            None => String::new(),
        };
        Ok(Value::Symbol(i.intern(&cap)))
    });
    m.insert("Symbol#start_with?", |i, r, a| {
        let text = symbol_text(i, r)?;
        for p in &a.pos {
            if text.starts_with(string(i, p, "prefix")?) {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    });
    m.insert("Symbol#end_with?", |i, r, a| {
        let text = symbol_text(i, r)?;
        for p in &a.pos {
            if text.ends_with(string(i, p, "suffix")?) {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    });
    m.insert("Symbol#succ", |i, r, _| {
        let next =
            super::string::string_succ(i, &Value::str_rc(symbol_text(i, r)?), Args::default())?;
        Ok(Value::Symbol(i.intern(s(i, &next)?)))
    });

    // Regexp
    m.insert("Regexp.new", |i, _, a| {
        let source = string(i, a.arg(0), "source")?;
        let flags = match a.pos.get(1) {
            Some(f) => string(i, f, "options")?.to_string(),
            None => String::new(),
        };
        for f in flags.chars() {
            if !matches!(f, 'i' | 'm' | 'x') {
                return Err(i.err_arg(&format!("unknown regexp option: {f}")));
            }
        }
        i.make_regexp(source, &flags)
    });
    m.insert("Regexp.escape", |i, _, a| {
        Ok(Value::string(regex::escape(string(i, a.arg(0), "text")?)))
    });
    m.insert("Regexp.union", |i, _, a| {
        let mut parts = Vec::with_capacity(a.pos.len());
        for p in &a.pos {
            parts.push(match p {
                Value::Regexp(rx) => format!("(?:{})", rx.source),
                other => regex::escape(string(i, other, "pattern")?),
            });
        }
        i.make_regexp(&parts.join("|"), "")
    });
    m.insert("Regexp#names", |i, r, _| {
        Ok(Value::array(
            re(i, r)?
                .regex
                .capture_names()
                .flatten()
                .map(Value::str)
                .collect(),
        ))
    });
    m.insert("Regexp#options", |i, r, _| Ok(Value::str(&re(i, r)?.flags)));
    m.insert("Regexp#inspect", |i, r, _| {
        Ok(Value::string(format!(
            "/{}/{}",
            re(i, r)?.source,
            re(i, r)?.flags
        )))
    });
    m.insert("Regexp#==", |i, r, a| {
        Ok(Value::Bool(match (re(i, r)?, a.arg(0)) {
            (x, Value::Regexp(y)) => x.source == y.source && x.flags == y.flags,
            _ => false,
        }))
    });
    m.insert("Regexp#hash", |i, r, _| {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        re(i, r)?.source.hash(&mut h);
        Ok(Value::Int((h.finish() >> 1) as i64))
    });

    // MatchData
    m.insert("MatchData#names", |i, r, _| {
        Ok(Value::array(
            md(i, r)?.names.iter().map(|(n, _)| Value::str(n)).collect(),
        ))
    });
    m.insert("MatchData#named_captures", |i, r, _| {
        let m = md(i, r)?;
        let mut out = ValueMap::default();
        for (name, idx) in &m.names {
            out.insert(Value::str(name), group_value(m, *idx));
        }
        Ok(Value::Hash(Rc::new(crate::value::HashData::from(out))))
    });
    m.insert("MatchData#size", |i, r, _| {
        Ok(Value::Int(md(i, r)?.groups.len() as i64))
    });
    m.insert("MatchData#to_a", |i, r, _| {
        let m = md(i, r)?;
        Ok(Value::array(
            (0..m.groups.len()).map(|k| group_value(m, k)).collect(),
        ))
    });
    m.insert("MatchData#values_at", |i, r, a| {
        let m = md(i, r)?;
        let mut out = Vec::with_capacity(a.pos.len());
        for idx in &a.pos {
            out.push(group_value(m, int(i, idx, "index")?.max(0) as usize));
        }
        Ok(Value::array(out))
    });
    m.insert("MatchData#inspect", |i, r, _| {
        Ok(Value::string(i.inspect(r)?))
    });
}

// ----- helpers ---------------------------------------------------------------------

fn symbol_text(interp: &Interp, v: &Value) -> Result<Rc<str>, Flow> {
    match v {
        Value::Symbol(sym) => Ok(interp.symbol_name(*sym)),
        _ => Err(interp.err_type("expected a Symbol")),
    }
}

fn group_value(m: &MatchDataVal, idx: usize) -> Value {
    match m.groups.get(idx).copied().flatten() {
        Some((st, en)) => Value::str(&m.text[st..en]),
        None => Value::Nil,
    }
}

/// `text[start, length]` / `slice(start, length)` / `slice(range)`.
fn string_slice(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    if let Value::Range(r) = args.arg(0) {
        return Ok(Value::string(slice_range(interp, text, r)?));
    }
    let start = int(interp, args.arg(0), "start")?;
    let len = int(interp, args.arg(1), "length")?;
    let n = text.chars().count() as i64;
    let start = if start < 0 { n + start } else { start };
    if start < 0 || start > n || len < 0 {
        return Err(interp.err_index("slice out of string bounds"));
    }
    let end = (start + len).min(n);
    Ok(Value::string(
        text.chars()
            .skip(start as usize)
            .take((end - start) as usize)
            .collect(),
    ))
}

fn string_partition(interp: &Interp, recv: &Value, args: Args, from_right: bool) -> EvalResult {
    let text = s(interp, recv)?;
    let found: Option<(usize, usize)> = match args.arg(0) {
        Value::Regexp(rx) => {
            if from_right {
                rx.regex
                    .find_iter(text)
                    .last()
                    .map(|m| (m.start(), m.end()))
            } else {
                rx.regex.find(text).map(|m| (m.start(), m.end()))
            }
        }
        other => {
            let sep = string(interp, other, "separator")?;
            let at = if from_right {
                text.rfind(sep)
            } else {
                text.find(sep)
            };
            at.map(|b| (b, b + sep.len()))
        }
    };
    let parts = match found {
        Some((st, en)) => vec![
            Value::str(&text[..st]),
            Value::str(&text[st..en]),
            Value::str(&text[en..]),
        ],
        None if from_right => vec![Value::str(""), Value::str(""), Value::str(text)],
        None => vec![Value::str(text), Value::str(""), Value::str("")],
    };
    Ok(Value::array(parts))
}

/// `index`/`rindex` with a String or Regexp needle and an optional start
/// position (in characters).
fn string_find(interp: &Interp, recv: &Value, args: Args, from_right: bool) -> EvalResult {
    let text = s(interp, recv)?;
    let n = text.chars().count() as i64;
    let start = match args.pos.get(1) {
        Some(v) => {
            let st = int(interp, v, "start")?;
            let st = if st < 0 { n + st } else { st };
            if st < 0 || st > n {
                return Ok(Value::Nil);
            }
            st as usize
        }
        None => {
            if from_right {
                n as usize
            } else {
                0
            }
        }
    };
    let byte_at = |chars: usize| -> usize {
        text.char_indices()
            .nth(chars)
            .map(|(b, _)| b)
            .unwrap_or(text.len())
    };
    let found: Option<usize> = match args.arg(0) {
        Value::Regexp(rx) => {
            if from_right {
                let limit = byte_at(start);
                rx.regex
                    .find_iter(text)
                    .map(|m| m.start())
                    .take_while(|b| *b <= limit)
                    .last()
            } else {
                let from = byte_at(start);
                rx.regex.find_at(text, from).map(|m| m.start())
            }
        }
        other => {
            let needle = string(interp, other, "other")?;
            if from_right {
                let limit = (byte_at(start) + needle.len()).min(text.len());
                text[..limit].rfind(needle)
            } else {
                let from = byte_at(start);
                text[from..].find(needle).map(|b| b + from)
            }
        }
    };
    Ok(match found {
        Some(b) => Value::Int(text[..b].chars().count() as i64),
        None => Value::Nil,
    })
}

/// `split` with an optional limit: at most `limit` pieces, the last one
/// holding the rest (a negative limit keeps trailing empty strings).
fn string_split_limit(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let Some(limit) = args.pos.get(1) else {
        return super::string::string_split(interp, recv, args);
    };
    let limit = int(interp, limit, "limit")?;
    let text = s(interp, recv)?;
    let pat = args.arg(0);
    let mut parts: Vec<&str> = match (pat, pat.as_str()) {
        (_, Some(sep)) if limit > 0 => text.splitn(limit as usize, sep).collect(),
        (_, Some(sep)) => text.split(sep).collect(),
        (Value::Regexp(rx), _) if limit > 0 => rx.regex.splitn(text, limit as usize).collect(),
        (Value::Regexp(rx), _) => rx.regex.split(text).collect(),
        (other, _) => {
            return Err(interp.err_type(&format!(
                "split takes a String or Regexp, got {}",
                interp.class_name(other)
            )))
        }
    };
    if limit == 0 {
        while parts.last() == Some(&"") {
            parts.pop();
        }
    }
    Ok(Value::array(parts.into_iter().map(Value::str).collect()))
}

/// `sub`/`gsub` with a block (the match is passed, the result replaces
/// it) or a Hash of replacements.
fn string_sub_block(interp: &Interp, recv: &Value, args: Args, global: bool) -> EvalResult {
    let text = s(interp, recv)?;
    let replacement = |matched: &str| -> Result<String, Flow> {
        if let Some(b) = &args.block {
            let v = interp.call_block(b, smallvec![Value::str(matched)])?;
            return Ok(interp.to_s(&v)?.to_string());
        }
        if let Value::Hash(h) = args.arg(1) {
            return Ok(match h.get(&Value::str(matched)) {
                Some(v) => interp.to_s(&v)?.to_string(),
                None => String::new(),
            });
        }
        Ok(String::new())
    };
    if args.block.is_none() && !matches!(args.arg(1), Value::Hash(_)) {
        return string_sub(interp, recv, args, global);
    }
    let mut out = String::with_capacity(text.len());
    let mut last = 0;
    let pattern = args.arg(0);
    match (pattern, pattern.as_str()) {
        (_, Some(pat)) => {
            let mut from = 0;
            while let Some(b) = text[from..].find(pat) {
                let st = from + b;
                let en = st + pat.len();
                out.push_str(&text[last..st]);
                out.push_str(&replacement(&text[st..en])?);
                last = en;
                from = if pat.is_empty() { en + 1 } else { en };
                if !global || from > text.len() {
                    break;
                }
            }
        }
        (Value::Regexp(rx), _) => {
            for m in rx.regex.find_iter(text) {
                out.push_str(&text[last..m.start()]);
                out.push_str(&replacement(m.as_str())?);
                last = m.end();
                if !global {
                    break;
                }
            }
        }
        (other, _) => {
            return Err(interp.err_type(&format!(
                "sub takes a String or Regexp, got {}",
                interp.class_name(other)
            )))
        }
    }
    out.push_str(&text[last.min(text.len())..]);
    Ok(Value::string(out))
}
