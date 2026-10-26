//! The second batch of text natives: the String, String::Builder, Symbol,
//! Regexp and MatchData methods the first batch left out.

use crate::rc::Rc;

use unicode_segmentation::UnicodeSegmentation;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::matching::{each_match, group_names, regex_split, substitute, utf8, Hay};
use super::numeric::enumerator;
use super::string::{char_offset, match_value, md, re, s, sb, slice_range, string_sub};
use super::{block, int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    // String
    native!(m, "String#slice", string_slice);
    native!(m, "String#codepoints", |i, r, _| {
        Ok(Value::array(
            s(i, r)?.chars().map(|c| Value::Int(c as i64)).collect(),
        ))
    });
    native!(m, "String#getbyte", |i, r, a| {
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
    native!(m, "String#each_byte", |i, r, a| {
        let b = block(i, &a)?;
        for byte in s(i, r)?.bytes() {
            i.call_block(&b, smallvec![Value::Int(byte as i64)])?;
        }
        Ok(Value::Nil)
    });
    native!(m, "String#graphemes", |i, r, _| {
        Ok(Value::array(
            s(i, r)?.graphemes(true).map(Value::str).collect(),
        ))
    });
    native!(m, "String#each_grapheme", |i, r, a| {
        let b = block(i, &a)?;
        let text = s(i, r)?;
        for g in text.graphemes(true) {
            i.call_block(&b, smallvec![Value::str(g)])?;
        }
        Ok(Value::Nil)
    });
    native!(m, "String#partition", |i, r, a| {
        string_partition(i, r, a, false)
    });
    native!(m, "String#rpartition", |i, r, a| {
        string_partition(i, r, a, true)
    });
    native!(m, "String#delete_prefix", |i, r, a| {
        let text = s(i, r)?;
        let prefix = string(i, a.arg(0), "prefix")?;
        Ok(Value::str(text.strip_prefix(prefix).unwrap_or(text)))
    });
    native!(m, "String#delete_suffix", |i, r, a| {
        let text = s(i, r)?;
        let suffix = string(i, a.arg(0), "suffix")?;
        Ok(Value::str(text.strip_suffix(suffix).unwrap_or(text)))
    });
    native!(m, "String#casecmp?", |i, r, a| {
        let other = string(i, a.arg(0), "other")?;
        Ok(Value::Bool(s(i, r)?.to_lowercase() == other.to_lowercase()))
    });
    native!(m, "String#casecmp", |i, r, a| {
        let other = string(i, a.arg(0), "other")?;
        Ok(Value::Int(
            s(i, r)?.to_lowercase().cmp(&other.to_lowercase()) as i64,
        ))
    });
    native!(m, "String#insert", |i, r, a| {
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
    native!(m, "String#prepend", |i, r, a| {
        Ok(Value::string(format!(
            "{}{}",
            string(i, a.arg(0), "other")?,
            s(i, r)?
        )))
    });
    native!(m, "String#ascii_only?", |i, r, _| {
        Ok(Value::Bool(s(i, r)?.is_ascii()))
    });
    native!(m, "String#next", super::string::string_succ);
    native!(m, "String#upto", |i, r, a| {
        let b = block(i, &a)?;
        let last = string(i, a.arg(0), "last")?;
        let mut steps = StringSteps::new(s(i, r)?, last, false);
        while let Some(v) = steps.next() {
            i.call_block(&b, smallvec![Value::string(v)])?;
        }
        Ok(Value::Nil)
    });
    native!(m, "String#each_char", |i, r, a| {
        if a.block.is_none() {
            return enumerator(i, r, "each_char", vec![]);
        }
        super::string::string_each_char(i, r, a)
    });
    native!(m, "String#squeeze", |i, r, a| {
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
    native!(m, "String#chomp", |i, r, a| {
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
    native!(m, "String#start_with?", |i, r, a| {
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
    });
    native!(m, "String#end_with?", |i, r, a| {
        let text = s(i, r)?;
        for p in &a.pos {
            if text.ends_with(string(i, p, "suffix")?) {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    });
    native!(m, "String#index", |i, r, a| string_find(i, r, a, false));
    native!(m, "String#rindex", |i, r, a| string_find(i, r, a, true));
    native!(m, "String#lines", |i, r, a| {
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
    native!(m, "String#split", string_split_limit);
    native!(m, "String#sub", |i, r, a| string_sub_block(i, r, a, false));
    native!(m, "String#gsub", |i, r, a| string_sub_block(i, r, a, true));
    native!(m, "String#scan", |i, r, a| {
        let Some(b) = a.block.clone() else {
            return super::string::string_scan(i, r, a);
        };
        let text = s(i, r)?;
        let pattern = a.arg(0);
        re(i, pattern)?;
        let wants = wants_match(i, &b);
        let names = group_names(pattern);
        let mut shared: Option<Rc<str>> = None;
        each_match(i, Hay::Str(text), pattern, true, wants, |groups| {
            let (st, en) = groups[0].unwrap_or((0, 0));
            let matched = Value::str(&text[st..en]);
            if wants {
                let shared = shared.get_or_insert_with(|| Rc::from(text));
                let md = match_value(shared, groups, &names);
                i.call_block(&b, smallvec![matched, md])?;
            } else {
                i.call_block(&b, smallvec![matched])?;
            }
            Ok(())
        })?;
        Ok(Value::Nil)
    });
    native!(m, "String#[]", |i, r, a| match (a.arg(0), a.pos.len()) {
        (Value::Regexp(rx), 1) => {
            let text = s(i, r)?;
            Ok(match rx.regex.find(text.as_bytes()) {
                Some((st, en)) => Value::str(&text[st..en]),
                None => Value::Nil,
            })
        }
        (Value::Int(_), 2) => string_slice(i, r, a),
        _ => super::string::string_index(i, r, a),
    });
    native!(m, "String#%", |i, r, a| {
        let fmt = s(i, r)?;
        let values: Vec<Value> = match a.arg(0) {
            Value::Array(items) => items.to_values(),
            other => vec![other.clone()],
        };
        Ok(Value::string(super::core::format_values(i, fmt, &values)?))
    });

    // String::Builder
    native!(m, "String::Builder#append", super::string::sb_push);
    native!(m, "String::Builder#prepend", |i, r, a| {
        let piece = string(i, a.arg(0), "piece")?;
        sb(i, r)?.borrow_mut().insert_str(0, piece);
        Ok(r.clone())
    });
    native!(m, "String::Builder#insert", |i, r, a| {
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
    native!(m, "String::Builder#delete_at", |i, r, a| {
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
    native!(m, "String::Builder#replace", |i, r, a| {
        let text = string(i, a.arg(0), "text")?;
        *sb(i, r)?.borrow_mut() = text.to_string();
        Ok(r.clone())
    });
    native!(m, "String::Builder#reverse!", |i, r, _| {
        let b = sb(i, r)?;
        let reversed: String = b.borrow().chars().rev().collect();
        *b.borrow_mut() = reversed;
        Ok(r.clone())
    });
    native!(m, "String::Builder#snapshot", |i, r, _| {
        Ok(Value::string(sb(i, r)?.borrow().clone()))
    });
    native!(m, "String::Builder#bytesize", |i, r, _| {
        Ok(Value::Int(sb(i, r)?.borrow().len() as i64))
    });

    // Symbol
    native!(m, "Symbol#length", |i, r, _| {
        Ok(Value::Int(symbol_text(i, r)?.chars().count() as i64))
    });
    native!(m, "Symbol#empty?", |i, r, _| {
        Ok(Value::Bool(symbol_text(i, r)?.is_empty()))
    });
    native!(m, "Symbol#upcase", |i, r, _| {
        Ok(Value::Symbol(i.intern(&symbol_text(i, r)?.to_uppercase())))
    });
    native!(m, "Symbol#downcase", |i, r, _| {
        Ok(Value::Symbol(i.intern(&symbol_text(i, r)?.to_lowercase())))
    });
    native!(m, "Symbol#capitalize", |i, r, _| {
        let text = symbol_text(i, r)?;
        let mut chars = text.chars();
        let cap = match chars.next() {
            Some(c) => c.to_uppercase().collect::<String>() + &chars.as_str().to_lowercase(),
            None => String::new(),
        };
        Ok(Value::Symbol(i.intern(&cap)))
    });
    native!(m, "Symbol#start_with?", |i, r, a| {
        let text = symbol_text(i, r)?;
        for p in &a.pos {
            if text.starts_with(string(i, p, "prefix")?) {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    });
    native!(m, "Symbol#end_with?", |i, r, a| {
        let text = symbol_text(i, r)?;
        for p in &a.pos {
            if text.ends_with(string(i, p, "suffix")?) {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    });
    native!(m, "Symbol#succ", |i, r, _| {
        let next =
            super::string::string_succ(i, &Value::str_rc(symbol_text(i, r)?), Args::default())?;
        Ok(Value::Symbol(i.intern(s(i, &next)?)))
    });

    // Regexp
    native!(m, "Regexp.new", |i, _, a| {
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
    native!(m, "Regexp.escape", |i, _, a| {
        Ok(Value::string(regex::escape(string(i, a.arg(0), "text")?)))
    });
    native!(m, "Regexp.union", |i, _, a| {
        if let [rx @ Value::Regexp(_)] = &a.pos[..] {
            return Ok(rx.clone());
        }
        let mut parts = Vec::with_capacity(a.pos.len());
        for p in &a.pos {
            parts.push(match p {
                // A group that keeps its flags, as Ruby's `Regexp#to_s`.
                Value::Regexp(rx) => {
                    let (on, off): (String, String) =
                        "mix".chars().partition(|f| rx.flags.contains(*f));
                    let off = if off.is_empty() {
                        off
                    } else {
                        format!("-{off}")
                    };
                    format!("(?{on}{off}:{})", rx.source)
                }
                other => regex::escape(string(i, other, "pattern")?),
            });
        }
        i.make_regexp(&parts.join("|"), "")
    });
    native!(m, "Regexp#names", |i, r, _| {
        Ok(Value::array(
            re(i, r)?
                .regex
                .capture_names()
                .flatten()
                .map(Value::str)
                .collect(),
        ))
    });
    native!(m, "Regexp#options", |i, r, _| Ok(Value::str(
        &re(i, r)?.flags
    )));
    native!(m, "Regexp#inspect", |i, r, _| {
        Ok(Value::string(format!(
            "/{}/{}",
            re(i, r)?.source,
            re(i, r)?.flags
        )))
    });
    native!(m, "Regexp#==", |i, r, a| {
        Ok(Value::Bool(match (re(i, r)?, a.arg(0)) {
            (x, Value::Regexp(y)) => x.source == y.source && x.flags == y.flags,
            _ => false,
        }))
    });
    native!(m, "Regexp#hash", |i, r, _| {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        re(i, r)?.source.hash(&mut h);
        Ok(Value::Int((h.finish() >> 1) as i64))
    });

    // MatchData and Bytes::MatchData
    native!(m, "MatchData#names", md_names);
    native!(m, "Bytes::MatchData#names", md_names);
    native!(m, "MatchData#named_captures", md_named_captures);
    native!(m, "Bytes::MatchData#named_captures", md_named_captures);
    native!(m, "MatchData#size", md_size);
    native!(m, "Bytes::MatchData#size", md_size);
    native!(m, "MatchData#to_a", md_to_a);
    native!(m, "Bytes::MatchData#to_a", md_to_a);
    native!(m, "MatchData#values_at", md_values_at);
    native!(m, "Bytes::MatchData#values_at", md_values_at);
    native!(m, "MatchData#inspect", md_inspect);
    native!(m, "Bytes::MatchData#inspect", md_inspect);
}

// ----- helpers ---------------------------------------------------------------------

fn symbol_text(interp: &Interp, v: &Value) -> Result<Rc<str>, Flow> {
    match v {
        Value::Symbol(sym) => Ok(interp.symbol_name(*sym)),
        _ => Err(interp.err_type("expected a Symbol")),
    }
}

fn md_names(i: &Interp, r: &Value, _: Args) -> EvalResult {
    Ok(Value::array(
        md(i, r)?.names.iter().map(|(n, _)| Value::str(n)).collect(),
    ))
}

fn md_named_captures(i: &Interp, r: &Value, _: Args) -> EvalResult {
    let m = md(i, r)?;
    let mut out = ValueMap::default();
    for (name, idx) in &m.names {
        out.insert(Value::str(name), m.group(*idx));
    }
    Ok(Value::Hash(Rc::new(crate::value::HashData::from(out))))
}

fn md_size(i: &Interp, r: &Value, _: Args) -> EvalResult {
    Ok(Value::Int(md(i, r)?.groups.len() as i64))
}

fn md_to_a(i: &Interp, r: &Value, _: Args) -> EvalResult {
    let m = md(i, r)?;
    Ok(Value::array(
        (0..m.groups.len()).map(|k| m.group(k)).collect(),
    ))
}

fn md_values_at(i: &Interp, r: &Value, a: Args) -> EvalResult {
    let m = md(i, r)?;
    let mut out = Vec::with_capacity(a.pos.len());
    for idx in &a.pos {
        out.push(m.group(int(i, idx, "index")?.max(0) as usize));
    }
    Ok(Value::array(out))
}

fn md_inspect(i: &Interp, r: &Value, _: Args) -> EvalResult {
    Ok(Value::string(i.inspect(r)?))
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
                rx.regex.last_match_before(text.as_bytes(), text.len())
            } else {
                rx.regex.find(text.as_bytes())
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
            // Past the end, `rindex` searches from the end (as in Ruby).
            let st = if from_right { st.min(n) } else { st };
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
                    .last_match_before(text.as_bytes(), limit)
                    .map(|(st, _)| st)
            } else {
                let from = byte_at(start);
                rx.regex.find_at(text.as_bytes(), from).map(|(st, _)| st)
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
        (Value::Regexp(_), _) => regex_split(interp, Hay::Str(text), pat, limit)?
            .into_iter()
            .map(|(a, b)| &text[a..b])
            .collect(),
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

/// `sub`/`gsub` with a block (the match is passed, with its `MatchData`
/// for a Regexp; the result replaces it) or a Hash of replacements.
fn string_sub_block(interp: &Interp, recv: &Value, args: Args, global: bool) -> EvalResult {
    if args.block.is_none() && !matches!(args.arg(1), Value::Hash(_)) {
        return string_sub(interp, recv, args, global);
    }
    let text = s(interp, recv)?;
    let pattern = args.arg(0);
    let wants = matches!(pattern, Value::Regexp(_))
        && args.block.as_ref().is_some_and(|b| wants_match(interp, b));
    let names = if wants {
        group_names(pattern)
    } else {
        Vec::new()
    };
    let mut shared: Option<Rc<str>> = None;
    let out = substitute(
        interp,
        Hay::Str(text),
        pattern,
        global,
        wants,
        |groups, out| {
            let (st, en) = groups[0].unwrap_or((0, 0));
            let matched = Value::str(&text[st..en]);
            if let Some(b) = &args.block {
                let v = if wants {
                    let shared = shared.get_or_insert_with(|| Rc::from(text));
                    let md = match_value(shared, groups, &names);
                    interp.call_block(b, smallvec![matched, md])?
                } else {
                    interp.call_block(b, smallvec![matched])?
                };
                out.extend_from_slice(interp.to_s(&v)?.as_bytes());
            } else if let Value::Hash(h) = args.arg(1) {
                if let Some(v) = h.get(&matched) {
                    out.extend_from_slice(interp.to_s(&v)?.as_bytes());
                }
            }
            Ok(())
        },
    )?;
    Ok(Value::string(utf8(out)))
}

/// Whether a block takes a `MatchData` after the match: it requires two
/// parameters or more (the overload checked for it; `|*xs|` and
/// `|s, *xs|` are checked as taking the match only), or is a method.
pub(super) fn wants_match(interp: &Interp, block: &Value) -> bool {
    match block {
        Value::Proc(c) => match &c.body {
            ClosureBody::Func(fid) => {
                let arity = interp.func(*fid).arity;
                arity >= 2 || arity <= -3
            }
            ClosureBody::MethodName(..) => false,
            ClosureBody::BoundMethod { .. } | ClosureBody::Native(_) => true,
        },
        _ => true,
    }
}

/// The strings from a start to `last` (`String#upto`, a string `Range`),
/// stepped one at a time as Ruby's `rb_str_upto_each` does: two single
/// ASCII characters by character; two strings of digits as numbers of
/// any size, padded to the start's width; otherwise by `succ` from the
/// start (nothing when it sorts after `last`), ending at `last`, at
/// `last.succ`, or once longer than `last` in bytes.
pub(super) enum StringSteps {
    Chars {
        next: u8,
        last: u8,
        exclusive: bool,
    },
    /// `next` and `last` without leading zeros.
    Digits {
        next: String,
        last: String,
        width: usize,
        exclusive: bool,
    },
    Succ {
        next: Option<String>,
        last: String,
        after_last: String,
        exclusive: bool,
    },
    Done,
}

impl StringSteps {
    pub(super) fn new(first: &str, last: &str, exclusive: bool) -> StringSteps {
        let (fb, lb) = (first.as_bytes(), last.as_bytes());
        if fb.len() == 1 && lb.len() == 1 && fb[0].is_ascii() && lb[0].is_ascii() {
            if fb[0] > lb[0] || (exclusive && fb[0] == lb[0]) {
                return StringSteps::Done;
            }
            return StringSteps::Chars {
                next: fb[0],
                last: lb[0],
                exclusive,
            };
        }
        let digits = |t: &[u8]| !t.is_empty() && t.iter().all(u8::is_ascii_digit);
        if digits(fb) && digits(lb) {
            let bare = |t: &str| {
                let t = t.trim_start_matches('0');
                if t.is_empty() {
                    "0".to_string()
                } else {
                    t.to_string()
                }
            };
            return StringSteps::Digits {
                next: bare(first),
                last: bare(last),
                width: first.len(),
                exclusive,
            };
        }
        let order = first.cmp(last);
        if order.is_gt() || (exclusive && order.is_eq()) {
            return StringSteps::Done;
        }
        StringSteps::Succ {
            next: Some(first.to_string()),
            last: last.to_string(),
            after_last: succ(last),
            exclusive,
        }
    }

    pub(super) fn next(&mut self) -> Option<String> {
        match self {
            StringSteps::Done => None,
            StringSteps::Chars {
                next,
                last,
                exclusive,
            } => {
                let c = *next;
                if c == *last || (*exclusive && c + 1 == *last) {
                    *self = StringSteps::Done;
                } else {
                    *next = c + 1;
                }
                Some((c as char).to_string())
            }
            StringSteps::Digits {
                next,
                last,
                width,
                exclusive,
            } => {
                let order = next
                    .len()
                    .cmp(&last.len())
                    .then_with(|| next.as_str().cmp(last));
                if order.is_gt() || (*exclusive && order.is_eq()) {
                    *self = StringSteps::Done;
                    return None;
                }
                let out = format!("{next:0>width$}", width = *width);
                increment_decimal(next);
                Some(out)
            }
            StringSteps::Succ {
                next,
                last,
                after_last,
                exclusive,
            } => {
                let current = next.take()?;
                if current == *after_last {
                    return None;
                }
                if *exclusive || current != *last {
                    let n = succ(&current);
                    let stop = (*exclusive && n == *last) || n.len() > last.len() || n.is_empty();
                    if !stop {
                        *next = Some(n);
                    }
                }
                Some(current)
            }
        }
    }
}

/// Adds one to a string of decimal digits.
pub(super) fn increment_decimal(n: &mut String) {
    let mut bytes = std::mem::take(n).into_bytes();
    let mut i = bytes.len();
    loop {
        if i == 0 {
            bytes.insert(0, b'1');
            break;
        }
        i -= 1;
        if bytes[i] == b'9' {
            bytes[i] = b'0';
        } else {
            bytes[i] += 1;
            break;
        }
    }
    *n = String::from_utf8(bytes).unwrap_or_default();
}

/// `String#succ`, as Ruby's `str_succ`: the rightmost letter or digit
/// steps (`z` to `a`, `Z` to `A` and `9` to `0`, and the end of any
/// other run of letters or digits to its start, carrying to the next one
/// on the left, across other characters but not from an ASCII letter to
/// an ASCII digit or back across them), a carry past the leftmost adding
/// a character (`a`, `A`, `1`, ...) there; a string without letters or
/// digits steps its last character, within its UTF-8 length.
pub(super) fn succ(text: &str) -> String {
    let mut chars: Vec<char> = text.chars().collect();
    let mut carry: Option<(usize, char)> = None;
    let mut last_alnum: Option<char> = None;
    let mut after_other = false;
    let mut i = chars.len();
    while i > 0 {
        i -= 1;
        let c = chars[i];
        if after_other {
            if let Some(l) = last_alnum {
                let (la, ld) = (l.is_ascii_alphabetic(), l.is_ascii_digit());
                if (la && c.is_ascii_digit()) || (ld && c.is_ascii_alphabetic()) {
                    break;
                }
            }
        }
        match succ_alnum(c) {
            Alnum::Other => after_other = true,
            Alnum::Found(next) => {
                chars[i] = next;
                return chars.into_iter().collect();
            }
            Alnum::Wrapped(next, w) => {
                chars[i] = next;
                after_other = false;
                last_alnum = Some(next);
                carry = Some((i, w));
            }
        }
    }
    if carry.is_none() {
        // No letter or digit: the last character steps, a wrap (past the
        // characters of its UTF-8 length) carrying left, then a "\x01".
        let mut i = chars.len();
        while i > 0 {
            i -= 1;
            match step_char(chars[i], true) {
                Some(next) => {
                    chars[i] = next;
                    return chars.into_iter().collect();
                }
                None => {
                    chars[i] = utf8_range(chars[i]).0;
                    carry = Some((i, '\u{1}'));
                }
            }
        }
    }
    if let Some((at, w)) = carry {
        chars.insert(at, w);
    }
    chars.into_iter().collect()
}

enum Alnum {
    Other,
    Found(char),
    /// The character it wraps to, and the one carried.
    Wrapped(char, char),
}

/// One letter or digit stepped, as Ruby's `enc_succ_alnum_char`: to the
/// next character, or the one after it, of the same kind; past the end
/// of its run, to the run's start, carrying it (a letter) or the digit
/// after it (`9` wraps to `0` and carries `1`).
fn succ_alnum(c: char) -> Alnum {
    let digit = is_decimal_digit(c);
    if !digit && !c.is_alphabetic() {
        return Alnum::Other;
    }
    let same = |x: char| {
        if digit {
            is_decimal_digit(x)
        } else {
            x.is_alphabetic()
        }
    };
    let mut p = c;
    for _ in 0..2 {
        match step_char(p, true) {
            Some(n) if same(n) => return Alnum::Found(n),
            Some(n) => p = n,
            None => break,
        }
    }
    let mut start = c;
    let mut run = 1;
    while let Some(q) = step_char(start, false).filter(|q| same(*q)) {
        start = q;
        run += 1;
    }
    if run == 1 {
        return Alnum::Other;
    }
    let carried = if digit {
        step_char(start, true).unwrap_or(start)
    } else {
        start
    };
    Alnum::Wrapped(start, carried)
}

/// A decimal digit of any script (Unicode `Nd`), as Onigmo's DIGIT.
fn is_decimal_digit(c: char) -> bool {
    if c.is_ascii() {
        return c.is_ascii_digit();
    }
    static ND: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    let nd = ND.get_or_init(|| regex::Regex::new(r"^\p{Nd}$").expect("a valid pattern"));
    let mut buf = [0u8; 4];
    nd.is_match(c.encode_utf8(&mut buf))
}

/// The first and last characters of `c`'s UTF-8 length.
fn utf8_range(c: char) -> (char, char) {
    match c.len_utf8() {
        1 => ('\0', '\u{7f}'),
        2 => ('\u{80}', '\u{7ff}'),
        3 => ('\u{800}', '\u{ffff}'),
        _ => ('\u{10000}', char::MAX),
    }
}

/// The character after (or before) `c` of the same UTF-8 length, `None`
/// past the end of those.
fn step_char(c: char, up: bool) -> Option<char> {
    let (lo, hi) = utf8_range(c);
    let mut n = c as u32;
    loop {
        if (up && n == hi as u32) || (!up && n == lo as u32) {
            return None;
        }
        n = if up { n + 1 } else { n - 1 };
        if let Some(ch) = char::from_u32(n) {
            return Some(ch);
        }
    }
}
