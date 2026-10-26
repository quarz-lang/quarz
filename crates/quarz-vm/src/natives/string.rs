//! String, String::Builder, Symbol, Regexp and MatchData.

use crate::rc::Rc;
use std::cell::RefCell;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::matching::{
    each_match, expand_replacement, group_names, names_of, regex_split, substitute, utf8, Hay,
};
use super::{block, int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "String.build", string_build);
    native!(m, "String#+", |i, r, a| {
        Ok(Value::string(format!(
            "{}{}",
            s(i, r)?,
            string(i, a.arg(0), "other")?
        )))
    });
    native!(m, "String#*", |i, r, a| {
        Ok(Value::string(
            s(i, r)?.repeat(int(i, a.arg(0), "count")?.max(0) as usize),
        ))
    });
    native!(m, "String#<=>", |i, r, a| {
        Ok(Value::Int(
            s(i, r)?.cmp(string(i, a.arg(0), "other")?) as i64
        ))
    });
    native!(m, "String#==", |i, r, a| {
        Ok(Value::Bool(a.arg(0).as_str() == Some(s(i, r)?)))
    });
    native!(m, "String#size", |i, r, _| {
        Ok(Value::Int(s(i, r)?.chars().count() as i64))
    });
    native!(m, "String#length", |i, r, _| {
        Ok(Value::Int(s(i, r)?.chars().count() as i64))
    });
    native!(m, "String#bytesize", |i, r, _| {
        Ok(Value::Int(s(i, r)?.len() as i64))
    });
    native!(m, "String#empty?", |i, r, _| {
        Ok(Value::Bool(s(i, r)?.is_empty()))
    });
    native!(m, "String#[]?", string_index_opt);
    native!(m, "String#chars", |i, r, _| {
        Ok(Value::array(
            s(i, r)?
                .chars()
                .map(|c| Value::string(c.to_string()))
                .collect(),
        ))
    });
    native!(m, "String#bytes", |i, r, _| {
        Ok(Value::array(
            s(i, r)?.bytes().map(|b| Value::Int(b as i64)).collect(),
        ))
    });
    native!(m, "String#match", string_match);
    native!(m, "String#matches", string_matches);
    native!(m, "String#match?", |i, r, a| {
        Ok(Value::Bool(
            re(i, a.arg(0))?.regex.is_match(s(i, r)?.as_bytes()),
        ))
    });
    native!(m, "String#=~", string_match_index);
    native!(m, "String#upcase", |i, r, _| {
        Ok(Value::string(s(i, r)?.to_uppercase()))
    });
    native!(m, "String#downcase", |i, r, _| {
        Ok(Value::string(s(i, r)?.to_lowercase()))
    });
    native!(m, "String#capitalize", string_capitalize);
    native!(m, "String#swapcase", |i, r, _| {
        Ok(Value::string(
            s(i, r)?
                .chars()
                .map(|c| {
                    if c.is_uppercase() {
                        c.to_lowercase().next().unwrap_or(c)
                    } else {
                        c.to_uppercase().next().unwrap_or(c)
                    }
                })
                .collect(),
        ))
    });
    native!(m, "String#strip", |i, r, _| Ok(Value::str(s(i, r)?.trim())));
    native!(m, "String#lstrip", |i, r, _| {
        Ok(Value::str(s(i, r)?.trim_start()))
    });
    native!(m, "String#rstrip", |i, r, _| {
        Ok(Value::str(s(i, r)?.trim_end()))
    });
    native!(m, "String#chop", |i, r, _| {
        let st = s(i, r)?;
        let mut c = st.to_string();
        c.pop();
        Ok(Value::string(c))
    });
    native!(m, "String#include?", |i, r, a| {
        Ok(Value::Bool(s(i, r)?.contains(string(
            i,
            a.arg(0),
            "other",
        )?)))
    });
    native!(m, "String#center", |i, r, a| pad(i, r, a, Pad::Center));
    native!(m, "String#ljust", |i, r, a| pad(i, r, a, Pad::Left));
    native!(m, "String#rjust", |i, r, a| pad(i, r, a, Pad::Right));
    native!(m, "String#tr", string_tr);
    native!(m, "String#delete", string_delete);
    native!(m, "String#count", string_count);
    native!(m, "String#reverse", |i, r, _| {
        Ok(Value::string(s(i, r)?.chars().rev().collect()))
    });
    native!(m, "String#each_line", string_each_line);
    native!(m, "String#to_i", string_to_i);
    native!(m, "String#to_f", string_to_f);
    native!(m, "String#to_sym", |i, r, _| {
        Ok(Value::Symbol(i.intern(s(i, r)?)))
    });
    native!(m, "String#to_s", |_, r, _| Ok(r.clone()));
    native!(m, "String#inspect", |i, r, _| {
        Ok(Value::string(crate::interp::inspect_str(s(i, r)?)))
    });
    native!(m, "String#hash", |i, r, _| {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        s(i, r)?.hash(&mut h);
        Ok(Value::Int((h.finish() >> 1) as i64))
    });
    native!(m, "String#succ", string_succ);
    native!(m, "String#ord", |i, r, _| {
        s(i, r)?
            .chars()
            .next()
            .map(|c| Ok(Value::Int(c as i64)))
            .unwrap_or_else(|| Err(i.err_arg("empty string")))
    });
    // As Ruby's: `hex` is `to_i(16)`, `oct` takes the base from a prefix
    // as `to_i(0)` does but reads one without a prefix as octal.
    native!(m, "String#hex", |i, r, _| read_int(i, s(i, r)?, 16, 10));
    native!(m, "String#oct", |i, r, _| read_int(i, s(i, r)?, 0, 8));
    native!(m, "String::Builder.new", |_, _, _| {
        Ok(Value::StringBuilder(Rc::new(RefCell::new(String::new()))))
    });
    native!(m, "String::Builder#<<", sb_push);
    native!(m, "String::Builder#push", sb_push);
    native!(m, "String::Builder#to_s", |i, r, _| {
        Ok(Value::string(std::mem::take(&mut *sb(i, r)?.borrow_mut())))
    });
    native!(m, "String::Builder#size", |i, r, _| {
        Ok(Value::Int(sb(i, r)?.borrow().chars().count() as i64))
    });
    native!(m, "String::Builder#empty?", |i, r, _| {
        Ok(Value::Bool(sb(i, r)?.borrow().is_empty()))
    });
    native!(m, "String::Builder#clear", |i, r, _| {
        sb(i, r)?.borrow_mut().clear();
        Ok(r.clone())
    });
    native!(m, "Symbol#<=>", |i, r, a| {
        Ok(Value::Int(i.compare(r, a.arg(0))? as i64))
    });
    native!(m, "Symbol#to_s", |i, r, _| match r {
        Value::Symbol(sym) => Ok(Value::str_rc(i.symbol_name(*sym))),
        _ => Err(i.err_type("expected a Symbol")),
    });
    native!(m, "Symbol#to_sym", |_, r, _| Ok(r.clone()));
    native!(m, "Symbol#inspect", |i, r, _| Ok(Value::string(
        i.inspect(r)?
    )));
    native!(m, "Symbol#size", |i, r, _| match r {
        Value::Symbol(sym) => Ok(Value::Int(i.symbol_name(*sym).chars().count() as i64)),
        _ => Err(i.err_type("expected a Symbol")),
    });
    native!(m, "Regexp#match", |i, r, a| {
        let rx = re(i, r)?.clone();
        match_data(i, &rx, string(i, a.arg(0), "text")?)
    });
    native!(m, "Regexp#match?", |i, r, a| {
        Ok(Value::Bool(
            re(i, r)?
                .regex
                .is_match(string(i, a.arg(0), "text")?.as_bytes()),
        ))
    });
    native!(m, "Regexp#=~", |i, r, a| {
        let text = string(i, a.arg(0), "text")?;
        Ok(match re(i, r)?.regex.find(text.as_bytes()) {
            Some((st, _)) => Value::Int(text[..st].chars().count() as i64),
            None => Value::Nil,
        })
    });
    native!(m, "Regexp#source", |i, r, _| Ok(Value::str(
        &re(i, r)?.source
    )));
    native!(m, "Regexp#to_s", |i, r, _| {
        Ok(Value::string(format!(
            "/{}/{}",
            re(i, r)?.source,
            re(i, r)?.flags
        )))
    });
    // MatchData and Bytes::MatchData (a String's or Bytes' pieces).
    native!(m, "MatchData#[]", md_index);
    native!(m, "Bytes::MatchData#[]", md_index);
    native!(m, "MatchData#pre_match", md_pre_match);
    native!(m, "Bytes::MatchData#pre_match", md_pre_match);
    native!(m, "MatchData#post_match", md_post_match);
    native!(m, "Bytes::MatchData#post_match", md_post_match);
    native!(m, "MatchData#captures", md_captures);
    native!(m, "Bytes::MatchData#captures", md_captures);
    native!(m, "MatchData#to_s", md_to_s);
    native!(m, "Bytes::MatchData#to_s", md_to_s);
    native!(m, "MatchData#begin", |i, r, a| md_bound(i, r, a, false));
    native!(m, "Bytes::MatchData#begin", |i, r, a| md_bound(
        i, r, a, false
    ));
    native!(m, "MatchData#end", |i, r, a| md_bound(i, r, a, true));
    native!(m, "Bytes::MatchData#end", |i, r, a| md_bound(i, r, a, true));
}

pub(super) fn s<'a>(interp: &Interp, v: &'a Value) -> Result<&'a str, Flow> {
    string(interp, v, "receiver")
}

pub(super) fn sb<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RefCell<String>>, Flow> {
    match v {
        Value::StringBuilder(b) => Ok(b),
        _ => Err(interp.err_type("expected a String::Builder")),
    }
}

pub(super) fn re<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RegexpVal>, Flow> {
    match v {
        Value::Regexp(r) => Ok(r),
        _ => Err(interp.err_type("expected a Regexp")),
    }
}

pub(super) fn md<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<MatchDataVal>, Flow> {
    match v {
        Value::MatchData(m) => Ok(m),
        _ => Err(interp.err_type("expected a MatchData")),
    }
}

fn string_build(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let builder = Rc::new(RefCell::new(String::new()));
    interp.call_block(&b, smallvec![Value::StringBuilder(builder.clone())])?;
    let s = std::mem::take(&mut *builder.borrow_mut());
    Ok(Value::string(s))
}

pub(super) fn sb_push(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let piece = interp.to_s(args.arg(0))?;
    sb(interp, recv)?.borrow_mut().push_str(&piece);
    Ok(recv.clone())
}

/// Character index (negative counts from the end) into a byte offset.
pub(super) fn char_offset(text: &str, index: i64) -> Option<(usize, usize)> {
    let n = text.chars().count() as i64;
    let i = if index < 0 { n + index } else { index };
    if i < 0 || i >= n {
        return None;
    }
    let mut it = text.char_indices();
    let (start, c) = it.nth(i as usize)?;
    Some((start, start + c.len_utf8()))
}

pub(super) fn string_index(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    match args.arg(0) {
        Value::Int(i) => match char_offset(text, *i) {
            Some((st, en)) => Ok(Value::str(&text[st..en])),
            None => Err(interp.err_index(&format!("index {i} out of string bounds"))),
        },
        Value::Range(r) => Ok(Value::string(slice_range(interp, text, r)?)),
        other => Err(interp.err_type(&format!(
            "String#[] takes an Int or Range, got {}",
            interp.class_name(other)
        ))),
    }
}

fn string_index_opt(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let i = int(interp, args.arg(0), "index")?;
    Ok(match char_offset(text, i) {
        Some((st, en)) => Value::str(&text[st..en]),
        None => Value::Nil,
    })
}

pub fn range_bounds(
    interp: &Interp,
    r: &RangeVal,
    len: usize,
) -> Result<Option<(usize, usize)>, Flow> {
    let n = len as i64;
    let lo = match &r.lo {
        Value::Nil => 0,
        v => int(interp, v, "range start")?,
    };
    let hi = match &r.hi {
        Value::Nil => n - 1,
        v => int(interp, v, "range end")?,
    };
    let lo = if lo < 0 { n + lo } else { lo };
    let mut hi = if hi < 0 { n + hi } else { hi };
    if r.exclusive && !r.hi.is_nil() {
        hi = hi.saturating_sub(1);
    }
    if lo < 0 || lo > n {
        return Ok(None);
    }
    let hi = hi.min(n - 1);
    if hi < lo {
        return Ok(Some((lo as usize, lo as usize)));
    }
    Ok(Some((lo as usize, hi as usize + 1)))
}

pub(super) fn slice_range(interp: &Interp, text: &str, r: &RangeVal) -> Result<String, Flow> {
    let chars: Vec<char> = text.chars().collect();
    match range_bounds(interp, r, chars.len())? {
        Some((st, en)) => Ok(chars[st..en].iter().collect()),
        None => Err(interp.err_index("range out of string bounds")),
    }
}

pub(super) fn string_split(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let first = args.pos.first();
    let parts: Vec<Value> = match (first, first.and_then(|v| v.as_str())) {
        (None, _) => text.split_whitespace().map(Value::str).collect(),
        (Some(_), Some(" ")) => text.split_whitespace().map(Value::str).collect(),
        (Some(_), Some("")) => text.chars().map(|c| Value::string(c.to_string())).collect(),
        (Some(_), Some(sep)) => {
            let mut v: Vec<&str> = text.split(sep).collect();
            while v.last() == Some(&"") {
                v.pop();
            }
            v.into_iter().map(Value::str).collect()
        }
        (Some(pattern @ Value::Regexp(_)), _) => regex_split(interp, Hay::Str(text), pattern, 0)?
            .into_iter()
            .map(|(a, b)| Value::str(&text[a..b]))
            .collect(),
        (Some(other), _) => {
            return Err(interp.err_type(&format!(
                "split takes a String or Regexp, got {}",
                interp.class_name(other)
            )))
        }
    };
    Ok(Value::array(parts))
}

/// `scan` without a block: each match, whole (its groups are in the
/// `MatchData` the block form passes).
pub(super) fn string_scan(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    re(interp, args.arg(0))?;
    let mut out = Vec::new();
    each_match(interp, Hay::Str(text), args.arg(0), true, false, |found| {
        let (st, en) = found[0].unwrap_or((0, 0));
        out.push(Value::str(&text[st..en]));
        Ok(())
    })?;
    Ok(Value::array(out))
}

/// A `MatchData` of `text` (shared by the matches of one call).
pub(super) fn match_value(text: &Rc<str>, groups: &Groups, names: &[(String, usize)]) -> Value {
    Value::MatchData(Rc::new(MatchDataVal {
        text: text.clone(),
        data: None,
        groups: groups.clone(),
        names: names.to_vec(),
    }))
}

pub fn match_data(interp: &Interp, r: &RegexpVal, text: &str) -> EvalResult {
    let _ = interp;
    match r.regex.captures(text.as_bytes()) {
        None => Ok(Value::Nil),
        Some(groups) => {
            let names = names_of(r);
            Ok(match_value(&Rc::from(text), &groups, &names))
        }
    }
}

fn string_match(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let r = re(interp, args.arg(0))?;
    match_data(interp, r, text)
}

fn string_matches(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let pattern = args.arg(0);
    re(interp, pattern)?;
    let shared: Rc<str> = Rc::from(text);
    let names = group_names(pattern);
    let mut out = Vec::new();
    each_match(interp, Hay::Str(text), pattern, true, true, |groups| {
        out.push(match_value(&shared, groups, &names));
        Ok(())
    })?;
    Ok(Value::array(out))
}

fn string_match_index(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let r = re(interp, args.arg(0))?;
    Ok(match r.regex.find(text.as_bytes()) {
        Some((st, _)) => Value::Int(text[..st].chars().count() as i64),
        None => Value::Nil,
    })
}

fn md_index(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let m = md(interp, recv)?;
    let idx = match args.arg(0) {
        Value::Int(i) => *i as usize,
        v if v.is_str() => {
            let name = v.as_str().unwrap_or("");
            match m.names.iter().find(|(n, _)| **n == *name) {
                Some((_, i)) => *i,
                None => return Err(interp.err_index(&format!("undefined group name {name}"))),
            }
        }
        other => {
            return Err(interp.err_type(&format!(
                "MatchData#[] takes an Int or String, got {}",
                interp.class_name(other)
            )))
        }
    };
    Ok(m.group(idx))
}

fn md_pre_match(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let m = md(interp, recv)?;
    let (st, _) = m.groups[0].unwrap_or((0, 0));
    Ok(m.piece(0, st))
}

fn md_post_match(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let m = md(interp, recv)?;
    let (_, en) = m.groups[0].unwrap_or((0, 0));
    Ok(m.piece(en, m.len()))
}

fn md_captures(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let m = md(interp, recv)?;
    Ok(Value::array(
        (1..m.groups.len()).map(|k| m.group(k)).collect(),
    ))
}

/// The match, as a String (Bytes as Bytes show themselves).
fn md_to_s(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::string(interp.format_value(recv, false)?))
}

/// Where group `n` begins (or ends): `nil` for a group that took no part,
/// an error past the groups.
fn md_bound(interp: &Interp, recv: &Value, args: Args, end: bool) -> EvalResult {
    let m = md(interp, recv)?;
    let n = int(interp, args.arg(0), "index")?;
    let Some(group) = usize::try_from(n).ok().and_then(|n| m.groups.get(n)) else {
        return Err(interp.err_index(&format!("index {n} out of matches")));
    };
    Ok(group
        .map(|(st, en)| Value::Int(m.offset(if end { en } else { st })))
        .unwrap_or(Value::Nil))
}

pub(super) fn string_sub(interp: &Interp, recv: &Value, args: Args, global: bool) -> EvalResult {
    let text = s(interp, recv)?;
    let rep = string(interp, args.arg(1), "replacement")?;
    let pattern = args.arg(0);
    // Without a backslash the replacement is itself: no groups to find.
    let escapes = rep.contains('\\');
    let names = if escapes {
        group_names(pattern)
    } else {
        Vec::new()
    };
    Ok(Value::string(utf8(substitute(
        interp,
        Hay::Str(text),
        pattern,
        global,
        escapes,
        |groups, out| {
            if escapes {
                expand_replacement(interp, rep.as_bytes(), text.as_bytes(), groups, &names, out)
            } else {
                out.extend_from_slice(rep.as_bytes());
                Ok(())
            }
        },
    )?)))
}

fn string_capitalize(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let mut chars = text.chars();
    Ok(Value::string(match chars.next() {
        Some(c) => c.to_uppercase().collect::<String>() + &chars.as_str().to_lowercase(),
        None => String::new(),
    }))
}

enum Pad {
    Left,
    Right,
    Center,
}

fn pad(interp: &Interp, recv: &Value, args: Args, how: Pad) -> EvalResult {
    let text = s(interp, recv)?;
    let width = int(interp, args.arg(0), "width")?.max(0) as usize;
    let padstr = match args.pos.get(1) {
        Some(p) => string(interp, p, "pad")?.to_string(),
        None => " ".to_string(),
    };
    let len = text.chars().count();
    if len >= width || padstr.is_empty() {
        return Ok(recv.clone());
    }
    let total = width - len;
    let make = |n: usize| -> String { padstr.chars().cycle().take(n).collect() };
    Ok(Value::string(match how {
        Pad::Left => format!("{text}{}", make(total)),
        Pad::Right => format!("{}{text}", make(total)),
        Pad::Center => {
            let left = total / 2;
            format!("{}{text}{}", make(left), make(total - left))
        }
    }))
}

/// Expand `a-z` ranges in a `tr`/`delete` character set.
fn expand_set(spec: &str) -> (Vec<char>, bool) {
    let (negate, spec) = match spec.strip_prefix('^') {
        Some(rest) if !rest.is_empty() => (true, rest),
        _ => (false, spec),
    };
    let chars: Vec<char> = spec.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if i + 2 < chars.len() && chars[i + 1] == '-' {
            let (a, b) = (chars[i] as u32, chars[i + 2] as u32);
            for c in a..=b {
                if let Some(c) = char::from_u32(c) {
                    out.push(c);
                }
            }
            i += 3;
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    (out, negate)
}

fn string_tr(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let (from, negate) = expand_set(string(interp, args.arg(0), "from")?);
    let (to, _) = expand_set(string(interp, args.arg(1), "to")?);
    let out: String = text
        .chars()
        .filter_map(|c| {
            let pos = from.iter().position(|f| *f == c);
            match (pos, negate) {
                (Some(p), false) => to.get(p).or(to.last()).copied(),
                (None, true) => to.last().copied(),
                _ => Some(c),
            }
        })
        .collect();
    Ok(Value::string(out))
}

fn string_delete(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let (set, negate) = expand_set(string(interp, args.arg(0), "chars")?);
    Ok(Value::string(
        text.chars().filter(|c| set.contains(c) == negate).collect(),
    ))
}

fn string_count(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let (set, negate) = expand_set(string(interp, args.arg(0), "chars")?);
    Ok(Value::Int(
        text.chars().filter(|c| set.contains(c) != negate).count() as i64,
    ))
}

pub(super) fn string_each_char(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let b = block(interp, &args)?;
    for c in text.chars() {
        interp.call_block(&b, smallvec![Value::string(c.to_string())])?;
    }
    Ok(Value::Nil)
}

fn string_each_line(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let b = block(interp, &args)?;
    for line in text.split_inclusive('\n') {
        interp.call_block(&b, smallvec![Value::str(line)])?;
    }
    Ok(Value::Nil)
}

fn string_to_i(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let base = match args.pos.first() {
        Some(b) => int(interp, b, "base")?,
        None => 10,
    };
    if base != 0 && !(2..=36).contains(&base) {
        return Err(interp.err_arg(&format!("invalid radix {base}")));
    }
    read_int(interp, text, base as u32, 10)
}

/// The integer at the start of `text` (`int_digits`), `OverflowError`
/// past an `Int`.
fn read_int(interp: &Interp, text: &str, base: u32, unprefixed: u32) -> EvalResult {
    let (negative, digits, base, _) = int_digits(text, base, unprefixed);
    let digits = if negative {
        format!("-{digits}")
    } else {
        digits
    };
    Ok(match i64::from_str_radix(&digits, base) {
        Ok(v) => Value::Int(v),
        Err(_) => {
            use num_traits::Num;
            match num_bigint::BigInt::from_str_radix(&digits, base) {
                Ok(b) => interp.int_of_big(&b)?,
                Err(_) => Value::Int(0),
            }
        }
    })
}

/// The integer at the start of `text`, as Ruby's `String#to_i` reads it:
/// after blanks and a sign, a prefix (`0x`, `0b`, `0o`, `0d`, either case)
/// is skipped when it names `base`; base 0 takes the base from it, octal
/// for a bare leading `0`, `unprefixed` otherwise. A single `_` may stand
/// between digits. Gives the sign, the digits (empty for none), the base
/// and the byte where the number ends.
pub(super) fn int_digits(text: &str, base: u32, unprefixed: u32) -> (bool, String, u32, usize) {
    let b = text.as_bytes();
    let mut i = 0;
    while i < b.len() && (b[i].is_ascii_whitespace() || b[i] == 0x0b) {
        i += 1;
    }
    let mut negative = false;
    if i < b.len() && (b[i] == b'-' || b[i] == b'+') {
        negative = b[i] == b'-';
        i += 1;
    }
    let mut base = base;
    if i + 1 < b.len() && b[i] == b'0' {
        let named = match b[i + 1].to_ascii_lowercase() {
            b'x' => 16,
            b'b' => 2,
            b'o' => 8,
            b'd' => 10,
            _ => 0,
        };
        if named != 0 && (base == 0 || base == named) {
            base = named;
            i += 2;
        } else if base == 0 {
            base = 8;
        }
    } else if base == 0 {
        base = unprefixed;
    }
    let digit = |c: u8| (c as char).is_digit(base);
    let mut out = String::new();
    while i < b.len() {
        if digit(b[i]) {
            out.push(b[i] as char);
        } else if b[i] == b'_' && !out.is_empty() && i + 1 < b.len() && digit(b[i + 1]) {
            // Between two digits.
        } else {
            break;
        }
        i += 1;
    }
    (negative, out, base, i)
}

fn string_to_f(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let t = text.trim_start();
    let mut end = 0;
    let bytes = t.as_bytes();
    let mut seen_dot = false;
    let mut seen_e = false;
    while end < bytes.len() {
        let c = bytes[end] as char;
        if c.is_ascii_digit() || (end == 0 && (c == '-' || c == '+')) {
            end += 1;
        } else if c == '.' && !seen_dot && !seen_e {
            seen_dot = true;
            end += 1;
        } else if (c == 'e' || c == 'E') && !seen_e && end > 0 {
            seen_e = true;
            end += 1;
            if end < bytes.len() && (bytes[end] == b'-' || bytes[end] == b'+') {
                end += 1;
            }
        } else {
            break;
        }
    }
    Ok(Value::Float(t[..end].parse().unwrap_or(0.0)))
}

pub(super) fn string_succ(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    Ok(Value::string(super::text::succ(s(interp, recv)?)))
}
