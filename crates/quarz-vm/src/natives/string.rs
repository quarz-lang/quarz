//! String, String::Builder, Symbol, Regexp and MatchData.

use crate::rc::Rc;
use std::cell::RefCell;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

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
        Ok(Value::Bool(re(i, a.arg(0))?.regex.is_match(s(i, r)?)))
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
    native!(m, "String#hex", |i, r, _| {
        Ok(Value::Int(
            i64::from_str_radix(s(i, r)?.trim().trim_start_matches("0x"), 16).unwrap_or(0),
        ))
    });
    native!(m, "String#oct", |i, r, _| {
        Ok(Value::Int(
            i64::from_str_radix(s(i, r)?.trim().trim_start_matches("0o"), 8).unwrap_or(0),
        ))
    });
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
        Ok(Value::Bool(re(i, r)?.regex.is_match(string(
            i,
            a.arg(0),
            "text",
        )?)))
    });
    native!(m, "Regexp#=~", |i, r, a| {
        let text = string(i, a.arg(0), "text")?;
        Ok(match re(i, r)?.regex.find(text) {
            Some(mt) => Value::Int(text[..mt.start()].chars().count() as i64),
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
    native!(m, "MatchData#[]", md_index);
    native!(m, "MatchData#pre_match", |i, r, _| {
        let m = md(i, r)?;
        let (st, _) = m.groups[0].unwrap_or((0, 0));
        Ok(Value::str(&m.text[..st]))
    });
    native!(m, "MatchData#post_match", |i, r, _| {
        let m = md(i, r)?;
        let (_, en) = m.groups[0].unwrap_or((0, 0));
        Ok(Value::str(&m.text[en..]))
    });
    native!(m, "MatchData#captures", |i, r, _| {
        let m = md(i, r)?;
        Ok(Value::array(
            m.groups
                .iter()
                .skip(1)
                .map(|g| {
                    g.map(|(st, en)| Value::str(&m.text[st..en]))
                        .unwrap_or(Value::Nil)
                })
                .collect(),
        ))
    });
    native!(m, "MatchData#to_s", |i, r, _| {
        let m = md(i, r)?;
        let (st, en) = m.groups[0].unwrap_or((0, 0));
        Ok(Value::str(&m.text[st..en]))
    });
    native!(m, "MatchData#begin", |i, r, a| {
        let m = md(i, r)?;
        let n = int(i, a.arg(0), "index")? as usize;
        Ok(m.groups
            .get(n)
            .copied()
            .flatten()
            .map(|(st, _)| Value::Int(m.text[..st].chars().count() as i64))
            .unwrap_or(Value::Nil))
    });
    native!(m, "MatchData#end", |i, r, a| {
        let m = md(i, r)?;
        let n = int(i, a.arg(0), "index")? as usize;
        Ok(m.groups
            .get(n)
            .copied()
            .flatten()
            .map(|(_, en)| Value::Int(m.text[..en].chars().count() as i64))
            .unwrap_or(Value::Nil))
    });
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
        hi -= 1;
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
        (Some(Value::Regexp(r)), _) => {
            let mut v: Vec<&str> = r.regex.split(text).collect();
            while v.last() == Some(&"") {
                v.pop();
            }
            v.into_iter().map(Value::str).collect()
        }
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
    each_match(interp, text, args.arg(0), true, false, |found| {
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
        groups: groups.clone(),
        names: names.to_vec(),
    }))
}

pub fn match_data(interp: &Interp, r: &RegexpVal, text: &str) -> EvalResult {
    let _ = interp;
    match r.regex.captures(text) {
        None => Ok(Value::Nil),
        Some(c) => {
            let groups = (0..c.len())
                .map(|i| c.get(i).map(|m| (m.start(), m.end())))
                .collect();
            let names = r
                .regex
                .capture_names()
                .enumerate()
                .filter_map(|(i, n)| n.map(|n| (n.to_string(), i)))
                .collect();
            Ok(Value::MatchData(Rc::new(MatchDataVal {
                text: Rc::from(text),
                groups,
                names,
            })))
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
    each_match(interp, text, pattern, true, true, |groups| {
        out.push(match_value(&shared, groups, &names));
        Ok(())
    })?;
    Ok(Value::array(out))
}

fn string_match_index(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let text = s(interp, recv)?;
    let r = re(interp, args.arg(0))?;
    Ok(match r.regex.find(text) {
        Some(m) => Value::Int(text[..m.start()].chars().count() as i64),
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
    Ok(match m.groups.get(idx).copied().flatten() {
        Some((st, en)) => Value::str(&m.text[st..en]),
        None => Value::Nil,
    })
}

/// Convert Ruby-style `\1` references to the regex crate's `$1`.
/// The byte ranges of a match and of its groups (`None`: a group that
/// took no part).
pub(super) type Groups = Vec<Option<(usize, usize)>>;

/// Calls `f` with each match of `pattern` (a String or a Regexp) in
/// `text`, in order; only the first unless `global`. The ranges of the
/// groups follow the match's only when `groups` (a String has none). As
/// in Ruby, an empty match may follow a match right where it ends, and
/// the search goes on a character after an empty one (an empty String
/// pattern matches before each character and at the end).
pub(super) fn each_match(
    interp: &Interp,
    text: &str,
    pattern: &Value,
    global: bool,
    groups: bool,
    mut f: impl FnMut(&Groups) -> Result<(), Flow>,
) -> Result<(), Flow> {
    let mut found: Groups = Vec::new();
    let mut locs = match pattern {
        Value::Regexp(rx) if groups => Some(rx.regex.capture_locations()),
        _ => None,
    };
    let mut pos = 0;
    while pos <= text.len() {
        found.clear();
        match (pattern, pattern.as_str()) {
            (_, Some(pat)) => {
                let Some(b) = text[pos..].find(pat) else {
                    break;
                };
                found.push(Some((pos + b, pos + b + pat.len())));
            }
            (Value::Regexp(rx), _) => match &mut locs {
                Some(locs) => {
                    if rx.regex.captures_read_at(locs, text, pos).is_none() {
                        break;
                    }
                    found.extend((0..locs.len()).map(|i| locs.get(i)));
                }
                None => {
                    let Some(m) = rx.regex.find_at(text, pos) else {
                        break;
                    };
                    found.push(Some((m.start(), m.end())));
                }
            },
            (other, _) => {
                return Err(interp.err_type(&format!(
                    "sub takes a String or Regexp, got {}",
                    interp.class_name(other)
                )))
            }
        }
        f(&found)?;
        let Some((st, en)) = found[0] else { break };
        if !global {
            break;
        }
        pos = if en > st {
            en
        } else if let Some(c) = text[en..].chars().next() {
            en + c.len_utf8()
        } else {
            break;
        };
    }
    Ok(())
}

/// `text` with each match of `pattern` replaced by what `replace` writes
/// for it.
pub(super) fn substitute(
    interp: &Interp,
    text: &str,
    pattern: &Value,
    global: bool,
    groups: bool,
    mut replace: impl FnMut(&Groups, &mut String) -> Result<(), Flow>,
) -> Result<String, Flow> {
    let mut out = String::with_capacity(text.len());
    let mut last = 0;
    each_match(interp, text, pattern, global, groups, |found| {
        let (st, en) = found[0].unwrap_or((last, last));
        out.push_str(&text[last..st]);
        replace(found, &mut out)?;
        last = en;
        Ok(())
    })?;
    out.push_str(&text[last..]);
    Ok(out)
}

/// The names of a pattern's groups, with their numbers.
pub(super) fn group_names(pattern: &Value) -> Vec<(String, usize)> {
    match pattern {
        Value::Regexp(rx) => rx
            .regex
            .capture_names()
            .enumerate()
            .filter_map(|(i, n)| n.map(|n| (n.to_string(), i)))
            .collect(),
        _ => Vec::new(),
    }
}

/// A replacement string as Ruby reads it: `\1`..`\9` and `\k<name>` are
/// groups (empty when they took no part), `\0` and `\&` the match, `` \` ``
/// and `\'` what precedes and follows it, `\\` a backslash; any other
/// backslash stays. A `\k<` without its `>` is an error, as in Ruby.
pub(super) fn expand_replacement(
    interp: &Interp,
    rep: &str,
    text: &str,
    groups: &Groups,
    names: &[(String, usize)],
    out: &mut String,
) -> Result<(), Flow> {
    let group = |i: usize| {
        groups
            .get(i)
            .copied()
            .flatten()
            .map_or("", |(st, en)| &text[st..en])
    };
    let (st, en) = groups[0].unwrap_or((0, 0));
    let mut chars = rep.char_indices().peekable();
    while let Some((_, c)) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.peek().map(|(_, d)| *d) {
            Some(d @ '0'..='9') => out.push_str(group(d as usize - '0' as usize)),
            Some('&') => out.push_str(group(0)),
            Some('`') => out.push_str(&text[..st]),
            Some('\'') => out.push_str(&text[en..]),
            Some('\\') => out.push('\\'),
            Some('k') if rep[chars.peek().unwrap().0 + 1..].starts_with('<') => {
                let at = chars.peek().unwrap().0 + 2;
                let Some(close) = rep[at..].find('>') else {
                    return Err(interp.err_arg("invalid group name reference format"));
                };
                let name = &rep[at..at + close];
                let Some((_, i)) = names.iter().find(|(n, _)| n == name) else {
                    return Err(
                        interp.err_index(&format!("undefined group name reference: {name}"))
                    );
                };
                out.push_str(group(*i));
                while chars.next_if(|(j, _)| *j <= at + close).is_some() {}
                continue;
            }
            _ => {
                out.push('\\');
                continue;
            }
        }
        chars.next();
    }
    Ok(())
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
    Ok(Value::string(substitute(
        interp,
        text,
        pattern,
        global,
        escapes,
        |groups, out| {
            if escapes {
                expand_replacement(interp, rep, text, groups, &names, out)
            } else {
                out.push_str(rep);
                Ok(())
            }
        },
    )?))
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
        Some(b) => int(interp, b, "base")? as u32,
        None => 10,
    };
    let t = text.trim_start();
    let mut end = 0;
    let bytes = t.as_bytes();
    if end < bytes.len() && (bytes[end] == b'-' || bytes[end] == b'+') {
        end += 1;
    }
    while end < bytes.len() && ((bytes[end] as char).is_digit(base) || bytes[end] == b'_') {
        end += 1;
    }
    let digits: String = t[..end].chars().filter(|c| *c != '_').collect();
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
    let text = s(interp, recv)?;
    let mut chars: Vec<char> = text.chars().collect();
    let mut i = chars.len();
    while i > 0 {
        i -= 1;
        let c = chars[i];
        let (next, carry) = match c {
            'z' => ('a', true),
            'Z' => ('A', true),
            '9' => ('0', true),
            c if c.is_ascii_alphanumeric() => (char::from_u32(c as u32 + 1).unwrap_or(c), false),
            c => (char::from_u32(c as u32 + 1).unwrap_or(c), false),
        };
        chars[i] = next;
        if !carry {
            return Ok(Value::string(chars.into_iter().collect()));
        }
        if i == 0 {
            let prefix = match c {
                'z' => 'a',
                'Z' => 'A',
                _ => '1',
            };
            chars.insert(0, prefix);
        }
    }
    Ok(Value::string(chars.into_iter().collect()))
}
