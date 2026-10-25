//! Searching with a pattern, shared by String and Bytes: a String's
//! bytes are searched as UTF-8 (matches at character boundaries), Bytes
//! byte by byte (`RegexpVal::for_bytes`). Everything here works on byte
//! offsets; the callers make Strings or Bytes of the ranges.

use crate::interp::{Flow, Interp};
use crate::value::*;

/// What is searched.
#[derive(Clone, Copy)]
pub(super) enum Hay<'a> {
    Str(&'a str),
    Bytes(&'a [u8]),
}

impl<'a> Hay<'a> {
    pub(super) fn bytes(&self) -> &'a [u8] {
        match self {
            Hay::Str(s) => s.as_bytes(),
            Hay::Bytes(b) => b,
        }
    }

    /// Where a search goes on after an empty match at `pos`: the next
    /// character (or byte), `None` at the end.
    fn after_empty(&self, pos: usize) -> Option<usize> {
        match self {
            Hay::Str(s) => s[pos..].chars().next().map(|c| pos + c.len_utf8()),
            Hay::Bytes(b) => (pos < b.len()).then_some(pos + 1),
        }
    }

    /// The literal a pattern of the haystack's own type is, if it is one.
    fn literal<'p>(&self, pattern: &'p Value) -> Option<&'p [u8]> {
        match (self, pattern) {
            (Hay::Str(_), p) => p.as_str().map(str::as_bytes),
            (Hay::Bytes(_), Value::Bytes(b)) => Some(b),
            _ => None,
        }
    }
}

/// The searches of `rx` for this haystack (for Bytes, an ArgumentError if
/// the pattern needs Unicode).
pub(super) fn engine<'r>(
    interp: &Interp,
    rx: &'r RegexpVal,
    hay: Hay,
) -> Result<&'r RegexEngine, Flow> {
    match hay {
        Hay::Str(_) => Ok(&rx.regex),
        Hay::Bytes(_) => rx.for_bytes().map_err(|e| interp.err_arg(e)),
    }
}

/// The first occurrence of `needle` in `text` from `pos`.
pub(super) fn find_literal(hay: Hay, needle: &[u8], pos: usize) -> Option<usize> {
    match hay {
        Hay::Str(s) => {
            let needle = std::str::from_utf8(needle).ok()?;
            s[pos..].find(needle).map(|b| pos + b)
        }
        Hay::Bytes(b) if needle.is_empty() => (pos <= b.len()).then_some(pos),
        Hay::Bytes(b) => b[pos..]
            .windows(needle.len())
            .position(|w| w == needle)
            .map(|i| pos + i),
    }
}

/// Calls `f` with each match of `pattern` (a literal of the haystack's
/// type, or a Regexp) in `hay`, in order; only the first unless `global`.
/// The ranges of the groups follow the match's only when `groups` (a
/// literal has none). As in Ruby, an empty match may follow a match right
/// where it ends, and the search goes on a character after an empty one
/// (an empty literal matches before each character and at the end).
pub(super) fn each_match(
    interp: &Interp,
    hay: Hay,
    pattern: &Value,
    global: bool,
    groups: bool,
    mut f: impl FnMut(&Groups) -> Result<(), Flow>,
) -> Result<(), Flow> {
    let text = hay.bytes();
    let literal = hay.literal(pattern);
    let rx = match (pattern, literal) {
        (_, Some(_)) => None,
        (Value::Regexp(rx), None) => Some(engine(interp, rx, hay)?),
        (other, None) => {
            let expected = match hay {
                Hay::Str(_) => "a String or Regexp",
                Hay::Bytes(_) => "Bytes or a Regexp",
            };
            return Err(interp.err_type(&format!(
                "the pattern must be {expected}, got {}",
                interp.class_name(other)
            )));
        }
    };
    let mut found: Groups = Vec::new();
    let mut locs = rx.filter(|_| groups).map(|rx| rx.capture_locations());
    let mut pos = 0;
    while pos <= text.len() {
        found.clear();
        match (literal, rx) {
            (Some(needle), _) => {
                let Some(st) = find_literal(hay, needle, pos) else {
                    break;
                };
                found.push(Some((st, st + needle.len())));
            }
            (None, Some(rx)) => match &mut locs {
                Some(locs) => {
                    if rx.captures_read_at(locs, text, pos).is_some() {
                        found.extend((0..locs.len()).map(|i| locs.get(i)));
                    } else {
                        // None found, or an empty match at the end, which
                        // needs checking.
                        let Some(c) = rx.captures_at(text, pos) else {
                            break;
                        };
                        found.extend(c);
                    }
                }
                None => {
                    let Some(m) = rx.find_at(text, pos) else {
                        break;
                    };
                    found.push(Some(m));
                }
            },
            (None, None) => unreachable!("a pattern is a literal or a Regexp"),
        }
        f(&found)?;
        let Some((st, en)) = found[0] else { break };
        if !global {
            break;
        }
        pos = if en > st {
            en
        } else {
            match hay.after_empty(en) {
                Some(next) => next,
                None => break,
            }
        };
    }
    Ok(())
}

/// The bytes of `hay` with each match of `pattern` replaced by what
/// `replace` writes for it.
pub(super) fn substitute(
    interp: &Interp,
    hay: Hay,
    pattern: &Value,
    global: bool,
    groups: bool,
    mut replace: impl FnMut(&Groups, &mut Vec<u8>) -> Result<(), Flow>,
) -> Result<Vec<u8>, Flow> {
    let text = hay.bytes();
    let mut out = Vec::with_capacity(text.len());
    let mut last = 0;
    each_match(interp, hay, pattern, global, groups, |found| {
        let (st, en) = found[0].unwrap_or((last, last));
        out.extend_from_slice(&text[last..st]);
        replace(found, &mut out)?;
        last = en;
        Ok(())
    })?;
    out.extend_from_slice(&text[last..]);
    Ok(out)
}

/// The ranges of the fields of `split` by a Regexp, as Ruby splits: an
/// empty match where a field starts separates nothing, the groups of each
/// separator follow the field before it, a positive `limit` gives at most
/// that many fields, and with no limit (0) the empty fields at the end are
/// dropped.
pub(super) fn regex_split(
    interp: &Interp,
    hay: Hay,
    pattern: &Value,
    limit: i64,
) -> Result<Vec<(usize, usize)>, Flow> {
    let len = hay.bytes().len();
    if limit == 1 {
        return Ok(if len == 0 { vec![] } else { vec![(0, len)] });
    }
    let groups = matches!(pattern, Value::Regexp(rx) if rx.regex.captures_len() > 1);
    let mut out = Vec::new();
    let mut fields = 0;
    let mut beg = 0;
    each_match(interp, hay, pattern, true, groups, |found| {
        let Some((st, en)) = found[0] else {
            return Ok(());
        };
        if (limit > 0 && fields + 1 >= limit) || (st == en && st == beg) {
            return Ok(());
        }
        out.push((beg, st));
        fields += 1;
        out.extend(found[1..].iter().flatten().copied());
        beg = en;
        Ok(())
    })?;
    if len > 0 && (limit != 0 || len > beg) {
        out.push((beg, len));
    }
    if limit == 0 {
        while out.last().is_some_and(|(a, b)| a == b) {
            out.pop();
        }
    }
    Ok(out)
}

/// The names of a pattern's groups, with their numbers (none for a
/// literal).
pub(super) fn group_names(pattern: &Value) -> Vec<(String, usize)> {
    match pattern {
        Value::Regexp(rx) => names_of(rx),
        _ => Vec::new(),
    }
}

pub(super) fn names_of(rx: &RegexpVal) -> Vec<(String, usize)> {
    rx.regex
        .capture_names()
        .enumerate()
        .filter_map(|(i, n)| n.map(|n| (n.to_string(), i)))
        .collect()
}

/// A replacement as Ruby reads it: `\1`..`\9` and `\k<name>` are groups
/// (empty when they took no part; with named groups, a number is none),
/// `\0` and `\&` the match, `` \` `` and `\'` what precedes and follows
/// it, `\\` a backslash; any other backslash stays. A `\k<` without its
/// `>` is an error, as in Ruby.
pub(super) fn expand_replacement(
    interp: &Interp,
    rep: &[u8],
    text: &[u8],
    groups: &Groups,
    names: &[(String, usize)],
    out: &mut Vec<u8>,
) -> Result<(), Flow> {
    let group = |i: usize| {
        groups
            .get(i)
            .copied()
            .flatten()
            .map_or(&[][..], |(st, en)| &text[st..en])
    };
    let (st, en) = groups[0].unwrap_or((0, 0));
    let mut i = 0;
    while i < rep.len() {
        let c = rep[i];
        i += 1;
        if c != b'\\' || i == rep.len() {
            out.push(c);
            continue;
        }
        match rep[i] {
            b'0' | b'&' => out.extend_from_slice(group(0)),
            d @ b'1'..=b'9' if names.is_empty() => {
                out.extend_from_slice(group((d - b'0') as usize))
            }
            b'1'..=b'9' => {}
            b'`' => out.extend_from_slice(&text[..st]),
            b'\'' => out.extend_from_slice(&text[en..]),
            b'\\' => out.push(b'\\'),
            b'k' if rep.get(i + 1) == Some(&b'<') => {
                let at = i + 2;
                let Some(close) = rep[at..].iter().position(|b| *b == b'>') else {
                    return Err(interp.err_arg("invalid group name reference format"));
                };
                let name = String::from_utf8_lossy(&rep[at..at + close]);
                let Some((_, g)) = names.iter().find(|(n, _)| *n == name) else {
                    return Err(
                        interp.err_index(&format!("undefined group name reference: {name}"))
                    );
                };
                out.extend_from_slice(group(*g));
                i = at + close + 1;
                continue;
            }
            _ => {
                out.push(b'\\');
                continue;
            }
        }
        i += 1;
    }
    Ok(())
}

/// A String of bytes made from a String's own pieces (always UTF-8).
pub(super) fn utf8(bytes: Vec<u8>) -> String {
    String::from_utf8(bytes).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}
