//! Searching in Bytes, as in a String but byte by byte: the same engine
//! (`matching`), positions in bytes, pieces and matches as Bytes and
//! `Bytes::MatchData`.

use crate::rc::Rc;
use smallvec::smallvec;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::int;
use super::matching::{
    each_match, engine, expand_replacement, find_literal, group_names, regex_split, substitute, Hay,
};
use super::text::wants_match;

pub fn register(m: &mut super::Registry<NativeFn>) {
    native!(m, "Bytes#start_with?", |i, r, a| {
        let data = bs(i, r)?;
        Ok(Value::Bool(match a.arg(0) {
            Value::Regexp(rx) => engine(i, rx, Hay::Bytes(&data))?
                .find(&data)
                .is_some_and(|(st, _)| st == 0),
            other => data.starts_with(&bs(i, other)?),
        }))
    });
    native!(m, "Bytes#end_with?", |i, r, a| {
        Ok(Value::Bool(bs(i, r)?.ends_with(&bs(i, a.arg(0))?)))
    });
    native!(m, "Bytes#include?", |i, r, a| {
        let data = bs(i, r)?;
        let needle = bs(i, a.arg(0))?;
        Ok(Value::Bool(
            find_literal(Hay::Bytes(&data), &needle, 0).is_some(),
        ))
    });
    native!(m, "Bytes#index", |i, r, a| bytes_find(i, r, a, false));
    native!(m, "Bytes#rindex", |i, r, a| bytes_find(i, r, a, true));
    native!(m, "Bytes#split", |i, r, a| {
        let data = bs(i, r)?;
        let limit = match a.pos.get(1) {
            Some(v) => int(i, v, "limit")?,
            None => 0,
        };
        let fields = regex_split(i, Hay::Bytes(&data), a.arg(0), limit)?;
        Ok(Value::array(
            fields
                .into_iter()
                .map(|(st, en)| Value::bytes(data[st..en].to_vec()))
                .collect(),
        ))
    });
    native!(m, "Bytes#partition", |i, r, a| bytes_partition(
        i, r, a, false
    ));
    native!(m, "Bytes#rpartition", |i, r, a| bytes_partition(
        i, r, a, true
    ));
    native!(m, "Bytes#=~", |i, r, a| {
        let data = bs(i, r)?;
        let rx = re(i, a.arg(0))?;
        Ok(match engine(i, rx, Hay::Bytes(&data))?.find(&data) {
            Some((st, _)) => Value::Int(st as i64),
            None => Value::Nil,
        })
    });
    native!(m, "Bytes#match?", |i, r, a| {
        let data = bs(i, r)?;
        let rx = re(i, a.arg(0))?;
        Ok(Value::Bool(
            engine(i, rx, Hay::Bytes(&data))?.is_match(&data),
        ))
    });
    native!(m, "Bytes#match", |i, r, a| {
        let data = bs(i, r)?;
        let pattern = a.arg(0);
        let rx = re(i, pattern)?;
        Ok(match engine(i, rx, Hay::Bytes(&data))?.captures(&data) {
            Some(groups) => match_value(&data, &groups, &group_names(pattern)),
            None => Value::Nil,
        })
    });
    native!(m, "Bytes#matches", |i, r, a| {
        let data = bs(i, r)?;
        let pattern = a.arg(0);
        re(i, pattern)?;
        let names = group_names(pattern);
        let mut out = Vec::new();
        each_match(i, Hay::Bytes(&data), pattern, true, true, |groups| {
            out.push(match_value(&data, groups, &names));
            Ok(())
        })?;
        Ok(Value::array(out))
    });
    native!(m, "Bytes#scan", |i, r, a| {
        let data = bs(i, r)?;
        let pattern = a.arg(0);
        re(i, pattern)?;
        let Some(b) = a.block.clone() else {
            let mut out = Vec::new();
            each_match(i, Hay::Bytes(&data), pattern, true, false, |found| {
                let (st, en) = found[0].unwrap_or((0, 0));
                out.push(Value::bytes(data[st..en].to_vec()));
                Ok(())
            })?;
            return Ok(Value::array(out));
        };
        let wants = wants_match(i, &b);
        let names = group_names(pattern);
        each_match(i, Hay::Bytes(&data), pattern, true, wants, |groups| {
            let (st, en) = groups[0].unwrap_or((0, 0));
            let matched = Value::bytes(data[st..en].to_vec());
            if wants {
                let md = match_value(&data, groups, &names);
                i.call_block(&b, smallvec![matched, md])?;
            } else {
                i.call_block(&b, smallvec![matched])?;
            }
            Ok(())
        })?;
        Ok(Value::Nil)
    });
    native!(m, "Bytes#sub", |i, r, a| bytes_sub(i, r, a, false));
    native!(m, "Bytes#gsub", |i, r, a| bytes_sub(i, r, a, true));
}

fn bs(interp: &Interp, v: &Value) -> Result<Rc<[u8]>, Flow> {
    match v {
        Value::Bytes(b) => Ok(b.clone()),
        _ => Err(interp.err_type(&format!("expected Bytes, got {}", interp.class_name(v)))),
    }
}

fn re<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RegexpVal>, Flow> {
    match v {
        Value::Regexp(r) => Ok(r),
        _ => Err(interp.err_type(&format!("expected a Regexp, got {}", interp.class_name(v)))),
    }
}

/// A `Bytes::MatchData` in `data`.
fn match_value(data: &Rc<[u8]>, groups: &Groups, names: &[(String, usize)]) -> Value {
    Value::MatchData(Rc::new(MatchDataVal {
        text: Rc::from(""),
        data: Some(data.clone()),
        groups: groups.clone(),
        names: names.to_vec(),
    }))
}

/// `index`/`rindex` with Bytes or a Regexp and an optional start (a byte
/// position; negative from the end).
fn bytes_find(interp: &Interp, recv: &Value, args: Args, from_right: bool) -> EvalResult {
    let data = bs(interp, recv)?;
    let n = data.len() as i64;
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
        None if from_right => data.len(),
        None => 0,
    };
    let hay = Hay::Bytes(&data);
    let found = match args.arg(0) {
        Value::Regexp(rx) => {
            let rx = engine(interp, rx, hay)?;
            if from_right {
                rx.last_match_before(&data, start).map(|(st, _)| st)
            } else {
                rx.find_at(&data, start).map(|(st, _)| st)
            }
        }
        other => {
            let needle = bs(interp, other)?;
            if from_right {
                (0..=start.min(data.len().saturating_sub(needle.len())))
                    .rev()
                    .find(|p| data[*p..].starts_with(&needle))
                    .filter(|_| needle.len() <= data.len())
            } else {
                find_literal(hay, &needle, start)
            }
        }
    };
    Ok(found.map_or(Value::Nil, |p| Value::Int(p as i64)))
}

/// `partition`/`rpartition`: before, the (first or last) match, after.
fn bytes_partition(interp: &Interp, recv: &Value, args: Args, from_right: bool) -> EvalResult {
    let data = bs(interp, recv)?;
    let hay = Hay::Bytes(&data);
    let found = match args.arg(0) {
        Value::Regexp(rx) => {
            let rx = engine(interp, rx, hay)?;
            if from_right {
                rx.last_match_before(&data, data.len())
            } else {
                rx.find(&data)
            }
        }
        other => {
            let sep = bs(interp, other)?;
            let at = if from_right {
                (sep.len() <= data.len())
                    .then(|| {
                        (0..=data.len() - sep.len())
                            .rev()
                            .find(|p| data[*p..].starts_with(&sep))
                    })
                    .flatten()
            } else {
                find_literal(hay, &sep, 0)
            };
            at.map(|st| (st, st + sep.len()))
        }
    };
    let piece = |st: usize, en: usize| Value::bytes(data[st..en].to_vec());
    let empty = || Value::bytes(Vec::new());
    let parts = match found {
        Some((st, en)) => vec![piece(0, st), piece(st, en), piece(en, data.len())],
        None if from_right => vec![empty(), empty(), piece(0, data.len())],
        None => vec![piece(0, data.len()), empty(), empty()],
    };
    Ok(Value::array(parts))
}

/// `sub`/`gsub`: with a replacement (read as a String's replacement is),
/// a block (given the match, and its `Bytes::MatchData` when it takes
/// two parameters), or a Hash of replacements.
fn bytes_sub(interp: &Interp, recv: &Value, args: Args, global: bool) -> EvalResult {
    let data = bs(interp, recv)?;
    let hay = Hay::Bytes(&data);
    let pattern = args.arg(0);
    let regexp = matches!(pattern, Value::Regexp(_));
    if let (None, Value::Bytes(rep)) = (&args.block, args.arg(1)) {
        let escapes = rep.contains(&b'\\');
        let names = if escapes {
            group_names(pattern)
        } else {
            Vec::new()
        };
        let out = substitute(interp, hay, pattern, global, escapes, |groups, out| {
            if escapes {
                expand_replacement(interp, rep, &data, groups, &names, out)
            } else {
                out.extend_from_slice(rep);
                Ok(())
            }
        })?;
        return Ok(Value::bytes(out));
    }
    let wants = regexp && args.block.as_ref().is_some_and(|b| wants_match(interp, b));
    let names = if wants {
        group_names(pattern)
    } else {
        Vec::new()
    };
    let out = substitute(interp, hay, pattern, global, wants, |groups, out| {
        let (st, en) = groups[0].unwrap_or((0, 0));
        let matched = Value::bytes(data[st..en].to_vec());
        if let Some(b) = &args.block {
            let v = if wants {
                let md = match_value(&data, groups, &names);
                interp.call_block(b, smallvec![matched, md])?
            } else {
                interp.call_block(b, smallvec![matched])?
            };
            out.extend_from_slice(&bs(interp, &v)?);
        } else if let Value::Hash(h) = args.arg(1) {
            if let Some(v) = h.get(&matched) {
                out.extend_from_slice(&bs(interp, &v)?);
            }
        }
        Ok(())
    })?;
    Ok(Value::bytes(out))
}
