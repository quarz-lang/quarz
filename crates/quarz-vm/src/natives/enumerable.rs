//! The second batch of collection natives: blockless enumerators, the
//! comparator forms of `sort`/`min`/`max`, and the Ruby methods on Array,
//! Hash, Set, Range and their builders that the first batch left out.

use crate::rc::Rc;

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;
use smallvec::smallvec;

use super::collections::{
    ab, arr, arr_data, block_ordering, hash, hash_update, hb, index_opt, range, range_to_vec, sb,
    set, set_update, update,
};
use super::numeric::enumerator;
use super::{block, collect, int, string};

pub fn register(m: &mut super::Registry<NativeFn>) {
    // Enumerable: enumerators for the blockless forms.
    native!(m, "Enumerable#to_enum", |i, r, _| {
        enumerator(i, r, "each", vec![])
    });
    native!(m, "Enumerable#map", |i, r, _| enumerator(
        i,
        r,
        "each",
        vec![]
    ));
    native!(m, "Enumerable#each_with_index", |i, r, _| {
        enumerator(i, r, "each_with_index_pairs", vec![])
    });
    native!(
        m,
        "Enumerable#sort_pairs",
        super::collections::enum_sort_pairs
    );
    native!(m, "Enumerable#each_with_index_pairs", |i, r, a| {
        let b = block(i, &a)?;
        for (k, x) in collect(i, r)?.into_iter().enumerate() {
            i.call_block(&b, smallvec![Value::array(vec![x, Value::Int(k as i64)])])?;
        }
        Ok(Value::Nil)
    });
    native!(m, "Enumerable#each_slice", |i, r, a| {
        enumerator(i, r, "each_slice", a.pos.to_vec())
    });
    native!(m, "Enumerable#each_cons", |i, r, a| {
        enumerator(i, r, "each_cons", a.pos.to_vec())
    });

    // Enumerator
    native!(m, "Enumerator#peek", |i, r, _| {
        let Value::Enumerator(e) = r else {
            return Err(i.err_type("expected an Enumerator"));
        };
        if !e.is_buffered() {
            let items = collect(i, r)?;
            e.fill(items);
        }
        e.current(false)
            .ok_or_else(|| i.raise(i.program.exc.stop_iteration, "iteration reached an end"))
    });
    native!(m, "Enumerator#rewind", |i, r, _| {
        let Value::Enumerator(e) = r else {
            return Err(i.err_type("expected an Enumerator"));
        };
        e.rewind();
        Ok(r.clone())
    });

    // Array
    native!(m, "Array#slice", |i, r, a| {
        let items = arr(i, r)?;
        Ok(Value::array(slice_of(&items, i, a.arg(0), a.arg(1))?))
    });
    native!(m, "Array#take", |i, r, a| {
        let n = int(i, a.arg(0), "count")?;
        if n < 0 {
            return Err(i.err_arg("attempt to take negative size"));
        }
        let data = arr_data(i, r)?;
        Ok(data.slice(0, (n as usize).min(data.len())))
    });
    native!(m, "Array#drop", |i, r, a| {
        let n = int(i, a.arg(0), "count")?;
        if n < 0 {
            return Err(i.err_arg("attempt to drop negative size"));
        }
        let data = arr_data(i, r)?;
        Ok(data.slice((n as usize).min(data.len()), data.len()))
    });
    native!(m, "Array#values_at", |i, r, a| {
        let data = arr_data(i, r)?;
        let n = data.len() as i64;
        let mut out = Vec::with_capacity(a.pos.len());
        for idx in &a.pos {
            let k = int(i, idx, "index")?;
            let k = if k < 0 { n + k } else { k };
            out.push(if (0..n).contains(&k) {
                data.get(k as usize).unwrap_or(Value::Nil)
            } else {
                Value::Nil
            });
        }
        Ok(Value::array(out))
    });
    native!(m, "Array#fill", |i, r, a| {
        let value = a.arg(0).clone();
        if a.pos.len() == 1 {
            return update(i, r, |v| v.iter_mut().for_each(|x| *x = value.clone()));
        }
        let (start, len) = fill_bounds(i, arr(i, r)?.len(), a.arg(1), a.arg(2))?;
        update(i, r, |v| {
            if v.len() < start + len {
                v.resize(start + len, Value::Nil);
            }
            v[start..start + len]
                .iter_mut()
                .for_each(|x| *x = value.clone());
        })
    });
    native!(m, "Array#product", |i, r, a| {
        let other = arr(i, a.arg(0))?;
        let mut out = Vec::new();
        for x in arr(i, r)?.iter() {
            for y in other.iter() {
                out.push(Value::array(vec![x.clone(), y.clone()]));
            }
        }
        Ok(Value::array(out))
    });
    native!(m, "Array#combination", |i, r, a| {
        let n = int(i, a.arg(0), "size")?;
        let items = arr(i, r)?;
        let mut out = Vec::new();
        if n >= 0 && n as usize <= items.len() {
            let mut current = Vec::new();
            combinations(&items, n as usize, 0, &mut current, &mut out);
        }
        Ok(Value::array(out))
    });
    native!(m, "Array#permutation", |i, r, a| {
        let items = arr(i, r)?;
        let n = match a.pos.first() {
            Some(n) => int(i, n, "size")?,
            None => items.len() as i64,
        };
        let mut out = Vec::new();
        if n >= 0 && n as usize <= items.len() {
            let mut used = vec![false; items.len()];
            let mut current = Vec::new();
            permutations(&items, n as usize, &mut used, &mut current, &mut out);
        }
        Ok(Value::array(out))
    });
    native!(m, "Array#bsearch", |i, r, a| {
        let b = block(i, &a)?;
        let data = arr_data(i, r)?.clone();
        let (mut lo, mut hi) = (0usize, data.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let x = data.get(mid).unwrap_or(Value::Nil);
            if i.call_block(&b, smallvec![x])?.is_truthy() {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        Ok(data.get(lo).unwrap_or(Value::Nil))
    });

    // Array::Builder
    native!(m, "Array::Builder#[]", |i, r, a| {
        let b = ab(i, r)?;
        if let Value::Range(rg) = a.arg(0) {
            let items = b.borrow();
            let (start, len) = range_bounds(i, items.len(), rg)?;
            return Ok(Value::array(items[start..start + len].to_vec()));
        }
        let v = index_opt(&b.borrow(), int(i, a.arg(0), "index")?);
        if v.is_nil() && !b.borrow().iter().any(|x| x.is_nil()) {
            return Err(i.err_index("index out of range"));
        }
        Ok(v)
    });
    native!(m, "Array::Builder#first", |i, r, a| {
        let items = ab(i, r)?.borrow();
        match a.pos.first() {
            None => Ok(items.first().cloned().unwrap_or(Value::Nil)),
            Some(n) => {
                let n = int(i, n, "count")?.max(0) as usize;
                Ok(Value::array(items.iter().take(n).cloned().collect()))
            }
        }
    });
    native!(m, "Array::Builder#last", |i, r, a| {
        let items = ab(i, r)?.borrow();
        match a.pos.first() {
            None => Ok(items.last().cloned().unwrap_or(Value::Nil)),
            Some(n) => {
                let n = int(i, n, "count")?.max(0) as usize;
                let skip = items.len().saturating_sub(n);
                Ok(Value::array(items.iter().skip(skip).cloned().collect()))
            }
        }
    });
    native!(m, "Array::Builder#index", |i, r, a| {
        Ok(ab(i, r)?
            .borrow()
            .iter()
            .position(|x| x == a.arg(0))
            .map(|p| Value::Int(p as i64))
            .unwrap_or(Value::Nil))
    });
    native!(m, "Array::Builder#join", |i, r, a| {
        let items = ab(i, r)?.borrow().clone();
        let sep = match a.pos.first() {
            Some(s) => string(i, s, "separator")?,
            None => "",
        };
        let mut parts = Vec::with_capacity(items.len());
        for x in &items {
            parts.push(i.to_s(x)?.to_string());
        }
        Ok(Value::string(parts.join(sep)))
    });
    native!(m, "Array::Builder#sort!", |i, r, a| {
        let b = ab(i, r)?;
        let mut items = std::mem::take(&mut *b.borrow_mut());
        let result = match &a.block {
            None => i.sort_values(&mut items, |x, y| i.compare(x, y)),
            Some(cmp) => i.sort_values(&mut items, |x, y| block_ordering(i, cmp, x, y)),
        };
        *b.borrow_mut() = items;
        result?;
        Ok(r.clone())
    });
    native!(m, "Array::Builder#sort_by!", |i, r, a| {
        let bl = block(i, &a)?;
        let b = ab(i, r)?;
        let items = b.borrow().clone();
        let mut keyed = Vec::with_capacity(items.len());
        for x in items {
            keyed.push((i.call_block(&bl, smallvec![x.clone()])?, x));
        }
        let mut indices: Vec<usize> = (0..keyed.len()).collect();
        let mut failure = None;
        indices.sort_by(|&x, &y| match i.compare(&keyed[x].0, &keyed[y].0) {
            Ok(o) => o,
            Err(e) => {
                failure.get_or_insert(e);
                std::cmp::Ordering::Equal
            }
        });
        if let Some(e) = failure {
            return Err(e);
        }
        *b.borrow_mut() = indices.into_iter().map(|k| keyed[k].1.clone()).collect();
        Ok(r.clone())
    });
    native!(m, "Array::Builder#uniq!", |i, r, _| {
        let b = ab(i, r)?;
        let seen: ValueSet = b.borrow().iter().cloned().collect();
        *b.borrow_mut() = seen.into_iter().collect();
        Ok(r.clone())
    });
    native!(m, "Array::Builder#compact!", |i, r, _| {
        ab(i, r)?.borrow_mut().retain(|x| !x.is_nil());
        Ok(r.clone())
    });
    native!(m, "Array::Builder#shuffle!", |i, r, _| {
        let b = ab(i, r)?;
        let mut v = b.borrow_mut();
        for k in (1..v.len()).rev() {
            let j = (super::random::next_random() % (k as u64 + 1)) as usize;
            v.swap(k, j);
        }
        drop(v);
        Ok(r.clone())
    });
    native!(m, "Array::Builder#rotate!", |i, r, a| {
        let count = match a.pos.first() {
            Some(n) => int(i, n, "count")?,
            None => 1,
        };
        let b = ab(i, r)?;
        let mut v = b.borrow_mut();
        if !v.is_empty() {
            let n = v.len() as i64;
            let k = count.rem_euclid(n) as usize;
            v.rotate_left(k);
        }
        drop(v);
        Ok(r.clone())
    });
    native!(m, "Array::Builder#fill", |i, r, a| {
        let value = a.arg(0).clone();
        let b = ab(i, r)?;
        if a.pos.len() == 1 {
            b.borrow_mut().iter_mut().for_each(|x| *x = value.clone());
            return Ok(r.clone());
        }
        let len_now = b.borrow().len();
        let (start, len) = fill_bounds(i, len_now, a.arg(1), a.arg(2))?;
        let mut v = b.borrow_mut();
        if v.len() < start + len {
            v.resize(start + len, Value::Nil);
        }
        v[start..start + len]
            .iter_mut()
            .for_each(|x| *x = value.clone());
        drop(v);
        Ok(r.clone())
    });
    native!(m, "Array::Builder#replace", |i, r, a| {
        let items = collect(i, a.arg(0))?;
        *ab(i, r)?.borrow_mut() = items;
        Ok(r.clone())
    });
    native!(m, "Array::Builder#slice!", |i, r, a| {
        let b = ab(i, r)?;
        let len_now = b.borrow().len();
        let (start, len) = fill_bounds(i, len_now, a.arg(0), a.arg(1))?;
        let mut v = b.borrow_mut();
        let end = (start + len).min(v.len());
        let start = start.min(v.len());
        let removed: Vec<Value> = v.drain(start..end).collect();
        drop(v);
        Ok(Value::array(removed))
    });
    native!(m, "Array::Builder#delete_if", |i, r, a| {
        builder_filter(i, r, a, false)
    });
    native!(m, "Array::Builder#keep_if", |i, r, a| {
        builder_filter(i, r, a, true)
    });

    // Hash
    native!(m, "Hash#include?", |i, r, a| {
        Ok(Value::Bool(hash(i, r)?.contains_key(a.arg(0))))
    });
    native!(m, "Hash#member?", |i, r, a| {
        Ok(Value::Bool(hash(i, r)?.contains_key(a.arg(0))))
    });
    native!(m, "Hash#has_value?", |i, r, a| {
        Ok(Value::Bool(
            hash(i, r)?.as_map().values().any(|v| v == a.arg(0)),
        ))
    });
    native!(m, "Hash#values_at", |i, r, a| {
        let h = hash(i, r)?;
        Ok(Value::array(
            a.pos
                .iter()
                .map(|k| h.get(k).unwrap_or(Value::Nil))
                .collect(),
        ))
    });
    native!(m, "Hash#fetch_values", |i, r, a| {
        let h = hash(i, r)?;
        let mut out = Vec::with_capacity(a.pos.len());
        for k in &a.pos {
            match h.get(k) {
                Some(v) => out.push(v.clone()),
                None => {
                    return Err(i.raise(
                        i.program.exc.key_error,
                        &format!("key not found: {}", i.inspect(k)?),
                    ))
                }
            }
        }
        Ok(Value::array(out))
    });
    native!(m, "Hash#compact", |i, r, _| {
        hash_update(i, r, |h| h.retain(|_, v| !v.is_nil()))
    });
    native!(m, "Hash#except", |i, r, a| {
        hash_update(i, r, |h| {
            for k in &a.pos {
                h.shift_remove(k);
            }
        })
    });
    native!(m, "Hash#slice", |i, r, a| {
        let h = hash(i, r)?;
        let mut out = ValueMap::default();
        for k in &a.pos {
            if let Some(v) = h.get(k) {
                out.insert(k.clone(), v.clone());
            }
        }
        Ok(Value::Hash(Rc::new(crate::value::HashData::from(out))))
    });

    // Hash::Builder
    native!(m, "Hash::Builder#merge!", |i, r, a| {
        let other = hash(i, a.arg(0))?.clone();
        let other = other.as_map();
        let b = hb(i, r)?;
        match &a.block {
            None => b
                .borrow_mut()
                .extend(other.iter().map(|(k, v)| (k.clone(), v.clone()))),
            Some(bl) => {
                for (k, v) in other.iter() {
                    let existing = b.borrow().get(k).cloned();
                    let merged = match existing {
                        Some(old) => i.call_block(bl, smallvec![k.clone(), old, v.clone()])?,
                        None => v.clone(),
                    };
                    b.borrow_mut().insert(k.clone(), merged);
                }
            }
        }
        Ok(r.clone())
    });
    native!(m, "Hash::Builder#update", |i, r, a| {
        let bl = block(i, &a)?;
        let b = hb(i, r)?;
        let key = a.arg(0).clone();
        let current = b.borrow().get(&key).cloned().unwrap_or(Value::Nil);
        let next = i.call_block(&bl, smallvec![current])?;
        b.borrow_mut().insert(key, next);
        Ok(r.clone())
    });
    native!(m, "Hash::Builder#each_pair", |i, r, a| {
        let b = block(i, &a)?;
        for (k, v) in builder_pairs(i, r)? {
            i.call_block(&b, smallvec![k, v])?;
        }
        Ok(Value::Nil)
    });
    native!(m, "Hash::Builder#each_key", |i, r, a| {
        let b = block(i, &a)?;
        for (k, _) in builder_pairs(i, r)? {
            i.call_block(&b, smallvec![k])?;
        }
        Ok(Value::Nil)
    });
    native!(m, "Hash::Builder#each_value", |i, r, a| {
        let b = block(i, &a)?;
        for (_, v) in builder_pairs(i, r)? {
            i.call_block(&b, smallvec![v])?;
        }
        Ok(Value::Nil)
    });
    native!(m, "Hash::Builder#fetch", |i, r, a| {
        let found = hb(i, r)?.borrow().get(a.arg(0)).cloned();
        match (found, &a.block) {
            (Some(v), _) => Ok(v),
            (None, Some(b)) => i.call_block(b, smallvec![a.arg(0).clone()]),
            (None, None) => Ok(a.arg(1).clone()),
        }
    });
    native!(m, "Hash::Builder#has_key?", |i, r, a| {
        Ok(Value::Bool(hb(i, r)?.borrow().contains_key(a.arg(0))))
    });
    native!(m, "Hash::Builder#include?", |i, r, a| {
        Ok(Value::Bool(hb(i, r)?.borrow().contains_key(a.arg(0))))
    });
    native!(m, "Hash::Builder#value?", |i, r, a| {
        Ok(Value::Bool(
            hb(i, r)?.borrow().values().any(|v| v == a.arg(0)),
        ))
    });
    native!(m, "Hash::Builder#length", |i, r, _| {
        Ok(Value::Int(hb(i, r)?.borrow().len() as i64))
    });
    native!(m, "Hash::Builder#select!", |i, r, a| {
        hash_builder_filter(i, r, a, true)
    });
    native!(m, "Hash::Builder#keep_if", |i, r, a| {
        hash_builder_filter(i, r, a, true)
    });
    native!(m, "Hash::Builder#reject!", |i, r, a| {
        hash_builder_filter(i, r, a, false)
    });
    native!(m, "Hash::Builder#delete_if", |i, r, a| {
        hash_builder_filter(i, r, a, false)
    });
    native!(m, "Hash::Builder#transform_values!", |i, r, a| {
        let bl = block(i, &a)?;
        let b = hb(i, r)?;
        let mut out = ValueMap::default();
        for (k, v) in builder_pairs(i, r)? {
            out.insert(k, i.call_block(&bl, smallvec![v])?);
        }
        *b.borrow_mut() = out;
        Ok(r.clone())
    });
    native!(m, "Hash::Builder#compact!", |i, r, _| {
        hb(i, r)?.borrow_mut().retain(|_, v| !v.is_nil());
        Ok(r.clone())
    });
    native!(m, "Hash::Builder#replace", |i, r, a| {
        let other = hash(i, a.arg(0))?.as_map().into_owned();
        *hb(i, r)?.borrow_mut() = other;
        Ok(r.clone())
    });

    // Set
    native!(m, "Set#proper_subset?", |i, r, a| {
        let other = set(i, a.arg(0))?;
        let mine = set(i, r)?;
        Ok(Value::Bool(
            mine.len() < other.len() && mine.iter().all(|x| other.contains(x)),
        ))
    });
    native!(m, "Set#proper_superset?", |i, r, a| {
        let other = set(i, a.arg(0))?;
        let mine = set(i, r)?;
        Ok(Value::Bool(
            mine.len() > other.len() && other.iter().all(|x| mine.contains(x)),
        ))
    });
    native!(m, "Set#disjoint?", |i, r, a| {
        let other = set(i, a.arg(0))?;
        Ok(Value::Bool(!set(i, r)?.iter().any(|x| other.contains(x))))
    });
    native!(m, "Set#intersect?", |i, r, a| {
        let other = set(i, a.arg(0))?;
        Ok(Value::Bool(set(i, r)?.iter().any(|x| other.contains(x))))
    });
    native!(m, "Set#merge", |i, r, a| {
        let items = collect(i, a.arg(0))?;
        set_update(i, r, |s| s.extend(items))
    });
    native!(m, "Set#add?", |i, r, a| {
        if set(i, r)?.contains(a.arg(0)) {
            return Ok(Value::Nil);
        }
        set_update(i, r, |s| {
            s.insert(a.arg(0).clone());
        })
    });
    native!(m, "Set#select", |i, r, a| set_filter(i, r, a, true));
    native!(m, "Set#reject", |i, r, a| set_filter(i, r, a, false));

    // Set::Builder
    native!(m, "Set::Builder#add?", |i, r, a| {
        Ok(Value::Bool(sb(i, r)?.borrow_mut().insert(a.arg(0).clone())))
    });
    native!(m, "Set::Builder#merge", |i, r, a| {
        let items = collect(i, a.arg(0))?;
        sb(i, r)?.borrow_mut().extend(items);
        Ok(r.clone())
    });
    native!(m, "Set::Builder#subtract", |i, r, a| {
        let items = collect(i, a.arg(0))?;
        let b = sb(i, r)?;
        for x in &items {
            b.borrow_mut().shift_remove(x);
        }
        Ok(r.clone())
    });
    native!(m, "Set::Builder#clear", |i, r, _| {
        sb(i, r)?.borrow_mut().clear();
        Ok(r.clone())
    });
    native!(m, "Set::Builder#replace", |i, r, a| {
        let items = collect(i, a.arg(0))?;
        *sb(i, r)?.borrow_mut() = items.into_iter().collect();
        Ok(r.clone())
    });
    native!(m, "Set::Builder#length", |i, r, _| {
        Ok(Value::Int(sb(i, r)?.borrow().len() as i64))
    });
    native!(m, "Set::Builder#select!", |i, r, a| {
        set_builder_filter(i, r, a, true)
    });
    native!(m, "Set::Builder#keep_if", |i, r, a| {
        set_builder_filter(i, r, a, true)
    });
    native!(m, "Set::Builder#reject!", |i, r, a| {
        set_builder_filter(i, r, a, false)
    });
    native!(m, "Set::Builder#delete_if", |i, r, a| {
        set_builder_filter(i, r, a, false)
    });

    // Range
    native!(m, "Range#empty?", |i, r, _| {
        let rg = range(i, r)?;
        Ok(Value::Bool(match (&rg.lo, &rg.hi) {
            (Value::Int(lo), Value::Int(hi)) => {
                if rg.exclusive {
                    lo >= hi
                } else {
                    lo > hi
                }
            }
            (_, Value::Nil) | (Value::Nil, _) => false,
            _ => range_to_vec(i, rg)?.is_empty(),
        }))
    });
    native!(m, "Range#reverse_each", |i, r, a| {
        let b = block(i, &a)?;
        for v in range_to_vec(i, range(i, r)?)?.into_iter().rev() {
            i.call_block(&b, smallvec![v])?;
        }
        Ok(Value::Nil)
    });
}

// ----- helpers ---------------------------------------------------------------------

/// `start`/`length` arguments normalized to a slice of `len` elements
/// (a negative start counts from the end; the slice is clamped).
fn fill_bounds(
    interp: &Interp,
    len: usize,
    start: &Value,
    length: &Value,
) -> Result<(usize, usize), Flow> {
    let start = int(interp, start, "start")?;
    let count = int(interp, length, "length")?;
    let start = if start < 0 { len as i64 + start } else { start };
    if start < 0 {
        return Err(interp.err_index("start out of range"));
    }
    Ok((start as usize, count.max(0) as usize))
}

/// The elements `items[start, length]` (empty past the end).
fn slice_of(
    items: &[Value],
    interp: &Interp,
    start: &Value,
    length: &Value,
) -> Result<Vec<Value>, Flow> {
    let (start, len) = fill_bounds(interp, items.len(), start, length)?;
    if start > items.len() {
        return Ok(Vec::new());
    }
    let end = (start + len).min(items.len());
    Ok(items[start..end].to_vec())
}

/// The bounds a range selects from `len` elements.
fn range_bounds(interp: &Interp, len: usize, rg: &RangeVal) -> Result<(usize, usize), Flow> {
    let n = len as i64;
    let lo = match &rg.lo {
        Value::Nil => 0,
        v => int(interp, v, "range start")?,
    };
    let hi = match &rg.hi {
        Value::Nil => n,
        v => {
            let h = int(interp, v, "range end")?;
            let h = if h < 0 { n + h } else { h };
            if rg.exclusive {
                h
            } else {
                h + 1
            }
        }
    };
    let lo = if lo < 0 { n + lo } else { lo };
    let lo = lo.clamp(0, n);
    let hi = hi.clamp(lo, n);
    Ok((lo as usize, (hi - lo) as usize))
}

fn combinations(
    items: &[Value],
    n: usize,
    from: usize,
    current: &mut Vec<Value>,
    out: &mut Vec<Value>,
) {
    if current.len() == n {
        out.push(Value::array(current.clone()));
        return;
    }
    for k in from..items.len() {
        current.push(items[k].clone());
        combinations(items, n, k + 1, current, out);
        current.pop();
    }
}

fn permutations(
    items: &[Value],
    n: usize,
    used: &mut [bool],
    current: &mut Vec<Value>,
    out: &mut Vec<Value>,
) {
    if current.len() == n {
        out.push(Value::array(current.clone()));
        return;
    }
    for k in 0..items.len() {
        if used[k] {
            continue;
        }
        used[k] = true;
        current.push(items[k].clone());
        permutations(items, n, used, current, out);
        current.pop();
        used[k] = false;
    }
}

fn builder_filter(interp: &Interp, recv: &Value, args: Args, keep: bool) -> EvalResult {
    let bl = block(interp, &args)?;
    let b = ab(interp, recv)?;
    let items = b.borrow().clone();
    let mut out = Vec::new();
    for x in items {
        if interp.call_block(&bl, smallvec![x.clone()])?.is_truthy() == keep {
            out.push(x);
        }
    }
    *b.borrow_mut() = out;
    Ok(recv.clone())
}

fn builder_pairs(interp: &Interp, recv: &Value) -> Result<Vec<(Value, Value)>, Flow> {
    Ok(hb(interp, recv)?
        .borrow()
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect())
}

fn hash_builder_filter(interp: &Interp, recv: &Value, args: Args, keep: bool) -> EvalResult {
    let bl = block(interp, &args)?;
    let b = hb(interp, recv)?;
    let mut out = ValueMap::default();
    for (k, v) in builder_pairs(interp, recv)? {
        if interp
            .call_block(&bl, smallvec![k.clone(), v.clone()])?
            .is_truthy()
            == keep
        {
            out.insert(k, v);
        }
    }
    *b.borrow_mut() = out;
    Ok(recv.clone())
}

fn set_filter(interp: &Interp, recv: &Value, args: Args, keep: bool) -> EvalResult {
    let bl = block(interp, &args)?;
    let mut out = ValueSet::default();
    for x in set(interp, recv)?.iter() {
        if interp.call_block(&bl, smallvec![x.clone()])?.is_truthy() == keep {
            out.insert(x.clone());
        }
    }
    Ok(Value::Set(Rc::new(out)))
}

fn set_builder_filter(interp: &Interp, recv: &Value, args: Args, keep: bool) -> EvalResult {
    let bl = block(interp, &args)?;
    let b = sb(interp, recv)?;
    let items: Vec<Value> = b.borrow().iter().cloned().collect();
    let mut out = ValueSet::default();
    for x in items {
        if interp.call_block(&bl, smallvec![x.clone()])?.is_truthy() == keep {
            out.insert(x);
        }
    }
    *b.borrow_mut() = out;
    Ok(recv.clone())
}
