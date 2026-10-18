//! Array, Hash, Set, their builders, Range, Enumerator and the
//! comparison-based Enumerable extensions.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn, OwnedNativeFn};
use crate::value::*;

use super::{block, collect, int, string};

/// In-place variants used when the caller owns the receiver
/// (`xs = xs.push(x)`): `Rc::make_mut` mutates without copying when the
/// reference is unique.
pub fn register_owned(m: &mut HashMap<&'static str, OwnedNativeFn>) {
    m.insert("Array#push", |_, r, a| {
        owned_update(r, |v| v.push(a.arg(0).clone()))
    });
    m.insert("Array#pop", |_, r, _| {
        owned_update(r, |v| {
            v.pop();
        })
    });
    m.insert("Array#shift", |_, r, _| {
        owned_update(r, |v| {
            if !v.is_empty() {
                v.remove(0);
            }
        })
    });
    m.insert("Array#unshift", |_, r, a| {
        owned_update(r, |v| v.insert(0, a.arg(0).clone()))
    });
    m.insert("Array#concat", |i, r, a| {
        let other = match arr(i, a.arg(0)) {
            Ok(o) => o.clone(),
            Err(e) => return Err((e, r)),
        };
        owned_update(r, |v| v.extend(other.iter().cloned()))
    });
    m.insert("Array#+", |i, r, a| {
        let other = match arr(i, a.arg(0)) {
            Ok(o) => o.clone(),
            Err(e) => return Err((e, r)),
        };
        owned_update(r, |v| v.extend(other.iter().cloned()))
    });
    m.insert("Array#set", |i, r, a| {
        let idx = match int(i, a.arg(0), "index") {
            Ok(x) => x,
            Err(e) => return Err((e, r)),
        };
        let n = match &r {
            Value::Array(v) => v.len() as i64,
            _ => 0,
        };
        let idx = if idx < 0 { n + idx } else { idx };
        if idx < 0 || idx >= n {
            return Err((i.err_index("index out of bounds"), r));
        }
        let value = a.arg(1).clone();
        owned_update(r, |v| v[idx as usize] = value)
    });
    m.insert("Array#delete", |_, r, a| {
        let x = a.arg(0).clone();
        owned_update(r, |v| v.retain(|y| *y != x))
    });
    m.insert("Array#compact", |_, r, _| {
        owned_update(r, |v| v.retain(|x| !x.is_nil()))
    });
    m.insert("Array#reverse", |_, r, _| owned_update(r, |v| v.reverse()));
    m.insert("Hash#put", |_, r, a| {
        owned_hash_update(r, |h| {
            h.insert(a.arg(0).clone(), a.arg(1).clone());
        })
    });
    m.insert("Hash#delete", |_, r, a| {
        owned_hash_update(r, |h| {
            h.shift_remove(a.arg(0));
        })
    });
    m.insert("Set#add", |_, r, a| {
        owned_set_update(r, |s| {
            s.insert(a.arg(0).clone());
        })
    });
    m.insert("Set#delete", |_, r, a| {
        owned_set_update(r, |s| {
            s.shift_remove(a.arg(0));
        })
    });
}

fn owned_update(recv: Value, f: impl FnOnce(&mut Vec<Value>)) -> Result<Value, (Flow, Value)> {
    match recv {
        Value::Array(mut rc) => {
            f(Rc::make_mut(&mut rc));
            Ok(Value::Array(rc))
        }
        other => Err((Flow::Raise(Value::Nil), other)),
    }
}

fn owned_hash_update(
    recv: Value,
    f: impl FnOnce(&mut IndexMap<Value, Value>),
) -> Result<Value, (Flow, Value)> {
    match recv {
        Value::Hash(mut rc) => {
            f(Rc::make_mut(&mut rc));
            Ok(Value::Hash(rc))
        }
        other => Err((Flow::Raise(Value::Nil), other)),
    }
}

fn owned_set_update(
    recv: Value,
    f: impl FnOnce(&mut IndexSet<Value>),
) -> Result<Value, (Flow, Value)> {
    match recv {
        Value::Set(mut rc) => {
            f(Rc::make_mut(&mut rc));
            Ok(Value::Set(rc))
        }
        other => Err((Flow::Raise(Value::Nil), other)),
    }
}

pub fn register(m: &mut HashMap<&'static str, NativeFn>) {
    // Array
    m.insert("Array.new", array_new);
    m.insert("Array.build", array_build);
    m.insert("Array#each", array_each);
    m.insert("Array#each_index", |i, r, a| {
        let b = block(i, &a)?;
        for k in 0..arr(i, r)?.len() {
            i.call_block(&b, vec![Value::Int(k as i64)])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Array#reverse_each", |i, r, a| {
        let b = block(i, &a)?;
        for x in arr(i, r)?.iter().rev() {
            i.call_block(&b, vec![x.clone()])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Array#[]", array_index);
    m.insert("Array#[]?", |i, r, a| {
        Ok(index_opt(arr(i, r)?, int(i, a.arg(0), "index")?))
    });
    m.insert("Array#at", |i, r, a| {
        Ok(index_opt(arr(i, r)?, int(i, a.arg(0), "index")?))
    });
    m.insert("Array#fetch", |i, r, a| {
        let v = index_opt(arr(i, r)?, int(i, a.arg(0), "index")?);
        Ok(if v.is_nil() { a.arg(1).clone() } else { v })
    });
    m.insert("Array#first", array_first);
    m.insert("Array#first?", |i, r, _| {
        Ok(arr(i, r)?.first().cloned().unwrap_or(Value::Nil))
    });
    m.insert("Array#last", array_last);
    m.insert("Array#last?", |i, r, _| {
        Ok(arr(i, r)?.last().cloned().unwrap_or(Value::Nil))
    });
    m.insert("Array#size", |i, r, _| {
        Ok(Value::Int(arr(i, r)?.len() as i64))
    });
    m.insert("Array#length", |i, r, _| {
        Ok(Value::Int(arr(i, r)?.len() as i64))
    });
    m.insert("Array#empty?", |i, r, _| {
        Ok(Value::Bool(arr(i, r)?.is_empty()))
    });
    m.insert("Array#push", |i, r, a| {
        update(i, r, |v| v.push(a.arg(0).clone()))
    });
    m.insert("Array#pop", |i, r, _| {
        update(i, r, |v| {
            v.pop();
        })
    });
    m.insert("Array#shift", |i, r, _| {
        update(i, r, |v| {
            if !v.is_empty() {
                v.remove(0);
            }
        })
    });
    m.insert("Array#unshift", |i, r, a| {
        update(i, r, |v| v.insert(0, a.arg(0).clone()))
    });
    m.insert("Array#insert", array_insert);
    m.insert("Array#set", array_set);
    m.insert("Array#delete", |i, r, a| {
        let x = a.arg(0).clone();
        update(i, r, |v| v.retain(|y| *y != x))
    });
    m.insert("Array#delete_at", array_delete_at);
    m.insert("Array#concat", |i, r, a| {
        let other = arr(i, a.arg(0))?;
        update(i, r, |v| v.extend(other.iter().cloned()))
    });
    m.insert("Array#+", |i, r, a| {
        let other = arr(i, a.arg(0))?;
        update(i, r, |v| v.extend(other.iter().cloned()))
    });
    m.insert("Array#-", |i, r, a| {
        let other = arr(i, a.arg(0))?;
        update(i, r, |v| v.retain(|x| !other.contains(x)))
    });
    m.insert("Array#*", |i, r, a| {
        let n = int(i, a.arg(0), "count")?.max(0) as usize;
        let items = arr(i, r)?;
        Ok(Value::array(
            items
                .iter()
                .cloned()
                .cycle()
                .take(items.len() * n)
                .collect(),
        ))
    });
    m.insert("Array#&", |i, r, a| {
        let other = arr(i, a.arg(0))?;
        let mut seen = IndexSet::new();
        for x in arr(i, r)?.iter() {
            if other.contains(x) {
                seen.insert(x.clone());
            }
        }
        Ok(Value::array(seen.into_iter().collect()))
    });
    m.insert("Array#|", |i, r, a| {
        let mut seen: IndexSet<Value> = arr(i, r)?.iter().cloned().collect();
        seen.extend(arr(i, a.arg(0))?.iter().cloned());
        Ok(Value::array(seen.into_iter().collect()))
    });
    m.insert("Array#reverse", |i, r, _| update(i, r, |v| v.reverse()));
    m.insert("Array#rotate", array_rotate);
    m.insert("Array#index", |i, r, a| {
        Ok(arr(i, r)?
            .iter()
            .position(|x| x == a.arg(0))
            .map(|p| Value::Int(p as i64))
            .unwrap_or(Value::Nil))
    });
    m.insert("Array#rindex", |i, r, a| {
        Ok(arr(i, r)?
            .iter()
            .rposition(|x| x == a.arg(0))
            .map(|p| Value::Int(p as i64))
            .unwrap_or(Value::Nil))
    });
    m.insert("Array#include?", |i, r, a| {
        Ok(Value::Bool(arr(i, r)?.contains(a.arg(0))))
    });
    m.insert("Array#join", array_join);
    m.insert("Array#sample", |i, r, _| {
        let items = arr(i, r)?;
        Ok(if items.is_empty() {
            Value::Nil
        } else {
            items[(super::core::next_random() % items.len() as u64) as usize].clone()
        })
    });
    m.insert("Array#shuffle", array_shuffle);
    m.insert("Array#flatten", |i, r, _| {
        let mut out = Vec::new();
        flatten_into(arr(i, r)?, &mut out);
        Ok(Value::array(out))
    });
    m.insert("Array#compact", |i, r, _| {
        update(i, r, |v| v.retain(|x| !x.is_nil()))
    });
    m.insert("Array#to_a", |_, r, _| Ok(r.clone()));
    m.insert("Array#to_s", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("Array#inspect", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("Array#==", |i, r, a| {
        Ok(Value::Bool(array_eq(i, r, a.arg(0))?))
    });
    m.insert("Array#hash", super::core_hash);
    m.insert("Array#map", array_map);
    m.insert("Array#select", array_select);
    m.insert("Array#sort_pairs", array_sort_pairs);
    m.insert("Array#<=>", |i, r, a| {
        Ok(Value::Int(i.compare(r, a.arg(0))? as i64))
    });
    // Enumerable extensions
    m.insert("Enumerable#sort", enum_sort);
    m.insert("Enumerable#min", |i, r, _| enum_extreme(i, r, true));
    m.insert("Enumerable#max", |i, r, _| enum_extreme(i, r, false));
    m.insert("Enumerable#minmax", |i, r, _| {
        Ok(Value::array(vec![
            enum_extreme(i, r, true)?,
            enum_extreme(i, r, false)?,
        ]))
    });
    // Array::Builder
    m.insert("Array::Builder.new", ab_new);
    m.insert("Array::Builder#<<", |i, r, a| {
        ab(i, r)?.borrow_mut().push(a.arg(0).clone());
        Ok(r.clone())
    });
    m.insert("Array::Builder#push", |i, r, a| {
        ab(i, r)?.borrow_mut().push(a.arg(0).clone());
        Ok(r.clone())
    });
    m.insert("Array::Builder#pop", |i, r, _| {
        Ok(ab(i, r)?.borrow_mut().pop().unwrap_or(Value::Nil))
    });
    m.insert("Array::Builder#shift", |i, r, _| {
        let b = ab(i, r)?;
        let mut v = b.borrow_mut();
        Ok(if v.is_empty() {
            Value::Nil
        } else {
            v.remove(0)
        })
    });
    m.insert("Array::Builder#unshift", |i, r, a| {
        ab(i, r)?.borrow_mut().insert(0, a.arg(0).clone());
        Ok(r.clone())
    });
    m.insert("Array::Builder#insert", |i, r, a| {
        let b = ab(i, r)?;
        let idx = int(i, a.arg(0), "index")?;
        let mut v = b.borrow_mut();
        let n = v.len() as i64;
        let idx = if idx < 0 { n + idx + 1 } else { idx };
        if idx < 0 || idx > n {
            return Err(i.err_index("index out of range"));
        }
        v.insert(idx as usize, a.arg(1).clone());
        Ok(r.clone())
    });
    m.insert("Array::Builder#concat", |i, r, a| {
        let items = collect(i, a.arg(0))?;
        ab(i, r)?.borrow_mut().extend(items);
        Ok(r.clone())
    });
    m.insert("Array::Builder#[]", |i, r, a| {
        let v = index_opt(&ab(i, r)?.borrow(), int(i, a.arg(0), "index")?);
        if v.is_nil() && !ab(i, r)?.borrow().iter().any(|x| x.is_nil()) {
            return Err(i.err_index("index out of range"));
        }
        Ok(v)
    });
    m.insert("Array::Builder#[]?", |i, r, a| {
        Ok(index_opt(&ab(i, r)?.borrow(), int(i, a.arg(0), "index")?))
    });
    m.insert("Array::Builder#[]=", ab_set);
    m.insert("Array::Builder#first", |i, r, _| {
        Ok(ab(i, r)?.borrow().first().cloned().unwrap_or(Value::Nil))
    });
    m.insert("Array::Builder#last", |i, r, _| {
        Ok(ab(i, r)?.borrow().last().cloned().unwrap_or(Value::Nil))
    });
    m.insert("Array::Builder#size", |i, r, _| {
        Ok(Value::Int(ab(i, r)?.borrow().len() as i64))
    });
    m.insert("Array::Builder#length", |i, r, _| {
        Ok(Value::Int(ab(i, r)?.borrow().len() as i64))
    });
    m.insert("Array::Builder#empty?", |i, r, _| {
        Ok(Value::Bool(ab(i, r)?.borrow().is_empty()))
    });
    m.insert("Array::Builder#include?", |i, r, a| {
        Ok(Value::Bool(ab(i, r)?.borrow().contains(a.arg(0))))
    });
    m.insert("Array::Builder#delete", |i, r, a| {
        ab(i, r)?.borrow_mut().retain(|x| x != a.arg(0));
        Ok(r.clone())
    });
    m.insert("Array::Builder#delete_at", |i, r, a| {
        let b = ab(i, r)?;
        let idx = int(i, a.arg(0), "index")?;
        let mut v = b.borrow_mut();
        let n = v.len() as i64;
        let idx = if idx < 0 { n + idx } else { idx };
        Ok(if idx < 0 || idx >= n {
            Value::Nil
        } else {
            v.remove(idx as usize)
        })
    });
    m.insert("Array::Builder#clear", |i, r, _| {
        ab(i, r)?.borrow_mut().clear();
        Ok(r.clone())
    });
    m.insert("Array::Builder#reverse!", |i, r, _| {
        ab(i, r)?.borrow_mut().reverse();
        Ok(r.clone())
    });
    m.insert("Array::Builder#sort!", |i, r, _| {
        let b = ab(i, r)?;
        let mut items = std::mem::take(&mut *b.borrow_mut());
        i.sort_values(&mut items, |x, y| i.compare(x, y))?;
        *b.borrow_mut() = items;
        Ok(r.clone())
    });
    m.insert("Array::Builder#map!", |i, r, a| {
        let bl = block(i, &a)?;
        let b = ab(i, r)?;
        let items = b.borrow().clone();
        let mut out = Vec::with_capacity(items.len());
        for x in items {
            out.push(i.call_block(&bl, vec![x])?);
        }
        *b.borrow_mut() = out;
        Ok(r.clone())
    });
    m.insert("Array::Builder#select!", |i, r, a| {
        let bl = block(i, &a)?;
        let b = ab(i, r)?;
        let items = b.borrow().clone();
        let mut out = Vec::new();
        for x in items {
            if i.call_block(&bl, vec![x.clone()])?.is_truthy() {
                out.push(x);
            }
        }
        *b.borrow_mut() = out;
        Ok(r.clone())
    });
    m.insert("Array::Builder#reject!", |i, r, a| {
        let bl = block(i, &a)?;
        let b = ab(i, r)?;
        let items = b.borrow().clone();
        let mut out = Vec::new();
        for x in items {
            if !i.call_block(&bl, vec![x.clone()])?.is_truthy() {
                out.push(x);
            }
        }
        *b.borrow_mut() = out;
        Ok(r.clone())
    });
    m.insert("Array::Builder#each", |i, r, a| {
        let b = block(i, &a)?;
        let items = ab(i, r)?.borrow().clone();
        for x in items {
            i.call_block(&b, vec![x])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Array::Builder#each_with_index", |i, r, a| {
        let b = block(i, &a)?;
        let items = ab(i, r)?.borrow().clone();
        for (k, x) in items.into_iter().enumerate() {
            i.call_block(&b, vec![x, Value::Int(k as i64)])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Array::Builder#to_a", |i, r, _| {
        Ok(Value::array(std::mem::take(&mut *ab(i, r)?.borrow_mut())))
    });
    m.insert("Array::Builder#snapshot", |i, r, _| {
        Ok(Value::array(ab(i, r)?.borrow().clone()))
    });
    m.insert("Array::Builder#to_s", |i, r, _| {
        Ok(Value::string(i.inspect(r)?))
    });
    m.insert("Array::Builder#inspect", |i, r, _| {
        Ok(Value::string(i.inspect(r)?))
    });
    // Hash
    m.insert("Hash.new", |_, _, _| {
        Ok(Value::Hash(Rc::new(IndexMap::new())))
    });
    m.insert("Hash.build", hash_build);
    m.insert("Hash#each", |i, r, a| {
        let b = block(i, &a)?;
        for (k, v) in hash(i, r)?.iter() {
            i.call_block(&b, vec![Value::array(vec![k.clone(), v.clone()])])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Hash#each_pair", |i, r, a| {
        let b = block(i, &a)?;
        for (k, v) in hash(i, r)?.iter() {
            i.call_block(&b, vec![k.clone(), v.clone()])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Hash#each_key", |i, r, a| {
        let b = block(i, &a)?;
        for k in hash(i, r)?.keys() {
            i.call_block(&b, vec![k.clone()])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Hash#each_value", |i, r, a| {
        let b = block(i, &a)?;
        for v in hash(i, r)?.values() {
            i.call_block(&b, vec![v.clone()])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Hash#[]", |i, r, a| match hash(i, r)?.get(a.arg(0)) {
        Some(v) => Ok(v.clone()),
        None => Err(i.raise(
            i.exc.key_error,
            &format!("key not found: {}", i.inspect(a.arg(0))?),
        )),
    });
    m.insert("Hash#[]?", |i, r, a| {
        Ok(hash(i, r)?.get(a.arg(0)).cloned().unwrap_or(Value::Nil))
    });
    m.insert("Hash#fetch", hash_fetch);
    m.insert("Hash#dig", |i, r, a| {
        Ok(hash(i, r)?.get(a.arg(0)).cloned().unwrap_or(Value::Nil))
    });
    m.insert("Hash#key?", |i, r, a| {
        Ok(Value::Bool(hash(i, r)?.contains_key(a.arg(0))))
    });
    m.insert("Hash#has_key?", |i, r, a| {
        Ok(Value::Bool(hash(i, r)?.contains_key(a.arg(0))))
    });
    m.insert("Hash#value?", |i, r, a| {
        Ok(Value::Bool(hash(i, r)?.values().any(|v| v == a.arg(0))))
    });
    m.insert("Hash#key", |i, r, a| {
        Ok(hash(i, r)?
            .iter()
            .find(|(_, v)| *v == a.arg(0))
            .map(|(k, _)| k.clone())
            .unwrap_or(Value::Nil))
    });
    m.insert("Hash#keys", |i, r, _| {
        Ok(Value::array(hash(i, r)?.keys().cloned().collect()))
    });
    m.insert("Hash#values", |i, r, _| {
        Ok(Value::array(hash(i, r)?.values().cloned().collect()))
    });
    m.insert("Hash#size", |i, r, _| {
        Ok(Value::Int(hash(i, r)?.len() as i64))
    });
    m.insert("Hash#length", |i, r, _| {
        Ok(Value::Int(hash(i, r)?.len() as i64))
    });
    m.insert("Hash#empty?", |i, r, _| {
        Ok(Value::Bool(hash(i, r)?.is_empty()))
    });
    m.insert("Hash#put", |i, r, a| {
        hash_update(i, r, |h| {
            h.insert(a.arg(0).clone(), a.arg(1).clone());
        })
    });
    m.insert("Hash#delete", |i, r, a| {
        hash_update(i, r, |h| {
            h.shift_remove(a.arg(0));
        })
    });
    m.insert("Hash#merge", hash_merge);
    m.insert("Hash#update", hash_update_key);
    m.insert("Hash#select", |i, r, a| hash_filter(i, r, a, true));
    m.insert("Hash#reject", |i, r, a| hash_filter(i, r, a, false));
    m.insert("Hash#transform_values", |i, r, a| {
        let b = block(i, &a)?;
        let mut out = IndexMap::new();
        for (k, v) in hash(i, r)?.iter() {
            out.insert(k.clone(), i.call_block(&b, vec![v.clone()])?);
        }
        Ok(Value::Hash(Rc::new(out)))
    });
    m.insert("Hash#transform_keys", |i, r, a| {
        let b = block(i, &a)?;
        let mut out = IndexMap::new();
        for (k, v) in hash(i, r)?.iter() {
            out.insert(i.call_block(&b, vec![k.clone()])?, v.clone());
        }
        Ok(Value::Hash(Rc::new(out)))
    });
    m.insert("Hash#invert", |i, r, _| {
        Ok(Value::Hash(Rc::new(
            hash(i, r)?
                .iter()
                .map(|(k, v)| (v.clone(), k.clone()))
                .collect(),
        )))
    });
    m.insert("Hash#to_a", |i, r, _| {
        Ok(Value::array(
            hash(i, r)?
                .iter()
                .map(|(k, v)| Value::array(vec![k.clone(), v.clone()]))
                .collect(),
        ))
    });
    m.insert("Hash#to_h", |_, r, _| Ok(r.clone()));
    m.insert("Hash#to_s", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("Hash#inspect", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("Hash#==", |_, r, a| Ok(Value::Bool(r == a.arg(0))));
    m.insert("Hash#hash", super::core_hash);
    // Hash::Builder
    m.insert("Hash::Builder.new", |_, _, _| {
        Ok(Value::HashBuilder(Rc::new(RefCell::new(IndexMap::new()))))
    });
    m.insert("Hash::Builder#[]", |i, r, a| {
        match hb(i, r)?.borrow().get(a.arg(0)) {
            Some(v) => Ok(v.clone()),
            None => Err(i.raise(
                i.exc.key_error,
                &format!("key not found: {}", i.inspect(a.arg(0))?),
            )),
        }
    });
    m.insert("Hash::Builder#[]?", |i, r, a| {
        Ok(hb(i, r)?
            .borrow()
            .get(a.arg(0))
            .cloned()
            .unwrap_or(Value::Nil))
    });
    m.insert("Hash::Builder#[]=", |i, r, a| {
        hb(i, r)?
            .borrow_mut()
            .insert(a.arg(0).clone(), a.arg(1).clone());
        Ok(a.arg(1).clone())
    });
    m.insert("Hash::Builder#store", |i, r, a| {
        hb(i, r)?
            .borrow_mut()
            .insert(a.arg(0).clone(), a.arg(1).clone());
        Ok(a.arg(1).clone())
    });
    m.insert("Hash::Builder#fetch", |i, r, a| {
        Ok(hb(i, r)?
            .borrow()
            .get(a.arg(0))
            .cloned()
            .unwrap_or_else(|| a.arg(1).clone()))
    });
    m.insert("Hash::Builder#delete", |i, r, a| {
        Ok(hb(i, r)?
            .borrow_mut()
            .shift_remove(a.arg(0))
            .unwrap_or(Value::Nil))
    });
    m.insert("Hash::Builder#key?", |i, r, a| {
        Ok(Value::Bool(hb(i, r)?.borrow().contains_key(a.arg(0))))
    });
    m.insert("Hash::Builder#keys", |i, r, _| {
        Ok(Value::array(hb(i, r)?.borrow().keys().cloned().collect()))
    });
    m.insert("Hash::Builder#values", |i, r, _| {
        Ok(Value::array(hb(i, r)?.borrow().values().cloned().collect()))
    });
    m.insert("Hash::Builder#size", |i, r, _| {
        Ok(Value::Int(hb(i, r)?.borrow().len() as i64))
    });
    m.insert("Hash::Builder#empty?", |i, r, _| {
        Ok(Value::Bool(hb(i, r)?.borrow().is_empty()))
    });
    m.insert("Hash::Builder#clear", |i, r, _| {
        hb(i, r)?.borrow_mut().clear();
        Ok(r.clone())
    });
    m.insert("Hash::Builder#merge!", |i, r, a| {
        let other = hash(i, a.arg(0))?;
        hb(i, r)?
            .borrow_mut()
            .extend(other.iter().map(|(k, v)| (k.clone(), v.clone())));
        Ok(r.clone())
    });
    m.insert("Hash::Builder#each", |i, r, a| {
        let b = block(i, &a)?;
        let items: Vec<(Value, Value)> = hb(i, r)?
            .borrow()
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        for (k, v) in items {
            i.call_block(&b, vec![k, v])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Hash::Builder#to_h", |i, r, _| {
        Ok(Value::Hash(Rc::new(std::mem::take(
            &mut *hb(i, r)?.borrow_mut(),
        ))))
    });
    m.insert("Hash::Builder#snapshot", |i, r, _| {
        Ok(Value::Hash(Rc::new(hb(i, r)?.borrow().clone())))
    });
    m.insert("Hash::Builder#to_s", |i, r, _| {
        Ok(Value::string(i.inspect(r)?))
    });
    m.insert("Hash::Builder#inspect", |i, r, _| {
        Ok(Value::string(i.inspect(r)?))
    });
    // Set
    m.insert("Set.new", |_, _, _| {
        Ok(Value::Set(Rc::new(IndexSet::new())))
    });
    m.insert("Set.[]", |_, _, a| {
        Ok(Value::Set(Rc::new(a.pos.into_iter().collect())))
    });
    m.insert("Set.build", set_build);
    m.insert("Set#each", |i, r, a| {
        let b = block(i, &a)?;
        for x in set(i, r)?.iter() {
            i.call_block(&b, vec![x.clone()])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Set#add", |i, r, a| {
        set_update(i, r, |s| {
            s.insert(a.arg(0).clone());
        })
    });
    m.insert("Set#delete", |i, r, a| {
        set_update(i, r, |s| {
            s.shift_remove(a.arg(0));
        })
    });
    m.insert("Set#include?", |i, r, a| {
        Ok(Value::Bool(set(i, r)?.contains(a.arg(0))))
    });
    m.insert("Set#size", |i, r, _| {
        Ok(Value::Int(set(i, r)?.len() as i64))
    });
    m.insert("Set#length", |i, r, _| {
        Ok(Value::Int(set(i, r)?.len() as i64))
    });
    m.insert("Set#empty?", |i, r, _| {
        Ok(Value::Bool(set(i, r)?.is_empty()))
    });
    m.insert("Set#|", |i, r, a| {
        let other = set(i, a.arg(0))?;
        set_update(i, r, |s| s.extend(other.iter().cloned()))
    });
    m.insert("Set#&", |i, r, a| {
        let other = set(i, a.arg(0))?;
        set_update(i, r, |s| s.retain(|x| other.contains(x)))
    });
    m.insert("Set#-", |i, r, a| {
        let other = set(i, a.arg(0))?;
        set_update(i, r, |s| s.retain(|x| !other.contains(x)))
    });
    m.insert("Set#^", |i, r, a| {
        let other = set(i, a.arg(0))?;
        let mine = set(i, r)?;
        let out: IndexSet<Value> = mine
            .iter()
            .filter(|x| !other.contains(*x))
            .chain(other.iter().filter(|x| !mine.contains(*x)))
            .cloned()
            .collect();
        Ok(Value::Set(Rc::new(out)))
    });
    m.insert("Set#subset?", |i, r, a| {
        let other = set(i, a.arg(0))?;
        Ok(Value::Bool(set(i, r)?.iter().all(|x| other.contains(x))))
    });
    m.insert("Set#superset?", |i, r, a| {
        let other = set(i, a.arg(0))?;
        let mine = set(i, r)?;
        Ok(Value::Bool(other.iter().all(|x| mine.contains(x))))
    });
    m.insert("Set#to_a", |i, r, _| {
        Ok(Value::array(set(i, r)?.iter().cloned().collect()))
    });
    m.insert("Set#to_s", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("Set#inspect", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("Set#==", |_, r, a| Ok(Value::Bool(r == a.arg(0))));
    m.insert("Set#hash", super::core_hash);
    // Set::Builder
    m.insert("Set::Builder.new", |_, _, _| {
        Ok(Value::SetBuilder(Rc::new(RefCell::new(IndexSet::new()))))
    });
    m.insert("Set::Builder#<<", |i, r, a| {
        sb(i, r)?.borrow_mut().insert(a.arg(0).clone());
        Ok(r.clone())
    });
    m.insert("Set::Builder#add", |i, r, a| {
        sb(i, r)?.borrow_mut().insert(a.arg(0).clone());
        Ok(r.clone())
    });
    m.insert("Set::Builder#delete", |i, r, a| {
        sb(i, r)?.borrow_mut().shift_remove(a.arg(0));
        Ok(r.clone())
    });
    m.insert("Set::Builder#include?", |i, r, a| {
        Ok(Value::Bool(sb(i, r)?.borrow().contains(a.arg(0))))
    });
    m.insert("Set::Builder#size", |i, r, _| {
        Ok(Value::Int(sb(i, r)?.borrow().len() as i64))
    });
    m.insert("Set::Builder#empty?", |i, r, _| {
        Ok(Value::Bool(sb(i, r)?.borrow().is_empty()))
    });
    m.insert("Set::Builder#each", |i, r, a| {
        let b = block(i, &a)?;
        let items: Vec<Value> = sb(i, r)?.borrow().iter().cloned().collect();
        for x in items {
            i.call_block(&b, vec![x])?;
        }
        Ok(Value::Nil)
    });
    m.insert("Set::Builder#to_set", |i, r, _| {
        Ok(Value::Set(Rc::new(std::mem::take(
            &mut *sb(i, r)?.borrow_mut(),
        ))))
    });
    m.insert("Set::Builder#to_a", |i, r, _| {
        Ok(Value::array(sb(i, r)?.borrow().iter().cloned().collect()))
    });
    m.insert("Set::Builder#to_s", |i, r, _| {
        Ok(Value::string(i.inspect(r)?))
    });
    m.insert("Set::Builder#inspect", |i, r, _| {
        Ok(Value::string(i.inspect(r)?))
    });
    // Range
    m.insert("Range#each", range_each);
    m.insert("Range#begin", |i, r, _| Ok(range(i, r)?.lo.clone()));
    m.insert("Range#end", |i, r, _| Ok(range(i, r)?.hi.clone()));
    m.insert("Range#first", |i, r, _| Ok(range(i, r)?.lo.clone()));
    m.insert("Range#last", |i, r, _| {
        let rg = range(i, r)?;
        Ok(if rg.exclusive {
            match &rg.hi {
                Value::Int(h) => Value::Int(h - 1),
                other => other.clone(),
            }
        } else {
            rg.hi.clone()
        })
    });
    m.insert("Range#exclude_end?", |i, r, _| {
        Ok(Value::Bool(range(i, r)?.exclusive))
    });
    m.insert("Range#include?", |i, r, a| {
        Ok(Value::Bool(i.range_covers(range(i, r)?, a.arg(0))?))
    });
    m.insert("Range#cover?", |i, r, a| {
        Ok(Value::Bool(i.range_covers(range(i, r)?, a.arg(0))?))
    });
    m.insert("Range#size", |i, r, _| {
        Ok(Value::Int(range_to_vec(i, range(i, r)?)?.len() as i64))
    });
    m.insert("Range#step", range_step);
    m.insert("Range#to_a", |i, r, _| {
        Ok(Value::array(range_to_vec(i, range(i, r)?)?))
    });
    m.insert("Range#to_s", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("Range#inspect", |i, r, _| Ok(Value::string(i.inspect(r)?)));
    m.insert("Range#==", |_, r, a| Ok(Value::Bool(r == a.arg(0))));
    m.insert("Range#hash", super::core_hash);
    // Enumerator
    m.insert("Enumerator#each", enumerator_each);
    m.insert("Enumerator#next", enumerator_next);
    m.insert("Enumerator#size", |i, r, _| {
        Ok(Value::Int(collect(i, r)?.len() as i64))
    });
    m.insert("Enumerator#with_index", |i, r, a| {
        let b = block(i, &a)?;
        for (k, x) in collect(i, r)?.into_iter().enumerate() {
            i.call_block(&b, vec![x, Value::Int(k as i64)])?;
        }
        Ok(Value::Nil)
    });
}

// ----- helpers ---------------------------------------------------------------------

fn arr<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<Vec<Value>>, Flow> {
    match v {
        Value::Array(a) => Ok(a),
        _ => Err(interp.err_type(&format!("expected an Array, got {}", interp.class_name(v)))),
    }
}

fn ab<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RefCell<Vec<Value>>>, Flow> {
    match v {
        Value::ArrayBuilder(a) => Ok(a),
        _ => Err(interp.err_type("expected an Array::Builder")),
    }
}

fn hash<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<IndexMap<Value, Value>>, Flow> {
    match v {
        Value::Hash(h) => Ok(h),
        _ => Err(interp.err_type(&format!("expected a Hash, got {}", interp.class_name(v)))),
    }
}

fn hb<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RefCell<IndexMap<Value, Value>>>, Flow> {
    match v {
        Value::HashBuilder(h) => Ok(h),
        _ => Err(interp.err_type("expected a Hash::Builder")),
    }
}

fn set<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<IndexSet<Value>>, Flow> {
    match v {
        Value::Set(s) => Ok(s),
        _ => Err(interp.err_type(&format!("expected a Set, got {}", interp.class_name(v)))),
    }
}

fn sb<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RefCell<IndexSet<Value>>>, Flow> {
    match v {
        Value::SetBuilder(s) => Ok(s),
        _ => Err(interp.err_type("expected a Set::Builder")),
    }
}

fn range<'a>(interp: &Interp, v: &'a Value) -> Result<&'a Rc<RangeVal>, Flow> {
    match v {
        Value::Range(r) => Ok(r),
        _ => Err(interp.err_type("expected a Range")),
    }
}

/// Produce a new array by modifying a copy (in place when unique).
fn update(interp: &Interp, recv: &Value, f: impl FnOnce(&mut Vec<Value>)) -> EvalResult {
    let mut rc = arr(interp, recv)?.clone();
    // `recv` holds one reference, `rc` another; `make_mut` copies when a
    // third party holds the array.
    f(Rc::make_mut(&mut rc));
    Ok(Value::Array(rc))
}

fn hash_update(
    interp: &Interp,
    recv: &Value,
    f: impl FnOnce(&mut IndexMap<Value, Value>),
) -> EvalResult {
    let mut rc = hash(interp, recv)?.clone();
    f(Rc::make_mut(&mut rc));
    Ok(Value::Hash(rc))
}

fn set_update(interp: &Interp, recv: &Value, f: impl FnOnce(&mut IndexSet<Value>)) -> EvalResult {
    let mut rc = set(interp, recv)?.clone();
    f(Rc::make_mut(&mut rc));
    Ok(Value::Set(rc))
}

fn index_opt(items: &[Value], i: i64) -> Value {
    let n = items.len() as i64;
    let i = if i < 0 { n + i } else { i };
    if i < 0 || i >= n {
        Value::Nil
    } else {
        items[i as usize].clone()
    }
}

fn flatten_into(items: &[Value], out: &mut Vec<Value>) {
    for x in items {
        match x {
            Value::Array(a) => flatten_into(a, out),
            other => out.push(other.clone()),
        }
    }
}

fn array_eq(interp: &Interp, a: &Value, b: &Value) -> Result<bool, Flow> {
    let (Value::Array(x), Value::Array(y)) = (a, b) else {
        return Ok(false);
    };
    if x.len() != y.len() {
        return Ok(false);
    }
    for (p, q) in x.iter().zip(y.iter()) {
        if !interp.values_equal(p, q)? {
            return Ok(false);
        }
    }
    Ok(true)
}

// ----- Array -------------------------------------------------------------------------

fn array_new(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    match (args.pos.first(), &args.block) {
        (None, _) => Ok(Value::array(vec![])),
        (Some(n), Some(b)) => {
            let n = int(interp, n, "size")?.max(0);
            let mut out = Vec::with_capacity(n as usize);
            for i in 0..n {
                out.push(interp.call_block(b, vec![Value::Int(i)])?);
            }
            Ok(Value::array(out))
        }
        (Some(_), None) => Err(interp.err_arg("Array.new(size) needs a block")),
    }
}

fn array_build(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let builder = Rc::new(RefCell::new(Vec::new()));
    interp.call_block(&b, vec![Value::ArrayBuilder(builder.clone())])?;
    let items = std::mem::take(&mut *builder.borrow_mut());
    Ok(Value::array(items))
}

fn array_each(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let items = arr(interp, recv)?.clone();
    for x in items.iter() {
        interp.call_block(&b, vec![x.clone()])?;
    }
    Ok(Value::Nil)
}

fn array_index(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let items = arr(interp, recv)?;
    match args.arg(0) {
        Value::Int(i) => {
            let n = items.len() as i64;
            let idx = if *i < 0 { n + i } else { *i };
            if idx < 0 || idx >= n {
                return Err(interp.err_index(&format!("index {i} out of bounds (size {n})")));
            }
            Ok(items[idx as usize].clone())
        }
        Value::Range(r) => match super::string::range_bounds(interp, r, items.len())? {
            Some((st, en)) => Ok(Value::array(items[st..en].to_vec())),
            None => Err(interp.err_index("range out of bounds")),
        },
        other => Err(interp.err_type(&format!(
            "Array#[] takes an Int or Range, got {}",
            interp.class_name(other)
        ))),
    }
}

fn array_first(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let items = arr(interp, recv)?;
    match args.pos.first() {
        None => Ok(items.first().cloned().unwrap_or(Value::Nil)),
        Some(n) => {
            let n = int(interp, n, "count")?.max(0) as usize;
            Ok(Value::array(items.iter().take(n).cloned().collect()))
        }
    }
}

fn array_last(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let items = arr(interp, recv)?;
    match args.pos.first() {
        None => Ok(items.last().cloned().unwrap_or(Value::Nil)),
        Some(n) => {
            let n = int(interp, n, "count")?.max(0) as usize;
            let start = items.len().saturating_sub(n);
            Ok(Value::array(items[start..].to_vec()))
        }
    }
}

fn array_insert(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let idx = int(interp, args.arg(0), "index")?;
    let value = args.arg(1).clone();
    let n = arr(interp, recv)?.len() as i64;
    let idx = if idx < 0 { n + idx + 1 } else { idx };
    if idx < 0 || idx > n {
        return Err(interp.err_index("index out of bounds"));
    }
    update(interp, recv, |v| v.insert(idx as usize, value))
}

fn array_set(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let idx = int(interp, args.arg(0), "index")?;
    let value = args.arg(1).clone();
    let n = arr(interp, recv)?.len() as i64;
    let idx = if idx < 0 { n + idx } else { idx };
    if idx < 0 || idx >= n {
        return Err(interp.err_index("index out of bounds"));
    }
    update(interp, recv, |v| v[idx as usize] = value)
}

fn array_delete_at(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let idx = int(interp, args.arg(0), "index")?;
    let n = arr(interp, recv)?.len() as i64;
    let idx = if idx < 0 { n + idx } else { idx };
    if idx < 0 || idx >= n {
        return Ok(recv.clone());
    }
    update(interp, recv, |v| {
        v.remove(idx as usize);
    })
}

fn array_rotate(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let n = match args.pos.first() {
        Some(v) => int(interp, v, "count")?,
        None => 1,
    };
    update(interp, recv, |v| {
        if !v.is_empty() {
            let len = v.len() as i64;
            let k = ((n % len) + len) % len;
            v.rotate_left(k as usize);
        }
    })
}

fn array_join(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let sep = match args.pos.first() {
        Some(s) => string(interp, s, "separator")?.to_string(),
        None => String::new(),
    };
    let mut parts = Vec::new();
    for x in arr(interp, recv)?.iter() {
        parts.push(interp.to_s(x)?.to_string());
    }
    Ok(Value::string(parts.join(&sep)))
}

fn array_shuffle(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    update(interp, recv, |v| {
        for i in (1..v.len()).rev() {
            let j = (super::core::next_random() % (i as u64 + 1)) as usize;
            v.swap(i, j);
        }
    })
}

fn array_map(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let items = arr(interp, recv)?.clone();
    let mut out = Vec::with_capacity(items.len());
    for x in items.iter() {
        out.push(interp.call_block(&b, vec![x.clone()])?);
    }
    Ok(Value::array(out))
}

fn array_select(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let items = arr(interp, recv)?.clone();
    let mut out = Vec::new();
    for x in items.iter() {
        if interp.call_block(&b, vec![x.clone()])?.is_truthy() {
            out.push(x.clone());
        }
    }
    Ok(Value::array(out))
}

/// Sort an array of `[key, value]` pairs by key (for `sort_by`).
fn array_sort_pairs(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let mut items: Vec<Value> = arr(interp, recv)?.iter().cloned().collect();
    interp.sort_values(&mut items, |a, b| {
        let ka = match a {
            Value::Array(p) => p.first().cloned().unwrap_or(Value::Nil),
            _ => Value::Nil,
        };
        let kb = match b {
            Value::Array(p) => p.first().cloned().unwrap_or(Value::Nil),
            _ => Value::Nil,
        };
        interp.compare(&ka, &kb)
    })?;
    Ok(Value::array(items))
}

fn enum_sort(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let mut items = collect(interp, recv)?;
    interp.sort_values(&mut items, |a, b| interp.compare(a, b))?;
    Ok(Value::array(items))
}

fn enum_extreme(interp: &Interp, recv: &Value, min: bool) -> EvalResult {
    let items = collect(interp, recv)?;
    let mut best: Option<Value> = None;
    for x in items {
        best = Some(match best {
            None => x,
            Some(b) => {
                let o = interp.compare(&x, &b)?;
                if (min && o.is_lt()) || (!min && o.is_gt()) {
                    x
                } else {
                    b
                }
            }
        });
    }
    Ok(best.unwrap_or(Value::Nil))
}

// ----- Array::Builder -------------------------------------------------------------------

fn ab_new(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let items = match args.pos.first() {
        None => Vec::new(),
        Some(n) => {
            let n = int(interp, n, "size")?.max(0) as usize;
            vec![args.arg(1).clone(); n]
        }
    };
    Ok(Value::ArrayBuilder(Rc::new(RefCell::new(items))))
}

fn ab_set(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let b = ab(interp, recv)?;
    let idx = int(interp, args.arg(0), "index")?;
    let mut v = b.borrow_mut();
    let n = v.len() as i64;
    let idx = if idx < 0 { n + idx } else { idx };
    if idx < 0 {
        return Err(interp.err_index("index out of bounds"));
    }
    let idx = idx as usize;
    if idx >= v.len() {
        v.resize(idx + 1, Value::Nil);
    }
    v[idx] = args.arg(1).clone();
    Ok(args.arg(1).clone())
}

// ----- Hash ------------------------------------------------------------------------------

fn hash_build(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let builder = Rc::new(RefCell::new(IndexMap::new()));
    interp.call_block(&b, vec![Value::HashBuilder(builder.clone())])?;
    let map = std::mem::take(&mut *builder.borrow_mut());
    Ok(Value::Hash(Rc::new(map)))
}

fn hash_fetch(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let h = hash(interp, recv)?;
    if let Some(v) = h.get(args.arg(0)) {
        return Ok(v.clone());
    }
    match (&args.block, args.pos.get(1)) {
        (Some(b), _) => interp.call_block(b, vec![args.arg(0).clone()]),
        (None, Some(d)) => Ok(d.clone()),
        (None, None) => Err(interp.raise(
            interp.exc.key_error,
            &format!("key not found: {}", interp.inspect(args.arg(0))?),
        )),
    }
}

fn hash_merge(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let other = hash(interp, args.arg(0))?.clone();
    let mut rc = hash(interp, recv)?.clone();
    let block = args.block.clone();
    let map = Rc::make_mut(&mut rc);
    for (k, v) in other.iter() {
        let merged = match (map.get(k), &block) {
            (Some(existing), Some(b)) => {
                interp.call_block(b, vec![k.clone(), existing.clone(), v.clone()])?
            }
            _ => v.clone(),
        };
        map.insert(k.clone(), merged);
    }
    Ok(Value::Hash(rc))
}

fn hash_update_key(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let key = args.arg(0).clone();
    let current = hash(interp, recv)?.get(&key).cloned().unwrap_or(Value::Nil);
    let new = interp.call_block(&b, vec![current])?;
    hash_update(interp, recv, |h| {
        h.insert(key, new);
    })
}

fn hash_filter(interp: &Interp, recv: &Value, args: Args, keep: bool) -> EvalResult {
    let b = block(interp, &args)?;
    let mut out = IndexMap::new();
    for (k, v) in hash(interp, recv)?.iter() {
        if interp
            .call_block(&b, vec![k.clone(), v.clone()])?
            .is_truthy()
            == keep
        {
            out.insert(k.clone(), v.clone());
        }
    }
    Ok(Value::Hash(Rc::new(out)))
}

fn set_build(interp: &Interp, _: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let builder = Rc::new(RefCell::new(IndexSet::new()));
    interp.call_block(&b, vec![Value::SetBuilder(builder.clone())])?;
    let s = std::mem::take(&mut *builder.borrow_mut());
    Ok(Value::Set(Rc::new(s)))
}

// ----- Range -------------------------------------------------------------------------------

pub fn range_to_vec(interp: &Interp, r: &RangeVal) -> Result<Vec<Value>, Flow> {
    match (&r.lo, &r.hi) {
        (Value::Int(lo), Value::Int(hi)) => {
            let end = if r.exclusive { *hi } else { hi + 1 };
            Ok((*lo..end).map(Value::Int).collect())
        }
        (Value::Str(lo), Value::Str(hi)) => {
            let mut out = Vec::new();
            let mut cur = Value::Str(lo.clone());
            let mut guard = 0;
            while let Value::Str(s) = &cur {
                if s.len() > hi.len() {
                    break;
                }
                if s == hi {
                    if !r.exclusive {
                        out.push(cur.clone());
                    }
                    break;
                }
                out.push(cur.clone());
                cur = interp.send(&cur, "succ", vec![], None)?;
                guard += 1;
                if guard > 1_000_000 {
                    break;
                }
            }
            Ok(out)
        }
        _ => Err(interp.err_type("cannot iterate over an endless or non-integer range")),
    }
}

fn range_each(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let b = block(interp, &args)?;
    let r = range(interp, recv)?;
    match (&r.lo, &r.hi) {
        (Value::Int(lo), Value::Int(hi)) => {
            let end = if r.exclusive { *hi } else { hi + 1 };
            let mut i = *lo;
            while i < end {
                interp.call_block(&b, vec![Value::Int(i)])?;
                i += 1;
            }
        }
        (Value::Int(lo), Value::Nil) => {
            let mut i = *lo;
            loop {
                interp.call_block(&b, vec![Value::Int(i)])?;
                i += 1;
            }
        }
        (Value::Int(lo), Value::Float(f)) if f.is_infinite() && *f > 0.0 => {
            let mut i = *lo;
            loop {
                interp.call_block(&b, vec![Value::Int(i)])?;
                i += 1;
            }
        }
        _ => {
            for v in range_to_vec(interp, r)? {
                interp.call_block(&b, vec![v])?;
            }
        }
    }
    Ok(Value::Nil)
}

fn range_step(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let step = int(interp, args.arg(0), "step")?;
    if step <= 0 {
        return Err(interp.err_arg("step must be positive"));
    }
    let b = block(interp, &args)?;
    let r = range(interp, recv)?;
    let (Value::Int(lo), Value::Int(hi)) = (&r.lo, &r.hi) else {
        return Err(interp.err_type("step needs an integer range"));
    };
    let end = if r.exclusive { *hi } else { hi + 1 };
    let mut i = *lo;
    while i < end {
        interp.call_block(&b, vec![Value::Int(i)])?;
        i += step;
    }
    Ok(Value::Nil)
}

// ----- Enumerator ----------------------------------------------------------------------------

fn enumerator_each(interp: &Interp, recv: &Value, args: Args) -> EvalResult {
    let Value::Enumerator(e) = recv else {
        return Err(interp.err_type("expected an Enumerator"));
    };
    let b = block(interp, &args)?;
    interp.send(&e.recv, &e.method, e.args.clone(), Some(b))
}

fn enumerator_next(interp: &Interp, recv: &Value, _: Args) -> EvalResult {
    let Value::Enumerator(e) = recv else {
        return Err(interp.err_type("expected an Enumerator"));
    };
    if e.buffer.borrow().is_none() {
        let items = collect(interp, recv)?;
        *e.buffer.borrow_mut() = Some(items);
    }
    let pos = e.position.get();
    let buffer = e.buffer.borrow();
    let items = buffer.as_ref().unwrap();
    if pos >= items.len() {
        return Err(interp.raise(interp.exc.stop_iteration, "iteration reached an end"));
    }
    e.position.set(pos + 1);
    Ok(items[pos].clone())
}
