//! Keys of hashes and members of sets compare by their own `==` and
//! `hash` (docs/03-data-model.md §6): a class that defines either has its
//! instances compared and hashed by calling it, through this thread's
//! interpreter, from inside `Value`'s `Eq` and `Hash`, which the tables
//! use. Built-in values, `data` types and enums without a `==` or `hash`
//! of their own, and other classes' instances (by identity) are compared
//! in Rust as before; an exception compares by its identity, the same in
//! its copies (`Exception#==`), also in Rust.
//!
//! What the methods raise cannot leave `Eq` or `Hash`: the first error is
//! kept, the methods are not called again until it is taken (a hash of 0,
//! unequal), and the native or the operation that used the table raises
//! it when it returns (`pending`, checked by the natives' wrappers). An
//! operation that changes a table in place looks the key up first, and
//! raises before changing anything when that failed.

use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicBool, Ordering};

use smallvec::smallvec;

use crate::interp::{Flow, Interp};
use crate::rc::Rc;
use crate::value::{Object, Value};
use quarz_ir::{ClassId, MethodId};

/// A class's own `==` and `hash`, either of which makes its instances
/// compared by calling them.
#[derive(Clone, Copy, Debug, Default)]
pub struct KeyMethods {
    pub eq: Option<MethodId>,
    pub hash: Option<MethodId>,
}

/// Whether a program of this process has such a class: otherwise, a
/// native's return costs this one load.
static ANY: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// Per class id, set by this thread's interpreter.
    static TABLE: RefCell<Vec<Option<KeyMethods>>> = const { RefCell::new(Vec::new()) };
    static INTERP: RefCell<std::rc::Weak<Interp>> = const { RefCell::new(std::rc::Weak::new()) };
    /// What a method raised, until the operation that called it raises it.
    static ERROR: RefCell<Option<Flow>> = const { RefCell::new(None) };
    static HAS_ERROR: Cell<bool> = const { Cell::new(false) };
}

/// Make `interp` this thread's, with `table` its classes' methods.
pub fn set(interp: &std::rc::Rc<Interp>, table: Vec<Option<KeyMethods>>) {
    if table.iter().any(Option::is_some) {
        ANY.store(true, Ordering::Relaxed);
    }
    TABLE.with(|t| *t.borrow_mut() = table);
    INTERP.with(|i| *i.borrow_mut() = std::rc::Rc::downgrade(interp));
}

/// The methods an instance of `class` is compared and hashed by, if any.
#[inline]
pub fn of(class: ClassId) -> Option<KeyMethods> {
    if !ANY.load(Ordering::Relaxed) {
        return None;
    }
    TABLE
        .try_with(|t| {
            t.try_borrow()
                .ok()
                .and_then(|t| t.get(class as usize).copied().flatten())
        })
        .ok()
        .flatten()
}

/// Whether a method called for a key raised, not yet raised again.
#[inline(always)]
pub fn pending() -> bool {
    ANY.load(Ordering::Relaxed) && HAS_ERROR.try_with(|h| h.get()).unwrap_or(false)
}

/// The error a method called for a key raised, if any.
pub fn take_error() -> Option<Flow> {
    if !pending() {
        return None;
    }
    HAS_ERROR.with(|h| h.set(false));
    ERROR.with(|e| e.borrow_mut().take())
}

/// `Err` with the pending error, if any (for an operation to raise it).
#[inline]
pub fn check() -> Result<(), Flow> {
    match take_error() {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

fn keep(e: Flow) {
    let _ = ERROR.try_with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.is_none() {
            *slot = Some(e);
        }
    });
    let _ = HAS_ERROR.try_with(|h| h.set(true));
}

fn interp() -> Option<std::rc::Rc<Interp>> {
    INTERP.try_with(|i| i.borrow().upgrade()).ok().flatten()
}

/// `o.hash` by its own method, or `None` after an error (kept).
#[cold]
#[inline(never)]
pub fn hash(o: &Rc<Object>, mid: MethodId) -> Option<i64> {
    if pending() {
        return None;
    }
    let interp = interp()?;
    match interp.invoke(mid, Value::Object(o.clone()), smallvec![], Vec::new(), None) {
        Ok(Value::Int(n)) => Some(n),
        Ok(other) => {
            // The checker holds `hash` to `-> Int`; a value of another type
            // is an internal error.
            keep(interp.err_type(&format!(
                "internal error: hash returned {}",
                interp.class_name(&other)
            )));
            None
        }
        Err(e) => {
            keep(e);
            None
        }
    }
}

/// `a == b` by `a`'s own method (unequal after an error, kept).
#[cold]
#[inline(never)]
pub fn eq(a: &Rc<Object>, b: &Value, mid: MethodId) -> bool {
    if pending() {
        return false;
    }
    let Some(interp) = interp() else {
        return false;
    };
    match interp.invoke(
        mid,
        Value::Object(a.clone()),
        smallvec![b.clone()],
        Vec::new(),
        None,
    ) {
        Ok(v) => v.is_truthy(),
        Err(e) => {
            keep(e);
            false
        }
    }
}

/// Whether comparing or hashing `v` may run Quarz code: an instance of a
/// class with its own `==` or `hash`, or a value holding one (an array's
/// elements, a `data` value's fields, a range's bounds, a hash's or set's
/// entries are compared in turn). An operation changing a table in place
/// looks such a key up first (`probe`), and the fast paths that promise
/// to run no Quarz code leave it to the natives.
pub fn is_custom(v: &Value) -> bool {
    if !ANY.load(Ordering::Relaxed) {
        return false;
    }
    reaches(v, 0)
}

fn reaches(v: &Value, depth: u32) -> bool {
    // Deep values are taken to reach one (cheaper than the walk).
    if depth > 16 {
        return true;
    }
    match v {
        Value::Object(o) => {
            of(o.class).is_some()
                || (crate::value::is_structural(o)
                    && o.fields().iter().any(|f| reaches(f, depth + 1)))
        }
        Value::Array(a) => a.iter().any(|x| reaches(&x, depth + 1)),
        Value::Range(r) => reaches(&r.lo, depth + 1) || reaches(&r.hi, depth + 1),
        Value::Hash(h) => h
            .as_map()
            .iter()
            .any(|(k, x)| reaches(k, depth + 1) || reaches(x, depth + 1)),
        Value::Set(s) => s.iter().any(|x| reaches(x, depth + 1)),
        _ => false,
    }
}

/// A table's map, by which `find` and `place` look keys up.
pub type Table<V> = indexmap::IndexMap<Value, V, rustc_hash::FxBuildHasher>;

/// The hash a table gives `key`, its own `hash` called once, or the error
/// that raised.
pub fn table_hash(key: &Value) -> Result<u64, Flow> {
    use std::hash::BuildHasher;
    let h = rustc_hash::FxBuildHasher.hash_one(key);
    check()?;
    Ok(h)
}

/// Where `key`, hashed `h` (`table_hash`), is in `map`: the candidates
/// with that hash compared by `key == candidate` (its own `==` the only
/// Quarz code that runs), or the error it raised. `map` is only read.
pub fn find<V>(map: &Table<V>, h: u64, key: &Value) -> Result<Option<usize>, Flow> {
    use indexmap::map::RawEntryApiV1;
    let found = map
        .raw_entry_v1()
        .from_hash_full(h, |k| key == k)
        .map(|(i, _, _)| i);
    check()?;
    Ok(found)
}

/// Give `key`, hashed `h` and found at `at` by `find`, the value `value`
/// in `map`: the entry there keeps its key, or a new one goes last. No
/// key is hashed or compared: no Quarz code runs. The old value, if any.
pub fn place<V>(map: &mut Table<V>, h: u64, at: Option<usize>, key: Value, value: V) -> Option<V> {
    use indexmap::map::raw_entry_v1::RawEntryMut;
    use indexmap::map::RawEntryApiV1;
    if let Some(i) = at {
        return map
            .get_index_mut(i)
            .map(|(_, v)| std::mem::replace(v, value));
    }
    // A lookup that matches nothing: a vacant entry, no comparison made.
    match map.raw_entry_mut_v1().from_hash(h, |_| false) {
        RawEntryMut::Vacant(e) => {
            e.insert_hashed_nocheck(h, key, value);
        }
        RawEntryMut::Occupied(_) => unreachable!("nothing matches"),
    }
    None
}
