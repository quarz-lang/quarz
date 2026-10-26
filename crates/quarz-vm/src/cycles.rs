//! The cycle collector: reclaims what reference counting cannot, values
//! that refer to one another and to which nothing else refers
//! (docs/05-execution.md §5).
//!
//! A value made later can only refer to values older than itself, so
//! immutable values alone never form a cycle: every cycle goes through a
//! value written after it was made, an object's field (`var`, or one
//! `initialize` assigned once `self` was in use), a heap frame's slot (a
//! captured variable) or a builder's contents. Those are the
//! *candidates*: each is listed when it is made (an object only when its
//! class has a field that may lead back to it), in a list of this
//! thread's, by address and with no count of its own, and leaves the list
//! when it is freed or shared (`Rc::mark_shared`; a shared value never
//! refers to a local one, so it is in no cycle with one). Its place in
//! the list is kept in its allocation's second word, which a local
//! allocation does not otherwise use (`crate::rc`).
//!
//! Every so many candidates made, the collector looks at the graph of
//! local values reachable from the candidates (CPython's algorithm): a
//! value whose count is more than the references to it from within the
//! graph is referred to from elsewhere (a register, a frame of the
//! interpreter, a native holding it), and so is everything it reaches;
//! the rest is garbage. Compiled code updates counts inline and holds no
//! reference without a count beyond what a counted one keeps alive (a
//! borrowed array element), so the collector needs nothing from it, and
//! it runs whenever a candidate is made, a point where every value in use
//! is counted. What the collector cannot look into (a builder borrowed
//! at that moment) counts as referred to from elsewhere.
//!
//! Garbage is freed by emptying the candidates among it (fields set to
//! nil, slots to nil, contents taken), which leaves no cycle, and letting
//! the counts do the rest. An object whose class defines `deinitialize`
//! is not freed so: it is queued as a released one is (`crate::deinit`),
//! intact, and what it reaches is kept for the next collection, which
//! frees it if it is still garbage once the method has run; the rest of
//! the garbage is freed now.
//!
//! A value being dropped may still be in the place that held it (a slot
//! is overwritten after its old value is dropped), with what it held
//! freed already: no collection starts while one is, which only the
//! rebuild of an object for its `deinitialize` would do (`quietly`).

use std::cell::{Cell, RefCell};

use crate::rc::{counts_at, Rc};
use crate::value::{
    ArrayData, Closure, ClosureBody, EnumeratorVal, Frame, HashData, Object, RangeVal, Value,
    ValueMap, ValueSet,
};

/// What an allocation in the graph holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum Kind {
    Object,
    Frame,
    Closure,
    Array,
    Hash,
    Set,
    Range,
    ArrayBuilder,
    HashBuilder,
    SetBuilder,
    Enumerator,
}

/// Collect once this many candidates have been made since the last
/// collection, or twice as many as the values and references the last
/// one found live, whichever is more: the work of looking at what
/// survives is then paid for by twice as much allocation (garbage is
/// paid for by its own allocation).
const MIN_LIMIT: usize = 10_000;

struct State {
    /// The candidates: the address of each one's counts, and its kind.
    list: RefCell<Vec<(usize, Kind)>>,
    /// Candidates made since the last collection.
    made: Cell<usize>,
    /// When to collect (see `MIN_LIMIT`).
    limit: Cell<usize>,
    /// A collection is running (what it frees may make candidates), or
    /// may not start now (`quietly`).
    running: Cell<bool>,
    /// `QUARZ_NO_CYCLES=1`: never collect (decided at the first
    /// candidate).
    off: Cell<Option<bool>>,
}

thread_local! {
    static STATE: State = const {
        State {
            list: RefCell::new(Vec::new()),
            made: Cell::new(0),
            limit: Cell::new(MIN_LIMIT),
            running: Cell::new(false),
            off: Cell::new(None),
        }
    };
}

/// The second word of a candidate at place `i` of the list.
#[inline(always)]
fn mark_of(i: usize) -> usize {
    (i + 1) << 1
}

/// List the fresh allocation at `addr` as a candidate, and collect when
/// enough have been made. The caller holds the only reference, so the
/// allocation and what it holds are live to the collection.
#[inline]
pub(crate) fn register(addr: usize, kind: Kind) {
    let _ = STATE.try_with(|s| {
        let Ok(mut list) = s.list.try_borrow_mut() else {
            return;
        };
        // SAFETY: a fresh, live allocation.
        let (_, mark) = unsafe { counts_at(addr) };
        debug_assert_eq!(mark.get(), 1);
        mark.set(mark_of(list.len()));
        list.push((addr, kind));
        drop(list);
        let made = s.made.get() + 1;
        s.made.set(made);
        if made >= s.limit.get() && !s.running.get() {
            collect(s);
        }
    });
}

/// Run `f`, making no collection start meanwhile (one that is due starts
/// at the next candidate made after).
pub(crate) fn quietly<R>(f: impl FnOnce() -> R) -> R {
    let _quiet = Quiet::new();
    f()
}

/// While it lives, no collection starts; dropped (also when what it
/// guards panics), it puts back what was.
struct Quiet {
    was: bool,
}

impl Quiet {
    fn new() -> Quiet {
        Quiet {
            was: STATE.try_with(|s| s.running.replace(true)).unwrap_or(true),
        }
    }
}

impl Drop for Quiet {
    fn drop(&mut self) {
        if !self.was {
            let _ = STATE.try_with(|s| s.running.set(false));
        }
    }
}

/// Take the allocation whose second word is `mark` out of the list, if it
/// is a candidate (an even word).
#[inline(always)]
pub(crate) fn forget(mark: usize) {
    if mark & 1 == 0 {
        forget_slow(mark);
    }
}

#[inline(never)]
fn forget_slow(mark: usize) {
    let i = (mark >> 1) - 1;
    let _ = STATE.try_with(|s| {
        let mut list = s.list.borrow_mut();
        let (addr, _) = list.swap_remove(i);
        // SAFETY: a candidate is live while listed.
        unsafe { counts_at(addr).1.set(1) };
        if let Some(&(moved, _)) = list.get(i) {
            // SAFETY: as above.
            unsafe { counts_at(moved).1.set(mark_of(i)) };
        }
    });
}

/// The allocation a value refers to, when it is one the collector looks
/// into and it is local.
#[inline]
fn node_of(v: &Value) -> Option<(usize, Kind)> {
    fn local<T: ?Sized + crate::rc::Target>(rc: &Rc<T>, kind: Kind) -> Option<(usize, Kind)> {
        (!Rc::is_shared(rc)).then(|| (Rc::addr(rc), kind))
    }
    match v {
        Value::Object(o) => local(o, Kind::Object),
        Value::Proc(c) => local(c, Kind::Closure),
        Value::Array(a) => local(a, Kind::Array),
        Value::Hash(h) => local(h, Kind::Hash),
        Value::Set(s) => local(s, Kind::Set),
        Value::Range(r) => local(r, Kind::Range),
        Value::ArrayBuilder(b) => local(b, Kind::ArrayBuilder),
        Value::HashBuilder(b) => local(b, Kind::HashBuilder),
        Value::SetBuilder(b) => local(b, Kind::SetBuilder),
        Value::Enumerator(e) => local(e, Kind::Enumerator),
        _ => None,
    }
}

fn frame_node(f: &Rc<Frame>) -> Option<(usize, Kind)> {
    (!Rc::is_shared(f)).then(|| (Rc::addr(f), Kind::Frame))
}

/// Call `f` with each allocation the one at `addr` refers to, or return
/// false when it cannot be looked into now (a borrowed builder).
///
/// # Safety
/// `addr` is a live local allocation of kind `kind`.
unsafe fn children(addr: usize, kind: Kind, f: &mut impl FnMut(Option<(usize, Kind)>)) -> bool {
    // SAFETY: as the caller promises, for each kind.
    unsafe {
        match kind {
            Kind::Object => {
                Rc::<Object>::value_at(addr).value_ptrs(|p| f(node_of(&*p)));
            }
            Kind::Frame => {
                let frame = Rc::<Frame>::value_at(addr);
                for v in frame.slots() {
                    f(node_of(v));
                }
                if let Some(p) = &frame.parent {
                    f(frame_node(p));
                }
            }
            Kind::Closure => {
                let c = Rc::<Closure>::value_at(addr);
                if let Some(fr) = &c.frame {
                    f(frame_node(fr));
                }
                f(node_of(&c.self_val));
                if let Some(b) = &c.method_block {
                    f(node_of(b));
                }
                if let ClosureBody::BoundMethod { recv, .. } = &c.body {
                    f(node_of(recv));
                }
            }
            Kind::Array => match Rc::<ArrayData>::value_at(addr) {
                ArrayData::Values(xs) => xs.iter().for_each(|v| f(node_of(v))),
                ArrayData::Objects(xs) => xs
                    .iter()
                    .for_each(|o| f((!Rc::is_shared(o)).then(|| (Rc::addr(o), Kind::Object)))),
                ArrayData::Ints(_) | ArrayData::Floats(_) => {}
            },
            Kind::Hash => {
                if let HashData::Values(m) = Rc::<HashData>::value_at(addr) {
                    for (k, v) in m {
                        f(node_of(k));
                        f(node_of(v));
                    }
                }
            }
            Kind::Set => Rc::<ValueSet>::value_at(addr)
                .iter()
                .for_each(|v| f(node_of(v))),
            Kind::Range => {
                let r = Rc::<RangeVal>::value_at(addr);
                f(node_of(&r.lo));
                f(node_of(&r.hi));
            }
            Kind::ArrayBuilder => {
                let Ok(xs) = Rc::<RefCell<Vec<Value>>>::value_at(addr).try_borrow() else {
                    return false;
                };
                xs.iter().for_each(|v| f(node_of(v)));
            }
            Kind::HashBuilder => {
                let Ok(m) = Rc::<RefCell<ValueMap>>::value_at(addr).try_borrow() else {
                    return false;
                };
                for (k, v) in m.iter() {
                    f(node_of(k));
                    f(node_of(v));
                }
            }
            Kind::SetBuilder => {
                let Ok(s) = Rc::<RefCell<ValueSet>>::value_at(addr).try_borrow() else {
                    return false;
                };
                s.iter().for_each(|v| f(node_of(v)));
            }
            Kind::Enumerator => {
                let e = Rc::<EnumeratorVal>::value_at(addr);
                f(node_of(&e.recv));
                e.args.iter().for_each(|v| f(node_of(v)));
                if !e.try_each_buffered(|v| f(node_of(v))) {
                    return false;
                }
            }
        }
    }
    true
}

/// A reference to a garbage allocation, which keeps it while garbage is
/// emptied.
enum Held {
    Value(#[allow(dead_code)] Value),
    Frame(#[allow(dead_code)] Rc<Frame>),
}

/// A new reference to the allocation at `addr`.
///
/// # Safety
/// `addr` is a live local allocation of kind `kind`.
unsafe fn hold(addr: usize, kind: Kind) -> Held {
    // SAFETY: as the caller promises.
    unsafe {
        Held::Value(match kind {
            Kind::Frame => return Held::Frame(Rc::clone_at(addr)),
            Kind::Object => Value::Object(Rc::clone_at(addr)),
            Kind::Closure => Value::Proc(Rc::clone_at(addr)),
            Kind::Array => Value::Array(Rc::clone_at(addr)),
            Kind::Hash => Value::Hash(Rc::clone_at(addr)),
            Kind::Set => Value::Set(Rc::clone_at(addr)),
            Kind::Range => Value::Range(Rc::clone_at(addr)),
            Kind::ArrayBuilder => Value::ArrayBuilder(Rc::clone_at(addr)),
            Kind::HashBuilder => Value::HashBuilder(Rc::clone_at(addr)),
            Kind::SetBuilder => Value::SetBuilder(Rc::clone_at(addr)),
            Kind::Enumerator => Value::Enumerator(Rc::clone_at(addr)),
        })
    }
}

/// An allocation of the graph.
struct Node {
    addr: usize,
    kind: Kind,
    /// Its second word, which holds its place in the graph while the
    /// graph is built (see `add`).
    word: usize,
    /// Its count less the references from within the graph.
    refs: isize,
    /// Referred to from outside the graph, or reachable from what is.
    live: bool,
    /// Its edges: `edges[first..first + len]`.
    first: u32,
    len: u32,
}

/// A second word that is a node's place in the graph: odd, as 1 is, but
/// never 1 (`NODE_TAG` in the low two bits, which 1 and a candidate's
/// even mark do not have).
const NODE_TAG: usize = 3;

/// The node of the allocation at `addr`, added when new. While the graph
/// is built, a node's second word is its place (`NODE_TAG`), the word it
/// had being kept in the node and put back by `restore`: nothing else
/// reads the word meanwhile, since building the graph drops no value and
/// runs no code, and the allocation is this thread's.
fn add(addr: usize, kind: Kind, nodes: &mut Vec<Node>) -> u32 {
    // SAFETY: a candidate, or reached from one through counted
    // references: live; local, so its count is the first word.
    let (count, word) = unsafe { counts_at(addr) };
    let w = word.get();
    if w & 3 == NODE_TAG {
        return (w >> 2) as u32;
    }
    let k = nodes.len();
    word.set((k << 2) | NODE_TAG);
    nodes.push(Node {
        addr,
        kind,
        word: w,
        refs: count.get() as isize,
        live: false,
        first: 0,
        len: 0,
    });
    k as u32
}

/// Put back the second words `add` borrowed.
fn restore(nodes: &[Node]) {
    for n in nodes {
        // SAFETY: a node is live (nothing was freed since `add`).
        unsafe { counts_at(n.addr).1.set(n.word) };
    }
}

/// What a collection found among the values reachable from the
/// candidates.
struct Found {
    /// Garbage to free now.
    free: Vec<(usize, Kind)>,
    /// Garbage objects whose `deinitialize` is to run first (what they
    /// reach is not in `free`).
    finalize: Vec<usize>,
    /// The size of what is live (values and references).
    live: usize,
}

/// The garbage among the values reachable from the candidates.
fn garbage(roots: &[(usize, Kind)]) -> Found {
    // Sized for the candidates and as much again that they reach.
    let room = roots.len() * 2;
    let mut nodes: Vec<Node> = Vec::with_capacity(room);
    let mut edges: Vec<u32> = Vec::with_capacity(room);
    for &(addr, kind) in roots {
        add(addr, kind, &mut nodes);
    }
    // Each node's references within the graph, found once (the nodes
    // are visited in order, new ones appended).
    let mut found: Vec<(usize, Kind)> = Vec::new();
    let mut i = 0;
    while i < nodes.len() {
        let (addr, kind) = (nodes[i].addr, nodes[i].kind);
        let first = edges.len() as u32;
        found.clear();
        // SAFETY: a node is live and local (see `add`).
        let complete = unsafe {
            children(addr, kind, &mut |c| {
                if let Some(c) = c {
                    found.push(c);
                }
            })
        };
        if !complete {
            nodes[i].live = true;
        }
        for &(caddr, ckind) in &found {
            let j = add(caddr, ckind, &mut nodes);
            nodes[j as usize].refs -= 1;
            edges.push(j);
        }
        nodes[i].first = first;
        nodes[i].len = edges.len() as u32 - first;
        i += 1;
    }
    restore(&nodes);
    // What is referred to from outside, and what it reaches, is live.
    let mut stack: Vec<u32> = (0..nodes.len() as u32)
        .filter(|&k| nodes[k as usize].refs > 0 || nodes[k as usize].live)
        .collect();
    for &k in &stack {
        nodes[k as usize].live = true;
    }
    while let Some(k) = stack.pop() {
        let n = &nodes[k as usize];
        for e in n.first..n.first + n.len {
            let j = edges[e as usize];
            if !nodes[j as usize].live {
                nodes[j as usize].live = true;
                stack.push(j);
            }
        }
    }
    let live: usize = nodes
        .iter()
        .filter(|n| n.live)
        .map(|n| 1 + n.len as usize)
        .sum();
    // Garbage objects to finalize, and what they reach, stay for now.
    let mut finalize = Vec::new();
    for (k, n) in nodes.iter().enumerate() {
        // SAFETY: a node is live (nothing was freed meanwhile).
        if !n.live
            && n.kind == Kind::Object
            && unsafe { Rc::<Object>::value_at(n.addr) }.needs_deinitialize()
        {
            finalize.push(n.addr);
            stack.push(k as u32);
        }
    }
    let mut kept = vec![false; nodes.len()];
    for &k in &stack {
        kept[k as usize] = true;
    }
    while let Some(k) = stack.pop() {
        let n = &nodes[k as usize];
        for e in n.first..n.first + n.len {
            let j = edges[e as usize] as usize;
            if !nodes[j].live && !kept[j] {
                kept[j] = true;
                stack.push(j as u32);
            }
        }
    }
    let free = nodes
        .iter()
        .zip(&kept)
        .filter(|(n, kept)| !n.live && !**kept)
        .map(|(n, _)| (n.addr, n.kind))
        .collect();
    Found {
        free,
        finalize,
        live,
    }
}

/// Empty a garbage allocation that may close a cycle (see the module
/// comment); what it held is dropped here.
///
/// # Safety
/// `addr` is a live local allocation of kind `kind`, garbage.
unsafe fn clear(addr: usize, kind: Kind) {
    // SAFETY: as the caller promises: nothing but garbage refers to it,
    // and nothing reads it while it is emptied.
    unsafe {
        match kind {
            Kind::Object => Rc::<Object>::value_at(addr).clear_values(),
            Kind::Frame => Rc::<Frame>::value_at(addr).clear_slots(),
            Kind::ArrayBuilder => {
                if let Ok(mut xs) = Rc::<RefCell<Vec<Value>>>::value_at(addr).try_borrow_mut() {
                    let taken = std::mem::take(&mut *xs);
                    drop(xs);
                    drop(taken);
                }
            }
            Kind::HashBuilder => {
                if let Ok(mut m) = Rc::<RefCell<ValueMap>>::value_at(addr).try_borrow_mut() {
                    let taken = std::mem::take(&mut *m);
                    drop(m);
                    drop(taken);
                }
            }
            Kind::SetBuilder => {
                if let Ok(mut s) = Rc::<RefCell<ValueSet>>::value_at(addr).try_borrow_mut() {
                    let taken = std::mem::take(&mut *s);
                    drop(s);
                    drop(taken);
                }
            }
            Kind::Enumerator => Rc::<EnumeratorVal>::value_at(addr).clear_buffer(),
            Kind::Closure | Kind::Array | Kind::Hash | Kind::Set | Kind::Range => {}
        }
    }
}

/// Collect this thread's garbage cycles now.
fn collect(s: &State) {
    if *s
        .off
        .get()
        .get_or_insert_with(|| std::env::var_os("QUARZ_NO_CYCLES").is_some_and(|v| v == "1"))
    {
        s.made.set(0);
        s.limit.set(usize::MAX);
        return;
    }
    let _quiet = Quiet::new();
    let roots: Vec<(usize, Kind)> = s.list.borrow().clone();
    let found = garbage(&roots);
    // The objects to finalize are queued, intact, and freed by a later
    // collection once their `deinitialize` has run.
    for &addr in &found.finalize {
        // SAFETY: garbage is live until released here.
        let o: Rc<Object> = unsafe { Rc::clone_at(addr) };
        o.set_deinitialized();
        crate::deinit::queue(o);
    }
    if !found.free.is_empty() {
        // A reference to each: none is freed until all are emptied.
        let held: Vec<Held> = found
            .free
            .iter()
            // SAFETY: as above.
            .map(|&(addr, kind)| unsafe { hold(addr, kind) })
            .collect();
        for &(addr, kind) in &found.free {
            // SAFETY: held above, so live; garbage, so nothing else uses it.
            unsafe { clear(addr, kind) };
        }
        drop(held);
    }
    s.made.set(0);
    // Sooner when objects wait for their `deinitialize`: they are freed
    // by the next collection.
    let limit = if found.finalize.is_empty() {
        found.live.saturating_mul(2).max(MIN_LIMIT)
    } else {
        MIN_LIMIT
    };
    s.limit.set(limit);
}

/// Collect now (for tests).
pub fn collect_now() {
    let _ = STATE.try_with(|s| {
        if !s.running.get() {
            collect(s);
        }
    });
}

/// How many candidates this thread has.
pub fn candidates() -> usize {
    STATE.try_with(|s| s.list.borrow().len()).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Fields;
    use smallvec::smallvec;

    /// Objects of a class the registry does not know: one field, a value.
    fn object(v: Value) -> Rc<Object> {
        let fields: Fields = smallvec![v];
        Object::new(u32::MAX - 1, fields)
    }

    #[test]
    fn frees_a_cycle_and_keeps_what_is_in_use() {
        let before = candidates();
        let a = object(Value::Nil);
        let b = object(Value::Object(a.clone()));
        a.set_field(0, Value::Object(b.clone()));
        // Another pair, still referred to from here.
        let c = object(Value::Nil);
        let d = object(Value::Array(Rc::new(ArrayData::Values(vec![
            Value::Object(c.clone()),
        ]))));
        c.set_field(0, Value::Object(d.clone()));
        let watch = d.clone();
        drop((a, b, c, d));
        assert_eq!(candidates(), before + 4);
        collect_now();
        // The first pair is gone; the second is intact.
        assert_eq!(candidates(), before + 2);
        let Some(Value::Array(xs)) = watch.field(0) else {
            panic!("field cleared")
        };
        let Some(Value::Object(c)) = xs.iter().next() else {
            panic!("element cleared")
        };
        assert!(matches!(c.field(0), Some(Value::Object(o)) if Rc::ptr_eq(&o, &watch)));
    }

    #[test]
    fn a_shared_value_is_no_candidate() {
        let before = candidates();
        let a = object(Value::Int(1));
        assert_eq!(candidates(), before + 1);
        Value::Object(a.clone()).share();
        assert_eq!(candidates(), before);
        drop(a);
    }
}
