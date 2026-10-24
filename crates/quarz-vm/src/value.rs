//! Run-time values.
//!
//! Immutable collections are reference-counted; updates use
//! `Rc::make_mut`, which modifies in place when the value is uniquely
//! referenced and copies otherwise (the "functional but in place"
//! behaviour described in the design documents).

use crate::rc::Rc;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use indexmap::{IndexMap, IndexSet};

/// The maps and sets of values, hashed with the Fx hasher.
pub type ValueMap = IndexMap<Value, Value, rustc_hash::FxBuildHasher>;
pub type ValueSet = IndexSet<Value, rustc_hash::FxBuildHasher>;
/// A hash whose keys and values are all `Int`, stored unboxed.
pub type IntMap = IndexMap<i64, i64, rustc_hash::FxBuildHasher>;

/// The updates that had to copy a shared collection, on every thread (a
/// copy is rare enough for an atomic count).
static COPIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The contents of a collection, for an update: in place when this is
/// its only reference, else a copy (counted: see `copies`).
pub fn unique_mut<T: Clone>(rc: &mut Rc<T>) -> &mut T {
    // The empty array (`Value::empty_array`) is shared by design, and has
    // nothing to copy; any other shared collection counts.
    if Rc::get_mut(rc).is_none() && !is_the_empty_array(Rc::as_ptr(rc).cast()) {
        COPIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
    Rc::make_mut(rc)
}

/// The empty array every `Value::array` of no elements returns.
static EMPTY_ARRAY: std::sync::OnceLock<SharedValue> = std::sync::OnceLock::new();

/// Whether `p` is the address of the shared empty array's `ArrayData`.
fn is_the_empty_array(p: *const u8) -> bool {
    match EMPTY_ARRAY.get().map(SharedValue::get) {
        Some(Value::Array(a)) => std::ptr::eq(Rc::as_ptr(a).cast(), p),
        _ => false,
    }
}

/// How many updates had to copy a shared collection.
/// `QUARZ_COUNT_COPIES=1` prints it at exit; tests use it to check that
/// the updates the compiler means to be in place are.
pub fn copies() -> u64 {
    COPIES.load(std::sync::atomic::Ordering::Relaxed)
}

/// The entries of a `Hash`: unboxed while every key and value is an
/// `Int` (the storage becomes boxed values, once, when anything else is
/// stored), boxed values otherwise. Iteration order is insertion order
/// either way.
#[derive(Clone, Debug)]
pub enum HashData {
    Values(ValueMap),
    Ints(IntMap),
}

impl Default for HashData {
    fn default() -> Self {
        HashData::Values(ValueMap::default())
    }
}

impl From<ValueMap> for HashData {
    /// A map of `Int` keys and values is stored unboxed.
    fn from(map: ValueMap) -> HashData {
        if !map.is_empty()
            && map
                .iter()
                .all(|(k, v)| matches!((k, v), (Value::Int(_), Value::Int(_))))
        {
            let mut ints = IntMap::with_capacity_and_hasher(map.len(), Default::default());
            for (k, v) in &map {
                if let (Value::Int(k), Value::Int(v)) = (k, v) {
                    ints.insert(*k, *v);
                }
            }
            return HashData::Ints(ints);
        }
        HashData::Values(map)
    }
}

impl FromIterator<(Value, Value)> for HashData {
    fn from_iter<I: IntoIterator<Item = (Value, Value)>>(items: I) -> HashData {
        HashData::from(items.into_iter().collect::<ValueMap>())
    }
}

impl HashData {
    pub fn len(&self) -> usize {
        match self {
            HashData::Values(m) => m.len(),
            HashData::Ints(m) => m.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The entries as boxed values: borrowed, or built for unboxed
    /// storage.
    pub fn as_map(&self) -> std::borrow::Cow<'_, ValueMap> {
        match self {
            HashData::Values(m) => std::borrow::Cow::Borrowed(m),
            HashData::Ints(m) => std::borrow::Cow::Owned(
                m.iter()
                    .map(|(k, v)| (Value::Int(*k), Value::Int(*v)))
                    .collect(),
            ),
        }
    }

    /// The entries as boxed values, to change (unboxed storage is
    /// converted, once).
    pub fn values_mut(&mut self) -> &mut ValueMap {
        if let HashData::Ints(m) = self {
            let map: ValueMap = m
                .iter()
                .map(|(k, v)| (Value::Int(*k), Value::Int(*v)))
                .collect();
            *self = HashData::Values(map);
        }
        match self {
            HashData::Values(m) => m,
            HashData::Ints(_) => unreachable!(),
        }
    }

    /// Change the entries as boxed values (unboxed storage is converted
    /// first).
    pub fn with_values<R>(&mut self, f: impl FnOnce(&mut ValueMap) -> R) -> R {
        f(self.values_mut())
    }

    pub fn get(&self, k: &Value) -> Option<Value> {
        match (self, k) {
            (HashData::Values(m), _) => m.get(k).cloned(),
            (HashData::Ints(m), Value::Int(k)) => m.get(k).map(|v| Value::Int(*v)),
            // An Int-keyed hash holds no other key (`1.0 == 1` is a key
            // equal to 1).
            (HashData::Ints(m), Value::Float(f)) if f.fract() == 0.0 && f.abs() < 9.2e18 => {
                m.get(&(*f as i64)).map(|v| Value::Int(*v))
            }
            (HashData::Ints(_), _) => None,
        }
    }

    pub fn contains_key(&self, k: &Value) -> bool {
        match (self, k) {
            (HashData::Values(m), _) => m.contains_key(k),
            (HashData::Ints(m), Value::Int(k)) => m.contains_key(k),
            (HashData::Ints(_), _) => self.get(k).is_some(),
        }
    }

    /// Insert or replace (keeping the key's position).
    pub fn insert(&mut self, k: Value, v: Value) {
        match (&mut *self, &k, &v) {
            (HashData::Ints(m), Value::Int(a), Value::Int(b)) => {
                m.insert(*a, *b);
            }
            (HashData::Values(m), Value::Int(a), Value::Int(b)) if m.is_empty() => {
                let mut ints = IntMap::default();
                ints.insert(*a, *b);
                *self = HashData::Ints(ints);
            }
            _ => {
                self.values_mut().insert(k, v);
            }
        }
    }

    /// Remove a key, keeping the order of the others.
    pub fn shift_remove(&mut self, k: &Value) -> Option<Value> {
        if let (HashData::Ints(m), Value::Int(a)) = (&mut *self, k) {
            return m.shift_remove(a).map(Value::Int);
        }
        if matches!(self, HashData::Ints(_)) && !self.contains_key(k) {
            return None;
        }
        self.values_mut().shift_remove(k)
    }
}
use num_bigint::BigInt;
use quarz_ir::{ClassId, FuncId, MethodId};
use smallvec::SmallVec;

use crate::interp::Flow;
use crate::sched::{ChannelInner, ScopeInner, SelectorState, TaskHandle};

/// An interned symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(pub u32);

/// The names of the symbols, which every task (and so every worker
/// thread) uses: the names are shared allocations.
#[derive(Default)]
pub struct SymbolTable {
    names: Vec<Rc<str>>,
    ids: HashMap<Rc<str>, Symbol>,
}

// SAFETY: the table holds only shared allocations (marked by `intern`),
// whose counts are updated atomically and which nothing changes.
unsafe impl Send for SymbolTable {}
unsafe impl Sync for SymbolTable {}

impl SymbolTable {
    pub fn intern(&mut self, name: &str) -> Symbol {
        if let Some(s) = self.ids.get(name) {
            return *s;
        }
        let rc: Rc<str> = Rc::from(name);
        Rc::mark_shared(&rc);
        let sym = Symbol(self.names.len() as u32);
        self.names.push(rc.clone());
        self.ids.insert(rc, sym);
        sym
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    pub fn lookup(&self, name: &str) -> Option<Symbol> {
        self.ids.get(name).copied()
    }

    pub fn name(&self, sym: Symbol) -> &Rc<str> {
        &self.names[sym.0 as usize]
    }
}

/// A local variable frame. Blocks keep a reference to the frame they were
/// created in. One allocation: the header, then the slots (`FrameOf` with
/// its tail; a frame that grows past it, which only a REPL's top level
/// does, moves its slots to a vector of their own).
pub type Frame = FrameOf<std::cell::UnsafeCell<[ManuallyDrop<Value>]>>;

/// The header with no slots, which gives the layout.
type FrameHeader = FrameOf<std::cell::UnsafeCell<[ManuallyDrop<Value>; 0]>>;

use std::mem::ManuallyDrop;

#[repr(C)]
pub struct FrameOf<S: ?Sized + FrameTail> {
    /// Where the slots live and how many there are, for compiled code
    /// (set by `bind` when the slots are created or moved).
    pub slots_ptr: Cell<*const Value>,
    pub nslots: Cell<u32>,
    /// How many slots follow the header (the tail's length).
    tail_len: u32,
    /// The parent frame's header, for compiled code (null at the top).
    pub parent_ptr: Cell<*const u8>,
    pub parent: Option<Rc<Frame>>,
    /// The slots once the frame grew past its tail, which then holds
    /// nothing (they were moved here). Boxed: one word in every frame
    /// rather than three, for what few frames need.
    #[allow(clippy::box_collection)]
    grown: std::cell::UnsafeCell<Option<Box<Vec<Value>>>>,
    /// Written through the slot view while the frame is borrowed.
    tail: S,
}

/// The slots after a frame's header.
pub trait FrameTail {}

impl FrameTail for std::cell::UnsafeCell<[ManuallyDrop<Value>]> {}
impl FrameTail for std::cell::UnsafeCell<[ManuallyDrop<Value>; 0]> {}

// What compiled code reads (`gen.rs`'s frame access): the slot view at
// 0, 8 and 16 of the frame.
const _: () = {
    assert!(std::mem::offset_of!(FrameHeader, slots_ptr) == 0);
    assert!(std::mem::offset_of!(FrameHeader, nslots) == 8);
    assert!(std::mem::offset_of!(FrameHeader, parent_ptr) == 16);
};

// SAFETY: a frame's allocation is the counts, then the header, which
// gives the tail's length (see `Frame::from_iter`).
unsafe impl crate::rc::Target for Frame {
    #[inline(always)]
    unsafe fn inner(p: *mut u8) -> *mut crate::rc::Inner<Frame> {
        type Inner = crate::rc::Inner<FrameHeader>;
        // SAFETY: the header of a live frame, as the caller promises.
        let len = unsafe {
            *p.add(std::mem::offset_of!(Inner, value) + std::mem::offset_of!(FrameHeader, tail_len))
                .cast::<u32>() as usize
        };
        std::ptr::slice_from_raw_parts_mut(p.cast::<ManuallyDrop<Value>>(), len)
            as *mut crate::rc::Inner<Frame>
    }
}

impl<S: ?Sized + FrameTail> Drop for FrameOf<S> {
    fn drop(&mut self) {
        if self.grown.get_mut().is_some() {
            // The tail's slots were moved out; the vector drops its own.
            return;
        }
        let n = self.tail_len as usize;
        let tail = (&raw mut self.tail).cast::<Value>();
        // SAFETY: the tail holds `n` live values, dropped once, here.
        unsafe { std::ptr::drop_in_place(std::ptr::slice_from_raw_parts_mut(tail, n)) }
    }
}

impl std::fmt::Debug for Frame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Frame")
            .field("slots", &self.slots())
            .field("parent", &self.parent)
            .finish()
    }
}

impl Frame {
    pub fn new(size: usize, parent: Option<Rc<Frame>>) -> Rc<Frame> {
        Frame::from_iter(std::iter::repeat_n(Value::Nil, size), parent)
    }

    pub fn from_slots(slots: Vec<Value>, parent: Option<Rc<Frame>>) -> Rc<Frame> {
        Frame::from_iter(slots.into_iter(), parent)
    }

    fn from_iter(
        slots: impl ExactSizeIterator<Item = Value>,
        parent: Option<Rc<Frame>>,
    ) -> Rc<Frame> {
        let n = slots.len();
        let header = std::alloc::Layout::new::<crate::rc::Inner<FrameHeader>>();
        let layout = std::alloc::Layout::from_size_align(
            header.size() + n * std::mem::size_of::<Value>(),
            header.align(),
        )
        .expect("frame too large");
        let parent_ptr = parent
            .as_ref()
            .map_or(std::ptr::null(), |p| Rc::as_ptr(p) as *const u8);
        // SAFETY: the layout is not zero-sized; every field of the header
        // and every slot is written before the reference is made.
        unsafe {
            let mem = std::alloc::alloc(layout);
            if mem.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            let p = std::ptr::slice_from_raw_parts_mut(mem.cast::<ManuallyDrop<Value>>(), n)
                as *mut crate::rc::Inner<Frame>;
            let f = &raw mut (*p).value;
            let tail = &raw mut (*f).tail as *mut ManuallyDrop<Value> as *mut Value;
            // Nil for what an iterator shorter than it said leaves.
            let mut slots = slots.fuse();
            for k in 0..n {
                tail.add(k).write(slots.next().unwrap_or(Value::Nil));
            }
            (&raw mut (*f).slots_ptr).write(Cell::new(tail));
            (&raw mut (*f).nslots).write(Cell::new(n as u32));
            (&raw mut (*f).tail_len).write(n as u32);
            (&raw mut (*f).parent_ptr).write(Cell::new(parent_ptr));
            (&raw mut (*f).parent).write(parent);
            (&raw mut (*f).grown).write(std::cell::UnsafeCell::new(None));
            Rc::from_fresh(p)
        }
    }

    /// The slots, through the slot view (as `get` reads them).
    pub fn slots(&self) -> &[Value] {
        // SAFETY: `slots_ptr`/`nslots` describe the live slots; see `get`
        // for why reading them without a borrow is sound.
        unsafe { std::slice::from_raw_parts(self.slots_ptr.get(), self.nslots.get() as usize) }
    }

    pub fn get(&self, depth: u32, slot: u32) -> Value {
        let mut frame = self;
        for _ in 0..depth {
            frame = frame.parent.as_deref().expect("frame depth");
        }
        // Through the slot view, as compiled code reads, not a borrow: the
        // frames a shareable procedure (or a `Task.spawn` block) copied are read
        // by every task that calls it, at once, and a borrow would update
        // the cell's count from several threads. Nothing writes them (the
        // checker rejects assigning a variable captured that way), and a
        // frame being written is read by its own task only.
        if slot < frame.nslots.get() {
            // SAFETY: `slots_ptr`/`nslots` describe the live slots, set
            // when they are created or moved.
            unsafe { (*frame.slots_ptr.get().add(slot as usize)).clone() }
        } else {
            Value::Nil
        }
    }

    /// Set a slot (its frame's own task only, as for `get`), growing the
    /// frame when the slot is beyond it.
    pub fn set(&self, depth: u32, slot: u32, value: Value) {
        let mut frame = self;
        for _ in 0..depth {
            frame = frame.parent.as_deref().expect("frame depth");
        }
        let i = slot as usize;
        if i >= frame.nslots.get() as usize {
            frame.grow(i + 1);
        }
        // SAFETY: a live slot (see `get`); no reference into the slots is
        // held across this store.
        unsafe { *(frame.slots_ptr.get() as *mut Value).add(i) = value }
    }

    /// Make room for `n` slots: in a vector of the frame's own, the tail's
    /// slots moved into it the first time.
    fn grow(&self, n: usize) {
        // SAFETY: only the frame's own task changes its slots, and no
        // reference into them is held across this call.
        unsafe {
            let grown = &mut *self.grown.get();
            if grown.is_none() {
                let tail = self.tail.get() as *const ManuallyDrop<Value> as *const Value;
                let moved: Vec<Value> = (0..self.tail_len as usize)
                    .map(|k| std::ptr::read(tail.add(k)))
                    .collect();
                *grown = Some(Box::new(moved));
            }
            let vec = grown.as_mut().unwrap();
            vec.resize(n, Value::Nil);
            self.slots_ptr.set(vec.as_ptr());
            self.nslots.set(vec.len() as u32);
        }
    }
}

/// The fields of an object, stored inline for up to four.
pub type Fields = SmallVec<[Value; 4]>;

/// The elements of an array: boxed values, or unboxed machine integers
/// or floats when every element is one (`Array[Int]`/`Array[Float]`
/// usually are). The layout is fixed (`repr(C, u8)`: the kind byte, then
/// the vector at offset 8) so that compiled code reads elements directly.
#[derive(Clone, Debug)]
#[repr(C, u8)]
pub enum ArrayData {
    Values(Vec<Value>),
    Ints(Vec<i64>),
    Floats(Vec<f64>),
}

pub const ARRAY_KIND_VALUES: u8 = 0;
pub const ARRAY_KIND_INTS: u8 = 1;
pub const ARRAY_KIND_FLOATS: u8 = 2;

/// Iterates an array's elements as values.
pub enum ArrayIter<'a> {
    Values(std::slice::Iter<'a, Value>),
    Ints(std::slice::Iter<'a, i64>),
    Floats(std::slice::Iter<'a, f64>),
}

impl Iterator for ArrayIter<'_> {
    type Item = Value;

    fn next(&mut self) -> Option<Value> {
        match self {
            ArrayIter::Values(it) => it.next().cloned(),
            ArrayIter::Ints(it) => it.next().map(|i| Value::Int(*i)),
            ArrayIter::Floats(it) => it.next().map(|f| Value::Float(*f)),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            ArrayIter::Values(it) => it.size_hint(),
            ArrayIter::Ints(it) => it.size_hint(),
            ArrayIter::Floats(it) => it.size_hint(),
        }
    }
}

impl ExactSizeIterator for ArrayIter<'_> {}

impl DoubleEndedIterator for ArrayIter<'_> {
    fn next_back(&mut self) -> Option<Value> {
        match self {
            ArrayIter::Values(it) => it.next_back().cloned(),
            ArrayIter::Ints(it) => it.next_back().map(|i| Value::Int(*i)),
            ArrayIter::Floats(it) => it.next_back().map(|f| Value::Float(*f)),
        }
    }
}

impl ArrayData {
    /// Store `items` unboxed when they are all machine integers or all
    /// floats (and there are some), boxed otherwise.
    pub fn from_values(items: Vec<Value>) -> ArrayData {
        if items.is_empty() {
            return ArrayData::Values(items);
        }
        if items.iter().all(|v| matches!(v, Value::Int(_))) {
            return ArrayData::Ints(
                items
                    .iter()
                    .map(|v| match v {
                        Value::Int(i) => *i,
                        _ => unreachable!(),
                    })
                    .collect(),
            );
        }
        if items.iter().all(|v| matches!(v, Value::Float(_))) {
            return ArrayData::Floats(
                items
                    .iter()
                    .map(|v| match v {
                        Value::Float(f) => *f,
                        _ => unreachable!(),
                    })
                    .collect(),
            );
        }
        ArrayData::Values(items)
    }

    pub fn kind(&self) -> u8 {
        match self {
            ArrayData::Values(_) => ARRAY_KIND_VALUES,
            ArrayData::Ints(_) => ARRAY_KIND_INTS,
            ArrayData::Floats(_) => ARRAY_KIND_FLOATS,
        }
    }

    pub fn len(&self) -> usize {
        match self {
            ArrayData::Values(v) => v.len(),
            ArrayData::Ints(v) => v.len(),
            ArrayData::Floats(v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, i: usize) -> Option<Value> {
        match self {
            ArrayData::Values(v) => v.get(i).cloned(),
            ArrayData::Ints(v) => v.get(i).map(|i| Value::Int(*i)),
            ArrayData::Floats(v) => v.get(i).map(|f| Value::Float(*f)),
        }
    }

    pub fn iter(&self) -> ArrayIter<'_> {
        match self {
            ArrayData::Values(v) => ArrayIter::Values(v.iter()),
            ArrayData::Ints(v) => ArrayIter::Ints(v.iter()),
            ArrayData::Floats(v) => ArrayIter::Floats(v.iter()),
        }
    }

    /// The elements as boxed values: borrowed when they are stored so,
    /// a fresh vector otherwise.
    pub fn values(&self) -> std::borrow::Cow<'_, [Value]> {
        match self {
            ArrayData::Values(v) => std::borrow::Cow::Borrowed(v.as_slice()),
            _ => std::borrow::Cow::Owned(self.iter().collect()),
        }
    }

    pub fn to_values(&self) -> Vec<Value> {
        self.iter().collect()
    }

    pub fn into_values(self) -> Vec<Value> {
        match self {
            ArrayData::Values(v) => v,
            other => other.iter().collect(),
        }
    }

    /// Switch to boxed storage and give the vector to `f`.
    pub fn with_values<R>(&mut self, f: impl FnOnce(&mut Vec<Value>) -> R) -> R {
        if !matches!(self, ArrayData::Values(_)) {
            *self = ArrayData::Values(self.to_values());
        }
        match self {
            ArrayData::Values(v) => f(v),
            _ => unreachable!(),
        }
    }

    /// Append `v`: in the unboxed storage when it fits (an empty boxed
    /// array takes the kind of its first element), boxing everything
    /// otherwise.
    pub fn push(&mut self, v: Value) {
        match (&mut *self, &v) {
            (ArrayData::Ints(xs), Value::Int(i)) => xs.push(*i),
            (ArrayData::Floats(xs), Value::Float(f)) => xs.push(*f),
            (ArrayData::Values(xs), Value::Int(i)) if xs.is_empty() => {
                *self = ArrayData::Ints(vec![*i]);
            }
            (ArrayData::Values(xs), Value::Float(f)) if xs.is_empty() => {
                *self = ArrayData::Floats(vec![*f]);
            }
            (ArrayData::Values(xs), _) => xs.push(v),
            _ => self.with_values(|xs| xs.push(v)),
        }
    }

    /// `self[i] = v` for an index in range.
    pub fn set(&mut self, i: usize, v: Value) {
        match (&mut *self, &v) {
            (ArrayData::Ints(xs), Value::Int(x)) => xs[i] = *x,
            (ArrayData::Floats(xs), Value::Float(x)) => xs[i] = *x,
            (ArrayData::Values(xs), _) => xs[i] = v,
            _ => self.with_values(|xs| xs[i] = v),
        }
    }

    pub fn extend_from(&mut self, other: &ArrayData) {
        match (&mut *self, other) {
            (ArrayData::Ints(xs), ArrayData::Ints(ys)) => xs.extend_from_slice(ys),
            (ArrayData::Floats(xs), ArrayData::Floats(ys)) => xs.extend_from_slice(ys),
            (ArrayData::Values(xs), ArrayData::Values(ys)) => xs.extend_from_slice(ys),
            (ArrayData::Values(xs), _) if xs.is_empty() => *self = other.clone(),
            _ => {
                let more = other.to_values();
                self.with_values(|xs| xs.extend(more));
            }
        }
    }
}

/// An instance of a user-defined class, data type, enum variant or
/// exception: `ObjectOf` with its fields as the tail of the allocation,
/// laid out as its class's `FieldLayout` says (an object is as large as
/// its class needs, so objects with different fields fall in different
/// size classes of the allocator, and none has a second allocation
/// unless a field declared `Int` holds a big integer).
///
/// A field declared `Int`, `Float` or `Bool` is the machine word of the
/// number or boolean (`quarz_ir::field_slots`); what the word cannot
/// hold is marked in it and kept aside: nil before the field is
/// assigned, a big integer or `i64::MIN` in an `Int` field (and, should
/// one ever be stored, a value of another type). The marks are
/// `INT_MARK`, `FLOAT_MARK` (a NaN no arithmetic produces: Quarz cannot
/// observe NaN payloads, and one stored with these bits would be kept
/// aside like the rest) and `BOOL_MARK`.
pub type Object = ObjectOf<std::cell::UnsafeCell<[u64]>>;

/// The mark of an `Int` field whose value is kept aside.
pub const INT_MARK: i64 = i64::MIN;
/// The mark of a `Float` field whose value is kept aside.
pub const FLOAT_MARK: u64 = 0xFFF4_0000_0000_C0DE;
/// The mark of a `Bool` field whose value is kept aside.
pub const BOOL_MARK: u64 = 2;

/// An object's header, then its fields `F` (see `Object`; the header
/// with no fields, `ObjectOf<UnsafeCell<[u64; 0]>>`, gives the layout).
#[repr(C)]
pub struct ObjectOf<F: ?Sized + FieldTail> {
    /// Where its fields are. First in the layout, right after the
    /// allocation's two counts (compiled code reads the offsets there).
    pub layout: &'static FieldLayout,
    /// `DEINITIALIZED` and `HAS_EXC`.
    flags: std::sync::atomic::AtomicU32,
    pub class: ClassId,
    /// The fields, without a borrow flag: an object that tasks share (its
    /// class has no `var` fields, or is an exception) is read by several
    /// threads at once and written by none once built, and a mutable one
    /// is only ever touched by its own task, so what guards them is that
    /// no reference into them outlives the operation that took it.
    fields: F,
}

// SAFETY: an object's allocation is the counts, then the header, whose
// layout (its first field) gives the fields' size in words, the length of
// the tail (see `Object::with_fields_from`).
unsafe impl crate::rc::Target for Object {
    #[inline(always)]
    unsafe fn inner(p: *mut u8) -> *mut crate::rc::Inner<Object> {
        type Header = crate::rc::Inner<ObjectOf<std::cell::UnsafeCell<[u64; 0]>>>;
        // SAFETY: the header of a live object, as the caller promises.
        let words = unsafe {
            let at = p.add(
                std::mem::offset_of!(Header, value)
                    + std::mem::offset_of!(ObjectOf<std::cell::UnsafeCell<[u64; 0]>>, layout),
            );
            (*at.cast::<&'static FieldLayout>()).words
        };
        std::ptr::slice_from_raw_parts_mut(p.cast::<u64>(), words) as *mut crate::rc::Inner<Object>
    }
}

/// An object's flag: its `deinitialize` has run (or is to run), so that
/// released again it is freed (see `crate::deinit`). Set before the
/// object is reachable, by the thread that makes it.
const DEINITIALIZED: u32 = 1;
/// An object's flag: it was raised, and `EXC_INFO` holds what was
/// captured then (set once, under the table's lock, by whichever of
/// several threads raising a shared exception gets there first).
const HAS_EXC: u32 = 2;

/// What raised exceptions captured, by the address of their allocation,
/// for an exception whose layout has no word for it (one made with other
/// fields than its class's layout has: `FieldLayout::values`). An entry lives as long as its
/// object, which removes it when freed.
static EXC_INFO: std::sync::Mutex<HashMap<usize, ExcEntry, rustc_hash::FxBuildHasher>> =
    std::sync::Mutex::new(HashMap::with_hasher(rustc_hash::FxBuildHasher));

/// An entry of `EXC_INFO`.
struct ExcEntry(Box<ExcInfo>);

// SAFETY: the table only moves the box; what it holds is reached through
// its object, as a field of the object would be: by the object's thread
// while it is local, and by any once it is shared, `init_exc` having
// marked the entry's values shared too. It is dropped when the object is.
unsafe impl Send for ExcEntry {}

/// An object's key in `EXC_INFO`: the address of its header.
fn exc_key(object: *const u8) -> usize {
    object as usize
}

fn exc_table() -> std::sync::MutexGuard<'static, HashMap<usize, ExcEntry, rustc_hash::FxBuildHasher>>
{
    // A panic while the lock was held leaves the table as it was.
    EXC_INFO.lock().unwrap_or_else(|e| e.into_inner())
}

/// The fields at the end of an object, as words.
pub trait FieldTail {}

impl FieldTail for std::cell::UnsafeCell<[u64]> {}
impl FieldTail for std::cell::UnsafeCell<[u64; 0]> {}

/// Where an object keeps each field (from `quarz_ir::field_slots`),
/// shared by all the objects of a class and never freed.
#[repr(C)]
pub struct FieldLayout {
    /// Byte offsets from the start of the fields (first: compiled code
    /// reads them through `layout::FIELD_LAYOUT_OFFSETS`).
    pub offsets: *const u32,
    pub kinds: &'static [FieldKind],
    /// The byte offset of the pointer to what is kept aside, if any.
    pub aside: Option<u32>,
    /// Exception classes only: the byte offset of the word that points
    /// at what the exception captured when raised (null until then).
    pub exc: Option<u32>,
    /// The fields' size, in words.
    pub words: usize,
}

// SAFETY: a layout is immutable once made; `offsets` points at a leaked
// slice as long as `kinds`.
unsafe impl Sync for FieldLayout {}
unsafe impl Send for FieldLayout {}

pub use quarz_ir::FieldKind;

/// What `Int` fields cannot hold (see `Object`), by field index.
type Aside = Vec<(u32, Value)>;

static NO_FIELDS: FieldLayout = FieldLayout {
    offsets: std::ptr::null(),
    kinds: &[],
    aside: None,
    exc: None,
    words: 0,
};

impl FieldLayout {
    /// `exc`: the objects are exceptions, with a word for what they
    /// capture after the fields.
    fn leak(slots: &quarz_ir::FieldSlots, exc: bool) -> &'static FieldLayout {
        if slots.kinds.is_empty() && !exc {
            return &NO_FIELDS;
        }
        let offsets: &'static [u32] = Box::leak(slots.offsets.clone().into_boxed_slice());
        let kinds: &'static [FieldKind] = Box::leak(slots.kinds.clone().into_boxed_slice());
        Box::leak(Box::new(FieldLayout {
            offsets: offsets.as_ptr(),
            kinds,
            aside: slots.aside,
            exc: exc.then_some(slots.size),
            words: slots.size as usize / 8 + usize::from(exc),
        }))
    }

    #[inline(always)]
    fn offset(&self, i: usize) -> usize {
        // SAFETY: `i` is below `kinds.len()`, as long as `offsets`.
        unsafe { *self.offsets.add(i) as usize }
    }

    /// `n` fields that are all values (a class the registry does not know
    /// or whose fields changed: what a REPL input redefines, say).
    fn values(n: usize) -> &'static FieldLayout {
        static CACHE: std::sync::Mutex<Vec<&'static FieldLayout>> =
            std::sync::Mutex::new(Vec::new());
        let mut cache = CACHE.lock().unwrap_or_else(|e| e.into_inner());
        while cache.len() <= n {
            let k = cache.len();
            let slots = quarz_ir::FieldSlots {
                kinds: vec![FieldKind::Value; k],
                offsets: (0..k as u32).map(|i| i * quarz_ir::VALUE_BYTES).collect(),
                aside: None,
                size: k as u32 * quarz_ir::VALUE_BYTES,
            };
            cache.push(FieldLayout::leak(&slots, false));
        }
        cache[n]
    }
}

/// Each class's layout, by class id (published whole: readers take no
/// lock).
static LAYOUTS: std::sync::atomic::AtomicPtr<Vec<&'static FieldLayout>> =
    std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());
static LAYOUTS_WRITE: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Make the layouts of `classes` (a program's, by id) the ones new
/// objects get. A class whose fields are as before keeps its layout.
pub fn register_layouts(classes: &[quarz_ir::RtClass]) {
    let _guard = LAYOUTS_WRITE.lock().unwrap_or_else(|e| e.into_inner());
    let old = LAYOUTS.load(std::sync::atomic::Ordering::Acquire);
    // SAFETY: a published table is never freed.
    let old: &[&'static FieldLayout] = if old.is_null() { &[] } else { unsafe { &*old } };
    // Exceptions get a word for what a raise captures (see `exc_info`).
    let table: Vec<&'static FieldLayout> = classes
        .iter()
        .enumerate()
        .map(|(id, c)| {
            let slots = quarz_ir::field_slots(&c.fields);
            let exc = c.is_exception;
            match old.get(id) {
                Some(l) if l.kinds == slots.kinds.as_slice() && l.exc.is_some() == exc => *l,
                _ => FieldLayout::leak(&slots, exc),
            }
        })
        .collect();
    let same = table.len() == old.len() && table.iter().zip(old).all(|(a, b)| std::ptr::eq(*a, *b));
    if !same {
        // The old table stays allocated: a reader may still hold it.
        LAYOUTS.store(
            Box::into_raw(Box::new(table)),
            std::sync::atomic::Ordering::Release,
        );
    }
}

/// The layout of a new object of `class` with `n` fields.
fn layout_for(class: ClassId, n: usize) -> &'static FieldLayout {
    let table = LAYOUTS.load(std::sync::atomic::Ordering::Acquire);
    if !table.is_null() {
        // SAFETY: a published table is never freed.
        if let Some(l) = unsafe { &*table }.get(class as usize) {
            if l.kinds.len() == n {
                return l;
            }
        }
    }
    FieldLayout::values(n)
}

impl<F: ?Sized + FieldTail> Drop for ObjectOf<F> {
    fn drop(&mut self) {
        let layout = self.layout;
        let base = &raw mut self.fields as *mut u8;
        // The last reference went: an object whose class defines
        // `deinitialize` lives on, rebuilt from its fields, until the
        // method has run on it.
        let flags = self.flags.load(std::sync::atomic::Ordering::Relaxed);
        if flags & DEINITIALIZED == 0 && crate::deinit::has(self.class) {
            // SAFETY: nothing else refers to the object now.
            let fields: Fields = (0..layout.kinds.len())
                .map(|i| unsafe { take_field_at(layout, base, i) })
                .collect();
            let o = Object::new(self.class, fields);
            o.flags
                .fetch_or(DEINITIALIZED, std::sync::atomic::Ordering::Relaxed);
            crate::deinit::queue(o);
        }
        // SAFETY: as above; each value is dropped once, here.
        unsafe {
            for (i, k) in layout.kinds.iter().enumerate() {
                if *k == FieldKind::Value {
                    std::ptr::drop_in_place(base.add(layout.offset(i)) as *mut Value);
                }
            }
            if let Some(a) = layout.aside {
                let p = *(base.add(a as usize) as *const *mut Aside);
                if !p.is_null() {
                    drop(Box::from_raw(p));
                }
            }
        }
        // Last, as when it was a field.
        if let Some(e) = layout.exc {
            // SAFETY: the word `with_fields_from` made, now this thread's
            // alone; a non-null pointer is a box `init_exc` leaked.
            unsafe {
                let p = *(base.add(e as usize) as *const *mut ExcInfo);
                if !p.is_null() {
                    drop(Box::from_raw(p));
                }
            }
        }
        // Taken out under the lock, dropped after it (its cause may be an
        // exception freed in turn).
        if flags & HAS_EXC != 0 {
            let info = exc_table().remove(&exc_key(self as *const Self as *const u8));
            drop(info);
        }
    }
}

/// Field `i` of the object whose fields start at `base`, leaving nil
/// there.
///
/// # Safety
/// A short write of field `i` (see `ObjectOf::fields`).
unsafe fn take_field_at(layout: &FieldLayout, base: *mut u8, i: usize) -> Value {
    // SAFETY: as the caller promises.
    unsafe {
        let k = layout.kinds[i];
        let at = base.add(layout.offset(i));
        if k == FieldKind::Value {
            return std::mem::replace(&mut *(at as *mut Value), Value::Nil);
        }
        let v = read_word(layout, base, i, k);
        store_word(layout, base, i, k, Value::Nil);
        v
    }
}

/// Word field `i` (of kind `k`) as a value.
///
/// # Safety
/// A short read of field `i`.
#[inline(always)]
unsafe fn read_word(layout: &FieldLayout, base: *mut u8, i: usize, k: FieldKind) -> Value {
    // SAFETY: as the caller promises.
    unsafe {
        let at = base.add(layout.offset(i));
        match k {
            FieldKind::Int => match *(at as *const i64) {
                INT_MARK => aside_get(layout, base, i),
                x => Value::Int(x),
            },
            FieldKind::Float => match *(at as *const u64) {
                FLOAT_MARK => aside_get(layout, base, i),
                bits => Value::Float(f64::from_bits(bits)),
            },
            _ => match *(at as *const u64) {
                0 => Value::Bool(false),
                1 => Value::Bool(true),
                _ => aside_get(layout, base, i),
            },
        }
    }
}

impl std::fmt::Debug for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Object")
            .field("class", &self.class)
            .field("fields", &self.fields())
            .finish()
    }
}

/// The backtrace and cause of a raised exception.
#[derive(Debug, Default)]
pub struct ExcInfo {
    pub backtrace: Option<Rc<Vec<String>>>,
    pub cause: Option<Value>,
}

impl Object {
    pub fn new(class: ClassId, mut fields: Fields) -> Rc<Object> {
        let n = fields.len();
        // SAFETY: the values are moved into the object, and the vector
        // forgets them.
        unsafe {
            let o = Object::with_fields_from(class, fields.as_ptr(), n);
            fields.set_len(0);
            o
        }
    }

    /// An object whose `n` fields are moved in from `src`, built in its
    /// allocation (no temporary to copy).
    ///
    /// # Safety
    /// `src` points at `n` initialized values that the caller gives up
    /// (they are moved, not cloned, and must not be dropped by it).
    pub unsafe fn with_fields_from(class: ClassId, src: *const Value, n: usize) -> Rc<Object> {
        type Header = crate::rc::Inner<ObjectOf<std::cell::UnsafeCell<[u64; 0]>>>;
        let layout_of = layout_for(class, n);
        let words = layout_of.words;
        let header = std::alloc::Layout::new::<Header>();
        // The fields follow the header (whose size is a multiple of a
        // word), as `Layout::for_value` finds them when the object is
        // freed.
        let layout = std::alloc::Layout::from_size_align(header.size() + words * 8, header.align())
            .expect("object too large");
        // SAFETY: the layout is not zero-sized; every field of the header
        // and every field slot is written before the reference is made.
        unsafe {
            let mem = std::alloc::alloc(layout);
            if mem.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            let p = std::ptr::slice_from_raw_parts_mut(mem as *mut u64, words)
                as *mut crate::rc::Inner<Object>;
            let o = &raw mut (*p).value;
            std::ptr::write(&raw mut (*o).layout, layout_of);
            std::ptr::write(&raw mut (*o).flags, std::sync::atomic::AtomicU32::new(0));
            std::ptr::write(&raw mut (*o).class, class);
            let base = mem.add(header.size());
            if let Some(a) = layout_of.aside {
                std::ptr::write(
                    base.add(a as usize) as *mut *mut Aside,
                    std::ptr::null_mut(),
                );
            }
            if let Some(e) = layout_of.exc {
                std::ptr::write(
                    base.add(e as usize) as *mut std::sync::atomic::AtomicPtr<ExcInfo>,
                    std::sync::atomic::AtomicPtr::new(std::ptr::null_mut()),
                );
            }
            for (i, k) in layout_of.kinds.iter().enumerate() {
                let at = base.add(layout_of.offset(i));
                let v = std::ptr::read(src.add(i));
                match k {
                    FieldKind::Value => std::ptr::write(at as *mut Value, v),
                    _ => {
                        // Marked first: what the word cannot hold goes
                        // aside (the object is not yet shared).
                        std::ptr::write(at as *mut u64, mark(*k));
                        store_word(layout_of, base, i, *k, v);
                    }
                }
            }
            let rc = crate::rc::Rc::from_fresh(p);
            debug_assert_eq!(std::alloc::Layout::for_value(&*p), layout);
            rc
        }
    }

    /// The start of the fields.
    #[inline(always)]
    fn base(&self) -> *mut u8 {
        self.fields.get() as *mut u64 as *mut u8
    }

    /// The backtrace captured when this (exception) object was raised.
    pub fn backtrace(&self) -> Option<Rc<Vec<String>>> {
        self.exc_info().and_then(|e| e.backtrace.clone())
    }

    pub fn cause(&self) -> Option<Value> {
        self.exc_info().and_then(|e| e.cause.clone())
    }

    /// The word an exception's capture is in, when its layout has one
    /// (a class the registry knew; the others use `EXC_INFO`).
    #[inline]
    fn exc_cell(&self) -> Option<&std::sync::atomic::AtomicPtr<ExcInfo>> {
        let e = self.layout.exc?;
        // SAFETY: the word `with_fields_from` made, only ever accessed
        // atomically once the object is built.
        Some(unsafe {
            &*(self.base().add(e as usize) as *const std::sync::atomic::AtomicPtr<ExcInfo>)
        })
    }

    /// What was captured when the exception was raised, if anything.
    pub fn exc_info(&self) -> Option<&ExcInfo> {
        if let Some(cell) = self.exc_cell() {
            // Acquire: what the pointer points at was written before it.
            let p = cell.load(std::sync::atomic::Ordering::Acquire);
            // SAFETY: set once, to a box freed only with the object, which
            // `&self` outlives.
            return (!p.is_null()).then(|| unsafe { &*p });
        }
        // Acquire: the entry was inserted before the flag was set.
        if self.flags.load(std::sync::atomic::Ordering::Acquire) & HAS_EXC == 0 {
            return None;
        }
        let info: *const ExcInfo = &*exc_table()
            .get(&exc_key(self as *const Self as *const u8))?
            .0;
        // SAFETY: the entry is never changed, and removed only when the
        // object is freed, which `&self` outlives.
        Some(unsafe { &*info })
    }

    /// Record the backtrace and cause, unless the exception has them
    /// already (it was raised before: its first backtrace stays, as in
    /// Ruby). Of several threads raising a shared exception at once, one
    /// wins. `shared`: the object is shared, so what it now refers to
    /// must be too.
    pub fn init_exc(&self, info: ExcInfo, shared: bool) {
        if self.exc_info().is_some() {
            return;
        }
        if shared {
            if let Some(b) = &info.backtrace {
                Rc::mark_shared(b);
            }
            if let Some(c) = &info.cause {
                c.share();
            }
        }
        if let Some(cell) = self.exc_cell() {
            let p = Box::into_raw(Box::new(info));
            // Release: the box's contents before the pointer; the first
            // raise wins, and a later one's capture is dropped.
            if cell
                .compare_exchange(
                    std::ptr::null_mut(),
                    p,
                    std::sync::atomic::Ordering::Release,
                    std::sync::atomic::Ordering::Relaxed,
                )
                .is_err()
            {
                // SAFETY: the box was not published.
                drop(unsafe { Box::from_raw(p) });
            }
            return;
        }
        let mut table = exc_table();
        if self.flags.load(std::sync::atomic::Ordering::Relaxed) & HAS_EXC != 0 {
            // Another thread was first; what this one captured is dropped
            // after the lock.
            drop(table);
            drop(info);
            return;
        }
        let old = table.insert(
            exc_key(self as *const Self as *const u8),
            ExcEntry(Box::new(info)),
        );
        self.flags
            .fetch_or(HAS_EXC, std::sync::atomic::Ordering::Release);
        drop(table);
        // A freed object removes its entry, so its address, given to
        // another, has none.
        debug_assert!(old.is_none(), "a stale exception entry");
        drop(old);
    }

    pub fn field_count(&self) -> usize {
        self.layout.kinds.len()
    }

    /// Field `i`, if the object has it.
    #[inline]
    pub fn field(&self, i: usize) -> Option<Value> {
        let k = *self.layout.kinds.get(i)?;
        // SAFETY: a short read of field `i`, which the object has (see
        // `ObjectOf::fields`).
        unsafe {
            Some(match k {
                FieldKind::Value => {
                    (*(self.base().add(self.layout.offset(i)) as *const Value)).clone()
                }
                _ => read_word(self.layout, self.base(), i, k),
            })
        }
    }

    /// Field `i` into `slot`, its old value dropped; false when the object
    /// has no such field. Built where it goes (see `vm::put`): a value
    /// returned and copied in is read back before its stores are done.
    ///
    /// # Safety
    /// `slot` holds a live value, is not inside this object, and dropping
    /// its old value cannot free this object.
    #[inline(always)]
    pub unsafe fn field_into(&self, i: usize, slot: *mut Value) -> bool {
        let Some(&k) = self.layout.kinds.get(i) else {
            return false;
        };
        // SAFETY: as the caller promises, and a short read of field `i`.
        unsafe {
            if (*slot).type_tag() as u64 >= NEEDS_DROP_FROM {
                std::ptr::drop_in_place(slot);
            }
            let at = self.base().add(self.layout.offset(i));
            match k {
                FieldKind::Value => Value::clone_into(slot, &*(at as *const Value)),
                FieldKind::Int => match *(at as *const i64) {
                    INT_MARK => slot.write(aside_get(self.layout, self.base(), i)),
                    x => slot.write(Value::Int(x)),
                },
                FieldKind::Float => match *(at as *const u64) {
                    FLOAT_MARK => slot.write(aside_get(self.layout, self.base(), i)),
                    bits => slot.write(Value::Float(f64::from_bits(bits))),
                },
                FieldKind::Bool => match *(at as *const u64) {
                    0 => slot.write(Value::Bool(false)),
                    1 => slot.write(Value::Bool(true)),
                    _ => slot.write(aside_get(self.layout, self.base(), i)),
                },
            }
        }
        true
    }

    /// Field `i` as a value in place, when it is stored as one (to read
    /// without a count).
    #[inline]
    pub fn field_ref(&self, i: usize) -> Option<&Value> {
        if *self.layout.kinds.get(i)? != FieldKind::Value {
            return None;
        }
        // SAFETY: as for `field`; the reference lasts as the caller's
        // operation does (it runs no Quarz code).
        unsafe { Some(&*(self.base().add(self.layout.offset(i)) as *const Value)) }
    }

    /// A copy of the field values.
    pub fn fields(&self) -> Fields {
        (0..self.field_count())
            .map(|i| self.field(i).unwrap_or(Value::Nil))
            .collect()
    }

    /// Store `v` in field `i` (which the object has: it is built with all
    /// of its class's).
    #[inline(always)]
    pub fn set_field(&self, i: usize, v: Value) {
        let Some(&k) = self.layout.kinds.get(i) else {
            no_field(i, self.field_count())
        };
        // SAFETY: a short write of field `i` (see `ObjectOf::fields`); the
        // replaced value is dropped after it.
        unsafe {
            let base = self.base();
            if k == FieldKind::Value {
                let at = base.add(self.layout.offset(i)) as *mut Value;
                let old = std::mem::replace(&mut *at, v);
                drop(old);
            } else {
                store_word(self.layout, base, i, k, v);
            }
        }
    }

    /// Field `i`, leaving nil there (`nil` when absent).
    pub fn take_field(&self, i: usize) -> Value {
        if i >= self.field_count() {
            return Value::Nil;
        }
        // SAFETY: a short write of field `i`.
        unsafe { take_field_at(self.layout, self.base(), i) }
    }

    /// Field `i` in place, to change, when it is stored as a value.
    ///
    /// # Safety
    /// No other reference into the fields may be alive or taken while
    /// this one is (an operation that runs no Quarz code), and the object
    /// is not shared with another thread.
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn field_value_mut(&self, i: usize) -> Option<&mut Value> {
        if *self.layout.kinds.get(i)? != FieldKind::Value {
            return None;
        }
        // SAFETY: as the caller promises.
        unsafe { Some(&mut *(self.base().add(self.layout.offset(i)) as *mut Value)) }
    }

    /// Replace every field (as many as the object has).
    pub fn set_fields(&self, fields: Fields) {
        assert_eq!(
            fields.len(),
            self.field_count(),
            "an object's fields replaced"
        );
        for (i, v) in fields.into_iter().enumerate() {
            self.set_field(i, v);
        }
    }

    /// Whether two objects of one class have equal fields.
    pub fn fields_eq(&self, other: &Object) -> bool {
        self.field_count() == other.field_count()
            && (0..self.field_count()).all(|i| match (self.field_ref(i), other.field_ref(i)) {
                (Some(a), Some(b)) => a == b,
                _ => self.field(i) == other.field(i),
            })
    }

    /// Hash the fields (as `fields_eq` compares them).
    pub fn hash_fields<H: Hasher>(&self, state: &mut H) {
        for i in 0..self.field_count() {
            match self.field_ref(i) {
                Some(v) => v.hash(state),
                None => self.field(i).unwrap_or(Value::Nil).hash(state),
            }
        }
    }

    /// Each value the object holds in place or aside (what it refers to).
    ///
    /// # Safety
    /// The pointers are valid while the object is and is not changed.
    pub unsafe fn value_ptrs(&self, mut f: impl FnMut(*const Value)) {
        // SAFETY: as the caller promises.
        unsafe {
            let base = self.base();
            for (i, k) in self.layout.kinds.iter().enumerate() {
                if *k == FieldKind::Value {
                    f(base.add(self.layout.offset(i)) as *const Value);
                }
            }
            if let Some(a) = self.layout.aside {
                let p = *(base.add(a as usize) as *const *mut Aside);
                if !p.is_null() {
                    for (_, v) in (*p).iter() {
                        f(v as *const Value);
                    }
                }
            }
        }
    }
}

/// Write `v` into word field `i` (of kind `k`) of the object whose
/// fields start at `base`: the word, or its mark with `v` aside.
///
/// # Safety
/// A short write of field `i` (see `ObjectOf::fields`), whose word and
/// aside pointer are initialized.
#[inline(always)]
unsafe fn store_word(layout: &FieldLayout, base: *mut u8, i: usize, k: FieldKind, v: Value) {
    // SAFETY: as the caller promises.
    unsafe {
        let at = base.add(layout.offset(i)) as *mut u64;
        let word = match (k, &v) {
            (FieldKind::Int, Value::Int(x)) if *x != INT_MARK => Some(*x as u64),
            (FieldKind::Float, Value::Float(x)) if x.to_bits() != FLOAT_MARK => Some(x.to_bits()),
            (FieldKind::Bool, Value::Bool(b)) => Some(u64::from(*b)),
            _ => None,
        };
        match word {
            Some(w) => {
                *at = w;
                // (Most objects keep nothing aside.)
                if let Some(a) = layout.aside {
                    if !(*(base.add(a as usize) as *const *mut Aside)).is_null() {
                        aside_set(layout, base, i, Value::Nil);
                    }
                }
            }
            None => {
                *at = mark(k);
                aside_set(layout, base, i, v);
            }
        }
    }
}

/// What field `i` keeps aside (nil when nothing).
#[cold]
#[inline(never)]
fn aside_get(layout: &FieldLayout, base: *mut u8, i: usize) -> Value {
    let Some(a) = layout.aside else {
        return Value::Nil;
    };
    // SAFETY: a short read of the aside pointer and its list.
    unsafe {
        let p = *(base.add(a as usize) as *const *mut Aside);
        if p.is_null() {
            return Value::Nil;
        }
        (*p).iter()
            .find(|(j, _)| *j as usize == i)
            .map(|(_, v)| v.clone())
            .unwrap_or(Value::Nil)
    }
}

/// Keep `v` aside for field `i` (nil: nothing).
///
/// # Safety
/// A short write (see `ObjectOf::fields`) of an initialized aside
/// pointer.
#[cold]
#[inline(never)]
unsafe fn aside_set(layout: &FieldLayout, base: *mut u8, i: usize, v: Value) {
    let Some(a) = layout.aside else {
        return;
    };
    // SAFETY: as the caller promises.
    unsafe {
        let slot = base.add(a as usize) as *mut *mut Aside;
        if (*slot).is_null() {
            if matches!(v, Value::Nil) {
                return;
            }
            *slot = Box::into_raw(Box::default());
        }
        let list = &mut **slot;
        let at = list.iter().position(|(j, _)| *j as usize == i);
        let old = match (at, matches!(v, Value::Nil)) {
            (Some(at), true) => Some(list.swap_remove(at).1),
            (Some(at), false) => Some(std::mem::replace(&mut list[at].1, v)),
            (None, true) => None,
            (None, false) => {
                list.push((i as u32, v));
                None
            }
        };
        drop(old);
    }
}

/// The mark of a word field of kind `k`.
fn mark(k: FieldKind) -> u64 {
    match k {
        FieldKind::Int => INT_MARK as u64,
        FieldKind::Float => FLOAT_MARK,
        _ => BOOL_MARK,
    }
}

#[cold]
fn no_field(i: usize, n: usize) -> ! {
    panic!("field {i} of an object with {n}")
}

/// A block implemented in Rust (used by natives that iterate). It stays
/// `std::rc::Rc`: a trait object needs std's unsized coercion, and such
/// a block never leaves the task that made it (no procedure type is
/// Shareable).
pub type NativeBlock =
    std::rc::Rc<dyn Fn(&crate::interp::Interp, crate::interp::ArgVec) -> crate::interp::EvalResult>;

/// The body a closure runs: a QIR function, a method reference
/// (`&:name`), or a native function.
pub enum ClosureBody {
    Func(FuncId),
    /// `&:name`: call `name` on the first argument. The cache holds the
    /// method found for the last (class, argument count); the method is
    /// the checker's resolution for the parameter's static type (an
    /// extension method is only reachable through it).
    MethodName(
        Rc<str>,
        Cell<Option<(ClassId, usize, MethodId)>>,
        Option<MethodId>,
    ),
    /// `obj.:name`: call `name` on a captured receiver.
    BoundMethod {
        recv: Value,
        name: Rc<str>,
    },
    Native(NativeBlock),
}

impl std::fmt::Debug for ClosureBody {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClosureBody::Func(id) => write!(f, "Func({id})"),
            ClosureBody::MethodName(n, ..) => write!(f, "MethodName({n})"),
            ClosureBody::BoundMethod { name, .. } => write!(f, "BoundMethod({name})"),
            ClosureBody::Native(_) => write!(f, "Native"),
        }
    }
}

/// A block, lambda or procedure value.
#[derive(Debug)]
pub struct Closure {
    pub body: ClosureBody,
    pub frame: Option<Rc<Frame>>,
    pub self_val: Value,
    /// How many parameters a single tuple argument is spread over.
    pub destructure: Option<usize>,
    pub is_lambda: bool,
    /// Identifies the block for `break`.
    pub tag: u64,
    /// The method the block was written in (for `yield` and `return`).
    pub method_block: Option<Value>,
    pub method_tag: u64,
    /// Source file index (for `__FILE__`).
    pub file: u32,
}

#[derive(Debug)]
pub struct RangeVal {
    pub lo: Value,
    pub hi: Value,
    pub exclusive: bool,
}

#[derive(Debug)]
pub struct RegexpVal {
    pub regex: regex::Regex,
    pub source: String,
    pub flags: String,
}

#[derive(Debug)]
pub struct MatchDataVal {
    pub text: Rc<str>,
    /// Byte ranges of the whole match and the groups.
    pub groups: Vec<Option<(usize, usize)>>,
    pub names: Vec<(String, usize)>,
}

/// A lazily evaluated enumerator: re-invokes `method` on `recv` with a
/// block.
#[derive(Debug)]
pub struct EnumeratorVal {
    pub recv: Value,
    pub method: Rc<str>,
    pub args: Vec<Value>,
    /// The elements, collected at the first `next` or `peek`. (Not
    /// Shareable: an enumerator stays in its task.)
    buffer: RefCell<Option<Vec<Value>>>,
    position: Cell<usize>,
}

impl EnumeratorVal {
    pub fn new(recv: Value, method: Rc<str>, args: Vec<Value>) -> EnumeratorVal {
        EnumeratorVal {
            recv,
            method,
            args,
            buffer: RefCell::new(None),
            position: Cell::new(0),
        }
    }

    /// Whether the elements have been collected.
    pub fn is_buffered(&self) -> bool {
        self.buffer.borrow().is_some()
    }

    /// Keep the collected elements for `next`.
    pub fn fill(&self, items: Vec<Value>) {
        *self.buffer.borrow_mut() = Some(items);
    }

    /// The element at the position (moving past it when `advance`), or
    /// `None` at the end.
    pub fn current(&self, advance: bool) -> Option<Value> {
        let pos = self.position.get();
        let v = self.buffer.borrow().as_ref()?.get(pos)?.clone();
        if advance {
            self.position.set(pos + 1);
        }
        Some(v)
    }

    /// Back to the start, collecting the elements again at the next use.
    pub fn rewind(&self) {
        self.position.set(0);
        *self.buffer.borrow_mut() = None;
    }

    /// Call `f` on each buffered element (for `Value::share`).
    fn each_buffered(&self, f: impl FnMut(&Value)) {
        if let Some(xs) = &*self.buffer.borrow() {
            xs.iter().for_each(f);
        }
    }
}

#[derive(Debug)]
pub enum IoKind {
    Stdin,
    Stdout,
    Stderr,
    /// An open file (`File.open`).
    File(IoCell<FileHandle>),
    /// A connected stream socket (TCP or Unix), non-blocking, driven by
    /// the scheduler's reactor.
    Socket(IoCell<SocketState>),
    /// A listening socket (`TCPServer`, `UNIXServer`).
    Listener(IoCell<ListenerState>),
    Udp(IoCell<UdpState>),
}

#[derive(Debug)]
pub enum Stream {
    Tcp(std::net::TcpStream),
    Unix(std::os::unix::net::UnixStream),
}

impl Stream {
    pub fn fd(&self) -> std::os::fd::RawFd {
        use std::os::fd::AsRawFd;
        match self {
            Stream::Tcp(s) => s.as_raw_fd(),
            Stream::Unix(s) => s.as_raw_fd(),
        }
    }
}

impl std::io::Read for Stream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self {
            Stream::Tcp(s) => s.read(buf),
            Stream::Unix(s) => s.read(buf),
        }
    }
}

impl std::io::Write for Stream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            Stream::Tcp(s) => s.write(buf),
            Stream::Unix(s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            Stream::Tcp(s) => s.flush(),
            Stream::Unix(s) => s.flush(),
        }
    }
}

/// The state of an IO handle, which tasks on any worker may use: behind a
/// lock that, like the `RefCell` it replaces, is only held for an
/// operation that does not wait (a task releases it before it parks).
/// Taking it twice on one thread is a bug, and panics rather than
/// deadlocking.
pub struct IoCell<T> {
    lock: std::sync::Mutex<T>,
    /// The thread holding it (see `thread_mark`), 0 when none.
    holder: std::sync::atomic::AtomicUsize,
}

pub struct IoGuard<'a, T> {
    guard: std::sync::MutexGuard<'a, T>,
    holder: &'a std::sync::atomic::AtomicUsize,
}

/// A number that tells the current thread from the others.
fn thread_mark() -> usize {
    thread_local! { static MARK: u8 = const { 0 }; }
    MARK.with(|m| m as *const u8 as usize)
}

impl<T> IoCell<T> {
    pub fn new(value: T) -> IoCell<T> {
        IoCell {
            lock: std::sync::Mutex::new(value),
            holder: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    pub fn borrow(&self) -> IoGuard<'_, T> {
        use std::sync::atomic::Ordering;
        let me = thread_mark();
        assert!(
            self.holder.load(Ordering::Relaxed) != me,
            "an IO handle's state taken twice"
        );
        let guard = crate::sched::lock(&self.lock);
        self.holder.store(me, Ordering::Relaxed);
        IoGuard {
            guard,
            holder: &self.holder,
        }
    }

    pub fn borrow_mut(&self) -> IoGuard<'_, T> {
        self.borrow()
    }
}

impl<T> std::ops::Deref for IoGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.guard
    }
}

impl<T> std::ops::DerefMut for IoGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.guard
    }
}

impl<T> Drop for IoGuard<'_, T> {
    fn drop(&mut self) {
        self.holder.store(0, std::sync::atomic::Ordering::Relaxed);
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for IoCell<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("IoCell(..)")
    }
}

/// What waiting on a descriptor needs besides its number: a serial that
/// tells it from an earlier descriptor with the same number (a worker
/// registers a descriptor with its poller when one of its tasks first
/// waits on it), and the tasks waiting on it, on any worker, which
/// closing it wakes.
#[derive(Debug)]
pub struct IoWatch {
    pub serial: u64,
    pub waiters: Vec<crate::sched::TaskRef>,
}

impl IoWatch {
    pub fn new() -> IoWatch {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        IoWatch {
            serial: NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            waiters: Vec::new(),
        }
    }
}

impl Default for IoWatch {
    fn default() -> IoWatch {
        IoWatch::new()
    }
}

/// An IO state with a descriptor tasks wait on.
pub trait Watched {
    fn watch(&mut self) -> &mut IoWatch;
}

impl Watched for SocketState {
    fn watch(&mut self) -> &mut IoWatch {
        &mut self.watch
    }
}

impl Watched for ListenerState {
    fn watch(&mut self) -> &mut IoWatch {
        &mut self.watch
    }
}

impl Watched for UdpState {
    fn watch(&mut self) -> &mut IoWatch {
        &mut self.watch
    }
}

#[derive(Debug)]
pub struct SocketState {
    /// `None` once closed: the descriptor is released at `close`, not
    /// when the value is dropped.
    pub stream: Option<Stream>,
    pub unix: bool,
    /// Bytes read from the socket but not yet consumed.
    pub rbuf: Vec<u8>,
    pub eof: bool,
    pub closed: bool,
    /// The path of a Unix socket.
    pub path: Option<String>,
    /// The addresses as of the connection (valid after the peer hangs
    /// up, when the system no longer reports them).
    pub local: Option<std::net::SocketAddr>,
    pub peer: Option<std::net::SocketAddr>,
    /// A task is in the middle of a write: one call goes out whole, and
    /// the other writers wait here for their turn.
    pub writing: bool,
    pub write_waiters: std::collections::VecDeque<crate::sched::TaskRef>,
    pub watch: IoWatch,
}

#[derive(Debug)]
pub enum Listener {
    Tcp(std::net::TcpListener),
    Unix(std::os::unix::net::UnixListener),
}

impl Listener {
    pub fn fd(&self) -> std::os::fd::RawFd {
        use std::os::fd::AsRawFd;
        match self {
            Listener::Tcp(l) => l.as_raw_fd(),
            Listener::Unix(l) => l.as_raw_fd(),
        }
    }
}

#[derive(Debug)]
pub struct ListenerState {
    pub listener: Option<Listener>,
    pub unix: bool,
    pub closed: bool,
    pub path: Option<String>,
    pub watch: IoWatch,
}

#[derive(Debug)]
pub struct UdpState {
    pub socket: Option<std::net::UdpSocket>,
    pub closed: bool,
    pub watch: IoWatch,
}

/// The state of an open file: a buffered reader or writer over it.
#[derive(Debug, Default)]
pub struct FileHandle {
    pub path: String,
    /// The buffered descriptors, shared with the helper thread that runs
    /// an operation needing a system call (the calling task waits, the
    /// others run; see `natives::io`).
    pub io: std::sync::Arc<std::sync::Mutex<FileIo>>,
    pub readable: bool,
    pub writable: bool,
    pub closed: bool,
}

#[derive(Debug, Default)]
pub struct FileIo {
    pub reader: Option<std::io::BufReader<std::fs::File>>,
    pub writer: Option<std::io::BufWriter<std::fs::File>>,
}

#[derive(Debug)]
pub struct IoVal {
    pub kind: IoKind,
}

/// A non-local flow caught by an `ensure` handler, carried through the
/// handler's body and continued by `Resume`.
pub type FlowBox = RefCell<Option<Flow>>;

/// The layout is fixed (`repr(u8)`: a tag byte, then the payload, at
/// the next byte for a short string and at the next word for the rest) so
/// that compiled code can build and test values inline. Two words: every
/// heap payload is a one-word `Rc`. The variants without reference
/// counting come first; see `NEEDS_DROP_FROM`.
#[derive(Clone, Debug)]
#[repr(u8)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    Symbol(Symbol),
    Class(ClassId),
    /// Nanoseconds.
    Duration(i64),
    /// A string of at most 14 bytes, kept in the value itself.
    Short(ShortStr),
    BigInt(Rc<BigInt>),
    /// A longer string.
    Str(Rc<str>),
    Array(Rc<ArrayData>),
    Hash(Rc<HashData>),
    Set(Rc<ValueSet>),
    Range(Rc<RangeVal>),
    Regexp(Rc<RegexpVal>),
    MatchData(Rc<MatchDataVal>),
    Object(Rc<Object>),
    Proc(Rc<Closure>),
    ArrayBuilder(Rc<RefCell<Vec<Value>>>),
    HashBuilder(Rc<RefCell<ValueMap>>),
    SetBuilder(Rc<RefCell<ValueSet>>),
    StringBuilder(Rc<RefCell<String>>),
    Channel(Rc<ChannelInner>),
    Task(Rc<TaskHandle>),
    Scope(Rc<ScopeInner>),
    Atom(Rc<std::sync::Mutex<Value>>),
    Selector(Rc<RefCell<SelectorState>>),
    Enumerator(Rc<EnumeratorVal>),
    Io(Rc<IoVal>),
    Bytes(Rc<[u8]>),
    BytesBuilder(Rc<RefCell<Vec<u8>>>),
    Time(Rc<TimeVal>),
    Random(Rc<RefCell<RandomState>>),
    /// Internal: a flow in transit through an `ensure` handler.
    Flow(Rc<FlowBox>),
}

/// A pseudo-random generator (xoshiro256**), seeded with splitmix64.
#[derive(Clone, Debug)]
pub struct RandomState {
    pub seed: i64,
    s: [u64; 4],
}

impl RandomState {
    pub fn new(seed: i64) -> RandomState {
        let mut x = seed as u64;
        let mut s = [0u64; 4];
        for word in &mut s {
            x = x.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            *word = z ^ (z >> 31);
        }
        RandomState { seed, s }
    }

    pub fn next_u64(&mut self) -> u64 {
        let s = &mut self.s;
        let result = s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = s[3].rotate_left(45);
        result
    }

    /// A float in `[0, 1)`.
    pub fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }

    /// An integer in `[0, bound)` without modulo bias.
    pub fn below(&mut self, bound: u64) -> u64 {
        let zone = u64::MAX - u64::MAX % bound;
        loop {
            let x = self.next_u64();
            if x < zone {
                return x % bound;
            }
        }
    }
}

/// Tags below this hold no reference-counted payload.
pub const NEEDS_DROP_FROM: u64 = 8;

/// A string short enough to live in a value's payload: its length,
/// then the bytes (valid UTF-8).
#[derive(Clone, Copy)]
#[repr(C)]
pub struct ShortStr {
    len: u8,
    bytes: [u8; ShortStr::MAX],
}

impl ShortStr {
    pub const MAX: usize = 14;

    pub fn new(s: &str) -> Option<ShortStr> {
        if s.len() > ShortStr::MAX {
            return None;
        }
        let mut bytes = [0u8; ShortStr::MAX];
        bytes[..s.len()].copy_from_slice(s.as_bytes());
        Some(ShortStr {
            len: s.len() as u8,
            bytes,
        })
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: built from a `str`, so the bytes are UTF-8.
        unsafe { std::str::from_utf8_unchecked(&self.bytes[..self.len as usize]) }
    }
}

impl ShortStr {
    pub fn make_ascii_uppercase(&mut self) {
        let n = self.len as usize;
        self.bytes[..n].make_ascii_uppercase();
    }

    pub fn make_ascii_lowercase(&mut self) {
        let n = self.len as usize;
        self.bytes[..n].make_ascii_lowercase();
    }
}

/// Write `i` in decimal into `buf`, returning the text (two digits at
/// a time; `fmt` is several times slower).
pub fn format_int(buf: &mut [u8; 20], i: i64) -> &str {
    const DIGITS: &[u8; 200] = b"0001020304050607080910111213141516171819\
2021222324252627282930313233343536373839\
4041424344454647484950515253545556575859\
6061626364656667686970717273747576777879\
8081828384858687888990919293949596979899";
    let mut n = i.unsigned_abs();
    let mut pos = buf.len();
    while n >= 100 {
        let d = (n % 100) as usize * 2;
        n /= 100;
        pos -= 2;
        buf[pos] = DIGITS[d];
        buf[pos + 1] = DIGITS[d + 1];
    }
    if n >= 10 {
        let d = n as usize * 2;
        pos -= 2;
        buf[pos] = DIGITS[d];
        buf[pos + 1] = DIGITS[d + 1];
    } else {
        pos -= 1;
        buf[pos] = b'0' + n as u8;
    }
    if i < 0 {
        pos -= 1;
        buf[pos] = b'-';
    }
    // SAFETY: only ASCII digits and '-' were written.
    unsafe { std::str::from_utf8_unchecked(&buf[pos..]) }
}

impl std::ops::Deref for ShortStr {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl std::fmt::Debug for ShortStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl Value {
    /// A copy that skips the reference count machinery for values that
    /// have none.
    #[inline]
    pub fn fast_clone(&self) -> Value {
        if (self.type_tag() as u64) < NEEDS_DROP_FROM {
            // SAFETY: the variant holds no heap payload, so a bitwise
            // copy is a complete value.
            unsafe { std::ptr::read(self) }
        } else {
            self.clone()
        }
    }

    /// `*dst = *src` without a temporary: a plain copy for values without
    /// a reference count.
    ///
    /// # Safety
    /// `dst` must point to writable space holding no live value.
    #[inline]
    pub unsafe fn clone_into(dst: *mut Value, src: &Value) {
        if (src.type_tag() as u64) < NEEDS_DROP_FROM {
            std::ptr::copy_nonoverlapping(src as *const Value, dst, 1);
        } else {
            std::ptr::write(dst, src.clone());
        }
    }

    /// Drop a value, skipping the destructor for those that need none.
    #[inline]
    pub fn fast_drop(self) {
        if (self.type_tag() as u64) < NEEDS_DROP_FROM {
            std::mem::forget(self);
        }
    }
}

/// A value that any thread may hold: it is marked shared when wrapped
/// (`Value::share`), so its counts are updated atomically, and nothing
/// changes what it refers to (what is Shareable is immutable, and a
/// value that is not, such as an `at_exit` block, is only used by one
/// thread at a time).
pub struct SharedValue(Value);

// SAFETY: as said above; see `rc.rs`.
unsafe impl Send for SharedValue {}
unsafe impl Sync for SharedValue {}

impl SharedValue {
    pub fn new(v: Value) -> SharedValue {
        v.share();
        SharedValue(v)
    }

    /// A value that lives as long as the program (see `rc::IMMORTAL`).
    pub fn immortal(v: Value) -> SharedValue {
        v.make_immortal();
        SharedValue(v)
    }

    pub fn get(&self) -> &Value {
        &self.0
    }

    pub fn into_inner(self) -> Value {
        self.0
    }
}

impl Clone for SharedValue {
    fn clone(&self) -> SharedValue {
        SharedValue(self.0.clone())
    }
}

impl std::fmt::Debug for SharedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Mark one allocation shared or immortal; whether it was not yet.
fn mark_rc<T: ?Sized + crate::rc::Target>(immortal: bool, r: &Rc<T>) -> bool {
    if immortal {
        Rc::make_immortal(r)
    } else {
        Rc::mark_shared(r)
    }
}

/// What `Value::share` has still to mark.
enum ShareItem {
    Value(*const Value),
    Frame(*const Frame),
}

impl Value {
    /// Mark the value and everything it refers to shared, before it
    /// becomes reachable from another task (and so, under an M:N
    /// scheduler, another thread): their counts are then updated
    /// atomically (see `rc.rs`). The walk stops at what is shared
    /// already, whose contents are shared too.
    ///
    /// The checker lets only Shareable values cross, but a `spawn`
    /// block's copied frames also hold the variables it does not capture,
    /// whatever their type: those are marked as well, so that their counts
    /// stay sound when the other task releases them (it never reads them).
    pub fn share(&self) {
        self.mark(false)
    }

    /// Mark the value and everything it refers to immortal (see
    /// `rc::IMMORTAL`): for what lives as long as the program, used by
    /// every worker at once (a constant's value, the top level's `self`).
    pub fn make_immortal(&self) {
        self.mark(true)
    }

    fn mark(&self, immortal: bool) {
        // An explicit worklist: a long list of `data` values would
        // overflow the native stack.
        let mut work = vec![ShareItem::Value(self as *const Value)];
        while let Some(item) = work.pop() {
            // SAFETY: every pointer is into a value that `self` keeps
            // alive, and nothing changes while the walk runs (it reads
            // the contents of `RefCell`s without borrowing them, as no
            // borrow can be in progress across this call).
            unsafe {
                let v = match item {
                    ShareItem::Value(v) => &*v,
                    ShareItem::Frame(f) => {
                        let f = &*f;
                        for s in f.slots().iter() {
                            work.push(ShareItem::Value(s));
                        }
                        if let Some(p) = &f.parent {
                            if mark_rc(immortal, p) {
                                work.push(ShareItem::Frame(Rc::as_ptr(p)));
                            }
                        }
                        continue;
                    }
                };
                let push = |work: &mut Vec<ShareItem>, v: &Value| work.push(ShareItem::Value(v));
                match v {
                    Value::Nil
                    | Value::Bool(_)
                    | Value::Int(_)
                    | Value::Float(_)
                    | Value::Symbol(_)
                    | Value::Class(_)
                    | Value::Duration(_)
                    | Value::Short(_) => {}
                    Value::BigInt(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Str(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Regexp(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Bytes(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Time(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Random(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::StringBuilder(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::BytesBuilder(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Array(r) => {
                        if mark_rc(immortal, r) {
                            if let ArrayData::Values(xs) = &**r {
                                xs.iter().for_each(|x| push(&mut work, x));
                            }
                        }
                    }
                    Value::Hash(r) => {
                        if mark_rc(immortal, r) {
                            if let HashData::Values(m) = &**r {
                                for (k, x) in m {
                                    push(&mut work, k);
                                    push(&mut work, x);
                                }
                            }
                        }
                    }
                    Value::Set(r) => {
                        if mark_rc(immortal, r) {
                            r.iter().for_each(|x| push(&mut work, x));
                        }
                    }
                    Value::Range(r) => {
                        if mark_rc(immortal, r) {
                            push(&mut work, &r.lo);
                            push(&mut work, &r.hi);
                        }
                    }
                    Value::MatchData(r) => {
                        if mark_rc(immortal, r) {
                            mark_rc(immortal, &r.text);
                        }
                    }
                    Value::Object(r) => {
                        if mark_rc(immortal, r) {
                            r.value_ptrs(|x| work.push(ShareItem::Value(x)));
                            if let Some(e) = r.exc_info() {
                                if let Some(b) = &e.backtrace {
                                    mark_rc(immortal, b);
                                }
                                if let Some(c) = &e.cause {
                                    push(&mut work, c);
                                }
                            }
                        }
                    }
                    Value::Proc(r) => {
                        if mark_rc(immortal, r) {
                            match &r.body {
                                ClosureBody::Func(_) | ClosureBody::Native(_) => {}
                                ClosureBody::MethodName(name, _, _) => {
                                    mark_rc(immortal, name);
                                }
                                ClosureBody::BoundMethod { recv, name } => {
                                    push(&mut work, recv);
                                    mark_rc(immortal, name);
                                }
                            }
                            if let Some(f) = &r.frame {
                                if mark_rc(immortal, f) {
                                    work.push(ShareItem::Frame(Rc::as_ptr(f)));
                                }
                            }
                            push(&mut work, &r.self_val);
                            if let Some(b) = &r.method_block {
                                push(&mut work, b);
                            }
                        }
                    }
                    Value::ArrayBuilder(r) => {
                        if mark_rc(immortal, r) {
                            (*r.as_ptr()).iter().for_each(|x| push(&mut work, x));
                        }
                    }
                    Value::HashBuilder(r) => {
                        if mark_rc(immortal, r) {
                            for (k, x) in (*r.as_ptr()).iter() {
                                push(&mut work, k);
                                push(&mut work, x);
                            }
                        }
                    }
                    Value::SetBuilder(r) => {
                        if mark_rc(immortal, r) {
                            (*r.as_ptr()).iter().for_each(|x| push(&mut work, x));
                        }
                    }
                    Value::Enumerator(r) => {
                        if mark_rc(immortal, r) {
                            push(&mut work, &r.recv);
                            mark_rc(immortal, &r.method);
                            r.args.iter().for_each(|x| push(&mut work, x));
                            // The vector stays put while the walk runs.
                            r.each_buffered(|x| push(&mut work, x));
                        }
                    }
                    // Made shared when created (`Rc::new_shared`), and
                    // their contents when they enter; a selector or a flow
                    // in transit never crosses.
                    Value::Channel(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Atom(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Task(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Scope(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Io(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Selector(r) => {
                        mark_rc(immortal, r);
                    }
                    Value::Flow(r) => {
                        mark_rc(immortal, r);
                    }
                }
            }
        }
    }
}

/// Compiled code bumps and lowers reference counts inline, assuming the
/// layout of `Rc`'s allocation: the strong count is its first word
/// (`rc.rs` fixes it at compile time). This checks it once at start-up,
/// through a value, together with the tags and offsets compiled code uses.
pub fn check_rc_layout() {
    let a: Rc<str> = Rc::from("layout");
    let value = Value::Str(a.clone());
    // The payload's first word is the pointer `Rc` keeps: the allocation.
    let strong_of = |v: &Value| -> usize {
        // SAFETY: `Value` is `repr(u8)`: the tag, then the payload at the
        // next word.
        unsafe {
            let words = v as *const Value as *const usize;
            let allocation = *words.add(1) as *const usize;
            *allocation
        }
    };
    assert_eq!(
        strong_of(&value),
        2,
        "Rc layout changed: the strong count must come first"
    );
    // The tags compiled code tests for, and the field view's place.
    assert_eq!(
        Value::Class(0).type_tag(),
        5,
        "Value layout changed: Class tag"
    );
    let object = Value::Object(Object::new(0, Fields::new()));
    assert_eq!(object.type_tag(), 16, "Value layout changed: Object tag");
    // A payload smaller than a word follows the tag (`repr(u8)`).
    let t = Value::Bool(true);
    let c = Value::Class(0x0102_0304);
    // SAFETY: the bytes read are the payloads.
    unsafe {
        let t = &t as *const Value as *const u8;
        assert_eq!(*t.add(1), 1, "Value layout changed: Bool");
        let c = &c as *const Value as *const u8;
        assert_eq!(
            c.add(4).cast::<u32>().read(),
            0x0102_0304,
            "Value layout changed: Class"
        );
    }
    let short = Value::str("short");
    assert_eq!(short.type_tag(), 7, "Value layout changed: Short tag");
    assert!(
        (short.type_tag() as u64) < NEEDS_DROP_FROM,
        "a short string must need no release"
    );
    assert_eq!(std::mem::offset_of!(Object, layout), 0);
    assert_eq!(std::mem::offset_of!(FieldLayout, offsets), 0);
    assert_eq!(std::mem::size_of::<Value>(), quarz_ir::VALUE_BYTES as usize);
    assert_eq!(std::mem::offset_of!(Frame, slots_ptr), 0);
    assert_eq!(std::mem::offset_of!(Frame, nslots), 8);
    assert_eq!(std::mem::offset_of!(Frame, parent_ptr), 16);
    let b = a.clone();
    assert_eq!(
        strong_of(&value),
        3,
        "Rc layout changed: the strong count must come first"
    );
    drop(b);
    assert_eq!(
        strong_of(&value),
        2,
        "Rc layout changed: the strong count must come first"
    );
}

/// Size of a value in bytes, as compiled code lays out its registers.
pub const VALUE_SIZE: usize = 16;

const _: () = assert!(std::mem::size_of::<Value>() == VALUE_SIZE);

/// A point in time: nanoseconds since the Unix epoch and the UTC offset
/// it is displayed in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TimeVal {
    pub ns: i64,
    /// Seconds east of UTC.
    pub offset: i32,
    /// Displayed as UTC (`Time.utc`, `Time#utc`).
    pub utc: bool,
}

impl Value {
    /// A string value: in the value itself when short, shared on the
    /// heap otherwise.
    pub fn str(s: &str) -> Value {
        match ShortStr::new(s) {
            Some(short) => Value::Short(short),
            None => Value::Str(Rc::from(s)),
        }
    }

    /// A string value from a shared string (kept shared when long).
    pub fn str_rc(s: Rc<str>) -> Value {
        match ShortStr::new(&s) {
            Some(short) => Value::Short(short),
            None => Value::Str(s),
        }
    }

    pub fn string(s: String) -> Value {
        match ShortStr::new(&s) {
            Some(short) => Value::Short(short),
            None => Value::Str(Rc::from(s)),
        }
    }

    /// A string built by `f` in a reused buffer: one allocation (the
    /// `Rc<str>`), none for the buffer. Reentrant (a nested build gets a
    /// fresh buffer).
    pub fn build_string(f: impl FnOnce(&mut String)) -> Value {
        Value::with_scratch(|buf| {
            f(buf);
            Value::str(buf.as_str())
        })
    }

    /// Run `f` on an empty, reused buffer (reentrant: a nested call gets
    /// a fresh one).
    pub fn with_scratch<R>(f: impl FnOnce(&mut String) -> R) -> R {
        thread_local! {
            static SCRATCH: RefCell<String> = const { RefCell::new(String::new()) };
        }
        let mut buf = SCRATCH.with(|s| std::mem::take(&mut *s.borrow_mut()));
        buf.clear();
        let r = f(&mut buf);
        if buf.capacity() <= 1 << 16 {
            SCRATCH.with(|s| *s.borrow_mut() = buf);
        }
        r
    }

    pub fn array(items: Vec<Value>) -> Value {
        if items.is_empty() {
            return Value::empty_array();
        }
        Value::Array(Rc::new(ArrayData::from_values(items)))
    }

    /// The empty array: one immortal allocation for the whole program
    /// (an append copies it, as it does any shared array).
    pub fn empty_array() -> Value {
        EMPTY_ARRAY
            .get_or_init(|| {
                SharedValue::immortal(Value::Array(Rc::new(ArrayData::Values(Vec::new()))))
            })
            .get()
            .clone()
    }

    pub fn ints(items: Vec<i64>) -> Value {
        Value::Array(Rc::new(ArrayData::Ints(items)))
    }

    pub fn floats(items: Vec<f64>) -> Value {
        Value::Array(Rc::new(ArrayData::Floats(items)))
    }

    pub fn bytes(bytes: Vec<u8>) -> Value {
        Value::Bytes(Rc::from(bytes))
    }

    pub fn is_truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, Value::Nil)
    }

    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(i) => Some(*i),
            _ => None,
        }
    }

    /// The text of a string value (short or long).
    #[inline]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::Short(s) => Some(s.as_str()),
            Value::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn is_str(&self) -> bool {
        matches!(self, Value::Short(_) | Value::Str(_))
    }

    /// The discriminant (the first byte of the `repr(u8)` layout).
    pub fn type_tag(&self) -> u8 {
        // SAFETY: `Value` is `repr(u8)`, so it starts with its tag.
        unsafe { *(self as *const Value as *const u8) }
    }

    /// Identity comparison (`equal?`): values without a heap payload are
    /// identical when equal, the others when they share the allocation.
    pub fn identical(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a.to_bits() == b.to_bits(),
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::Class(a), Value::Class(b)) => a == b,
            (Value::Duration(a), Value::Duration(b)) => a == b,
            (Value::BigInt(a), Value::BigInt(b)) => Rc::ptr_eq(a, b) || a == b,
            (Value::Str(a), Value::Str(b)) => Rc::ptr_eq(a, b) || a == b,
            (Value::Short(a), Value::Short(b)) => a.as_str() == b.as_str(),
            (Value::Str(a), Value::Short(b)) | (Value::Short(b), Value::Str(a)) => {
                **a == *b.as_str()
            }
            (Value::Array(a), Value::Array(b)) => Rc::ptr_eq(a, b),
            (Value::Hash(a), Value::Hash(b)) => Rc::ptr_eq(a, b),
            (Value::Set(a), Value::Set(b)) => Rc::ptr_eq(a, b),
            (Value::Range(a), Value::Range(b)) => Rc::ptr_eq(a, b),
            (Value::Regexp(a), Value::Regexp(b)) => Rc::ptr_eq(a, b),
            (Value::MatchData(a), Value::MatchData(b)) => Rc::ptr_eq(a, b),
            (Value::Object(a), Value::Object(b)) => Rc::ptr_eq(a, b),
            (Value::Proc(a), Value::Proc(b)) => Rc::ptr_eq(a, b),
            (Value::ArrayBuilder(a), Value::ArrayBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::HashBuilder(a), Value::HashBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::SetBuilder(a), Value::SetBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::StringBuilder(a), Value::StringBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::Channel(a), Value::Channel(b)) => Rc::ptr_eq(a, b),
            (Value::Task(a), Value::Task(b)) => Rc::ptr_eq(a, b),
            (Value::Scope(a), Value::Scope(b)) => Rc::ptr_eq(a, b),
            (Value::Atom(a), Value::Atom(b)) => Rc::ptr_eq(a, b),
            (Value::Selector(a), Value::Selector(b)) => Rc::ptr_eq(a, b),
            (Value::Enumerator(a), Value::Enumerator(b)) => Rc::ptr_eq(a, b),
            (Value::Io(a), Value::Io(b)) => Rc::ptr_eq(a, b),
            (Value::Bytes(a), Value::Bytes(b)) => Rc::ptr_eq(a, b) || a == b,
            (Value::BytesBuilder(a), Value::BytesBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::Time(a), Value::Time(b)) => a.ns == b.ns,
            (Value::Random(a), Value::Random(b)) => Rc::ptr_eq(a, b),
            (Value::Flow(a), Value::Flow(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

/// Structural equality for immutable values (used for hash keys and as the
/// default `==`). Mutable objects compare by identity; data types and enum
/// variants compare field-wise.
impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => {
                (*a as f64) == *b
            }
            (Value::Int(a), Value::BigInt(b)) | (Value::BigInt(b), Value::Int(a)) => {
                **b == BigInt::from(*a)
            }
            (Value::BigInt(a), Value::BigInt(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Short(a), Value::Short(b)) => a.as_str() == b.as_str(),
            (Value::Str(a), Value::Short(b)) | (Value::Short(b), Value::Str(a)) => {
                **a == *b.as_str()
            }
            (Value::Array(a), Value::Array(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y)
            }
            (Value::Hash(a), Value::Hash(b)) => match (&**a, &**b) {
                (HashData::Ints(x), HashData::Ints(y)) => {
                    x.len() == y.len() && x.iter().all(|(k, v)| y.get(k) == Some(v))
                }
                _ => {
                    let (a, b) = (a.as_map(), b.as_map());
                    a.len() == b.len() && a.iter().all(|(k, v)| b.get(k).is_some_and(|w| w == v))
                }
            },
            (Value::Set(a), Value::Set(b)) => a.len() == b.len() && a.iter().all(|x| b.contains(x)),
            (Value::Range(a), Value::Range(b)) => {
                a.lo == b.lo && a.hi == b.hi && a.exclusive == b.exclusive
            }
            (Value::Regexp(a), Value::Regexp(b)) => a.source == b.source && a.flags == b.flags,
            (Value::Object(a), Value::Object(b)) => {
                if Rc::ptr_eq(a, b) {
                    return true;
                }
                // Data-like objects (no mutable fields) compare structurally.
                // The interpreter decides which classes are structural by
                // the `structural` flag kept on the object.
                a.class == b.class && is_structural(a) && a.fields_eq(b)
            }
            _ => self.identical(other),
        }
    }
}

impl Eq for Value {}

thread_local! {
    /// Classes whose instances compare and hash structurally (data types,
    /// enum variants). Set up by the interpreter.
    pub static STRUCTURAL_CLASSES: RefCell<Vec<bool>> = const { RefCell::new(Vec::new()) };
}

pub fn is_structural(obj: &Object) -> bool {
    STRUCTURAL_CLASSES.with(|s| s.borrow().get(obj.class as usize).copied().unwrap_or(false))
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Nil => 0u8.hash(state),
            Value::Bool(b) => b.hash(state),
            // Numbers that are equal hash the same (`1 == 1.0`): an
            // integral value hashes as the integer it is, which keeps
            // the common Int key a plain integer hash.
            Value::Int(i) => {
                2u8.hash(state);
                i.hash(state);
            }
            Value::BigInt(b) => {
                2u8.hash(state);
                match i64::try_from(&**b) {
                    Ok(i) => i.hash(state),
                    Err(_) => b.hash(state),
                }
            }
            Value::Float(f) => {
                2u8.hash(state);
                if f.fract() == 0.0 && f.abs() < 9.2e18 {
                    (*f as i64).hash(state);
                } else {
                    f.to_bits().hash(state);
                }
            }
            Value::Str(s) => {
                4u8.hash(state);
                (**s).hash(state);
            }
            Value::Short(s) => {
                4u8.hash(state);
                s.as_str().hash(state);
            }
            Value::Symbol(s) => {
                5u8.hash(state);
                s.hash(state);
            }
            Value::Array(a) => {
                6u8.hash(state);
                a.len().hash(state);
                for x in a.iter() {
                    x.hash(state);
                }
            }
            Value::Hash(h) => {
                7u8.hash(state);
                h.len().hash(state);
            }
            Value::Set(s) => {
                8u8.hash(state);
                s.len().hash(state);
            }
            Value::Range(r) => {
                9u8.hash(state);
                r.lo.hash(state);
                r.hi.hash(state);
            }
            Value::Object(o) => {
                12u8.hash(state);
                o.class.hash(state);
                if is_structural(o) {
                    o.hash_fields(state);
                } else {
                    (Rc::as_ptr(o).cast::<u8>() as usize).hash(state);
                }
            }
            Value::Class(c) => {
                13u8.hash(state);
                c.hash(state);
            }
            Value::Duration(d) => {
                24u8.hash(state);
                d.hash(state);
            }
            Value::Bytes(b) => {
                27u8.hash(state);
                b.hash(state);
            }
            Value::Time(t) => {
                29u8.hash(state);
                t.ns.hash(state);
            }
            other => {
                other.type_tag().hash(state);
                // Identity for the rest.
                match other {
                    Value::Proc(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::ArrayBuilder(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::HashBuilder(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::StringBuilder(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::Channel(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::Task(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::Atom(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::BytesBuilder(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::Random(p) => (Rc::as_ptr(p) as usize).hash(state),
                    _ => {}
                }
            }
        }
    }
}

/// An `Integer` (of any size): always a `BigInt`, small or not, so that
/// it is told from an `Int` (its class, its methods).
pub fn integer(b: BigInt) -> Value {
    Value::BigInt(Rc::new(b))
}

/// `b` as an `Int`, if it fits.
pub fn fit_int(b: &BigInt) -> Option<Value> {
    use num_traits::ToPrimitive;
    b.to_i64().map(Value::Int)
}
