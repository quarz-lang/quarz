//! The heap side of the 8-byte value: a reference-counted box with a
//! kind byte in its header, and thin strings and byte strings (their
//! length in the header, the bytes after it). Compiled code bumps and
//! lowers the counts inline and reads the kind, through the offsets
//! `layout` exports.

use std::alloc::{alloc, dealloc, Layout};
use std::cell::{Cell, RefCell};
use std::ptr::NonNull;
use std::rc::Rc;

use num_bigint::BigInt;

use crate::sched::{ChannelInner, ScopeInner, SelectorState, TaskHandle};
use crate::value::{
    ArrayData, Closure, EnumeratorVal, FlowBox, IoVal, MatchDataVal, Object, RandomState, RangeVal,
    RegexpVal, TimeVal, Value, ValueMap, ValueSet,
};

/// What a heap box holds (its header's kind byte).
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// An `Int` that does not fit the 63-bit immediate.
    Int = 1,
    /// A `Float` that is not a flonum.
    Float = 2,
    /// A `Duration` that does not fit the 62-bit immediate.
    Duration = 3,
    BigInt = 4,
    Str = 5,
    Bytes = 6,
    Array = 7,
    Hash = 8,
    Set = 9,
    Range = 10,
    Regexp = 11,
    MatchData = 12,
    Object = 13,
    Proc = 14,
    ArrayBuilder = 15,
    HashBuilder = 16,
    SetBuilder = 17,
    StringBuilder = 18,
    Channel = 19,
    Task = 20,
    Scope = 21,
    Atom = 22,
    Selector = 23,
    Enumerator = 24,
    Io = 25,
    BytesBuilder = 26,
    Time = 27,
    Random = 28,
    Flow = 29,
}

/// The first two words of every heap box: the reference count and the
/// kind (compiled code reads both).
#[repr(C, align(16))]
pub struct Header {
    pub strong: Cell<usize>,
    pub kind: Kind,
    _pad: [u8; 7],
}

/// A boxed `T`: the header, then the value (at `VALUE_OFF`).
#[repr(C, align(16))]
pub struct HeapBox<T> {
    pub header: Header,
    pub value: T,
}

/// Byte offset of the value in a heap box.
pub const VALUE_OFF: usize = 16;
pub const KIND_OFF: usize = 8;

/// A type that lives in a heap box, with its kind, and the bit its
/// word carries above the alignment bits (boxes are 16-byte aligned:
/// an `Object`'s word has bit 3 set, so that compiled code tells an
/// object from the other heap values without reading its header).
pub trait Boxed: Sized {
    const KIND: Kind;
    const TAG: u64 = 0;
}

/// The word bit of an `Object`.
pub const OBJECT_TAG: u64 = 8;
/// Clears the tag bits of a heap word: the box's address.
pub const ADDR_MASK: u64 = !0xF;

/// A big duration, boxed.
#[derive(Clone, Copy, Debug)]
pub struct Dur(pub i64);

macro_rules! boxed {
    ($($t:ty => $k:ident),* $(,)?) => {
        $(impl Boxed for $t { const KIND: Kind = Kind::$k; })*
    };
}

impl Boxed for Object {
    const KIND: Kind = Kind::Object;
    const TAG: u64 = OBJECT_TAG;
}

boxed! {
    i64 => Int,
    f64 => Float,
    Dur => Duration,
    BigInt => BigInt,
    ArrayData => Array,
    ValueMap => Hash,
    ValueSet => Set,
    RangeVal => Range,
    RegexpVal => Regexp,
    MatchDataVal => MatchData,
    Closure => Proc,
    RefCell<Vec<Value>> => ArrayBuilder,
    RefCell<ValueMap> => HashBuilder,
    RefCell<ValueSet> => SetBuilder,
    RefCell<String> => StringBuilder,
    Rc<ChannelInner> => Channel,
    Rc<TaskHandle> => Task,
    Rc<ScopeInner> => Scope,
    RefCell<Value> => Atom,
    RefCell<SelectorState> => Selector,
    EnumeratorVal => Enumerator,
    IoVal => Io,
    RefCell<Vec<u8>> => BytesBuilder,
    TimeVal => Time,
    RefCell<RandomState> => Random,
    FlowBox => Flow,
}

/// A shared, reference-counted `T` on the heap (what `Rc<T>` was, with
/// the kind in the header and no weak count).
#[repr(transparent)]
pub struct Heap<T: Boxed>(NonNull<HeapBox<T>>);

impl<T: Boxed> Heap<T> {
    pub fn new(value: T) -> Heap<T> {
        let b = Box::new(HeapBox {
            header: Header {
                strong: Cell::new(1),
                kind: T::KIND,
                _pad: [0; 7],
            },
            value,
        });
        let addr = Box::into_raw(b) as u64;
        // SAFETY: a box is never null.
        Heap(unsafe { NonNull::new_unchecked((addr | T::TAG) as *mut HeapBox<T>) })
    }

    /// The box.
    #[inline]
    fn raw(&self) -> *mut HeapBox<T> {
        ((self.0.as_ptr() as u64) & !T::TAG) as *mut HeapBox<T>
    }

    #[inline]
    fn header(&self) -> &Header {
        // SAFETY: the pointer is valid while this handle lives.
        unsafe { &(*self.raw()).header }
    }

    pub fn ptr_eq(a: &Heap<T>, b: &Heap<T>) -> bool {
        a.0 == b.0
    }

    pub fn as_ptr(this: &Heap<T>) -> *const T {
        // SAFETY: as in `header`.
        unsafe { std::ptr::addr_of!((*this.raw()).value) }
    }

    pub fn strong_count(this: &Heap<T>) -> usize {
        this.header().strong.get()
    }

    pub fn get_mut(this: &mut Heap<T>) -> Option<&mut T> {
        if this.header().strong.get() == 1 {
            // SAFETY: the only reference.
            Some(unsafe { &mut (*this.raw()).value })
        } else {
            None
        }
    }

    /// The value, cloned first when it is shared.
    pub fn make_mut(this: &mut Heap<T>) -> &mut T
    where
        T: Clone,
    {
        if this.header().strong.get() != 1 {
            *this = Heap::new((**this).clone());
        }
        // SAFETY: unique now.
        unsafe { &mut (*this.raw()).value }
    }

    /// The word a value holds for this box.
    #[inline]
    pub fn into_bits(this: Heap<T>) -> u64 {
        let bits = this.0.as_ptr() as u64;
        std::mem::forget(this);
        bits
    }

    /// # Safety
    /// `bits` must be the address of a live box of `T` whose count this
    /// handle takes over.
    #[inline]
    pub unsafe fn from_bits(bits: u64) -> Heap<T> {
        Heap(NonNull::new_unchecked(bits as *mut HeapBox<T>))
    }
}

impl<T: Boxed> Clone for Heap<T> {
    #[inline]
    fn clone(&self) -> Heap<T> {
        let h = self.header();
        h.strong.set(h.strong.get() + 1);
        Heap(self.0)
    }
}

impl<T: Boxed> Drop for Heap<T> {
    #[inline]
    fn drop(&mut self) {
        let h = self.header();
        let n = h.strong.get();
        if n > 1 {
            h.strong.set(n - 1);
        } else {
            // SAFETY: the last reference: the box goes back to the
            // allocator (it was a `Box`).
            unsafe { drop(Box::from_raw(self.raw())) };
        }
    }
}

impl<T: Boxed> std::ops::Deref for Heap<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: as in `header`.
        unsafe { &(*self.raw()).value }
    }
}

impl<T: Boxed + std::fmt::Debug> std::fmt::Debug for Heap<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: Boxed + PartialEq> PartialEq for Heap<T> {
    fn eq(&self, other: &Heap<T>) -> bool {
        Heap::ptr_eq(self, other) || **self == **other
    }
}

impl<T: Boxed + Eq> Eq for Heap<T> {}

impl<T: Boxed + std::hash::Hash> std::hash::Hash for Heap<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<T: Boxed> From<T> for Heap<T> {
    fn from(value: T) -> Heap<T> {
        Heap::new(value)
    }
}

impl<T: Boxed> From<&Heap<T>> for Heap<T> {
    fn from(h: &Heap<T>) -> Heap<T> {
        h.clone()
    }
}

/// The header of a string or byte string box: the length, then the
/// bytes.
#[repr(C, align(16))]
pub struct BytesHeader {
    pub header: Header,
    pub len: usize,
}

const BYTES_OFF: usize = std::mem::size_of::<BytesHeader>();

fn bytes_layout(len: usize) -> Layout {
    Layout::from_size_align(BYTES_OFF + len, 16).expect("string layout")
}

unsafe fn alloc_bytes(kind: Kind, bytes: &[u8]) -> NonNull<BytesHeader> {
    let layout = bytes_layout(bytes.len());
    let p = alloc(layout) as *mut BytesHeader;
    let Some(p) = NonNull::new(p) else {
        std::alloc::handle_alloc_error(layout)
    };
    std::ptr::write(
        p.as_ptr(),
        BytesHeader {
            header: Header {
                strong: Cell::new(1),
                kind,
                _pad: [0; 7],
            },
            len: bytes.len(),
        },
    );
    std::ptr::copy_nonoverlapping(
        bytes.as_ptr(),
        (p.as_ptr() as *mut u8).add(BYTES_OFF),
        bytes.len(),
    );
    p
}

#[inline]
unsafe fn bytes_of<'a>(p: NonNull<BytesHeader>) -> &'a [u8] {
    let len = (*p.as_ptr()).len;
    std::slice::from_raw_parts((p.as_ptr() as *const u8).add(BYTES_OFF), len)
}

/// Release the last reference of a string or byte string box.
unsafe fn free_bytes(p: NonNull<BytesHeader>) {
    let len = (*p.as_ptr()).len;
    dealloc(p.as_ptr() as *mut u8, bytes_layout(len));
}

/// A shared string on the heap, one allocation, a thin pointer.
#[repr(transparent)]
pub struct HeapStr(NonNull<BytesHeader>);

impl HeapStr {
    pub fn new(s: &str) -> HeapStr {
        // SAFETY: `alloc_bytes` builds a complete box.
        HeapStr(unsafe { alloc_bytes(Kind::Str, s.as_bytes()) })
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: built from a `str`.
        unsafe { std::str::from_utf8_unchecked(bytes_of(self.0)) }
    }

    pub fn ptr_eq(a: &HeapStr, b: &HeapStr) -> bool {
        a.0 == b.0
    }

    #[inline]
    pub fn into_bits(this: HeapStr) -> u64 {
        let bits = this.0.as_ptr() as u64;
        std::mem::forget(this);
        bits
    }

    /// # Safety
    /// As for `Heap::from_bits`.
    #[inline]
    pub unsafe fn from_bits(bits: u64) -> HeapStr {
        HeapStr(NonNull::new_unchecked(bits as *mut BytesHeader))
    }
}

impl Clone for HeapStr {
    #[inline]
    fn clone(&self) -> HeapStr {
        // SAFETY: valid while this handle lives.
        let h = unsafe { &(*self.0.as_ptr()).header };
        h.strong.set(h.strong.get() + 1);
        HeapStr(self.0)
    }
}

impl Drop for HeapStr {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: valid while this handle lives.
        let h = unsafe { &(*self.0.as_ptr()).header };
        let n = h.strong.get();
        if n > 1 {
            h.strong.set(n - 1);
        } else {
            // SAFETY: the last reference.
            unsafe { free_bytes(self.0) };
        }
    }
}

impl std::ops::Deref for HeapStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl std::fmt::Debug for HeapStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_str().fmt(f)
    }
}

impl std::fmt::Display for HeapStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_str().fmt(f)
    }
}

impl PartialEq for HeapStr {
    fn eq(&self, other: &HeapStr) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for HeapStr {}

impl PartialEq<str> for HeapStr {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl From<&str> for HeapStr {
    fn from(s: &str) -> HeapStr {
        HeapStr::new(s)
    }
}

impl From<String> for HeapStr {
    fn from(s: String) -> HeapStr {
        HeapStr::new(&s)
    }
}

impl From<&String> for HeapStr {
    fn from(s: &String) -> HeapStr {
        HeapStr::new(s)
    }
}

impl From<Rc<str>> for HeapStr {
    fn from(s: Rc<str>) -> HeapStr {
        HeapStr::new(&s)
    }
}

impl From<&Rc<str>> for HeapStr {
    fn from(s: &Rc<str>) -> HeapStr {
        HeapStr::new(s)
    }
}

/// A shared byte string on the heap (as `HeapStr`).
#[repr(transparent)]
pub struct HeapBytes(NonNull<BytesHeader>);

impl HeapBytes {
    pub fn new(b: &[u8]) -> HeapBytes {
        // SAFETY: `alloc_bytes` builds a complete box.
        HeapBytes(unsafe { alloc_bytes(Kind::Bytes, b) })
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: valid while this handle lives.
        unsafe { bytes_of(self.0) }
    }

    pub fn ptr_eq(a: &HeapBytes, b: &HeapBytes) -> bool {
        a.0 == b.0
    }

    #[inline]
    pub fn into_bits(this: HeapBytes) -> u64 {
        let bits = this.0.as_ptr() as u64;
        std::mem::forget(this);
        bits
    }

    /// # Safety
    /// As for `Heap::from_bits`.
    #[inline]
    pub unsafe fn from_bits(bits: u64) -> HeapBytes {
        HeapBytes(NonNull::new_unchecked(bits as *mut BytesHeader))
    }
}

impl Clone for HeapBytes {
    #[inline]
    fn clone(&self) -> HeapBytes {
        // SAFETY: valid while this handle lives.
        let h = unsafe { &(*self.0.as_ptr()).header };
        h.strong.set(h.strong.get() + 1);
        HeapBytes(self.0)
    }
}

impl Drop for HeapBytes {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: valid while this handle lives.
        let h = unsafe { &(*self.0.as_ptr()).header };
        let n = h.strong.get();
        if n > 1 {
            h.strong.set(n - 1);
        } else {
            // SAFETY: the last reference.
            unsafe { free_bytes(self.0) };
        }
    }
}

impl std::ops::Deref for HeapBytes {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl std::fmt::Debug for HeapBytes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl PartialEq for HeapBytes {
    fn eq(&self, other: &HeapBytes) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Eq for HeapBytes {}

impl From<&[u8]> for HeapBytes {
    fn from(b: &[u8]) -> HeapBytes {
        HeapBytes::new(b)
    }
}

impl From<Vec<u8>> for HeapBytes {
    fn from(b: Vec<u8>) -> HeapBytes {
        HeapBytes::new(&b)
    }
}

impl From<Rc<[u8]>> for HeapBytes {
    fn from(b: Rc<[u8]>) -> HeapBytes {
        HeapBytes::new(&b)
    }
}

/// The kind of the box at `bits`.
///
/// # Safety
/// `bits` must be the address of a live heap box.
#[inline]
pub unsafe fn kind_of(bits: u64) -> Kind {
    (*((bits & ADDR_MASK) as *const Header)).kind
}

/// Release one reference to the box at `bits`, freeing it when it was
/// the last.
///
/// # Safety
/// As for `kind_of`; the caller gives up its reference.
pub unsafe fn release(bits: u64) {
    let addr = bits & ADDR_MASK;
    let h = &*(addr as *const Header);
    let n = h.strong.get();
    if n > 1 {
        h.strong.set(n - 1);
        return;
    }
    // The last one: run the destructor of what the box holds.
    macro_rules! free {
        ($t:ty) => {
            drop(Box::from_raw(addr as *mut HeapBox<$t>))
        };
    }
    match h.kind {
        Kind::Int => free!(i64),
        Kind::Float => free!(f64),
        Kind::Duration => free!(Dur),
        Kind::BigInt => free!(BigInt),
        Kind::Str | Kind::Bytes => free_bytes(NonNull::new_unchecked(addr as *mut BytesHeader)),
        Kind::Array => free!(ArrayData),
        Kind::Hash => free!(ValueMap),
        Kind::Set => free!(ValueSet),
        Kind::Range => free!(RangeVal),
        Kind::Regexp => free!(RegexpVal),
        Kind::MatchData => free!(MatchDataVal),
        Kind::Object => free!(Object),
        Kind::Proc => free!(Closure),
        Kind::ArrayBuilder => free!(RefCell<Vec<Value>>),
        Kind::HashBuilder => free!(RefCell<ValueMap>),
        Kind::SetBuilder => free!(RefCell<ValueSet>),
        Kind::StringBuilder => free!(RefCell<String>),
        Kind::Channel => free!(Rc<ChannelInner>),
        Kind::Task => free!(Rc<TaskHandle>),
        Kind::Scope => free!(Rc<ScopeInner>),
        Kind::Atom => free!(RefCell<Value>),
        Kind::Selector => free!(RefCell<SelectorState>),
        Kind::Enumerator => free!(EnumeratorVal),
        Kind::Io => free!(IoVal),
        Kind::BytesBuilder => free!(RefCell<Vec<u8>>),
        Kind::Time => free!(TimeVal),
        Kind::Random => free!(RefCell<RandomState>),
        Kind::Flow => free!(FlowBox),
    }
}

/// Add one reference to the box at `bits`.
///
/// # Safety
/// As for `kind_of`.
#[inline]
pub unsafe fn retain(bits: u64) {
    let h = &*((bits & ADDR_MASK) as *const Header);
    h.strong.set(h.strong.get() + 1);
}
