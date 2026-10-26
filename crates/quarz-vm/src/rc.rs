//! The reference count of every heap value: `std::rc::Rc`'s layout and
//! behaviour, in a type of the runtime's own.
//!
//! Values are to be shared between the threads of an M:N scheduler: a
//! value that crosses from one task to another (a channel message, what
//! `spawn` captures, an `Atom`'s content, a task's result, a constant)
//! is marked shared (`Value::share`), and only a shared value's count is
//! updated atomically (as in Lean 4; docs/04-concurrency.md §7). The
//! values confined to a task, nearly all of them, keep plain counts.
//!
//! The allocation is laid out as `std::rc::Rc`'s was, which compiled
//! code reads and updates inline (checked below at compile time): two
//! words, then the value.
//! - A local allocation (reachable from one thread only) keeps its count
//!   in the first word, updated with plain loads and stores, and in the
//!   second (where std kept its weak count; there are no weak references)
//!   1, or, for a candidate of the cycle collector, its place in this
//!   thread's list of them (`crate::cycles`: an even word, which only the
//!   runtime reads).
//! - A shared one has 0 in the first word, which no count ever is, and
//!   its count in the second, updated atomically.
//!
//! A reference is one word, the address of the counts, whatever the
//! value: an unsized value finds its length in the allocation (see
//! `Target`), so that a `Value` holding one is two words.
//!
//! So compiled code reads only the first word: it bumps a count that is
//! not 0 and lowers one above 1 inline, and calls the runtime for the
//! rest (a shared count, or the last reference); a count of 1 means a
//! unique, local value, which an update may change in place. The runtime
//! makes a shared value local again when it finds itself holding the only
//! reference (`get_mut`, `make_mut`).
//!
//! What makes the plain accesses sound:
//! - A local allocation is reachable from one thread only: every
//!   allocation reachable from a shared one is shared too (`share` marks
//!   a whole value before it crosses, and stops at what is shared
//!   already). So a local count is never touched by another thread.
//! - The first word of a shared allocation stays 0 while another thread
//!   holds a reference (it is set before the value crosses, and changed
//!   only by the thread holding the only reference), so reading it is no
//!   race, and a thread that finds it 0 updates the second word
//!   atomically, as every other thread does.

use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::borrow::Borrow;
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::Deref;
use std::ptr::NonNull;
use std::sync::atomic::{fence, AtomicUsize, Ordering as AtomicOrdering};

/// The first word of a shared allocation.
pub const SHARED: usize = 0;

/// A shared count at or above this is an immortal allocation's: one that
/// lives as long as the program (a constant's value, the top level's
/// `self`), whose count is not updated, so that threads using it at once
/// only read the cache line it is on. (`make_immortal` sets it to
/// `IMMORTAL * 2`, far enough from the bound for updates that race with
/// it.)
pub const IMMORTAL: usize = 1 << 61;

/// The allocation: the two words, then the value.
#[repr(C)]
pub struct Inner<T: ?Sized> {
    /// A local allocation's count, or `SHARED` (see the module comment).
    pub(crate) local: Cell<usize>,
    /// A shared allocation's count (atomic), or 1.
    pub(crate) shared: Cell<usize>,
    pub(crate) value: T,
}

impl<T: ?Sized> Inner<T> {
    #[inline(always)]
    fn is_shared(&self) -> bool {
        self.local.get() == SHARED
    }

    /// A shared allocation's count, updated atomically.
    #[inline(always)]
    fn shared_count(&self) -> &AtomicUsize {
        // SAFETY: `AtomicUsize` has the layout of `usize`; while the
        // allocation is shared, this word is only accessed atomically
        // (see the module comment).
        unsafe { AtomicUsize::from_ptr(self.shared.as_ptr()) }
    }

    /// Whether this is the only reference; a shared allocation found so
    /// is made local again (no other thread can reach it any more).
    #[inline]
    fn take_unique(&self) -> bool {
        match self.local.get() {
            1 => true,
            // Acquire: the other threads' last uses happen before what
            // this thread does with the value now. (The second word is
            // then 1, as a local allocation's is.)
            SHARED if self.shared_count().load(AtomicOrdering::Acquire) == 1 => {
                self.local.set(1);
                true
            }
            _ => false,
        }
    }
}

// What compiled code assumes (`quarz-aot`'s `gen.rs`): the first word at
// 0, the second at 8, the value at 16.
const _: () = {
    type ObjectHeader = crate::value::ObjectOf<std::cell::UnsafeCell<[u64; 0]>>;
    assert!(std::mem::offset_of!(Inner<ObjectHeader>, local) == 0);
    assert!(std::mem::offset_of!(Inner<ObjectHeader>, shared) == 8);
    assert!(std::mem::offset_of!(Inner<ObjectHeader>, value) == 16);
    assert!(std::mem::offset_of!(Inner<crate::value::ArrayData>, value) == 16);
};

/// What an `Rc` can refer to: how to find the allocation's `Inner`
/// from the address of its counts, which is all a reference keeps. A
/// sized value needs nothing more; an unsized one keeps its length in
/// the allocation (a string's or byte string's in the word before the
/// counts, an object's in its layout).
///
/// # Safety
/// `inner` gives back the `Inner` the allocation was made with, and
/// `PREFIX` is how many bytes the allocation has before the counts.
pub unsafe trait Target {
    const PREFIX: usize = 0;

    /// # Safety
    /// `p` is the address of a live allocation's counts.
    unsafe fn inner(p: *mut u8) -> *mut Inner<Self>;
}

// SAFETY: a sized value's `Inner` starts at the counts.
unsafe impl<T> Target for T {
    #[inline(always)]
    unsafe fn inner(p: *mut u8) -> *mut Inner<T> {
        p.cast()
    }
}

// SAFETY: made by `Rc::from_bytes`, the length in the word before.
unsafe impl Target for [u8] {
    const PREFIX: usize = 8;

    #[inline(always)]
    unsafe fn inner(p: *mut u8) -> *mut Inner<[u8]> {
        // SAFETY: as the caller promises.
        let len = unsafe { *p.cast::<usize>().sub(1) };
        std::ptr::slice_from_raw_parts_mut(p, len) as *mut Inner<[u8]>
    }
}

// SAFETY: as `[u8]`, of which a string is the bytes.
unsafe impl Target for str {
    const PREFIX: usize = 8;

    #[inline(always)]
    unsafe fn inner(p: *mut u8) -> *mut Inner<str> {
        // SAFETY: as the caller promises.
        unsafe { <[u8] as Target>::inner(p) as *mut Inner<str> }
    }
}

/// A counted reference to a heap value (see the module comment).
pub struct Rc<T: ?Sized + Target> {
    /// The allocation's counts.
    ptr: NonNull<u8>,
    _owns: PhantomData<Inner<T>>,
}

impl<T> Rc<T> {
    #[inline]
    pub fn new(value: T) -> Rc<T> {
        let inner = Box::new(Inner {
            local: Cell::new(1),
            shared: Cell::new(1),
            value,
        });
        Rc {
            // SAFETY: `Box::into_raw` never returns null.
            ptr: unsafe { NonNull::new_unchecked(Box::into_raw(inner).cast()) },
            _owns: PhantomData,
        }
    }
}

impl<T> Rc<T> {
    /// An allocation shared from the start: a channel, task, scope, atom
    /// or IO handle, which several tasks reach by design. What enters it
    /// later is marked when it does (`Value::share`).
    #[inline]
    pub fn new_shared(value: T) -> Rc<T> {
        let rc = Rc::new(value);
        Rc::mark_shared(&rc);
        rc
    }
}

impl<T> Rc<MaybeUninit<T>> {
    /// An allocation whose value the caller writes (through `get_mut`)
    /// before `assume_init`.
    #[inline]
    pub fn new_uninit() -> Rc<MaybeUninit<T>> {
        Rc::new(MaybeUninit::uninit())
    }

    /// # Safety
    /// The value has been fully written.
    #[inline]
    pub unsafe fn assume_init(self) -> Rc<T> {
        let ptr = self.ptr;
        std::mem::forget(self);
        // `MaybeUninit<T>` has the layout of `T`, so `Inner` keeps its own.
        Rc {
            ptr,
            _owns: PhantomData,
        }
    }
}

impl<T: ?Sized + Target> Rc<T> {
    /// The first reference to an allocation the caller made (with the
    /// global allocator, in the layout of `Inner<T>`) and whose value it
    /// wrote: the counts are set here.
    ///
    /// # Safety
    /// As said; nothing else refers to the allocation.
    pub(crate) unsafe fn from_fresh(ptr: *mut Inner<T>) -> Rc<T> {
        // Nothing here writes what comes before the counts.
        debug_assert_eq!(T::PREFIX, 0);
        // SAFETY: as the caller promises.
        unsafe {
            (&raw mut (*ptr).local).write(Cell::new(1));
            (&raw mut (*ptr).shared).write(Cell::new(1));
            Rc {
                ptr: NonNull::new_unchecked(ptr.cast()),
                _owns: PhantomData,
            }
        }
    }

    #[inline(always)]
    fn inner_ptr(&self) -> *mut Inner<T> {
        // SAFETY: the allocation lives while a reference does.
        unsafe { T::inner(self.ptr.as_ptr()) }
    }

    #[inline(always)]
    fn inner(&self) -> &Inner<T> {
        // SAFETY: the allocation lives while a reference does.
        unsafe { &*self.inner_ptr() }
    }

    /// Whether both point at the same allocation.
    #[inline]
    pub fn ptr_eq(a: &Rc<T>, b: &Rc<T>) -> bool {
        a.ptr == b.ptr
    }

    /// The address of the value.
    #[inline]
    pub fn as_ptr(this: &Rc<T>) -> *const T {
        // SAFETY: a field of a live allocation.
        unsafe { &raw const (*this.inner_ptr()).value }
    }

    /// The value, when this is its only reference.
    #[inline]
    pub fn get_mut(this: &mut Rc<T>) -> Option<&mut T> {
        if this.inner().take_unique() {
            // SAFETY: the only reference, borrowed mutably.
            Some(unsafe { &mut (*this.inner_ptr()).value })
        } else {
            None
        }
    }

    pub fn strong_count(this: &Rc<T>) -> usize {
        let inner = this.inner();
        if inner.is_shared() {
            inner.shared_count().load(AtomicOrdering::Relaxed)
        } else {
            inner.local.get()
        }
    }

    /// Whether other threads may hold the allocation.
    #[inline]
    pub fn is_shared(this: &Rc<T>) -> bool {
        this.inner().is_shared()
    }

    /// Mark the allocation shared, before it becomes reachable from
    /// another thread. Returns whether it was local: the caller then
    /// marks what it refers to (`Value::share`), and need not when it was
    /// shared already.
    #[inline]
    pub fn mark_shared(this: &Rc<T>) -> bool {
        let inner = this.inner();
        if inner.is_shared() {
            return false;
        }
        // A shared allocation is no candidate of this thread's collector.
        crate::cycles::forget(inner.shared.get());
        // A local allocation is reachable from this thread only: plain
        // stores, published by whatever hands the value over.
        inner.shared.set(inner.local.get());
        inner.local.set(SHARED);
        true
    }

    /// Make the allocation immortal (see `IMMORTAL`), shared if it was
    /// local. Returns whether it was not immortal yet: the caller then
    /// makes what it refers to immortal too (`Value::make_immortal`).
    pub fn make_immortal(this: &Rc<T>) -> bool {
        let inner = this.inner();
        if !inner.is_shared() {
            crate::cycles::forget(inner.shared.get());
            inner.shared.set(IMMORTAL * 2);
            inner.local.set(SHARED);
            return true;
        }
        let count = inner.shared_count();
        if count.load(AtomicOrdering::Relaxed) >= IMMORTAL {
            return false;
        }
        // Other threads may update the count meanwhile: whatever they do
        // leaves it far above `IMMORTAL`, and this reference keeps it
        // alive until then.
        count.store(IMMORTAL * 2, AtomicOrdering::Relaxed);
        true
    }

    /// The allocation's layout, for freeing it.
    fn layout(&self) -> Layout {
        let value = Layout::for_value(self.inner());
        Layout::from_size_align(T::PREFIX + value.size(), value.align()).unwrap()
    }
}

/// The cycle collector's access to allocations by address (the address
/// of their counts, `Rc::addr`): a candidate is listed by its address,
/// with no count of its own.
impl<T: ?Sized + Target> Rc<T> {
    /// The address of the allocation's counts.
    #[inline(always)]
    pub(crate) fn addr(this: &Rc<T>) -> usize {
        this.ptr.as_ptr() as usize
    }

    /// The value of the allocation at `addr`.
    ///
    /// # Safety
    /// `addr` is the address of a live allocation of a `T`, which outlives
    /// the reference.
    #[inline(always)]
    pub(crate) unsafe fn value_at<'a>(addr: usize) -> &'a T {
        // SAFETY: as the caller promises.
        unsafe { &(*T::inner(addr as *mut u8)).value }
    }

    /// A new reference to the allocation at `addr` (its count goes up).
    ///
    /// # Safety
    /// As for `value_at`, and the allocation is local.
    pub(crate) unsafe fn clone_at(addr: usize) -> Rc<T> {
        // SAFETY: as the caller promises.
        let inner = unsafe { &*T::inner(addr as *mut u8) };
        debug_assert!(!inner.is_shared());
        inner.local.set(inner.local.get() + 1);
        Rc {
            // SAFETY: the address of a live allocation is not null.
            ptr: unsafe { NonNull::new_unchecked(addr as *mut u8) },
            _owns: PhantomData,
        }
    }
}

/// The two words of the allocation at `addr` (of any value).
///
/// # Safety
/// `addr` is the address of a live allocation's counts.
#[inline(always)]
pub(crate) unsafe fn counts_at<'a>(addr: usize) -> (&'a Cell<usize>, &'a Cell<usize>) {
    // SAFETY: as the caller promises; the counts are the first two
    // words of every allocation (`Inner` is `repr(C)`).
    unsafe {
        let inner = &*(addr as *const Inner<()>);
        (&inner.local, &inner.shared)
    }
}

impl<T: Clone> Rc<T> {
    /// The value to update: in place when this is its only reference,
    /// else a copy this then refers to.
    #[inline]
    pub fn make_mut(this: &mut Rc<T>) -> &mut T {
        if !this.inner().take_unique() {
            *this = Rc::new((**this).clone());
        }
        // SAFETY: the only reference now, borrowed mutably.
        unsafe { &mut (*this.inner_ptr()).value }
    }
}

impl<T: ?Sized + Target> Clone for Rc<T> {
    #[inline]
    fn clone(&self) -> Rc<T> {
        let inner = self.inner();
        let n = inner.local.get();
        if n != SHARED {
            inner.local.set(n + 1);
        } else {
            // Relaxed, as in `std::sync::Arc`: a new reference comes from
            // an existing one, which keeps the allocation alive.
            let count = inner.shared_count();
            if count.load(AtomicOrdering::Relaxed) < IMMORTAL {
                count.fetch_add(1, AtomicOrdering::Relaxed);
            }
        }
        Rc {
            ptr: self.ptr,
            _owns: PhantomData,
        }
    }
}

impl<T: ?Sized + Target> Drop for Rc<T> {
    #[inline]
    fn drop(&mut self) {
        let inner = self.inner();
        let n = inner.local.get();
        if n > 1 {
            inner.local.set(n - 1);
        } else if n == 1 {
            // SAFETY: the last reference: drop the value, then free the
            // allocation (there are no weak references).
            unsafe { self.drop_slow() };
        } else if inner.shared_count().load(AtomicOrdering::Relaxed) >= IMMORTAL {
            // Immortal: never freed.
        } else if inner.shared_count().fetch_sub(1, AtomicOrdering::Release) == 1 {
            // As in `std::sync::Arc`: every other thread's use of the
            // value happens before it is dropped.
            fence(AtomicOrdering::Acquire);
            // SAFETY: the last reference, as above.
            unsafe { self.drop_slow() };
        }
    }
}

impl<T: ?Sized + Target> Rc<T> {
    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        let layout = self.layout();
        let inner = self.inner();
        if !inner.is_shared() {
            // Out of the cycle collector's candidates first: what the
            // value's drop runs may start a collection.
            crate::cycles::forget(inner.shared.get());
        }
        // SAFETY: the caller holds the last reference.
        unsafe {
            std::ptr::drop_in_place(&raw mut (*self.inner_ptr()).value);
            dealloc(self.ptr.as_ptr().sub(T::PREFIX), layout);
        }
    }
}

impl<T: ?Sized + Target> Deref for Rc<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner().value
    }
}

impl<T: ?Sized + Target> AsRef<T> for Rc<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: ?Sized + Target> Borrow<T> for Rc<T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl From<&str> for Rc<str> {
    fn from(s: &str) -> Rc<str> {
        let bytes: Rc<[u8]> = Rc::from_bytes(s.as_bytes());
        let ptr = bytes.ptr;
        std::mem::forget(bytes);
        // The allocation holds valid UTF-8; `str` and `[u8]` have the
        // same layout and are found the same way.
        Rc {
            ptr,
            _owns: PhantomData,
        }
    }
}

impl From<String> for Rc<str> {
    fn from(s: String) -> Rc<str> {
        Rc::from(s.as_str())
    }
}

impl From<&String> for Rc<str> {
    fn from(s: &String) -> Rc<str> {
        Rc::from(s.as_str())
    }
}

impl From<Box<str>> for Rc<str> {
    fn from(s: Box<str>) -> Rc<str> {
        Rc::from(&*s)
    }
}

impl From<&[u8]> for Rc<[u8]> {
    fn from(bytes: &[u8]) -> Rc<[u8]> {
        Rc::from_bytes(bytes)
    }
}

impl From<Vec<u8>> for Rc<[u8]> {
    fn from(bytes: Vec<u8>) -> Rc<[u8]> {
        Rc::from_bytes(&bytes)
    }
}

impl<T> From<T> for Rc<T> {
    fn from(value: T) -> Rc<T> {
        Rc::new(value)
    }
}

impl Rc<[u8]> {
    /// The length, then the counts, then the bytes (see `Target`).
    fn from_bytes(bytes: &[u8]) -> Rc<[u8]> {
        let (inner, offset) = Layout::new::<Inner<()>>()
            .extend(Layout::array::<u8>(bytes.len()).expect("string too large"))
            .expect("string too large");
        let layout = Layout::from_size_align(
            <[u8] as Target>::PREFIX + inner.pad_to_align().size(),
            inner.align(),
        )
        .expect("string too large");
        // SAFETY: the layout is not zero-sized (it has the counts); the
        // memory is initialized before the reference is made.
        unsafe {
            let mem = alloc(layout);
            if mem.is_null() {
                handle_alloc_error(layout);
            }
            mem.cast::<usize>().write(bytes.len());
            let counts = mem.add(<[u8] as Target>::PREFIX);
            let inner = <[u8] as Target>::inner(counts);
            (&raw mut (*inner).local).write(Cell::new(1));
            (&raw mut (*inner).shared).write(Cell::new(1));
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), counts.add(offset), bytes.len());
            Rc {
                ptr: NonNull::new_unchecked(counts),
                _owns: PhantomData,
            }
        }
    }
}

impl<T: ?Sized + Target + fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + Target + fmt::Display> fmt::Display for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + Target + PartialEq> PartialEq for Rc<T> {
    fn eq(&self, other: &Rc<T>) -> bool {
        **self == **other
    }
}

impl<T: ?Sized + Target + Eq> Eq for Rc<T> {}

impl<T: ?Sized + Target + PartialOrd> PartialOrd for Rc<T> {
    fn partial_cmp(&self, other: &Rc<T>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + Target + Ord> Ord for Rc<T> {
    fn cmp(&self, other: &Rc<T>) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + Target + Hash> Hash for Rc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<T: Default> Default for Rc<T> {
    fn default() -> Rc<T> {
        Rc::new(T::default())
    }
}

/// A reference to a shared allocation, which may move to another thread
/// (a task handle placed on another worker).
pub struct SendRc<T: ?Sized + Target>(Rc<T>);

// SAFETY: the allocation is shared (checked when wrapped): its count is
// updated atomically, and what is reachable from it is shared too.
unsafe impl<T: ?Sized + Target> Send for SendRc<T> {}
unsafe impl<T: ?Sized + Target> Sync for SendRc<T> {}

impl<T: ?Sized + Target> SendRc<T> {
    pub fn new(rc: Rc<T>) -> SendRc<T> {
        assert!(
            Rc::is_shared(&rc),
            "only a shared allocation crosses threads"
        );
        SendRc(rc)
    }

    pub fn into_inner(self) -> Rc<T> {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{ArrayData, Value};

    /// A value moved to another thread, as the M:N scheduler is to move
    /// shared values.
    struct Crossing(Value);
    // SAFETY: the value is marked shared before it crosses.
    unsafe impl Send for Crossing {}

    #[test]
    fn shared_counts_across_threads() {
        let long = Value::str("a string longer than fifteen bytes");
        let inner = Value::array(vec![long, Value::Int(1)]);
        let outer = Value::array(vec![inner, Value::Nil]);
        outer.share();
        let Value::Array(a) = &outer else {
            unreachable!()
        };
        assert!(Rc::is_shared(a));
        let ArrayData::Values(xs) = &**a else {
            unreachable!()
        };
        let Value::Array(i) = &xs[0] else {
            unreachable!()
        };
        assert!(Rc::is_shared(i), "contents are marked too");
        let threads: Vec<_> = (0..4)
            .map(|_| {
                let c = Crossing(outer.clone());
                std::thread::spawn(move || {
                    let c = c;
                    for _ in 0..100_000 {
                        drop(c.0.clone());
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        let Value::Array(mut a) = outer else {
            unreachable!()
        };
        assert_eq!(Rc::strong_count(&a), 1);
        // The only reference again: local, and updated in place.
        assert!(Rc::get_mut(&mut a).is_some());
        assert!(!Rc::is_shared(&a));
    }
}
