//! The reference count of every heap value: `std::rc::Rc`'s layout and
//! behaviour, in a type of the runtime's own.
//!
//! Values are to be shared between the threads of an M:N scheduler: a
//! value that crosses from one task to another (a channel message, what
//! `spawn` captures, an `Atom`'s content, a task's result, a constant)
//! will be marked shared, and only a shared value's count will be
//! updated atomically (as in Lean 4; docs/04-concurrency.md §7). That
//! needs a count the runtime controls, which `std::rc::Rc` is not. For
//! now the count is the plain one.
//!
//! The allocation is laid out as `std::rc::Rc`'s was, which compiled
//! code reads and updates inline (checked below at compile time): the
//! strong count, a second word that is always 1 (std's weak count: there
//! are no weak references; an update in place checks both words, as with
//! std), and the value.

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

/// The allocation: the counts, then the value.
#[repr(C)]
pub struct Inner<T: ?Sized> {
    pub(crate) strong: Cell<usize>,
    /// Always 1 (see the module comment).
    pub(crate) weak: Cell<usize>,
    pub(crate) value: T,
}

// What compiled code assumes (`quarz-aot`'s `gen.rs`): the strong count
// first, the second word at 8, the value at 16.
const _: () = {
    assert!(std::mem::offset_of!(Inner<crate::value::Object>, strong) == 0);
    assert!(std::mem::offset_of!(Inner<crate::value::Object>, weak) == 8);
    assert!(std::mem::offset_of!(Inner<crate::value::Object>, value) == 16);
    assert!(std::mem::offset_of!(Inner<crate::value::ArrayData>, value) == 16);
};

/// A counted reference to a heap value (see the module comment).
pub struct Rc<T: ?Sized> {
    ptr: NonNull<Inner<T>>,
    _owns: PhantomData<Inner<T>>,
}

impl<T> Rc<T> {
    #[inline]
    pub fn new(value: T) -> Rc<T> {
        let inner = Box::new(Inner {
            strong: Cell::new(1),
            weak: Cell::new(1),
            value,
        });
        Rc {
            // SAFETY: `Box::into_raw` never returns null.
            ptr: unsafe { NonNull::new_unchecked(Box::into_raw(inner)) },
            _owns: PhantomData,
        }
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
        let ptr = self.ptr.cast::<Inner<T>>();
        std::mem::forget(self);
        // `MaybeUninit<T>` has the layout of `T`, so `Inner` keeps its own.
        Rc {
            ptr,
            _owns: PhantomData,
        }
    }
}

impl<T: ?Sized> Rc<T> {
    #[inline(always)]
    fn inner(&self) -> &Inner<T> {
        // SAFETY: the allocation lives while a reference does.
        unsafe { self.ptr.as_ref() }
    }

    /// Whether both point at the same allocation.
    #[inline]
    pub fn ptr_eq(a: &Rc<T>, b: &Rc<T>) -> bool {
        std::ptr::addr_eq(a.ptr.as_ptr(), b.ptr.as_ptr())
    }

    /// The address of the value.
    #[inline]
    pub fn as_ptr(this: &Rc<T>) -> *const T {
        // SAFETY: a field of a live allocation.
        unsafe { &raw const (*this.ptr.as_ptr()).value }
    }

    /// The value, when this is its only reference.
    #[inline]
    pub fn get_mut(this: &mut Rc<T>) -> Option<&mut T> {
        if this.inner().strong.get() == 1 {
            // SAFETY: the only reference, borrowed mutably.
            Some(unsafe { &mut (*this.ptr.as_ptr()).value })
        } else {
            None
        }
    }

    pub fn strong_count(this: &Rc<T>) -> usize {
        this.inner().strong.get()
    }

    /// The allocation's layout, for freeing it.
    fn layout(&self) -> Layout {
        Layout::for_value(self.inner())
    }
}

impl<T: Clone> Rc<T> {
    /// The value to update: in place when this is its only reference,
    /// else a copy this then refers to.
    #[inline]
    pub fn make_mut(this: &mut Rc<T>) -> &mut T {
        if this.inner().strong.get() != 1 {
            *this = Rc::new((**this).clone());
        }
        // SAFETY: the only reference now, borrowed mutably.
        unsafe { &mut (*this.ptr.as_ptr()).value }
    }
}

impl<T: ?Sized> Clone for Rc<T> {
    #[inline]
    fn clone(&self) -> Rc<T> {
        let s = &self.inner().strong;
        s.set(s.get() + 1);
        Rc {
            ptr: self.ptr,
            _owns: PhantomData,
        }
    }
}

impl<T: ?Sized> Drop for Rc<T> {
    #[inline]
    fn drop(&mut self) {
        let s = &self.inner().strong;
        let n = s.get() - 1;
        s.set(n);
        if n == 0 {
            // SAFETY: the last reference: drop the value, then free the
            // allocation (there are no weak references).
            unsafe { self.drop_slow() };
        }
    }
}

impl<T: ?Sized> Rc<T> {
    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        let layout = self.layout();
        // SAFETY: the caller holds the last reference.
        unsafe {
            std::ptr::drop_in_place(&raw mut (*self.ptr.as_ptr()).value);
            dealloc(self.ptr.as_ptr().cast(), layout);
        }
    }
}

impl<T: ?Sized> Deref for Rc<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner().value
    }
}

impl<T: ?Sized> AsRef<T> for Rc<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: ?Sized> Borrow<T> for Rc<T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl From<&str> for Rc<str> {
    fn from(s: &str) -> Rc<str> {
        let bytes: Rc<[u8]> = Rc::from_bytes(s.as_bytes());
        let ptr = bytes.ptr.as_ptr() as *mut Inner<str>;
        std::mem::forget(bytes);
        Rc {
            // SAFETY: the allocation holds valid UTF-8; `str` and `[u8]`
            // have the same layout and metadata.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
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
    fn from_bytes(bytes: &[u8]) -> Rc<[u8]> {
        let (layout, offset) = Layout::new::<Inner<()>>()
            .extend(Layout::array::<u8>(bytes.len()).expect("string too large"))
            .expect("string too large");
        let layout = layout.pad_to_align();
        // SAFETY: the layout is not zero-sized (it has the counts); the
        // memory is initialized before the reference is made.
        unsafe {
            let mem = alloc(layout);
            if mem.is_null() {
                handle_alloc_error(layout);
            }
            let inner = std::ptr::slice_from_raw_parts_mut(mem, bytes.len()) as *mut Inner<[u8]>;
            (&raw mut (*inner).strong).write(Cell::new(1));
            (&raw mut (*inner).weak).write(Cell::new(1));
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), mem.add(offset), bytes.len());
            Rc {
                ptr: NonNull::new_unchecked(inner),
                _owns: PhantomData,
            }
        }
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Rc<T> {
    fn eq(&self, other: &Rc<T>) -> bool {
        **self == **other
    }
}

impl<T: ?Sized + Eq> Eq for Rc<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for Rc<T> {
    fn partial_cmp(&self, other: &Rc<T>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + Ord> Ord for Rc<T> {
    fn cmp(&self, other: &Rc<T>) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + Hash> Hash for Rc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<T: Default> Default for Rc<T> {
    fn default() -> Rc<T> {
        Rc::new(T::default())
    }
}
