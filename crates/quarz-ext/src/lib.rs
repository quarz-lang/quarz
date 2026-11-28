//! Write a Quarz cog's native methods in Rust (docs/15).
//!
//! A cog whose `Cog.toml` declares native code (`[native] crate =
//! "native"`) declares its methods `native def` in Quarz and implements
//! them in a crate of its own, a `cdylib` and `staticlib` depending on
//! this one by git, on the quarz repository (it is not on crates.io):
//!
//! ```toml
//! [dependencies]
//! quarz-ext = { git = "https://github.com/quarz-lang/quarz", tag = "v0.1.0" }
//! ```
//!
//! The ABI's version (this crate's major and minor), not the commit
//! pinned, decides whether a cog runs on a given quarz. Then:
//!
//! ```ignore
//! use quarz_ext::{Call, Result, Value};
//!
//! fn crc32(cx: &Call<'_>, _recv: Value<'_>, args: &[Value<'_>]) -> Result<Value<'_>> {
//!     let data = cx.get_bytes(args[0])?;
//!     Ok(cx.int(i64::from(checksum(data))))
//! }
//!
//! quarz_ext::module! {
//!     cog: "zlib",
//!     "Zlib.crc32" => crc32,
//! }
//! ```
//!
//! Values are handles (`Value`) valid for the call (`Call`) only: no
//! value can be kept, nor taken to another thread. An error is raised in
//! Quarz by returning `Err`: the `Raised` a failed call gives, or
//! `cx.raise(...)`'s. A panic is caught at the entry and raised as
//! `NativePanic`.
//!
//! The ABI under it is `sys`, whose major version is this crate's.

pub mod sys;

use std::marker::PhantomData;
use sys::*;

/// An exception is pending in the call: returned from an entry, it is
/// raised in Quarz.
#[derive(Debug)]
pub struct Raised(());

pub type Result<T> = std::result::Result<T, Raised>;

/// A value of the call `'c`: a handle that is not valid once the call
/// returns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Value<'c> {
    handle: QzValue,
    _call: PhantomData<&'c ()>,
}

impl<'c> Value<'c> {
    /// No value: what a method declared `-> Void` returns.
    pub const NONE: Value<'c> = Value {
        handle: 0,
        _call: PhantomData,
    };

    fn new(handle: QzValue) -> Self {
        Value {
            handle,
            _call: PhantomData,
        }
    }

    /// The raw handle, for `sys`'s functions.
    pub fn handle(self) -> QzValue {
        self.handle
    }

    /// A value of a raw handle.
    ///
    /// # Safety
    /// Nothing is unsound if `handle` is not one of the call's (quarz
    /// refuses it with a `TypeError`), but it is a value of this call only
    /// if it came from this call.
    pub unsafe fn from_raw(handle: QzValue) -> Value<'c> {
        Value::new(handle)
    }
}

// `entry` reads the handles as values: the same size and alignment.
const _: () = {
    assert!(std::mem::size_of::<Value<'static>>() == std::mem::size_of::<QzValue>());
    assert!(std::mem::align_of::<Value<'static>>() == std::mem::align_of::<QzValue>());
};

/// What a value is (`Call::kind`). Later minor versions may add kinds;
/// until the wrapper knows one, it is `Other`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Kind {
    Nil,
    Bool,
    Int,
    Float,
    String,
    Bytes,
    Symbol,
    Array,
    Hash,
    /// Anything else (a class value, an object, `Bytes::Secret`, ...).
    Other,
    /// Not a value of this call's (`QZ_INVALID`): from another call, or
    /// released.
    Invalid,
}

/// One call of a native method: what makes and reads its values. Not
/// `Send`: the values are the calling task's.
pub struct Call<'c> {
    cx: *mut QzCall,
    api: &'c QzApi,
    block: QzValue,
    _not_send: PhantomData<*mut ()>,
}

fn status(s: QzStatus) -> Result<()> {
    if s == QZ_OK {
        Ok(())
    } else {
        Err(Raised(()))
    }
}

impl<'c> Call<'c> {
    /// What `v` is.
    pub fn kind(&self, v: Value<'c>) -> Kind {
        match unsafe { (self.api.kind)(self.cx, v.handle) } {
            QZ_NIL => Kind::Nil,
            QZ_BOOL => Kind::Bool,
            QZ_INT => Kind::Int,
            QZ_FLOAT => Kind::Float,
            QZ_STRING => Kind::String,
            QZ_BYTES => Kind::Bytes,
            QZ_SYMBOL => Kind::Symbol,
            QZ_ARRAY => Kind::Array,
            QZ_HASH => Kind::Hash,
            QZ_INVALID => Kind::Invalid,
            _ => Kind::Other,
        }
    }

    /// The block the method was given (ABI 1.1 calls it).
    pub fn block(&self) -> Option<Value<'c>> {
        (self.block != 0).then(|| Value::new(self.block))
    }

    /// An object of the cog's native class `class` (its full name, as
    /// `module!`'s `classes` lists it with its Rust type) holding `value`
    /// (ABI 1.1): a value of the call's. `T` must be the class's type,
    /// and the method's declaration must return the class (docs/15);
    /// else a `TypeError`, and `value` is dropped.
    pub fn object<T: 'static>(&self, class: &str, value: T) -> Result<Value<'c>> {
        if __private::class_type(class) != Some(std::any::TypeId::of::<T>()) {
            return Err(self.raise(
                "TypeError",
                &format!("a native method made an object of `{class}` from another Rust type than the class's"),
            ));
        }
        let data = Box::into_raw(Box::new(__private::Tagged {
            type_id: std::any::TypeId::of::<T>(),
            value,
        }));
        let mut out: QzValue = 0;
        let st = unsafe {
            (self.api.object_new)(self.cx, class.as_ptr(), class.len(), data.cast(), &mut out)
        };
        if st != QZ_OK {
            // SAFETY: refused, so still ours.
            drop(unsafe { Box::from_raw(data) });
            return Err(Raised(()));
        }
        Ok(Value::new(out))
    }

    /// The data of `v`, an object of the cog's native class `class` whose
    /// Rust type is `T` (ABI 1.1); else a `TypeError`. Shared only (`&T`):
    /// the block may call another method on the same object, and two
    /// values can name it; mutate through `Cell`, `RefCell` or a lock.
    pub fn data<T: 'static>(&self, v: Value<'c>, class: &str) -> Result<&'c T> {
        let mut data: *mut std::ffi::c_void = std::ptr::null_mut();
        let st = unsafe {
            (self.api.object_data)(self.cx, v.handle, class.as_ptr(), class.len(), &mut data)
        };
        status(st)?;
        // SAFETY: the runtime gave an object of `class`, which this
        // wrapper boxed as a `Tagged<_>`, its `TypeId` at offset 0.
        let type_id = unsafe { *(data as *const std::any::TypeId) };
        if type_id != std::any::TypeId::of::<T>() {
            return Err(self.raise(
                "TypeError",
                &format!("a native method asked for the data of a `{class}` as another Rust type"),
            ));
        }
        // SAFETY: a `Tagged<T>`, alive while `v` is (the call holds it).
        Ok(unsafe { &(*(data as *const __private::Tagged<T>)).value })
    }

    /// Call the method's block with `args` (ABI 1.1): its value. What
    /// the block raises, and a `break` or `return` out of it, comes back
    /// as `Err(Raised)`, to return at once (`?`). The block may suspend
    /// the task and may enter this cog's natives again: hold no lock and
    /// no `RefCell` borrow across the call (docs/15). Raises `ArgumentError`
    /// when the method was given no block.
    pub fn call_block(&self, args: &[Value<'c>]) -> Result<Value<'c>> {
        if self.block == 0 {
            return Err(self.raise("ArgumentError", "the native method was given no block"));
        }
        let mut out: QzValue = 0;
        // SAFETY: `Value` is a `QzValue` (`repr(transparent)`).
        let st = unsafe {
            (self.api.call_block)(
                self.cx,
                self.block,
                args.as_ptr().cast(),
                args.len(),
                &mut out,
            )
        };
        status(st)?;
        Ok(Value::new(out))
    }

    pub fn nil(&self) -> Value<'c> {
        Value::new(unsafe { (self.api.nil)(self.cx) })
    }

    pub fn bool(&self, b: bool) -> Value<'c> {
        Value::new(unsafe { (self.api.bool_new)(self.cx, QzBool::from(b)) })
    }

    pub fn int(&self, i: i64) -> Value<'c> {
        Value::new(unsafe { (self.api.int_new)(self.cx, i) })
    }

    pub fn float(&self, f: f64) -> Value<'c> {
        Value::new(unsafe { (self.api.float_new)(self.cx, f) })
    }

    pub fn string(&self, s: &str) -> Result<Value<'c>> {
        let mut out = 0;
        status(unsafe { (self.api.string_new)(self.cx, s.as_ptr(), s.len(), &mut out) })?;
        Ok(Value::new(out))
    }

    pub fn bytes(&self, b: &[u8]) -> Value<'c> {
        Value::new(unsafe { (self.api.bytes_new)(self.cx, b.as_ptr(), b.len()) })
    }

    /// `n` bytes written in place by `fill` (zeroed before it): a large
    /// result made without a copy.
    pub fn bytes_with(&self, n: usize, fill: impl FnOnce(&mut [u8])) -> Value<'c> {
        let mut p: *mut u8 = std::ptr::null_mut();
        let v = unsafe { (self.api.bytes_new_uninit)(self.cx, n, &mut p) };
        if v != 0 && !p.is_null() {
            // SAFETY: quarz gives `n` zeroed bytes, the call's until it
            // returns.
            fill(unsafe { std::slice::from_raw_parts_mut(p, n) });
        }
        Value::new(v)
    }

    pub fn symbol(&self, name: &str) -> Result<Value<'c>> {
        let mut out = 0;
        status(unsafe { (self.api.symbol_new)(self.cx, name.as_ptr(), name.len(), &mut out) })?;
        Ok(Value::new(out))
    }

    pub fn get_bool(&self, v: Value<'c>) -> Result<bool> {
        let mut b: QzBool = 0;
        status(unsafe { (self.api.bool_get)(self.cx, v.handle, &mut b) })?;
        Ok(b != 0)
    }

    pub fn get_int(&self, v: Value<'c>) -> Result<i64> {
        let mut i = 0;
        status(unsafe { (self.api.int_get)(self.cx, v.handle, &mut i) })?;
        Ok(i)
    }

    pub fn get_float(&self, v: Value<'c>) -> Result<f64> {
        let mut f = 0.0;
        status(unsafe { (self.api.float_get)(self.cx, v.handle, &mut f) })?;
        Ok(f)
    }

    fn get_slice(
        &self,
        v: Value<'c>,
        get: unsafe extern "C" fn(*mut QzCall, QzValue, *mut *const u8, *mut usize) -> QzStatus,
    ) -> Result<&'c [u8]> {
        let (mut p, mut n): (*const u8, usize) = (std::ptr::null(), 0);
        status(unsafe { get(self.cx, v.handle, &mut p, &mut n) })?;
        if n == 0 {
            return Ok(&[]);
        }
        // SAFETY: quarz lends the bytes until the call returns.
        Ok(unsafe { std::slice::from_raw_parts(p, n) })
    }

    /// A `String`'s text, lent for the call.
    pub fn get_str(&self, v: Value<'c>) -> Result<&'c str> {
        let b = self.get_slice(v, self.api.string_get)?;
        // SAFETY: a `String` is UTF-8.
        Ok(unsafe { std::str::from_utf8_unchecked(b) })
    }

    /// `Bytes`, lent for the call.
    pub fn get_bytes(&self, v: Value<'c>) -> Result<&'c [u8]> {
        self.get_slice(v, self.api.bytes_get)
    }

    /// A `Symbol`'s name, lent for the call.
    pub fn get_symbol(&self, v: Value<'c>) -> Result<&'c str> {
        let b = self.get_slice(v, self.api.symbol_get)?;
        // SAFETY: a symbol's name is UTF-8.
        Ok(unsafe { std::str::from_utf8_unchecked(b) })
    }

    pub fn array_len(&self, a: Value<'c>) -> Result<usize> {
        let mut n = 0;
        status(unsafe { (self.api.array_len)(self.cx, a.handle, &mut n) })?;
        Ok(n)
    }

    pub fn array_get(&self, a: Value<'c>, i: usize) -> Result<Value<'c>> {
        let mut out = 0;
        status(unsafe { (self.api.array_get)(self.cx, a.handle, i, &mut out) })?;
        Ok(Value::new(out))
    }

    /// A new array, to `push` to before it is returned or put elsewhere.
    pub fn array(&self, capacity: usize) -> Value<'c> {
        Value::new(unsafe { (self.api.array_new)(self.cx, capacity) })
    }

    pub fn push(&self, a: Value<'c>, v: Value<'c>) -> Result<()> {
        status(unsafe { (self.api.array_push)(self.cx, a.handle, v.handle) })
    }

    pub fn hash_len(&self, h: Value<'c>) -> Result<usize> {
        let mut n = 0;
        status(unsafe { (self.api.hash_len)(self.cx, h.handle, &mut n) })?;
        Ok(n)
    }

    /// The value at `key` (an `Int`, `String`, `Bytes`, `Symbol` or nil).
    pub fn hash_get(&self, h: Value<'c>, key: Value<'c>) -> Result<Option<Value<'c>>> {
        let (mut out, mut found): (QzValue, QzBool) = (0, 0);
        status(unsafe {
            (self.api.hash_get)(self.cx, h.handle, key.handle, &mut out, &mut found)
        })?;
        Ok((found != 0).then(|| Value::new(out)))
    }

    /// The `i`th entry, in insertion order.
    pub fn hash_entry(&self, h: Value<'c>, i: usize) -> Result<(Value<'c>, Value<'c>)> {
        let (mut k, mut v) = (0, 0);
        status(unsafe { (self.api.hash_entry)(self.cx, h.handle, i, &mut k, &mut v) })?;
        Ok((Value::new(k), Value::new(v)))
    }

    /// A new hash, to `put` in before it is returned or put elsewhere.
    pub fn hash(&self) -> Value<'c> {
        Value::new(unsafe { (self.api.hash_new)(self.cx) })
    }

    pub fn put(&self, h: Value<'c>, key: Value<'c>, value: Value<'c>) -> Result<()> {
        status(unsafe { (self.api.hash_put)(self.cx, h.handle, key.handle, value.handle) })
    }

    /// The exception class named `name` (`"ArgumentError"`,
    /// `"Zlib::DataError"`).
    pub fn exception_class(&self, name: &str) -> Result<Value<'c>> {
        let mut out = 0;
        status(unsafe {
            (self.api.exception_class)(self.cx, name.as_ptr(), name.len(), &mut out)
        })?;
        Ok(Value::new(out))
    }

    /// Raise an exception of class `class` with `message`: return the
    /// `Err` it gives.
    pub fn raise(&self, class: &str, message: &str) -> Raised {
        if let Ok(c) = self.exception_class(class) {
            unsafe { (self.api.raise)(self.cx, c.handle, message.as_ptr(), message.len()) };
        }
        Raised(())
    }

    /// Let go of `v` before the call returns (a long loop of `array_get`s).
    /// Nothing happens to a value whose bytes were lent (`get_str`,
    /// `get_bytes`, `bytes_with`): the slices stay valid to the end of the
    /// call, whatever is released.
    pub fn release(&self, v: Value<'c>) {
        unsafe { (self.api.release)(self.cx, v.handle) }
    }
}

/// A native method: the receiver and the declared parameters, in their
/// declared order (positional, then keyword-only).
pub type Method = for<'c> fn(&Call<'c>, Value<'c>, &[Value<'c>]) -> Result<Value<'c>>;

#[doc(hidden)]
pub mod __private {
    use super::*;
    pub use quarz_ext_macros::init_symbol;
    use std::sync::atomic::{AtomicPtr, Ordering};

    /// The API quarz gave at init, for every entry.
    pub static API: AtomicPtr<QzApi> = AtomicPtr::new(std::ptr::null_mut());

    /// `init`'s body: the API kept, the module given (null on another
    /// major).
    pub unsafe fn init(api: *const QzApi, module: &'static QzModule) -> *const QzModule {
        if api.is_null() || (*api).abi_major != QZ_ABI_MAJOR {
            return std::ptr::null();
        }
        API.store(api as *mut QzApi, Ordering::Release);
        module
    }

    /// An entry's body: `method` called on the call's values, a panic
    /// caught and raised as `NativePanic`.
    ///
    /// # Safety
    /// As `QzEntry`: quarz's arguments.
    pub unsafe fn entry(
        method: Method,
        cx: *mut QzCall,
        recv: QzValue,
        args: *const QzValue,
        nargs: usize,
        blk: QzValue,
        out: *mut QzValue,
    ) -> QzStatus {
        let api = API.load(Ordering::Acquire);
        if api.is_null() {
            return QZ_RAISED;
        }
        let call = Call {
            cx,
            api: &*api,
            block: blk,
            _not_send: PhantomData,
        };
        let raw = if nargs == 0 {
            &[][..]
        } else {
            std::slice::from_raw_parts(args, nargs)
        };
        // SAFETY: `Value` is a `QzValue` (`repr(transparent)`, its
        // `PhantomData` zero-sized: asserted below), so the handles are
        // the values, with no copy.
        let values: &[Value<'_>] = std::slice::from_raw_parts(raw.as_ptr().cast(), raw.len());
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            method(&call, Value::new(recv), values)
        }));
        match result {
            Ok(Ok(v)) => {
                *out = v.handle;
                QZ_OK
            }
            Ok(Err(Raised(()))) => QZ_RAISED,
            Err(panic) => {
                let message = panic
                    .downcast_ref::<&str>()
                    .map(|s| s.to_string())
                    .or_else(|| panic.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "a panic in native code".to_string());
                let _ = call.raise("NativePanic", &message);
                QZ_RAISED
            }
        }
    }

    /// A `Sync` wrapper of the module's static tables (their pointers
    /// are to statics).
    pub struct Static<T>(pub T);
    unsafe impl<T> Sync for Static<T> {}

    /// A native object's data as the wrapper boxes it: the Rust type's
    /// `TypeId` first (`#[repr(C)]`, at offset 0 whatever `T`), so that
    /// `Call::data` compares it before any cast (ABI 1.1).
    #[repr(C)]
    pub struct Tagged<T> {
        pub type_id: std::any::TypeId,
        pub value: T,
    }

    /// A native class: its name and its Rust type's `TypeId`.
    pub type ClassEntry = (&'static str, fn() -> std::any::TypeId);

    /// The cog's native classes: each one's name and Rust type, set by
    /// `module!`'s init (`set_classes`).
    pub static CLASSES: AtomicPtr<ClassEntry> = AtomicPtr::new(std::ptr::null_mut());
    pub static N_CLASSES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    pub fn set_classes(classes: &'static [ClassEntry]) {
        N_CLASSES.store(classes.len(), Ordering::Release);
        CLASSES.store(classes.as_ptr() as *mut _, Ordering::Release);
    }

    /// The Rust type of the cog's class `name`, when it has one.
    pub fn class_type(name: &str) -> Option<std::any::TypeId> {
        let p = CLASSES.load(Ordering::Acquire);
        if p.is_null() {
            return None;
        }
        // SAFETY: `set_classes` stored a static slice of this length.
        let classes = unsafe { std::slice::from_raw_parts(p, N_CLASSES.load(Ordering::Acquire)) };
        classes.iter().find(|(n, _)| *n == name).map(|(_, t)| t())
    }

    static DROP_REPORTED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

    /// Drop a `Tagged<T>` the runtime no longer holds (`QzDrop`): a panic
    /// in `T`'s drop is caught (it cannot cross into the runtime),
    /// reported once and the rest leaked (decided on #677).
    ///
    /// # Safety
    /// `data` is a `Box<Tagged<T>>` this wrapper made, dropped once.
    pub unsafe fn drop_tagged<T>(data: *mut std::ffi::c_void, class: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            drop(Box::from_raw(data as *mut Tagged<T>));
        }));
        if let Err(panic) = r {
            if !DROP_REPORTED.swap(true, Ordering::Relaxed) {
                let message = panic
                    .downcast_ref::<&str>()
                    .map(|s| s.to_string())
                    .or_else(|| panic.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "a panic".to_string());
                eprintln!(
                    "quarz: the drop of a native object of class {class} panicked: {message} (its data leaked; reported once)"
                );
            }
            std::mem::forget(panic);
        }
    }

    /// A shareable class's data is `Send + Sync` (checked at compile
    /// time by `module!`).
    pub const fn shareable<T: Send + Sync>() {}
}

/// The cog's module: its name (as in its `Cog.toml`) and its methods by
/// key (`"Owner#name"`, `"Owner.name"`), each a `Method`. Makes the
/// cog's init function, `qz_cog_init_<cog>`.
#[macro_export]
macro_rules! module {
    (cog: $cog:literal, $($key:literal => $method:path),* $(,)?) => {
        $crate::module! { cog: $cog, classes: {}, $($key => $method),* }
    };
    (cog: $cog:literal, classes: { $($class:literal => $ty:ty $(: $share:ident)?),* $(,)? }, $($key:literal => $method:path),* $(,)?) => {
        const _: () = {
            use $crate::sys::*;
            static METHODS: $crate::__private::Static<[QzMethod; $crate::module!(@count $($key)*)]> =
                $crate::__private::Static([$(
                    QzMethod {
                        key: $key.as_ptr(),
                        key_len: $key.len(),
                        entry: {
                            unsafe extern "C" fn entry(
                                cx: *mut QzCall,
                                recv: QzValue,
                                args: *const QzValue,
                                nargs: usize,
                                blk: QzValue,
                                out: *mut QzValue,
                            ) -> QzStatus {
                                $crate::__private::entry($method, cx, recv, args, nargs, blk, out)
                            }
                            entry
                        },
                    },
                )*]);
            static CLASSES: $crate::__private::Static<[QzClass; $crate::module!(@count $($class)*)]> =
                $crate::__private::Static([$(
                    QzClass {
                        name: $class.as_ptr(),
                        name_len: $class.len(),
                        drop: {
                            unsafe extern "C" fn drop(data: *mut ::std::ffi::c_void) {
                                $crate::__private::drop_tagged::<$ty>(data, $class)
                            }
                            drop
                        },
                        flags: $crate::module!(@flag $ty $(, $share)?),
                    },
                )*]);
            static TYPES: [$crate::__private::ClassEntry; $crate::module!(@count $($class)*)] =
                [$(($class, ::std::any::TypeId::of::<$ty>)),*];
            static MODULE: $crate::__private::Static<QzModule> =
                $crate::__private::Static(QzModule {
                    abi_major: QZ_ABI_MAJOR,
                    abi_minor: QZ_ABI_MINOR,
                    methods: METHODS.0.as_ptr() as *const QzMethod,
                    n_methods: $crate::module!(@count $($key)*),
                    method_size: ::std::mem::size_of::<QzMethod>(),
                    classes: CLASSES.0.as_ptr() as *const QzClass,
                    n_classes: $crate::module!(@count $($class)*),
                    class_size: ::std::mem::size_of::<QzClass>(),
                });
            #[export_name = $crate::__private::init_symbol!($cog)]
            unsafe extern "C" fn init(api: *const QzApi) -> *const QzModule {
                $crate::__private::set_classes(&TYPES);
                $crate::__private::init(api, &MODULE.0)
            }
        };
    };
    (@count $($x:tt)*) => { 0usize $(+ $crate::module!(@one $x))* };
    (@flag $ty:ty) => { 0u32 };
    (@flag $ty:ty, shareable) => {{
        const _: () = $crate::__private::shareable::<$ty>();
        $crate::sys::QZ_CLASS_SHAREABLE
    }};
    (@one $x:tt) => { 1usize };
}
