//! Write a Quarz cog's native methods in Rust (docs/15).
//!
//! A cog whose `Cog.toml` declares native code (`[native] crate =
//! "native"`) declares its methods `native def` in Quarz and implements
//! them in a crate of its own, a `cdylib` and `staticlib` depending on
//! this one:
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
        let values: Vec<Value<'_>> = raw.iter().map(|h| Value::new(*h)).collect();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            method(&call, Value::new(recv), &values)
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
}

/// The cog's module: its name (as in its `Cog.toml`) and its methods by
/// key (`"Owner#name"`, `"Owner.name"`), each a `Method`. Makes the
/// cog's init function, `qz_cog_init_<cog>`.
#[macro_export]
macro_rules! module {
    (cog: $cog:literal, $($key:literal => $method:path),* $(,)?) => {
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
            static MODULE: $crate::__private::Static<QzModule> =
                $crate::__private::Static(QzModule {
                    abi_major: QZ_ABI_MAJOR,
                    abi_minor: QZ_ABI_MINOR,
                    methods: METHODS.0.as_ptr() as *const QzMethod,
                    n_methods: $crate::module!(@count $($key)*),
                    method_size: ::std::mem::size_of::<QzMethod>(),
                });
            #[export_name = $crate::__private::init_symbol!($cog)]
            unsafe extern "C" fn init(api: *const QzApi) -> *const QzModule {
                $crate::__private::init(api, &MODULE.0)
            }
        };
    };
    (@count $($x:tt)*) => { 0usize $(+ $crate::module!(@one $x))* };
    (@one $x:tt) => { 1usize };
}
