//! The native ABI, version 1.0 (docs/15): what crosses between quarz and
//! a cog's native code. This module is the source of truth;
//! `include/quarz_ext.h` is its C copy, checked against it by a test
//! (sizes, offsets and constants).
//!
//! Only fixed-width types cross: no C `enum`, no `bool`. Structs are
//! `#[repr(C)]` with natural alignment. `QzApi`, `QzModule` and
//! `QzMethod` grow only at their end; their first fields
//! (`abi_major, abi_minor` and `QzApi::size`) never change.

#![allow(non_camel_case_types)]

use std::ffi::c_void;

/// The ABI's major version: a module of another is refused.
pub const QZ_ABI_MAJOR: u32 = 1;
/// The ABI's minor version: a module needing a greater one is refused.
pub const QZ_ABI_MINOR: u32 = 1;

/// An opaque handle on a value; 0 is no value.
pub type QzValue = u64;
/// The status of an entry or an API call: `QZ_OK` or `QZ_RAISED`.
pub type QzStatus = i32;
/// A value's kind (`QZ_NIL` ...); more may come in later minors.
pub type QzKind = u32;
/// A boolean: 0 is false, anything else true (quarz gives 0 or 1).
pub type QzBool = u8;

pub const QZ_OK: QzStatus = 0;
pub const QZ_RAISED: QzStatus = 1;

pub const QZ_NIL: QzKind = 0;
pub const QZ_BOOL: QzKind = 1;
pub const QZ_INT: QzKind = 2;
pub const QZ_FLOAT: QzKind = 3;
pub const QZ_STRING: QzKind = 4;
pub const QZ_BYTES: QzKind = 5;
pub const QZ_SYMBOL: QzKind = 6;
pub const QZ_ARRAY: QzKind = 7;
pub const QZ_HASH: QzKind = 8;
pub const QZ_OTHER: QzKind = 9;
/// What `kind` gives for an invalid handle.
pub const QZ_INVALID: QzKind = 0xFFFF_FFFF;

/// One call of one native: opaque.
#[repr(C)]
pub struct QzCall {
    _private: [u8; 0],
}

/// A native method's entry: the receiver, the declared parameters in
/// declaration order (positional, then keyword-only; `nargs` is their
/// count), the block (0 without one); the result in `*out`.
pub type QzEntry = unsafe extern "C" fn(
    cx: *mut QzCall,
    recv: QzValue,
    args: *const QzValue,
    nargs: usize,
    blk: QzValue,
    out: *mut QzValue,
) -> QzStatus;

/// A method of the module: its key (`Owner#name`, `Owner.name`, UTF-8,
/// not NUL-terminated) and its entry.
#[repr(C)]
pub struct QzMethod {
    pub key: *const u8,
    pub key_len: usize,
    pub entry: QzEntry,
}

/// What a cog's init gives quarz: the ABI it was built against and its
/// methods (`method_size` is `QzMethod`'s size as the cog knows it: the
/// array's stride).
#[repr(C)]
pub struct QzModule {
    pub abi_major: u32,
    pub abi_minor: u32,
    pub methods: *const QzMethod,
    pub n_methods: usize,
    pub method_size: usize,
    // ABI 1.1 (read only from a module whose `abi_minor` is 1 or more).
    /// The cog's `native class`es: `n_classes` of them, `class_size` apart.
    pub classes: *const QzClass,
    pub n_classes: usize,
    pub class_size: usize,
}

/// Drop a native object's data (ABI 1.1): the cog's, run once, when the
/// object's last reference goes.
pub type QzDrop = unsafe extern "C" fn(data: *mut c_void);

/// A `native class` of the cog (ABI 1.1): its name as the cog declares it
/// (`Zlib::Deflater`), how its objects' data is dropped, and its flags.
#[repr(C)]
pub struct QzClass {
    pub name: *const u8,
    pub name_len: usize,
    pub drop: QzDrop,
    pub flags: u32,
}

/// A class whose objects may be shared between tasks (its data is `Send +
/// Sync`): its declaration must include `Shareable`, and only then.
pub const QZ_CLASS_SHAREABLE: u32 = 1;

/// The functions quarz gives a cog, ABI 1.0.
#[repr(C)]
pub struct QzApi {
    pub abi_major: u32,
    pub abi_minor: u32,
    /// `size_of::<QzApi>()` as quarz knows it.
    pub size: usize,

    pub kind: unsafe extern "C" fn(*mut QzCall, QzValue) -> QzKind,

    pub nil: unsafe extern "C" fn(*mut QzCall) -> QzValue,
    pub bool_new: unsafe extern "C" fn(*mut QzCall, QzBool) -> QzValue,
    pub bool_get: unsafe extern "C" fn(*mut QzCall, QzValue, *mut QzBool) -> QzStatus,
    pub int_new: unsafe extern "C" fn(*mut QzCall, i64) -> QzValue,
    pub int_get: unsafe extern "C" fn(*mut QzCall, QzValue, *mut i64) -> QzStatus,
    pub float_new: unsafe extern "C" fn(*mut QzCall, f64) -> QzValue,
    pub float_get: unsafe extern "C" fn(*mut QzCall, QzValue, *mut f64) -> QzStatus,

    pub string_new: unsafe extern "C" fn(*mut QzCall, *const u8, usize, *mut QzValue) -> QzStatus,
    pub string_get:
        unsafe extern "C" fn(*mut QzCall, QzValue, *mut *const u8, *mut usize) -> QzStatus,
    pub bytes_new: unsafe extern "C" fn(*mut QzCall, *const u8, usize) -> QzValue,
    pub bytes_new_uninit: unsafe extern "C" fn(*mut QzCall, usize, *mut *mut u8) -> QzValue,
    pub bytes_get:
        unsafe extern "C" fn(*mut QzCall, QzValue, *mut *const u8, *mut usize) -> QzStatus,
    pub symbol_new: unsafe extern "C" fn(*mut QzCall, *const u8, usize, *mut QzValue) -> QzStatus,
    pub symbol_get:
        unsafe extern "C" fn(*mut QzCall, QzValue, *mut *const u8, *mut usize) -> QzStatus,

    pub array_len: unsafe extern "C" fn(*mut QzCall, QzValue, *mut usize) -> QzStatus,
    pub array_get: unsafe extern "C" fn(*mut QzCall, QzValue, usize, *mut QzValue) -> QzStatus,
    pub array_new: unsafe extern "C" fn(*mut QzCall, usize) -> QzValue,
    pub array_push: unsafe extern "C" fn(*mut QzCall, QzValue, QzValue) -> QzStatus,

    pub hash_len: unsafe extern "C" fn(*mut QzCall, QzValue, *mut usize) -> QzStatus,
    pub hash_get:
        unsafe extern "C" fn(*mut QzCall, QzValue, QzValue, *mut QzValue, *mut QzBool) -> QzStatus,
    pub hash_entry:
        unsafe extern "C" fn(*mut QzCall, QzValue, usize, *mut QzValue, *mut QzValue) -> QzStatus,
    pub hash_new: unsafe extern "C" fn(*mut QzCall) -> QzValue,
    pub hash_put: unsafe extern "C" fn(*mut QzCall, QzValue, QzValue, QzValue) -> QzStatus,

    pub exception_class:
        unsafe extern "C" fn(*mut QzCall, *const u8, usize, *mut QzValue) -> QzStatus,
    pub raise: unsafe extern "C" fn(*mut QzCall, QzValue, *const u8, usize) -> QzStatus,

    pub release: unsafe extern "C" fn(*mut QzCall, QzValue),

    // ABI 1.1.
    /// Call the method's block (`blk`) with `nargs` arguments: its value
    /// in `*out`, a handle of the call's (docs/15).
    pub call_block:
        unsafe extern "C" fn(*mut QzCall, QzValue, *const QzValue, usize, *mut QzValue) -> QzStatus,
    /// Make an object of the module's class `cls` (its index in
    /// `QzModule::classes`; one the calling method's declaration returns)
    /// holding `data`, dropped by the class's `QzDrop` when its last
    /// reference goes: a handle of the call's (docs/15).
    pub object_new: unsafe extern "C" fn(*mut QzCall, u32, *mut c_void, *mut QzValue) -> QzStatus,
    /// The data of `v`, an object of exactly the module's class `cls`
    /// (its index): else `TypeError`.
    pub object_data: unsafe extern "C" fn(*mut QzCall, QzValue, u32, *mut *mut c_void) -> QzStatus,
}

/// A cog's init: `qz_cog_init_<cog>` (`init_symbol`), its only export.
pub type QzInit = unsafe extern "C" fn(api: *const QzApi) -> *const QzModule;

/// The init symbol of cog `name` (`[a-z][a-z0-9_-]*`): each `_` as `__`,
/// each `-` as `_h`, so that two cogs never share one.
pub fn init_symbol(name: &str) -> String {
    let mut s = String::from("qz_cog_init_");
    for c in name.chars() {
        match c {
            '_' => s.push_str("__"),
            '-' => s.push_str("_h"),
            c => s.push(c),
        }
    }
    s
}
