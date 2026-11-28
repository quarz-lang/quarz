//! ABI 1.0's layout, pinned by numbers (docs/15): cogs outside this
//! repository depend on `quarz-ext` by git at any commit (decided on
//! #677), so a change of `sys` that is not append-only would break them
//! when they are built, silently. The header test compares the Rust and
//! the C definitions with each other; this one compares the Rust ones
//! with 1.0 as released, so that a reordering or a resized field fails
//! even when both sides change together. A later minor appends fields
//! after these (`QzApi` after `release`, `QzModule` after
//! `method_size`), which this test does not see.

#![cfg(target_pointer_width = "64")]

use quarz_ext::sys::*;
use std::mem::{offset_of, size_of};

#[test]
fn the_abi_1_0_layout_never_changes() {
    assert_eq!(QZ_ABI_MAJOR, 1);
    assert_eq!((QZ_OK, QZ_RAISED), (0, 1));
    assert_eq!(
        [
            QZ_NIL, QZ_BOOL, QZ_INT, QZ_FLOAT, QZ_STRING, QZ_BYTES, QZ_SYMBOL, QZ_ARRAY, QZ_HASH,
            QZ_OTHER
        ],
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    );
    assert_eq!(QZ_INVALID, u32::MAX);
    assert_eq!(size_of::<QzValue>(), 8);
    assert_eq!(size_of::<QzStatus>(), 4);
    assert_eq!(size_of::<QzKind>(), 4);
    assert_eq!(size_of::<QzBool>(), 1);

    // An element of the methods' array: its size is `method_size`, which
    // may grow, but these offsets never move.
    assert_eq!(
        [
            offset_of!(QzMethod, key),
            offset_of!(QzMethod, key_len),
            offset_of!(QzMethod, entry)
        ],
        [0, 8, 16]
    );
    assert!(size_of::<QzMethod>() >= 24);

    assert_eq!(
        [
            offset_of!(QzModule, abi_major),
            offset_of!(QzModule, abi_minor),
            offset_of!(QzModule, methods),
            offset_of!(QzModule, n_methods),
            offset_of!(QzModule, method_size),
        ],
        [0, 4, 8, 16, 24]
    );

    // `QzApi`: its prefix, then 1.0's functions in their order, one
    // pointer each.
    assert_eq!(
        [
            offset_of!(QzApi, abi_major),
            offset_of!(QzApi, abi_minor),
            offset_of!(QzApi, size)
        ],
        [0, 4, 8]
    );
    let functions = [
        offset_of!(QzApi, kind),
        offset_of!(QzApi, nil),
        offset_of!(QzApi, bool_new),
        offset_of!(QzApi, bool_get),
        offset_of!(QzApi, int_new),
        offset_of!(QzApi, int_get),
        offset_of!(QzApi, float_new),
        offset_of!(QzApi, float_get),
        offset_of!(QzApi, string_new),
        offset_of!(QzApi, string_get),
        offset_of!(QzApi, bytes_new),
        offset_of!(QzApi, bytes_new_uninit),
        offset_of!(QzApi, bytes_get),
        offset_of!(QzApi, symbol_new),
        offset_of!(QzApi, symbol_get),
        offset_of!(QzApi, array_len),
        offset_of!(QzApi, array_get),
        offset_of!(QzApi, array_new),
        offset_of!(QzApi, array_push),
        offset_of!(QzApi, hash_len),
        offset_of!(QzApi, hash_get),
        offset_of!(QzApi, hash_entry),
        offset_of!(QzApi, hash_new),
        offset_of!(QzApi, hash_put),
        offset_of!(QzApi, exception_class),
        offset_of!(QzApi, raise),
        offset_of!(QzApi, release),
    ];
    let expected: Vec<usize> = (0..functions.len()).map(|i| 16 + 8 * i).collect();
    assert_eq!(functions.to_vec(), expected);
    assert!(size_of::<QzApi>() >= 16 + 8 * functions.len());
}

/// ABI 1.0's function types, pinned at compile time: each of `QzApi`'s
/// 1.0 functions, `QzMethod::entry` (`QzEntry`) and `QzInit` must coerce
/// to the type written here, so that a parameter added, removed or
/// retyped (a `usize` turned `u32`, a pointer turned a value) fails to
/// compile even when the header changes with it. The aliases are spelled
/// out (`QzValue` as `u64`, `QzStatus` as `i32`, `QzKind` as `u32`,
/// `QzBool` as `u8`), so that an alias changed underneath fails too.
#[allow(dead_code)]
fn the_abi_1_0_signatures_never_change(api: &QzApi, method: &QzMethod, init: QzInit) {
    type Cx = *mut QzCall;
    let _: unsafe extern "C" fn(Cx, u64) -> u32 = api.kind;
    let _: unsafe extern "C" fn(Cx) -> u64 = api.nil;
    let _: unsafe extern "C" fn(Cx, u8) -> u64 = api.bool_new;
    let _: unsafe extern "C" fn(Cx, u64, *mut u8) -> i32 = api.bool_get;
    let _: unsafe extern "C" fn(Cx, i64) -> u64 = api.int_new;
    let _: unsafe extern "C" fn(Cx, u64, *mut i64) -> i32 = api.int_get;
    let _: unsafe extern "C" fn(Cx, f64) -> u64 = api.float_new;
    let _: unsafe extern "C" fn(Cx, u64, *mut f64) -> i32 = api.float_get;
    let _: unsafe extern "C" fn(Cx, *const u8, usize, *mut u64) -> i32 = api.string_new;
    let _: unsafe extern "C" fn(Cx, u64, *mut *const u8, *mut usize) -> i32 = api.string_get;
    let _: unsafe extern "C" fn(Cx, *const u8, usize) -> u64 = api.bytes_new;
    let _: unsafe extern "C" fn(Cx, usize, *mut *mut u8) -> u64 = api.bytes_new_uninit;
    let _: unsafe extern "C" fn(Cx, u64, *mut *const u8, *mut usize) -> i32 = api.bytes_get;
    let _: unsafe extern "C" fn(Cx, *const u8, usize, *mut u64) -> i32 = api.symbol_new;
    let _: unsafe extern "C" fn(Cx, u64, *mut *const u8, *mut usize) -> i32 = api.symbol_get;
    let _: unsafe extern "C" fn(Cx, u64, *mut usize) -> i32 = api.array_len;
    let _: unsafe extern "C" fn(Cx, u64, usize, *mut u64) -> i32 = api.array_get;
    let _: unsafe extern "C" fn(Cx, usize) -> u64 = api.array_new;
    let _: unsafe extern "C" fn(Cx, u64, u64) -> i32 = api.array_push;
    let _: unsafe extern "C" fn(Cx, u64, *mut usize) -> i32 = api.hash_len;
    let _: unsafe extern "C" fn(Cx, u64, u64, *mut u64, *mut u8) -> i32 = api.hash_get;
    let _: unsafe extern "C" fn(Cx, u64, usize, *mut u64, *mut u64) -> i32 = api.hash_entry;
    let _: unsafe extern "C" fn(Cx) -> u64 = api.hash_new;
    let _: unsafe extern "C" fn(Cx, u64, u64, u64) -> i32 = api.hash_put;
    let _: unsafe extern "C" fn(Cx, *const u8, usize, *mut u64) -> i32 = api.exception_class;
    let _: unsafe extern "C" fn(Cx, u64, *const u8, usize) -> i32 = api.raise;
    let _: unsafe extern "C" fn(Cx, u64) = api.release;
    let _: unsafe extern "C" fn(Cx, u64, *const u64, usize, u64, *mut u64) -> i32 = method.entry;
    let _: unsafe extern "C" fn(*const QzApi) -> *const QzModule = init;
    let _: (*const u8, usize) = (method.key, method.key_len);
    let _: (u32, u32, *const QzMethod, usize, usize) = {
        let m: &QzModule = unsafe { &*init(api) };
        (
            m.abi_major,
            m.abi_minor,
            m.methods,
            m.n_methods,
            m.method_size,
        )
    };
    let _: (u32, u32, usize) = (api.abi_major, api.abi_minor, api.size);
}
