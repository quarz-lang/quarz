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
