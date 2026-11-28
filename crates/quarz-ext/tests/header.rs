//! `include/quarz_ext.h` against `quarz_ext::sys`, the ABI's source: a
//! C file asserting every struct's size and every field's offset as Rust
//! computes them, and every constant, must compile (with `cc`, skipped
//! with a message where there is none).

use quarz_ext::sys::*;
use std::mem::{offset_of, size_of};
use std::process::Command;

#[test]
fn the_header_matches_the_rust_definitions() {
    let mut c = String::from("#include \"quarz_ext.h\"\n");
    let mut check = |expr: String, value: usize| {
        c.push_str(&format!(
            "_Static_assert(({expr}) == {value}u, \"{expr}\");\n"
        ));
    };
    macro_rules! layout {
        ($ty:ident: $($field:ident),*) => {
            check(format!("sizeof({})", stringify!($ty)), size_of::<$ty>());
            $(check(format!("offsetof({}, {})", stringify!($ty), stringify!($field)), offset_of!($ty, $field));)*
        };
    }
    layout!(QzMethod: key, key_len, entry);
    layout!(QzModule: abi_major, abi_minor, methods, n_methods, method_size);
    layout!(QzApi: abi_major, abi_minor, size, kind, nil, bool_new, bool_get, int_new, int_get,
        float_new, float_get, string_new, string_get, bytes_new, bytes_new_uninit, bytes_get,
        symbol_new, symbol_get, array_len, array_get, array_new, array_push, hash_len, hash_get,
        hash_entry, hash_new, hash_put, exception_class, raise, release, call_block);
    for (name, size) in [
        ("QzValue", size_of::<QzValue>()),
        ("QzStatus", size_of::<QzStatus>()),
        ("QzKind", size_of::<QzKind>()),
        ("QzBool", size_of::<QzBool>()),
    ] {
        check(format!("sizeof({name})"), size);
    }
    for (name, value) in [
        ("QZ_ABI_MAJOR", QZ_ABI_MAJOR as usize),
        ("QZ_ABI_MINOR", QZ_ABI_MINOR as usize),
        ("QZ_OK", QZ_OK as usize),
        ("QZ_RAISED", QZ_RAISED as usize),
        ("QZ_NIL", QZ_NIL as usize),
        ("QZ_BOOL", QZ_BOOL as usize),
        ("QZ_INT", QZ_INT as usize),
        ("QZ_FLOAT", QZ_FLOAT as usize),
        ("QZ_STRING", QZ_STRING as usize),
        ("QZ_BYTES", QZ_BYTES as usize),
        ("QZ_SYMBOL", QZ_SYMBOL as usize),
        ("QZ_ARRAY", QZ_ARRAY as usize),
        ("QZ_HASH", QZ_HASH as usize),
        ("QZ_OTHER", QZ_OTHER as usize),
        ("QZ_INVALID", QZ_INVALID as usize),
    ] {
        check(name.to_string(), value);
    }
    let dir = std::env::temp_dir().join(format!("quarz-ext-header-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("check.c");
    std::fs::write(&file, &c).unwrap();
    let include = concat!(env!("CARGO_MANIFEST_DIR"), "/include");
    let out = Command::new("cc")
        .args(["-std=c11", "-fsyntax-only", "-I", include])
        .arg(&file)
        .output();
    let _ = std::fs::remove_dir_all(&dir);
    match out {
        Err(e) => eprintln!("skipped: no cc to compile the header ({e})"),
        Ok(o) => assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr)),
    }
}

#[test]
fn init_symbols_are_distinct() {
    assert_eq!(init_symbol("zlib"), "qz_cog_init_zlib");
    assert_eq!(init_symbol("zlib-ng"), "qz_cog_init_zlib_hng");
    assert_eq!(init_symbol("zlib_ng"), "qz_cog_init_zlib__ng");
    assert_ne!(init_symbol("a-b"), init_symbol("a_b"));
    assert_eq!(quarz_ext_macros_symbol(), init_symbol("zlib-ng"));
}

/// The macro's encoding is `init_symbol`'s.
fn quarz_ext_macros_symbol() -> String {
    quarz_ext::__private::init_symbol!("zlib-ng").to_string()
}
