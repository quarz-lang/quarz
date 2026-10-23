//! The memory allocator of `quarz` and of compiled programs (this crate
//! is linked into both). Built with the `mimalloc` feature, it is
//! mimalloc (a reference-counted runtime frees as often as it allocates,
//! mostly small blocks, which mimalloc was designed for) unless
//! `QUARZ_ALLOC=system` selects the system's `malloc`. The choice is made
//! at the first allocation and kept: a block must go back to the
//! allocator it came from.
//!
//! mimalloc asks for transparent huge pages by default, which the kernel
//! zeroes 2 MiB at a time: half a millisecond more for every process,
//! for a gain only to programs that use a lot of memory. Like most
//! runtimes (Go, the JVM, glibc's malloc), Quarz leaves them to programs
//! that ask: `QUARZ_THP=1`.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU8, Ordering};

#[global_allocator]
static GLOBAL: Allocator = Allocator;

struct Allocator;

const UNDECIDED: u8 = 0;
const SYSTEM: u8 = 1;
const MIMALLOC: u8 = 2;

static CHOICE: AtomicU8 = AtomicU8::new(UNDECIDED);

/// The allocator chosen (read from the environment without allocating).
#[inline(always)]
fn choice() -> u8 {
    match CHOICE.load(Ordering::Relaxed) {
        UNDECIDED => decide(),
        c => c,
    }
}

#[cold]
fn decide() -> u8 {
    let system = env_is("QUARZ_ALLOC", b"system");
    let c = if system { SYSTEM } else { MIMALLOC };
    if c == MIMALLOC && !env_is("QUARZ_THP", b"1") {
        // SAFETY: before mimalloc's first allocation, which reads its
        // options.
        unsafe { libmimalloc_sys::mi_option_set(MI_OPTION_ALLOW_THP, 0) };
    }
    // Threads deciding at once read the same environment.
    CHOICE.store(c, Ordering::Relaxed);
    c
}

/// `mi_option_allow_thp` in the bundled mimalloc's `mi_option_e` (3.3.2;
/// the crates are pinned in Cargo.toml).
const MI_OPTION_ALLOW_THP: libmimalloc_sys::mi_option_t = 43;

/// Whether environment variable `name` is `value`, read without
/// allocating (elsewhere than on Unix, never).
fn env_is(name: &str, value: &[u8]) -> bool {
    #[cfg(unix)]
    {
        let mut buf = [0u8; 32];
        buf[..name.len()].copy_from_slice(name.as_bytes());
        // SAFETY: a NUL-terminated name; the value is only read here,
        // before anything could change the environment.
        unsafe {
            let v = libc::getenv(buf.as_ptr().cast());
            !v.is_null() && std::ffi::CStr::from_ptr(v).to_bytes() == value
        }
    }
    #[cfg(not(unix))]
    {
        let _ = (name, value);
        false
    }
}

/// The allocator in use, for diagnostics.
pub fn name() -> &'static str {
    match choice() {
        SYSTEM => "system",
        _ => "mimalloc",
    }
}

// SAFETY: every call goes to the one allocator chosen for the process,
// which upholds `GlobalAlloc`'s contract.
unsafe impl GlobalAlloc for Allocator {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        match choice() {
            SYSTEM => unsafe { System.alloc(layout) },
            _ => unsafe { mimalloc::MiMalloc.alloc(layout) },
        }
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        match choice() {
            SYSTEM => unsafe { System.alloc_zeroed(layout) },
            _ => unsafe { mimalloc::MiMalloc.alloc_zeroed(layout) },
        }
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        match choice() {
            SYSTEM => unsafe { System.dealloc(ptr, layout) },
            _ => unsafe { mimalloc::MiMalloc.dealloc(ptr, layout) },
        }
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        match choice() {
            SYSTEM => unsafe { System.realloc(ptr, layout, new_size) },
            _ => unsafe { mimalloc::MiMalloc.realloc(ptr, layout, new_size) },
        }
    }
}
