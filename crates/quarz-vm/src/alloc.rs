//! The memory allocator of `quarz` and of compiled programs (this crate
//! is linked into both). Built with the `mimalloc` feature, it is
//! mimalloc (a reference-counted runtime frees as often as it allocates,
//! mostly small blocks, which mimalloc was designed for) unless
//! `QUARZ_ALLOC=system` selects the system's `malloc`. The choice is made
//! at the first allocation and kept: a block must go back to the
//! allocator it came from.

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
    // SAFETY: `getenv` with a constant name; the value is only read here,
    // before anything could change the environment.
    #[cfg(unix)]
    let system = unsafe {
        let v = libc::getenv(c"QUARZ_ALLOC".as_ptr());
        !v.is_null() && std::ffi::CStr::from_ptr(v).to_bytes() == b"system"
    };
    // (Elsewhere reading the environment would allocate.)
    #[cfg(not(unix))]
    let system = false;
    let c = if system { SYSTEM } else { MIMALLOC };
    // Threads deciding at once read the same environment.
    CHOICE.store(c, Ordering::Relaxed);
    c
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
