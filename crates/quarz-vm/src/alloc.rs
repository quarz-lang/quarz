//! The memory allocator of `quarz` and of compiled programs (this crate
//! is linked into both). Built with the `mimalloc` feature, it is
//! mimalloc for blocks under `LARGE` (a reference-counted runtime frees
//! as often as it allocates, mostly small blocks, which mimalloc was
//! designed for) and the system's `malloc` for larger ones (glibc grows a
//! large block in place or by remapping its pages, where mimalloc copies
//! it: an array or string built up by appends), unless
//! `QUARZ_ALLOC=system` selects the system's for everything. The choice
//! is made at the first allocation and kept, and a block's size, which
//! comes back with it to `dealloc` and `realloc`, says which allocator
//! it came from.
//!
//! mimalloc asks for transparent huge pages by default, which the kernel
//! zeroes 2 MiB at a time: half a millisecond more for every process,
//! for a gain only to programs that use a lot of memory. Like most
//! runtimes (Go, the JVM, glibc's malloc), Quarz leaves them to programs
//! that ask: `QUARZ_THP=1`.
//!
//! A compiled program's start-up (decoding its module, building the
//! runtime's tables) allocates thousands of small blocks that live as
//! long as the program: between `startup_begin` and `startup_end` they
//! are cut one after another from `ARENA`, a static area of which only
//! the pages used are ever mapped, with no per-block bookkeeping and no
//! zeroing (the area starts zeroed and is never reused). Such a block is
//! never freed (`dealloc` ignores it) and moves to the heap when it grows.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

#[global_allocator]
static GLOBAL: Allocator = Allocator;

struct Allocator;

const UNDECIDED: u8 = 0;
const SYSTEM: u8 = 1;
const MIMALLOC: u8 = 2;
/// mimalloc, but start-up blocks from `ARENA`.
const STARTUP: u8 = 3;

const ARENA_SIZE: usize = 8 << 20;

#[repr(C, align(64))]
struct Arena(UnsafeCell<[u8; ARENA_SIZE]>);

// SAFETY: blocks are handed out once each, by an atomic bump.
unsafe impl Sync for Arena {}

static ARENA: Arena = Arena(UnsafeCell::new([0; ARENA_SIZE]));
static ARENA_NEXT: AtomicUsize = AtomicUsize::new(0);

/// Whether `ptr` was cut from `ARENA`.
#[inline(always)]
fn in_arena(ptr: *mut u8) -> bool {
    (ptr as usize).wrapping_sub(ARENA.0.get() as usize) < ARENA_SIZE
}

/// A block from `ARENA` (zeroed), or null when it is full.
fn arena_alloc(layout: Layout) -> *mut u8 {
    let align = layout.align().max(8);
    let mut next = ARENA_NEXT.load(Ordering::Relaxed);
    loop {
        let start = (next + align - 1) & !(align - 1);
        let end = start + layout.size();
        if end > ARENA_SIZE {
            return std::ptr::null_mut();
        }
        match ARENA_NEXT.compare_exchange_weak(next, end, Ordering::Relaxed, Ordering::Relaxed) {
            // SAFETY: within the area.
            Ok(_) => return unsafe { (ARENA.0.get() as *mut u8).add(start) },
            Err(n) => next = n,
        }
    }
}

/// Cut the allocations from here on from `ARENA` (with mimalloc), until
/// `startup_end`: for what a program's start-up builds to keep.
pub fn startup_begin() {
    if choice() == MIMALLOC {
        CHOICE.store(STARTUP, Ordering::Relaxed);
    }
}

pub fn startup_end() {
    if CHOICE.load(Ordering::Relaxed) == STARTUP {
        CHOICE.store(MIMALLOC, Ordering::Relaxed);
    }
}

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

/// From this size on, blocks go to the system's allocator.
const LARGE: usize = 32 * 1024;

/// Whether a block of `size` bytes is mimalloc's (when mimalloc is in use).
#[inline(always)]
fn small(size: usize) -> bool {
    size < LARGE
}

/// The allocator in use, for diagnostics.
pub fn name() -> &'static str {
    match choice() {
        SYSTEM => "system",
        _ => "mimalloc",
    }
}

/// A start-up block: from `ARENA`, or as mimalloc would give it.
#[cold]
unsafe fn startup_alloc(layout: Layout) -> *mut u8 {
    let p = arena_alloc(layout);
    if !p.is_null() {
        return p;
    }
    if small(layout.size()) {
        unsafe { mimalloc::MiMalloc.alloc(layout) }
    } else {
        unsafe { System.alloc(layout) }
    }
}

// SAFETY: a block goes back to the allocator it came from: the one chosen
// for the process, and with mimalloc, the one its size picks (the same
// size comes back with it); a block whose size crosses `LARGE` in a
// `realloc` is moved from one to the other.
unsafe impl GlobalAlloc for Allocator {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let c = choice();
        if c == MIMALLOC && small(layout.size()) {
            unsafe { mimalloc::MiMalloc.alloc(layout) }
        } else if c == STARTUP {
            unsafe { startup_alloc(layout) }
        } else {
            unsafe { System.alloc(layout) }
        }
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let c = choice();
        if c == MIMALLOC && small(layout.size()) {
            unsafe { mimalloc::MiMalloc.alloc_zeroed(layout) }
        } else if c == STARTUP {
            // (The area is zeroed and never reused; the fall-backs are
            // not.)
            let p = arena_alloc(layout);
            if !p.is_null() {
                return p;
            }
            if small(layout.size()) {
                unsafe { mimalloc::MiMalloc.alloc_zeroed(layout) }
            } else {
                unsafe { System.alloc_zeroed(layout) }
            }
        } else {
            unsafe { System.alloc_zeroed(layout) }
        }
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // A start-up block stays.
        if in_arena(ptr) {
            return;
        }
        if choice() != SYSTEM && small(layout.size()) {
            unsafe { mimalloc::MiMalloc.dealloc(ptr, layout) }
        } else {
            unsafe { System.dealloc(ptr, layout) }
        }
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // A start-up block grows into a new one (from the area too while
        // starting up).
        if in_arena(ptr) {
            return unsafe {
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                let new = self.alloc(new_layout);
                if !new.is_null() {
                    std::ptr::copy_nonoverlapping(ptr, new, layout.size().min(new_size));
                }
                new
            };
        }
        if choice() == SYSTEM {
            return unsafe { System.realloc(ptr, layout, new_size) };
        }
        match (small(layout.size()), small(new_size)) {
            (true, true) => unsafe { mimalloc::MiMalloc.realloc(ptr, layout, new_size) },
            (false, false) => unsafe { System.realloc(ptr, layout, new_size) },
            // Crossing over: a new block from the other allocator.
            _ => unsafe {
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                let new = self.alloc(new_layout);
                if !new.is_null() {
                    std::ptr::copy_nonoverlapping(ptr, new, layout.size().min(new_size));
                    self.dealloc(ptr, layout);
                }
                new
            },
        }
    }
}
