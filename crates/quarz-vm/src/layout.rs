//! The offsets compiled code uses to build activations and to reach the
//! interpreter's call stack, and a signature of them: a program built
//! against one runtime refuses to start on another.

use std::mem::{offset_of, size_of};

use crate::interp::{Hot, Interp};
use crate::vm::Activation;

pub const ACT_SIZE: usize = size_of::<Activation>();
pub const ACT_FID: usize = offset_of!(Activation, fid);
pub const ACT_TASK: usize = offset_of!(Activation, task);
pub const ACT_LINE: usize = offset_of!(Activation, line);
pub const ACT_FILE: usize = offset_of!(Activation, file);
pub const ACT_SELF: usize = offset_of!(Activation, self_val);
pub const ACT_FRAME: usize = offset_of!(Activation, frame);
pub const ACT_BLOCK: usize = offset_of!(Activation, block);
pub const ACT_METHOD_TAG: usize = offset_of!(Activation, method_tag);
pub const ACT_CLOSURE_TAG: usize = offset_of!(Activation, closure_tag);
pub const ACT_PROVIDED: usize = offset_of!(Activation, provided);
pub const ACT_ARGS_PTR: usize = offset_of!(Activation, args_ptr);
pub const ACT_NARGS: usize = offset_of!(Activation, nargs);
pub const ACT_YIELD_CALLER: usize = offset_of!(Activation, yield_caller);
pub const ACT_SP: usize = offset_of!(Activation, sp);
pub const ACT_NATIVE: usize = offset_of!(Activation, native);

pub const HOT_STACK_PTR: usize = offset_of!(Interp, hot) + offset_of!(Hot, stack_ptr);
pub const HOT_STACK_LEN: usize = offset_of!(Interp, hot) + offset_of!(Hot, stack_len);
pub const HOT_STACK_CAP: usize = offset_of!(Interp, hot) + offset_of!(Hot, stack_cap);
pub const HOT_LIMIT_PTR: usize = offset_of!(Interp, hot) + offset_of!(Hot, limit_ptr);
pub const CURRENT_TASK: usize = offset_of!(Interp, current_task_id);
/// The heap box layout compiled code reads (see `heap`).
pub const HEAP_VALUE_OFF: usize = crate::heap::VALUE_OFF;
pub const HEAP_KIND_OFF: usize = crate::heap::KIND_OFF;
pub const KIND_ARRAY: u8 = crate::heap::Kind::Array as u8;
pub const KIND_OBJECT: u8 = crate::heap::Kind::Object as u8;
pub const OBJECT_TAG: u64 = crate::heap::OBJECT_TAG;

/// Everything above, folded into one number.
pub const SIGNATURE: u64 = {
    let xs = [
        ACT_SIZE,
        ACT_FID,
        ACT_TASK,
        ACT_LINE,
        ACT_FILE,
        ACT_SELF,
        ACT_FRAME,
        ACT_BLOCK,
        ACT_METHOD_TAG,
        ACT_CLOSURE_TAG,
        ACT_PROVIDED,
        ACT_ARGS_PTR,
        ACT_NARGS,
        ACT_YIELD_CALLER,
        ACT_SP,
        ACT_NATIVE,
        HOT_STACK_PTR,
        HOT_STACK_LEN,
        HOT_STACK_CAP,
        HOT_LIMIT_PTR,
        CURRENT_TASK,
        HEAP_VALUE_OFF,
        HEAP_KIND_OFF,
        KIND_ARRAY as usize,
        KIND_OBJECT as usize,
        OBJECT_TAG as usize,
        crate::value::VALUE_SIZE,
    ];
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut i = 0;
    while i < xs.len() {
        h ^= xs[i] as u64;
        h = h.wrapping_mul(0x0100_0000_01b3);
        i += 1;
    }
    h
};

/// Where a `Vec<Value>` keeps its pointer, length and capacity (byte
/// offsets), found by probing one: the standard library does not fix
/// them. Compiled code reads arrays through them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VecLayout {
    pub ptr: usize,
    pub len: usize,
    pub cap: usize,
}

pub fn vec_layout() -> VecLayout {
    let mut v: Vec<crate::value::Value> = Vec::with_capacity(7);
    v.push(crate::value::Value::Nil);
    v.push(crate::value::Value::Nil);
    v.push(crate::value::Value::Nil);
    let ptr = v.as_ptr() as usize;
    // SAFETY: a `Vec` is three words; which is which is what we find out.
    let words: [usize; 3] = unsafe { std::ptr::read(&v as *const Vec<_> as *const [usize; 3]) };
    let find = |x: usize| words.iter().position(|w| *w == x).expect("Vec layout") * 8;
    let layout = VecLayout {
        ptr: find(ptr),
        len: find(3),
        cap: find(7),
    };
    assert!(
        layout.ptr != layout.len && layout.len != layout.cap && layout.ptr != layout.cap,
        "Vec layout"
    );
    layout
}

/// `vec_layout` as one word (for the start-up check).
pub fn vec_layout_packed() -> u64 {
    let l = vec_layout();
    (l.ptr as u64) | ((l.len as u64) << 8) | ((l.cap as u64) << 16)
}

/// Where an array's data keeps its kind byte and its vector (byte
/// offsets from the `ArrayData`, which sits after the allocation's two
/// counts); `repr(C, u8)` fixes them.
/// Where an object keeps its class id (byte offset from the `Object`,
/// which sits after the allocation's two counts).
pub const OBJECT_CLASS_OFF: usize = 12;

pub const ARRAY_KIND_OFF: usize = 0;
pub const ARRAY_VEC_OFF: usize = 8;

/// Refuse to run code built against another layout, and check the bit
/// patterns the compiled code writes for "nothing".
pub fn check(sig: u64, vec: u64) {
    if sig != SIGNATURE || vec != vec_layout_packed() {
        eprintln!("quarz: this program was built against a different runtime; rebuild it");
        std::process::exit(70);
    }
    assert_eq!(
        std::mem::offset_of!(crate::value::Object, class),
        OBJECT_CLASS_OFF,
        "Object layout changed: class"
    );
    // The array data layout compiled code reads.
    {
        use crate::value::{ArrayData, ARRAY_KIND_INTS};
        let mut v: Vec<i64> = Vec::with_capacity(7);
        v.extend([1, 2, 3]);
        let ptr = v.as_ptr() as usize;
        let data = ArrayData::Ints(v);
        // SAFETY: reading the bytes of a live value.
        let (kind, words) = unsafe {
            let base = &data as *const ArrayData as *const u8;
            let kind = *base.add(ARRAY_KIND_OFF);
            let words = std::ptr::read(base.add(ARRAY_VEC_OFF) as *const [usize; 3]);
            (kind, words)
        };
        let l = vec_layout();
        assert_eq!(kind, ARRAY_KIND_INTS, "ArrayData layout changed: kind byte");
        assert_eq!(words[l.ptr / 8], ptr, "ArrayData layout changed: vector");
        assert_eq!(words[l.len / 8], 3, "ArrayData layout changed: vector");
        assert_eq!(words[l.cap / 8], 7, "ArrayData layout changed: vector");
    }
    assert_eq!(
        crate::value::Value::array(Vec::new()).heap_kind(),
        Some(crate::heap::Kind::Array),
        "Value layout changed: Array kind"
    );
    // SAFETY: a zeroed `Option<Rc<_>>` is `None`, verified here before
    // compiled code relies on it.
    unsafe {
        let none: Option<std::rc::Rc<crate::value::Frame>> = None;
        assert_eq!(
            std::mem::transmute::<Option<std::rc::Rc<crate::value::Frame>>, usize>(none),
            0,
            "Option<Rc> layout changed"
        );
    }
    assert_eq!(
        crate::value::Value::Nil.bits(),
        0,
        "Value layout changed: nil"
    );
}
