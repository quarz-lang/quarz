//! The offsets compiled code uses to build activations and to reach the
//! interpreter's call stack, and a signature of them: a program built
//! against one runtime refuses to start on another.

use std::mem::{offset_of, size_of};

use crate::interp::{Hot, Interp};
use crate::vm::Activation;

pub const ACT_SIZE: usize = size_of::<Activation>();
/// Space compiled code reserves for an `Activation` it builds itself
/// (`qz_enter`): at least its size (asserted below).
pub const ACT_BUF_SIZE: usize = 320;
const _: () = assert!(ACT_SIZE <= ACT_BUF_SIZE);
const _: () = assert!(std::mem::align_of::<Activation>() <= 16);
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
pub const ACT_ARGS_OWNED: usize = offset_of!(Activation, args_owned);

pub const HOT_STACK_PTR: usize = offset_of!(Interp, hot) + offset_of!(Hot, stack_ptr);
pub const HOT_STACK_LEN: usize = offset_of!(Interp, hot) + offset_of!(Hot, stack_len);
pub const HOT_STACK_CAP: usize = offset_of!(Interp, hot) + offset_of!(Hot, stack_cap);
pub const HOT_LIMIT_PTR: usize = offset_of!(Interp, hot) + offset_of!(Hot, limit_ptr);
pub const HOT_TYPED_STATUS: usize = offset_of!(Interp, hot) + offset_of!(Hot, typed_status);
pub const CURRENT_TASK: usize = offset_of!(Interp, current_task_id);
/// Where an object's fields start, from its allocation (after the counts
/// and the header: see `value::Object`).
pub const OBJECT_FIELDS_OFF: usize =
    size_of::<crate::rc::Inner<crate::value::ObjectOf<std::cell::UnsafeCell<[u64; 0]>>>>();
/// Where an object's layout keeps its field offsets (a pointer to `u32`
/// byte offsets from the fields' start; the layout's address is the
/// object's first word).
pub const FIELD_LAYOUT_OFFSETS: usize = std::mem::offset_of!(crate::value::FieldLayout, offsets);
/// The marks of word fields whose value is kept aside (see
/// `value::Object`).
pub const FIELD_INT_MARK: i64 = crate::value::INT_MARK;
pub const FIELD_FLOAT_MARK: u64 = crate::value::FLOAT_MARK;
pub const FIELD_BOOL_MARK: u64 = crate::value::BOOL_MARK;

/// The errors `ffi::qz_raise` raises.
pub const RAISE_OVERFLOW: u32 = 0;
pub const RAISE_ZERO_DIVISION: u32 = 1;
pub const RAISE_UNSOUND: u32 = 2;

/// The size of a value, as compiled code lays out its registers and an
/// object's value fields (`quarz_ir::VALUE_BYTES`, which the lowering's
/// field offsets use too; `value.rs` asserts `Value`'s size).
pub const VALUE_SIZE: usize = quarz_ir::VALUE_BYTES as usize;

/// The tags of the `Value`s compiled code builds and tests inline: they
/// are `Value`'s discriminants (`value.rs` declares them so, `repr(u8)`).
pub const TAG_NIL: u8 = 0;
pub const TAG_BOOL: u8 = 1;
pub const TAG_INT: u8 = 2;
pub const TAG_FLOAT: u8 = 3;
pub const TAG_CLASS: u8 = 5;
pub const TAG_ARRAY: u8 = 10;
pub const TAG_OBJECT: u8 = 16;
/// Tags below this hold no reference-counted payload (`Value` puts the
/// variants without reference counting first).
pub const NEEDS_DROP_FROM: u64 = 8;
/// Where a `Bool`'s byte and a `Class`'s id are in a value: right after
/// the tag, as `repr(u8)` lays out a variant whose payload is smaller than
/// a word (`check` verifies both at start-up). Every other payload is at
/// the next word.
pub const BOOL_OFF: usize = 1;
pub const CLASS_OFF: usize = 4;
/// Where an object's field layout pointer is, from its allocation (the
/// header's first word, after the allocation's two counts).
pub const OBJECT_FIELDS_PTR_OFF: usize = offset_of!(
    crate::rc::Inner<crate::value::ObjectOf<std::cell::UnsafeCell<[u64; 0]>>>,
    value
) + offset_of!(
    crate::value::ObjectOf<std::cell::UnsafeCell<[u64; 0]>>,
    layout
);

/// The statuses the runtime's entries return to compiled code.
pub const STATUS_OK: u32 = 0;
pub const STATUS_RAISE: u32 = 1;
pub const STATUS_BREAK: u32 = 2;
pub const STATUS_NEXT: u32 = 3;
pub const STATUS_RETURN: u32 = 4;
pub const STATUS_RETRY: u32 = 5;
pub const STATUS_EXIT: u32 = 6;
/// `qz_enter_virtual` ran the whole call itself (the result is in
/// `regs[dst]`, the argument area is empty).
pub const STATUS_DONE: u32 = 7;
/// A typed entry's result did not fit its declared type: it is boxed in
/// the caller's `out` instead (compiled code writes and reads it).
pub const STATUS_BOXED: u32 = 8;

/// The operand tag of a call's kind in `qz_op_call`'s descriptor:
/// `CallKind`, written by the generator and decoded by `ffi_ops`.
pub const CALL_METHOD: u32 = 0;
pub const CALL_SEND: u32 = 1;
pub const CALL_CONSTRUCT: u32 = 2;
pub const CALL_CONSTRUCT_RECV: u32 = 3;
pub const CALL_PROC: u32 = 4;
pub const CALL_YIELD: u32 = 5;
pub const CALL_SUPER: u32 = 6;
pub const CALL_RAISE: u32 = 7;
pub const CALL_INSTANCE_EXEC: u32 = 8;
pub const CALL_FUNCTION: u32 = 9;

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
        HOT_TYPED_STATUS,
        CURRENT_TASK,
        OBJECT_FIELDS_OFF,
        FIELD_LAYOUT_OFFSETS,
        FIELD_INT_MARK as usize,
        FIELD_FLOAT_MARK as usize,
        FIELD_BOOL_MARK as usize,
        quarz_ir::VALUE_BYTES as usize,
        RAISE_OVERFLOW as usize,
        RAISE_ZERO_DIVISION as usize,
        RAISE_UNSOUND as usize,
        ACT_BUF_SIZE,
        VALUE_SIZE,
        TAG_NIL as usize,
        TAG_BOOL as usize,
        TAG_INT as usize,
        TAG_FLOAT as usize,
        TAG_CLASS as usize,
        TAG_ARRAY as usize,
        TAG_OBJECT as usize,
        NEEDS_DROP_FROM as usize,
        BOOL_OFF,
        CLASS_OFF,
        OBJECT_FIELDS_PTR_OFF,
        STATUS_OK as usize,
        STATUS_RAISE as usize,
        STATUS_BREAK as usize,
        STATUS_NEXT as usize,
        STATUS_RETURN as usize,
        STATUS_RETRY as usize,
        STATUS_EXIT as usize,
        STATUS_DONE as usize,
        STATUS_BOXED as usize,
        CALL_METHOD as usize,
        CALL_SEND as usize,
        CALL_CONSTRUCT as usize,
        CALL_CONSTRUCT_RECV as usize,
        CALL_PROC as usize,
        CALL_YIELD as usize,
        CALL_SUPER as usize,
        CALL_RAISE as usize,
        CALL_INSTANCE_EXEC as usize,
        CALL_FUNCTION as usize,
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
        // Objects: their kind, the references a word each, as `Vec`.
        let o = crate::value::Object::new(0, crate::value::Fields::new());
        let objects = ArrayData::Objects(vec![o]);
        // SAFETY: reading the bytes of a live value.
        let (kind, words) = unsafe {
            let base = &objects as *const ArrayData as *const u8;
            let kind = *base.add(ARRAY_KIND_OFF);
            let words = std::ptr::read(base.add(ARRAY_VEC_OFF) as *const [usize; 3]);
            (kind, words)
        };
        assert_eq!(
            kind,
            crate::value::ARRAY_KIND_OBJECTS,
            "ArrayData layout changed: kind byte"
        );
        assert_eq!(words[l.len / 8], 1, "ArrayData layout changed: objects");
        assert_eq!(
            std::mem::size_of::<crate::rc::Rc<crate::value::Object>>(),
            8
        );
    }
    assert_eq!(
        crate::value::Value::array(Vec::new()).type_tag(),
        10,
        "Value layout changed: Array tag"
    );
    // SAFETY: a zeroed `Option<Rc<_>>` is `None`, verified here before
    // compiled code relies on it.
    unsafe {
        let none: Option<crate::rc::Rc<crate::value::Frame>> = None;
        assert_eq!(
            std::mem::transmute::<Option<crate::rc::Rc<crate::value::Frame>>, usize>(none),
            0,
            "Option<Rc> layout changed"
        );
    }
    assert_eq!(
        crate::value::Value::Nil.type_tag(),
        0,
        "Value layout changed: Nil tag"
    );
    // A `Bool`'s byte and a `Class`'s id where compiled code reads and
    // writes them (`BOOL_OFF`, `CLASS_OFF`).
    {
        let b = crate::value::Value::Bool(true);
        let c = crate::value::Value::Class(0x0102_0304);
        // SAFETY: reading the bytes of live values, within their size.
        let (byte, id) = unsafe {
            let bp = &b as *const crate::value::Value as *const u8;
            let cp = &c as *const crate::value::Value as *const u8;
            (
                *bp.add(BOOL_OFF),
                std::ptr::read_unaligned(cp.add(CLASS_OFF) as *const u32),
            )
        };
        assert_eq!(byte, 1, "Value layout changed: a Bool's byte");
        assert_eq!(id, 0x0102_0304, "Value layout changed: a Class's id");
    }
}
