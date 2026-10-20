//! Run-time values.
//!
//! Immutable collections are reference-counted; updates use
//! `Rc::make_mut`, which modifies in place when the value is uniquely
//! referenced and copies otherwise (the "functional but in place"
//! behaviour described in the design documents).

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

/// The maps and sets of values, hashed with the Fx hasher.
pub type ValueMap = IndexMap<Value, Value, rustc_hash::FxBuildHasher>;
pub type ValueSet = IndexSet<Value, rustc_hash::FxBuildHasher>;
use num_bigint::BigInt;
use quarz_ir::{ClassId, FuncId, MethodId};
use smallvec::SmallVec;

use crate::heap::{
    kind_of, release, retain, Boxed, Dur, Heap, HeapBox, HeapBytes, HeapStr, Kind, KIND_OFF,
    VALUE_OFF,
};
use crate::interp::Flow;
use crate::sched::{ChannelInner, ScopeInner, SelectorState, TaskHandle};

/// An interned symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(pub u32);

#[derive(Default)]
pub struct SymbolTable {
    names: Vec<Rc<str>>,
    ids: HashMap<Rc<str>, Symbol>,
}

impl SymbolTable {
    pub fn intern(&mut self, name: &str) -> Symbol {
        if let Some(s) = self.ids.get(name) {
            return *s;
        }
        let rc: Rc<str> = Rc::from(name);
        let sym = Symbol(self.names.len() as u32);
        self.names.push(rc.clone());
        self.ids.insert(rc, sym);
        sym
    }

    pub fn name(&self, sym: Symbol) -> &Rc<str> {
        &self.names[sym.0 as usize]
    }
}

/// A local variable frame. Blocks keep a reference to the frame they were
/// created in.
#[derive(Debug)]
#[repr(C)]
pub struct Frame {
    /// Where the slots live and how many there are, for compiled code
    /// (set by `bind` when the slots are created or resized).
    pub slots_ptr: Cell<*const Value>,
    pub nslots: Cell<u32>,
    /// The parent frame, for compiled code (null at the top).
    pub parent_ptr: Cell<*const Frame>,
    pub slots: RefCell<SmallVec<[Value; 8]>>,
    pub parent: Option<Rc<Frame>>,
}

impl Frame {
    pub fn new(size: usize, parent: Option<Rc<Frame>>) -> Rc<Frame> {
        Frame::from_slots(smallvec::smallvec![Value::Nil; size], parent)
    }

    pub fn from_slots(slots: SmallVec<[Value; 8]>, parent: Option<Rc<Frame>>) -> Rc<Frame> {
        let parent_ptr = parent.as_ref().map_or(std::ptr::null(), Rc::as_ptr);
        let f = Rc::new(Frame {
            slots_ptr: Cell::new(std::ptr::null()),
            nslots: Cell::new(0),
            parent_ptr: Cell::new(parent_ptr),
            slots: RefCell::new(slots),
            parent,
        });
        f.bind();
        f
    }

    /// Point the slot view at the slot vector.
    pub fn bind(&self) {
        let slots = self.slots.borrow();
        self.slots_ptr.set(slots.as_ptr());
        self.nslots.set(slots.len() as u32);
    }

    pub fn get(&self, depth: u32, slot: u32) -> Value {
        let mut frame = self;
        for _ in 0..depth {
            frame = frame.parent.as_deref().expect("frame depth");
        }
        let slots = frame.slots.borrow();
        slots.get(slot as usize).cloned().unwrap_or(Value::Nil)
    }

    pub fn set(&self, depth: u32, slot: u32, value: Value) {
        let mut frame = self;
        for _ in 0..depth {
            frame = frame.parent.as_deref().expect("frame depth");
        }
        let mut slots = frame.slots.borrow_mut();
        let i = slot as usize;
        if i >= slots.len() {
            slots.resize(i + 1, Value::Nil);
            drop(slots);
            frame.bind();
            frame.slots.borrow_mut()[i] = value;
            return;
        }
        slots[i] = value;
    }
}

/// The fields of an object, stored inline for up to four.
pub type Fields = SmallVec<[Value; 4]>;

/// The elements of an array: boxed values, or unboxed machine integers
/// or floats when every element is one (`Array[Int]`/`Array[Float]`
/// usually are). The layout is fixed (`repr(C, u8)`: the kind byte, then
/// the vector at offset 8) so that compiled code reads elements directly.
#[derive(Clone, Debug)]
#[repr(C, u8)]
pub enum ArrayData {
    Values(Vec<Value>),
    Ints(Vec<i64>),
    Floats(Vec<f64>),
}

pub const ARRAY_KIND_VALUES: u8 = 0;
pub const ARRAY_KIND_INTS: u8 = 1;
pub const ARRAY_KIND_FLOATS: u8 = 2;

/// Iterates an array's elements as values.
pub enum ArrayIter<'a> {
    Values(std::slice::Iter<'a, Value>),
    Ints(std::slice::Iter<'a, i64>),
    Floats(std::slice::Iter<'a, f64>),
}

impl Iterator for ArrayIter<'_> {
    type Item = Value;

    fn next(&mut self) -> Option<Value> {
        match self {
            ArrayIter::Values(it) => it.next().cloned(),
            ArrayIter::Ints(it) => it.next().map(|i| Value::Int(*i)),
            ArrayIter::Floats(it) => it.next().map(|f| Value::Float(*f)),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            ArrayIter::Values(it) => it.size_hint(),
            ArrayIter::Ints(it) => it.size_hint(),
            ArrayIter::Floats(it) => it.size_hint(),
        }
    }
}

impl ExactSizeIterator for ArrayIter<'_> {}

impl DoubleEndedIterator for ArrayIter<'_> {
    fn next_back(&mut self) -> Option<Value> {
        match self {
            ArrayIter::Values(it) => it.next_back().cloned(),
            ArrayIter::Ints(it) => it.next_back().map(|i| Value::Int(*i)),
            ArrayIter::Floats(it) => it.next_back().map(|f| Value::Float(*f)),
        }
    }
}

impl ArrayData {
    /// Store `items` unboxed when they are all machine integers or all
    /// floats (and there are some), boxed otherwise.
    pub fn from_values(items: Vec<Value>) -> ArrayData {
        if items.is_empty() {
            return ArrayData::Values(items);
        }
        if items.iter().all(|v| matches!(v.view(), V::Int(_))) {
            return ArrayData::Ints(
                items
                    .iter()
                    .map(|v| match v.view() {
                        V::Int(i) => i,
                        _ => unreachable!(),
                    })
                    .collect(),
            );
        }
        if items.iter().all(|v| matches!(v.view(), V::Float(_))) {
            return ArrayData::Floats(
                items
                    .iter()
                    .map(|v| match v.view() {
                        V::Float(f) => f,
                        _ => unreachable!(),
                    })
                    .collect(),
            );
        }
        ArrayData::Values(items)
    }

    pub fn kind(&self) -> u8 {
        match self {
            ArrayData::Values(_) => ARRAY_KIND_VALUES,
            ArrayData::Ints(_) => ARRAY_KIND_INTS,
            ArrayData::Floats(_) => ARRAY_KIND_FLOATS,
        }
    }

    pub fn len(&self) -> usize {
        match self {
            ArrayData::Values(v) => v.len(),
            ArrayData::Ints(v) => v.len(),
            ArrayData::Floats(v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, i: usize) -> Option<Value> {
        match self {
            ArrayData::Values(v) => v.get(i).cloned(),
            ArrayData::Ints(v) => v.get(i).map(|i| Value::Int(*i)),
            ArrayData::Floats(v) => v.get(i).map(|f| Value::Float(*f)),
        }
    }

    pub fn iter(&self) -> ArrayIter<'_> {
        match self {
            ArrayData::Values(v) => ArrayIter::Values(v.iter()),
            ArrayData::Ints(v) => ArrayIter::Ints(v.iter()),
            ArrayData::Floats(v) => ArrayIter::Floats(v.iter()),
        }
    }

    /// The elements as boxed values: borrowed when they are stored so,
    /// a fresh vector otherwise.
    pub fn values(&self) -> std::borrow::Cow<'_, [Value]> {
        match self {
            ArrayData::Values(v) => std::borrow::Cow::Borrowed(v.as_slice()),
            _ => std::borrow::Cow::Owned(self.iter().collect()),
        }
    }

    pub fn to_values(&self) -> Vec<Value> {
        self.iter().collect()
    }

    pub fn into_values(self) -> Vec<Value> {
        match self {
            ArrayData::Values(v) => v,
            other => other.iter().collect(),
        }
    }

    /// Switch to boxed storage and give the vector to `f`.
    pub fn with_values<R>(&mut self, f: impl FnOnce(&mut Vec<Value>) -> R) -> R {
        if !matches!(self, ArrayData::Values(_)) {
            *self = ArrayData::Values(self.to_values());
        }
        match self {
            ArrayData::Values(v) => f(v),
            _ => unreachable!(),
        }
    }

    /// Append `v`: in the unboxed storage when it fits (an empty boxed
    /// array takes the kind of its first element), boxing everything
    /// otherwise.
    pub fn push(&mut self, v: Value) {
        match (&mut *self, v.view()) {
            (ArrayData::Ints(xs), V::Int(i)) => xs.push(i),
            (ArrayData::Floats(xs), V::Float(f)) => xs.push(f),
            (ArrayData::Values(xs), V::Int(i)) if xs.is_empty() => {
                *self = ArrayData::Ints(vec![i]);
            }
            (ArrayData::Values(xs), V::Float(f)) if xs.is_empty() => {
                *self = ArrayData::Floats(vec![f]);
            }
            (ArrayData::Values(xs), _) => xs.push(v),
            _ => self.with_values(|xs| xs.push(v)),
        }
    }

    /// `self[i] = v` for an index in range.
    pub fn set(&mut self, i: usize, v: Value) {
        match (&mut *self, v.view()) {
            (ArrayData::Ints(xs), V::Int(x)) => xs[i] = x,
            (ArrayData::Floats(xs), V::Float(x)) => xs[i] = x,
            (ArrayData::Values(xs), _) => xs[i] = v,
            _ => self.with_values(|xs| xs[i] = v),
        }
    }

    pub fn extend_from(&mut self, other: &ArrayData) {
        match (&mut *self, other) {
            (ArrayData::Ints(xs), ArrayData::Ints(ys)) => xs.extend_from_slice(ys),
            (ArrayData::Floats(xs), ArrayData::Floats(ys)) => xs.extend_from_slice(ys),
            (ArrayData::Values(xs), ArrayData::Values(ys)) => xs.extend_from_slice(ys),
            (ArrayData::Values(xs), _) if xs.is_empty() => *self = other.clone(),
            _ => {
                let more = other.to_values();
                self.with_values(|xs| xs.extend(more));
            }
        }
    }
}

/// An instance of a user-defined class, data type, enum variant or
/// exception.
#[derive(Debug)]
#[repr(C)]
pub struct Object {
    /// Where the fields live, for compiled code: set by `bind_fields`
    /// whenever the field vector is created or replaced. First in the
    /// layout, right after the allocation's two counts.
    pub fields_ptr: Cell<*const Value>,
    pub nfields: Cell<u32>,
    pub class: ClassId,
    pub fields: RefCell<Fields>,
    /// Exceptions only: what was captured when raised.
    pub exc: RefCell<Option<Box<ExcInfo>>>,
}

/// The backtrace and cause of a raised exception.
#[derive(Debug, Default)]
pub struct ExcInfo {
    pub backtrace: Option<Rc<Vec<String>>>,
    pub cause: Option<Value>,
}

impl Object {
    pub fn new(class: ClassId, fields: Fields) -> Heap<Object> {
        let o = Heap::new(Object {
            fields_ptr: Cell::new(std::ptr::null()),
            nfields: Cell::new(0),
            class,
            fields: RefCell::new(fields),
            exc: RefCell::new(None),
        });
        o.bind_fields();
        o
    }

    /// An object whose `n` fields are moved in from `src`, built in its
    /// allocation (no temporary to copy).
    ///
    /// # Safety
    /// `src` points at `n` initialized values that the caller gives up
    /// (they are moved, not cloned, and must not be dropped by it).
    pub unsafe fn with_fields_from(class: ClassId, src: *const Value, n: usize) -> Heap<Object> {
        let mut fields = Fields::with_capacity(n);
        // SAFETY: the caller gives up the `n` values at `src`.
        unsafe {
            std::ptr::copy_nonoverlapping(src, fields.as_mut_ptr(), n);
            fields.set_len(n);
        }
        Object::new(class, fields)
    }

    /// Point the field view at the field vector (after it was created,
    /// resized or replaced).
    /// The backtrace captured when this (exception) object was raised.
    pub fn backtrace(&self) -> Option<Rc<Vec<String>>> {
        self.exc.borrow().as_ref().and_then(|e| e.backtrace.clone())
    }

    pub fn set_backtrace(&self, bt: Option<Rc<Vec<String>>>) {
        self.exc
            .borrow_mut()
            .get_or_insert_with(Default::default)
            .backtrace = bt;
    }

    pub fn cause(&self) -> Option<Value> {
        self.exc.borrow().as_ref().and_then(|e| e.cause.clone())
    }

    pub fn set_cause(&self, cause: Option<Value>) {
        self.exc
            .borrow_mut()
            .get_or_insert_with(Default::default)
            .cause = cause;
    }

    pub fn bind_fields(&self) {
        let f = self.fields.borrow();
        self.fields_ptr.set(f.as_ptr());
        self.nfields.set(f.len() as u32);
    }
}

/// A block implemented in Rust (used by natives that iterate).
pub type NativeBlock =
    Rc<dyn Fn(&crate::interp::Interp, crate::interp::ArgVec) -> crate::interp::EvalResult>;

/// The body a closure runs: a QIR function, a method reference
/// (`&:name`), or a native function.
pub enum ClosureBody {
    Func(FuncId),
    /// `&:name`: call `name` on the first argument. The cache holds the
    /// method found for the last (class, argument count); the method is
    /// the checker's resolution for the parameter's static type (an
    /// extension method is only reachable through it).
    MethodName(
        Rc<str>,
        Cell<Option<(ClassId, usize, MethodId)>>,
        Option<MethodId>,
    ),
    /// `obj.:name`: call `name` on a captured receiver.
    BoundMethod {
        recv: Value,
        name: Rc<str>,
    },
    Native(NativeBlock),
}

impl std::fmt::Debug for ClosureBody {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClosureBody::Func(id) => write!(f, "Func({id})"),
            ClosureBody::MethodName(n, ..) => write!(f, "MethodName({n})"),
            ClosureBody::BoundMethod { name, .. } => write!(f, "BoundMethod({name})"),
            ClosureBody::Native(_) => write!(f, "Native"),
        }
    }
}

/// A block, lambda or procedure value.
#[derive(Debug)]
pub struct Closure {
    pub body: ClosureBody,
    pub frame: Option<Rc<Frame>>,
    pub self_val: Value,
    /// How many parameters a single tuple argument is spread over.
    pub destructure: Option<usize>,
    pub is_lambda: bool,
    /// Identifies the block for `break`.
    pub tag: u64,
    /// The method the block was written in (for `yield` and `return`).
    pub method_block: Option<Value>,
    pub method_tag: u64,
    /// Source file index (for `__FILE__`).
    pub file: u32,
}

#[derive(Debug)]
pub struct RangeVal {
    pub lo: Value,
    pub hi: Value,
    pub exclusive: bool,
}

#[derive(Debug)]
pub struct RegexpVal {
    pub regex: regex::Regex,
    pub source: String,
    pub flags: String,
}

#[derive(Debug)]
pub struct MatchDataVal {
    pub text: Rc<str>,
    /// Byte ranges of the whole match and the groups.
    pub groups: Vec<Option<(usize, usize)>>,
    pub names: Vec<(String, usize)>,
}

/// A lazily evaluated enumerator: re-invokes `method` on `recv` with a
/// block.
#[derive(Debug)]
pub struct EnumeratorVal {
    pub recv: Value,
    pub method: Rc<str>,
    pub args: Vec<Value>,
    /// Buffered elements for `next`.
    pub buffer: RefCell<Option<Vec<Value>>>,
    pub position: Cell<usize>,
}

#[derive(Debug)]
pub enum IoKind {
    Stdin,
    Stdout,
    Stderr,
    /// An open file (`File.open`).
    File(RefCell<FileHandle>),
    /// A connected stream socket (TCP or Unix), non-blocking, driven by
    /// the scheduler's reactor.
    Socket(RefCell<SocketState>),
    /// A listening socket (`TCPServer`, `UNIXServer`).
    Listener(RefCell<ListenerState>),
    Udp(RefCell<UdpState>),
}

#[derive(Debug)]
pub enum Stream {
    Tcp(std::net::TcpStream),
    Unix(std::os::unix::net::UnixStream),
}

impl Stream {
    pub fn fd(&self) -> std::os::fd::RawFd {
        use std::os::fd::AsRawFd;
        match self {
            Stream::Tcp(s) => s.as_raw_fd(),
            Stream::Unix(s) => s.as_raw_fd(),
        }
    }
}

impl std::io::Read for Stream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self {
            Stream::Tcp(s) => s.read(buf),
            Stream::Unix(s) => s.read(buf),
        }
    }
}

impl std::io::Write for Stream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            Stream::Tcp(s) => s.write(buf),
            Stream::Unix(s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            Stream::Tcp(s) => s.flush(),
            Stream::Unix(s) => s.flush(),
        }
    }
}

#[derive(Debug)]
pub struct SocketState {
    /// `None` once closed: the descriptor is released at `close`, not
    /// when the value is dropped.
    pub stream: Option<Stream>,
    pub unix: bool,
    /// Bytes read from the socket but not yet consumed.
    pub rbuf: Vec<u8>,
    pub eof: bool,
    pub closed: bool,
    /// The path of a Unix socket.
    pub path: Option<String>,
    /// The addresses as of the connection (valid after the peer hangs
    /// up, when the system no longer reports them).
    pub local: Option<std::net::SocketAddr>,
    pub peer: Option<std::net::SocketAddr>,
}

#[derive(Debug)]
pub enum Listener {
    Tcp(std::net::TcpListener),
    Unix(std::os::unix::net::UnixListener),
}

impl Listener {
    pub fn fd(&self) -> std::os::fd::RawFd {
        use std::os::fd::AsRawFd;
        match self {
            Listener::Tcp(l) => l.as_raw_fd(),
            Listener::Unix(l) => l.as_raw_fd(),
        }
    }
}

#[derive(Debug)]
pub struct ListenerState {
    pub listener: Option<Listener>,
    pub unix: bool,
    pub closed: bool,
    pub path: Option<String>,
}

#[derive(Debug)]
pub struct UdpState {
    pub socket: Option<std::net::UdpSocket>,
    pub closed: bool,
}

/// The state of an open file: a buffered reader or writer over it.
#[derive(Debug, Default)]
pub struct FileHandle {
    pub path: String,
    pub reader: Option<std::io::BufReader<std::fs::File>>,
    pub writer: Option<std::io::BufWriter<std::fs::File>>,
    pub closed: bool,
}

#[derive(Debug)]
pub struct IoVal {
    pub kind: IoKind,
}

/// A non-local flow caught by an `ensure` handler, carried through the
/// handler's body and continued by `Resume`.
pub type FlowBox = RefCell<Option<Flow>>;

/// A Quarz value in one machine word (see `docs/05-execution.md` §5).
///
/// The low bits say what it is:
///
/// - `…1`: an `Int` of 63 bits, shifted left by one;
/// - `…10`: a `Float` (a "flonum": the double's bits rotated so that
///   the exponent's redundant top bits make room for the tag; doubles
///   outside the covered range, and -0.0, live in a box);
/// - `…100`: nothing on the heap, bits 3-5 telling what: `false` (4),
///   `true` (12), a `Symbol` or a `Class` (their id above bit 8), or a
///   `Duration` of 58 bits of nanoseconds above bit 6 (a longer one,
///   beyond about four and a half years, lives in a box);
/// - `0`: `nil`;
/// - `…000`, nonzero: the address of a heap box (`heap::HeapBox`), whose
///   header holds the reference count and the kind.
///
/// Copying a value is a word copy plus, for a heap value, a count
/// increment; dropping one a decrement. `view` gives the value as an
/// enum to match on; `unpack` the same with the heap handles owned.
#[repr(transparent)]
pub struct Value(u64);

const FALSE_BITS: u64 = 0x04;
const TRUE_BITS: u64 = 0x0C;
const SYMBOL_TAG: u64 = 0x14;
const CLASS_TAG: u64 = 0x1C;
/// A `Duration` word: nanoseconds above bit 6.
const DURATION_TAG: u64 = 0x24;
const DURATION_SHIFT: u32 = 6;
/// The flonum of `0.0`.
const FLONUM_ZERO: u64 = 0x8000_0000_0000_0002;

/// Encode a double as a flonum, when its exponent allows it.
#[inline]
fn flonum(f: f64) -> Option<u64> {
    let bits = f.to_bits();
    let top = (bits >> 60) & 0x7;
    if bits != 0x3000_0000_0000_0000 && (top.wrapping_sub(3) & !1) == 0 {
        Some((bits.rotate_left(3) & !1) | 2)
    } else if bits == 0 {
        Some(FLONUM_ZERO)
    } else {
        None
    }
}

/// The double a flonum encodes.
#[inline]
fn unflonum(v: u64) -> f64 {
    if v == FLONUM_ZERO {
        return 0.0;
    }
    let b63 = v >> 63;
    f64::from_bits(((2 - b63) | (v & !3)).rotate_right(3))
}

/// A heap box's handle for each kind of heap value, as the `view` and
/// `unpack` of a value give them, and the constructors take them.
macro_rules! heap_variants {
    ($($variant:ident($ty:ty) => $kind:ident),* $(,)?) => {
        /// A value, borrowed, as an enum to match on.
        #[derive(Debug, Clone, Copy)]
        pub enum V<'a> {
            Nil,
            Bool(bool),
            Int(i64),
            Float(f64),
            Symbol(Symbol),
            Class(ClassId),
            Duration(i64),
            Str(&'a HeapStr),
            Bytes(&'a HeapBytes),
            $($variant(&'a Heap<$ty>),)*
        }

        /// A value, borrowed mutably: its heap handle can be replaced or,
        /// when unshared, its contents changed in place.
        pub enum VM<'a> {
            Nil,
            Bool(bool),
            Int(i64),
            Float(f64),
            Symbol(Symbol),
            Class(ClassId),
            Duration(i64),
            Str(&'a mut HeapStr),
            Bytes(&'a mut HeapBytes),
            $($variant(&'a mut Heap<$ty>),)*
        }

        /// A value, consumed, with its heap handle owned.
        pub enum U {
            Nil,
            Bool(bool),
            Int(i64),
            Float(f64),
            Symbol(Symbol),
            Class(ClassId),
            Duration(i64),
            Str(HeapStr),
            Bytes(HeapBytes),
            $($variant(Heap<$ty>),)*
        }

        impl U {
            /// Back to a value.
            #[inline]
            pub fn repack(self) -> Value {
                match self {
                    U::Nil => Value::Nil,
                    U::Bool(b) => Value::Bool(b),
                    U::Int(i) => Value::Int(i),
                    U::Float(f) => Value::Float(f),
                    U::Symbol(s) => Value::Symbol(s),
                    U::Class(c) => Value::Class(c),
                    U::Duration(d) => Value::Duration(d),
                    U::Str(s) => Value::from(s),
                    U::Bytes(b) => Value::from(b),
                    $(U::$variant(h) => Value::from(h),)*
                }
            }
        }

        #[allow(non_snake_case)]
        impl Value {
            $(
                #[inline]
                pub fn $variant(v: impl Into<Heap<$ty>>) -> Value {
                    Value(Heap::into_bits(v.into()))
                }
            )*

            /// The value as an enum, borrowed.
            #[inline]
            pub fn view(&self) -> V<'_> {
                let b = self.0;
                if b & 1 == 1 {
                    return V::Int((b as i64) >> 1);
                }
                if b & 3 == 2 {
                    return V::Float(unflonum(b));
                }
                if b & 7 == 4 {
                    return match (b >> 3) & 7 {
                        0 => V::Bool(false),
                        1 => V::Bool(true),
                        2 => V::Symbol(Symbol((b >> 8) as u32)),
                        3 => V::Class((b >> 8) as ClassId),
                        _ => V::Duration((b as i64) >> DURATION_SHIFT),
                    };
                }
                if b == 0 {
                    return V::Nil;
                }
                // SAFETY: a nonzero word with its low bits clear is the
                // address of a live box, and the handle types are
                // transparent over that address.
                unsafe {
                    match kind_of(b) {
                        Kind::Int => V::Int((*(b as *const HeapBox<i64>)).value),
                        Kind::Float => V::Float((*(b as *const HeapBox<f64>)).value),
                        Kind::Duration => V::Duration((*(b as *const HeapBox<Dur>)).value.0),
                        Kind::Str => V::Str(&*(self as *const Value as *const HeapStr)),
                        Kind::Bytes => V::Bytes(&*(self as *const Value as *const HeapBytes)),
                        $(Kind::$kind => V::$variant(&*(self as *const Value as *const Heap<$ty>)),)*
                    }
                }
            }

            /// The value as an enum, its heap handle borrowed mutably.
            #[inline]
            pub fn view_mut(&mut self) -> VM<'_> {
                let b = self.0;
                if b & 1 == 1 {
                    return VM::Int((b as i64) >> 1);
                }
                if b & 3 == 2 {
                    return VM::Float(unflonum(b));
                }
                if b & 7 == 4 {
                    return match (b >> 3) & 7 {
                        0 => VM::Bool(false),
                        1 => VM::Bool(true),
                        2 => VM::Symbol(Symbol((b >> 8) as u32)),
                        3 => VM::Class((b >> 8) as ClassId),
                        _ => VM::Duration((b as i64) >> DURATION_SHIFT),
                    };
                }
                if b == 0 {
                    return VM::Nil;
                }
                // SAFETY: as in `view`.
                unsafe {
                    match kind_of(b) {
                        Kind::Int => VM::Int((*(b as *const HeapBox<i64>)).value),
                        Kind::Float => VM::Float((*(b as *const HeapBox<f64>)).value),
                        Kind::Duration => VM::Duration((*(b as *const HeapBox<Dur>)).value.0),
                        Kind::Str => VM::Str(&mut *(self as *mut Value as *mut HeapStr)),
                        Kind::Bytes => VM::Bytes(&mut *(self as *mut Value as *mut HeapBytes)),
                        $(Kind::$kind => VM::$variant(&mut *(self as *mut Value as *mut Heap<$ty>)),)*
                    }
                }
            }

            /// The value as an enum, consumed: a heap handle is owned.
            #[inline]
            pub fn unpack(self) -> U {
                let b = self.0;
                std::mem::forget(self);
                if b & 1 == 1 {
                    return U::Int((b as i64) >> 1);
                }
                if b & 3 == 2 {
                    return U::Float(unflonum(b));
                }
                if b & 7 == 4 {
                    return match (b >> 3) & 7 {
                        0 => U::Bool(false),
                        1 => U::Bool(true),
                        2 => U::Symbol(Symbol((b >> 8) as u32)),
                        3 => U::Class((b >> 8) as ClassId),
                        _ => U::Duration((b as i64) >> DURATION_SHIFT),
                    };
                }
                if b == 0 {
                    return U::Nil;
                }
                // SAFETY: as in `view`; the reference moves into the handle.
                unsafe {
                    match kind_of(b) {
                        Kind::Int => {
                            let v = (*(b as *const HeapBox<i64>)).value;
                            release(b);
                            U::Int(v)
                        }
                        Kind::Float => {
                            let v = (*(b as *const HeapBox<f64>)).value;
                            release(b);
                            U::Float(v)
                        }
                        Kind::Duration => {
                            let v = (*(b as *const HeapBox<Dur>)).value.0;
                            release(b);
                            U::Duration(v)
                        }
                        Kind::Str => U::Str(HeapStr::from_bits(b)),
                        Kind::Bytes => U::Bytes(HeapBytes::from_bits(b)),
                        $(Kind::$kind => U::$variant(Heap::from_bits(b)),)*
                    }
                }
            }
        }
    };
}

heap_variants! {
    BigInt(BigInt) => BigInt,
    Array(ArrayData) => Array,
    Hash(ValueMap) => Hash,
    Set(ValueSet) => Set,
    Range(RangeVal) => Range,
    Regexp(RegexpVal) => Regexp,
    MatchData(MatchDataVal) => MatchData,
    Object(Object) => Object,
    Proc(Closure) => Proc,
    ArrayBuilder(RefCell<Vec<Value>>) => ArrayBuilder,
    HashBuilder(RefCell<ValueMap>) => HashBuilder,
    SetBuilder(RefCell<ValueSet>) => SetBuilder,
    StringBuilder(RefCell<String>) => StringBuilder,
    Channel(Rc<ChannelInner>) => Channel,
    Task(Rc<TaskHandle>) => Task,
    Scope(Rc<ScopeInner>) => Scope,
    Atom(RefCell<Value>) => Atom,
    Selector(RefCell<SelectorState>) => Selector,
    Enumerator(EnumeratorVal) => Enumerator,
    Io(IoVal) => Io,
    BytesBuilder(RefCell<Vec<u8>>) => BytesBuilder,
    Time(TimeVal) => Time,
    Random(RefCell<RandomState>) => Random,
    Flow(FlowBox) => Flow,
}

/// `nil`, to borrow (a `&Value::Nil` would be a temporary).
pub static NIL: Value = Value(0);

#[allow(non_upper_case_globals, non_snake_case)]
impl Value {
    pub const Nil: Value = Value(0);

    #[inline]
    pub fn Bool(b: bool) -> Value {
        Value(if b { TRUE_BITS } else { FALSE_BITS })
    }

    #[inline]
    pub fn Int(i: i64) -> Value {
        if (i << 1) >> 1 == i {
            Value(((i as u64) << 1) | 1)
        } else {
            Value(Heap::into_bits(Heap::new(i)))
        }
    }

    #[inline]
    pub fn Float(f: f64) -> Value {
        match flonum(f) {
            Some(bits) => Value(bits),
            None => Value(Heap::into_bits(Heap::new(f))),
        }
    }

    #[inline]
    pub fn Symbol(s: Symbol) -> Value {
        Value(((s.0 as u64) << 8) | SYMBOL_TAG)
    }

    #[inline]
    pub fn Class(c: ClassId) -> Value {
        Value(((c as u64) << 8) | CLASS_TAG)
    }

    #[inline]
    pub fn Duration(ns: i64) -> Value {
        if (ns << DURATION_SHIFT) >> DURATION_SHIFT == ns {
            Value(((ns as u64) << DURATION_SHIFT) | DURATION_TAG)
        } else {
            Value(Heap::into_bits(Heap::new(Dur(ns))))
        }
    }

    #[inline]
    pub fn Str(s: impl Into<HeapStr>) -> Value {
        Value(HeapStr::into_bits(s.into()))
    }

    #[inline]
    pub fn Bytes(b: impl Into<HeapBytes>) -> Value {
        Value(HeapBytes::into_bits(b.into()))
    }

    /// The word.
    #[inline]
    pub fn bits(&self) -> u64 {
        self.0
    }

    /// A value from its word, taking over the reference it holds.
    ///
    /// # Safety
    /// `bits` must be a value's word whose heap reference (if any) the
    /// caller gives up.
    #[inline]
    pub unsafe fn from_bits(bits: u64) -> Value {
        Value(bits)
    }

    /// Whether the value is a heap box (and so reference counted).
    #[inline]
    pub fn is_heap(&self) -> bool {
        self.0 & 7 == 0 && self.0 != 0
    }

    /// The kind of a heap value.
    #[inline]
    pub fn heap_kind(&self) -> Option<Kind> {
        if self.is_heap() {
            // SAFETY: a heap value's word is a live box's address.
            Some(unsafe { kind_of(self.0) })
        } else {
            None
        }
    }

    /// A copy that skips the reference count machinery for values that
    /// have none.
    #[inline]
    pub fn fast_clone(&self) -> Value {
        self.clone()
    }

    /// `*dst = *src` without a temporary.
    ///
    /// # Safety
    /// `dst` must point to writable space holding no live value.
    #[inline]
    pub unsafe fn clone_into(dst: *mut Value, src: &Value) {
        std::ptr::write(dst, src.clone());
    }

    /// Drop a value, skipping the destructor for those that need none.
    #[inline]
    pub fn fast_drop(self) {
        drop(self);
    }
}

impl Clone for Value {
    #[inline]
    fn clone(&self) -> Value {
        if self.is_heap() {
            // SAFETY: a heap value's word is a live box's address.
            unsafe { retain(self.0) };
        }
        Value(self.0)
    }
}

impl Drop for Value {
    #[inline]
    fn drop(&mut self) {
        if self.is_heap() {
            // SAFETY: a heap value's word is a live box's address, and
            // this handle's reference ends here.
            unsafe { release(self.0) };
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.view().fmt(f)
    }
}

impl<T: Boxed> From<Heap<T>> for Value {
    #[inline]
    fn from(h: Heap<T>) -> Value {
        Value(Heap::into_bits(h))
    }
}

impl From<HeapStr> for Value {
    #[inline]
    fn from(s: HeapStr) -> Value {
        Value(HeapStr::into_bits(s))
    }
}

impl From<HeapBytes> for Value {
    #[inline]
    fn from(b: HeapBytes) -> Value {
        Value(HeapBytes::into_bits(b))
    }
}

/// Compiled code reads and writes values by their bits and the heap
/// box layout; this checks the assumptions once at start-up.
pub fn check_heap_layout() {
    let value = Value::Str("layout");
    // The word is the box's address; the count is its first word.
    let strong_of = |v: &Value| -> usize {
        // SAFETY: a heap value's word is a live box's address.
        unsafe { *(v.bits() as *const usize) }
    };
    assert_eq!(strong_of(&value), 1, "heap layout changed: the count");
    let b = value.clone();
    assert_eq!(strong_of(&value), 2, "heap layout changed: the count");
    drop(b);
    assert_eq!(strong_of(&value), 1, "heap layout changed: the count");
    assert_eq!(
        value.heap_kind(),
        Some(Kind::Str),
        "heap layout changed: the kind"
    );
    assert_eq!(std::mem::offset_of!(crate::heap::Header, kind), KIND_OFF);
    let object = Value::Object(Object::new(0, Fields::new()));
    assert_eq!(
        object.bits() & 0xF,
        crate::heap::OBJECT_TAG,
        "object words carry their tag"
    );
    assert_eq!(object.heap_kind(), Some(Kind::Object));
    assert_eq!(value.bits() & 0xF, 0, "a string word is its box's address");
    assert_eq!(std::mem::offset_of!(HeapBox<Object>, value), VALUE_OFF);
    assert_eq!(std::mem::offset_of!(HeapBox<ArrayData>, value), VALUE_OFF);
    assert_eq!(std::mem::offset_of!(Object, fields_ptr), 0);
    assert_eq!(std::mem::offset_of!(Frame, slots_ptr), 0);
    assert_eq!(std::mem::offset_of!(Frame, nslots), 8);
    assert_eq!(std::mem::offset_of!(Frame, parent_ptr), 16);
    assert_eq!(Value::Int(5).bits(), 11, "value encoding changed: Int");
    assert_eq!(Value::Bool(false).bits(), FALSE_BITS);
    assert_eq!(Value::Bool(true).bits(), TRUE_BITS);
    assert_eq!(Value::Nil.bits(), 0);
    assert_eq!(Value::Class(3).bits(), (3 << 8) | CLASS_TAG);
    for ns in [
        0,
        1,
        -1,
        20_000_000,
        1 << 56,
        -(1 << 56),
        1 << 60,
        i64::MAX,
        i64::MIN,
    ] {
        match Value::Duration(ns).view() {
            V::Duration(m) => assert_eq!(ns, m, "duration round trip"),
            other => panic!("duration of {ns} viewed as {other:?}"),
        }
    }
    assert!(matches!(Value::Int(20_000_000).view(), V::Int(20_000_000)));
    for f in [0.0, 1.0, -2.5, 1e300, 1e-300, f64::NAN, f64::INFINITY, -0.0] {
        match Value::Float(f).view() {
            V::Float(g) => assert!(g.to_bits() == f.to_bits(), "flonum round trip of {f}"),
            other => panic!("flonum of {f} viewed as {other:?}"),
        }
    }
    for i in [
        0,
        1,
        -1,
        i64::MAX,
        i64::MIN,
        1 << 62,
        -(1 << 62),
        (1 << 62) - 1,
    ] {
        match Value::Int(i).view() {
            V::Int(j) => assert_eq!(i, j, "fixnum round trip"),
            other => panic!("Int {i} viewed as {other:?}"),
        }
    }
}

/// Size of a value in bytes, as compiled code lays out its registers.
pub const VALUE_SIZE: usize = 8;

const _: () = assert!(std::mem::size_of::<Value>() == VALUE_SIZE);

/// A pseudo-random generator (xoshiro256**), seeded with splitmix64.
#[derive(Clone, Debug)]
pub struct RandomState {
    pub seed: i64,
    s: [u64; 4],
}

impl RandomState {
    pub fn new(seed: i64) -> RandomState {
        let mut x = seed as u64;
        let mut s = [0u64; 4];
        for word in &mut s {
            x = x.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            *word = z ^ (z >> 31);
        }
        RandomState { seed, s }
    }

    pub fn next_u64(&mut self) -> u64 {
        let s = &mut self.s;
        let result = s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = s[3].rotate_left(45);
        result
    }

    /// A float in `[0, 1)`.
    pub fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }

    /// An integer in `[0, bound)` without modulo bias.
    pub fn below(&mut self, bound: u64) -> u64 {
        let zone = u64::MAX - u64::MAX % bound;
        loop {
            let x = self.next_u64();
            if x < zone {
                return x % bound;
            }
        }
    }
}

/// Write `i` in decimal into `buf`, returning the text (two digits at
/// a time; `fmt` is several times slower).
pub fn format_int(buf: &mut [u8; 20], i: i64) -> &str {
    const DIGITS: &[u8; 200] = b"0001020304050607080910111213141516171819\
2021222324252627282930313233343536373839\
4041424344454647484950515253545556575859\
6061626364656667686970717273747576777879\
8081828384858687888990919293949596979899";
    let mut n = i.unsigned_abs();
    let mut pos = buf.len();
    while n >= 100 {
        let d = (n % 100) as usize * 2;
        n /= 100;
        pos -= 2;
        buf[pos] = DIGITS[d];
        buf[pos + 1] = DIGITS[d + 1];
    }
    if n >= 10 {
        let d = n as usize * 2;
        pos -= 2;
        buf[pos] = DIGITS[d];
        buf[pos + 1] = DIGITS[d + 1];
    } else {
        pos -= 1;
        buf[pos] = b'0' + n as u8;
    }
    if i < 0 {
        pos -= 1;
        buf[pos] = b'-';
    }
    // SAFETY: only ASCII digits and '-' were written.
    unsafe { std::str::from_utf8_unchecked(&buf[pos..]) }
}

/// A point in time: nanoseconds since the Unix epoch and the UTC offset
/// it is displayed in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TimeVal {
    pub ns: i64,
    /// Seconds east of UTC.
    pub offset: i32,
    /// Displayed as UTC (`Time.utc`, `Time#utc`).
    pub utc: bool,
}

thread_local! {
    /// Classes whose instances compare and hash structurally (data types,
    /// enum variants). Set up by the interpreter.
    pub static STRUCTURAL_CLASSES: RefCell<Vec<bool>> = const { RefCell::new(Vec::new()) };
}

pub fn is_structural(obj: &Object) -> bool {
    STRUCTURAL_CLASSES.with(|s| s.borrow().get(obj.class as usize).copied().unwrap_or(false))
}

impl Value {
    /// A string value.
    pub fn str(s: &str) -> Value {
        Value::Str(HeapStr::new(s))
    }

    /// A string value from a shared string.
    pub fn str_rc(s: Rc<str>) -> Value {
        Value::Str(HeapStr::new(&s))
    }

    pub fn string(s: String) -> Value {
        Value::Str(HeapStr::new(&s))
    }

    /// A string built by `f` in a reused buffer: one allocation (the
    /// box), none for the buffer. Reentrant (a nested build gets a
    /// fresh buffer).
    pub fn build_string(f: impl FnOnce(&mut String)) -> Value {
        thread_local! {
            static SCRATCH: RefCell<String> = const { RefCell::new(String::new()) };
        }
        let mut buf = SCRATCH.with(|s| std::mem::take(&mut *s.borrow_mut()));
        buf.clear();
        f(&mut buf);
        let v = Value::str(buf.as_str());
        if buf.capacity() <= 1 << 16 {
            SCRATCH.with(|s| *s.borrow_mut() = buf);
        }
        v
    }

    pub fn array(items: Vec<Value>) -> Value {
        Value::Array(ArrayData::from_values(items))
    }

    pub fn ints(items: Vec<i64>) -> Value {
        Value::Array(ArrayData::Ints(items))
    }

    pub fn floats(items: Vec<f64>) -> Value {
        Value::Array(ArrayData::Floats(items))
    }

    pub fn bytes(bytes: Vec<u8>) -> Value {
        Value::Bytes(HeapBytes::new(&bytes))
    }

    #[inline]
    pub fn is_truthy(&self) -> bool {
        self.0 != 0 && self.0 != FALSE_BITS
    }

    #[inline]
    pub fn is_nil(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub fn as_int(&self) -> Option<i64> {
        match self.view() {
            V::Int(i) => Some(i),
            _ => None,
        }
    }

    /// The text of a string value.
    #[inline]
    pub fn as_str(&self) -> Option<&str> {
        match self.view() {
            V::Str(s) => Some(s.as_str()),
            _ => None,
        }
    }

    #[inline]
    pub fn is_str(&self) -> bool {
        self.heap_kind() == Some(Kind::Str)
    }

    /// Identity comparison (`equal?`): values without a heap payload are
    /// identical when equal, the others when they share the allocation.
    pub fn identical(&self, other: &Value) -> bool {
        if self.0 == other.0 {
            return true;
        }
        match (self.view(), other.view()) {
            (V::Int(a), V::Int(b)) => a == b,
            (V::Float(a), V::Float(b)) => a.to_bits() == b.to_bits(),
            (V::Duration(a), V::Duration(b)) => a == b,
            (V::BigInt(a), V::BigInt(b)) => a == b,
            (V::Str(a), V::Str(b)) => a == b,
            (V::Bytes(a), V::Bytes(b)) => a == b,
            (V::Time(a), V::Time(b)) => a.ns == b.ns,
            _ => false,
        }
    }
}

/// Structural equality for immutable values (used for hash keys and as the
/// default `==`). Mutable objects compare by identity; data types and enum
/// variants compare field-wise.
impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        if self.0 == other.0 {
            return true;
        }
        match (self.view(), other.view()) {
            (V::Int(a), V::Int(b)) => a == b,
            (V::Int(a), V::Float(b)) | (V::Float(b), V::Int(a)) => (a as f64) == b,
            (V::Int(a), V::BigInt(b)) | (V::BigInt(b), V::Int(a)) => **b == BigInt::from(a),
            (V::BigInt(a), V::BigInt(b)) => a == b,
            (V::Float(a), V::Float(b)) => a == b,
            (V::Str(a), V::Str(b)) => a == b,
            (V::Array(a), V::Array(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y)
            }
            (V::Hash(a), V::Hash(b)) => {
                a.len() == b.len() && a.iter().all(|(k, v)| b.get(k).is_some_and(|w| w == v))
            }
            (V::Set(a), V::Set(b)) => a.len() == b.len() && a.iter().all(|x| b.contains(x)),
            (V::Range(a), V::Range(b)) => {
                a.lo == b.lo && a.hi == b.hi && a.exclusive == b.exclusive
            }
            (V::Regexp(a), V::Regexp(b)) => a.source == b.source && a.flags == b.flags,
            (V::Object(a), V::Object(b)) => {
                // Data-like objects (no mutable fields) compare structurally.
                // The interpreter decides which classes are structural by
                // the `structural` flag kept on the object.
                a.class == b.class && is_structural(a) && *a.fields.borrow() == *b.fields.borrow()
            }
            _ => self.identical(other),
        }
    }
}

impl Eq for Value {}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.view() {
            V::Nil => 0u8.hash(state),
            V::Bool(b) => b.hash(state),
            // Numbers that are equal hash the same (`1 == 1.0`): an
            // integral value hashes as the integer it is, which keeps
            // the common Int key a plain integer hash.
            V::Int(i) => {
                2u8.hash(state);
                i.hash(state);
            }
            V::BigInt(b) => {
                2u8.hash(state);
                match i64::try_from(&**b) {
                    Ok(i) => i.hash(state),
                    Err(_) => b.hash(state),
                }
            }
            V::Float(f) => {
                2u8.hash(state);
                if f.fract() == 0.0 && f.abs() < 9.2e18 {
                    (f as i64).hash(state);
                } else {
                    f.to_bits().hash(state);
                }
            }
            V::Str(s) => {
                4u8.hash(state);
                s.as_str().hash(state);
            }
            V::Symbol(s) => {
                5u8.hash(state);
                s.hash(state);
            }
            V::Array(a) => {
                6u8.hash(state);
                a.len().hash(state);
                for x in a.iter() {
                    x.hash(state);
                }
            }
            V::Hash(h) => {
                7u8.hash(state);
                h.len().hash(state);
            }
            V::Set(s) => {
                8u8.hash(state);
                s.len().hash(state);
            }
            V::Range(r) => {
                9u8.hash(state);
                r.lo.hash(state);
                r.hi.hash(state);
            }
            V::Object(o) => {
                12u8.hash(state);
                o.class.hash(state);
                if is_structural(o) {
                    for f in o.fields.borrow().iter() {
                        f.hash(state);
                    }
                } else {
                    self.0.hash(state);
                }
            }
            V::Class(c) => {
                13u8.hash(state);
                c.hash(state);
            }
            V::Duration(d) => {
                24u8.hash(state);
                d.hash(state);
            }
            V::Bytes(b) => {
                27u8.hash(state);
                b.as_slice().hash(state);
            }
            V::Time(t) => {
                29u8.hash(state);
                t.ns.hash(state);
            }
            // Identity for the rest.
            _ => self.0.hash(state),
        }
    }
}

/// Normalize a big integer back to `Int` when it fits.
pub fn int_from_big(b: BigInt) -> Value {
    use num_traits::ToPrimitive;
    match b.to_i64() {
        Some(i) => Value::Int(i),
        None => Value::BigInt(b),
    }
}
