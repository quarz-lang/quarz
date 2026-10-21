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
/// A hash whose keys and values are all `Int`, stored unboxed.
pub type IntMap = IndexMap<i64, i64, rustc_hash::FxBuildHasher>;

thread_local! {
    static COPIES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The contents of a collection, for an update: in place when this is
/// its only reference, else a copy (counted: see `copies`).
pub fn unique_mut<T: Clone>(rc: &mut Rc<T>) -> &mut T {
    if Rc::get_mut(rc).is_none() {
        COPIES.with(|c| c.set(c.get() + 1));
    }
    Rc::make_mut(rc)
}

/// How many updates on this thread had to copy a shared collection.
/// `QUARZ_COUNT_COPIES=1` prints it at exit; tests use it to check that
/// the updates the compiler means to be in place are.
pub fn copies() -> u64 {
    COPIES.with(|c| c.get())
}

/// The entries of a `Hash`: unboxed while every key and value is an
/// `Int` (the storage becomes boxed values, once, when anything else is
/// stored), boxed values otherwise. Iteration order is insertion order
/// either way.
#[derive(Clone, Debug)]
pub enum HashData {
    Values(ValueMap),
    Ints(IntMap),
}

impl Default for HashData {
    fn default() -> Self {
        HashData::Values(ValueMap::default())
    }
}

impl From<ValueMap> for HashData {
    /// A map of `Int` keys and values is stored unboxed.
    fn from(map: ValueMap) -> HashData {
        if !map.is_empty()
            && map
                .iter()
                .all(|(k, v)| matches!((k, v), (Value::Int(_), Value::Int(_))))
        {
            let mut ints = IntMap::with_capacity_and_hasher(map.len(), Default::default());
            for (k, v) in &map {
                if let (Value::Int(k), Value::Int(v)) = (k, v) {
                    ints.insert(*k, *v);
                }
            }
            return HashData::Ints(ints);
        }
        HashData::Values(map)
    }
}

impl FromIterator<(Value, Value)> for HashData {
    fn from_iter<I: IntoIterator<Item = (Value, Value)>>(items: I) -> HashData {
        HashData::from(items.into_iter().collect::<ValueMap>())
    }
}

impl HashData {
    pub fn len(&self) -> usize {
        match self {
            HashData::Values(m) => m.len(),
            HashData::Ints(m) => m.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The entries as boxed values: borrowed, or built for unboxed
    /// storage.
    pub fn as_map(&self) -> std::borrow::Cow<'_, ValueMap> {
        match self {
            HashData::Values(m) => std::borrow::Cow::Borrowed(m),
            HashData::Ints(m) => std::borrow::Cow::Owned(
                m.iter()
                    .map(|(k, v)| (Value::Int(*k), Value::Int(*v)))
                    .collect(),
            ),
        }
    }

    /// The entries as boxed values, to change (unboxed storage is
    /// converted, once).
    pub fn values_mut(&mut self) -> &mut ValueMap {
        if let HashData::Ints(m) = self {
            let map: ValueMap = m
                .iter()
                .map(|(k, v)| (Value::Int(*k), Value::Int(*v)))
                .collect();
            *self = HashData::Values(map);
        }
        match self {
            HashData::Values(m) => m,
            HashData::Ints(_) => unreachable!(),
        }
    }

    /// Change the entries as boxed values (unboxed storage is converted
    /// first).
    pub fn with_values<R>(&mut self, f: impl FnOnce(&mut ValueMap) -> R) -> R {
        f(self.values_mut())
    }

    pub fn get(&self, k: &Value) -> Option<Value> {
        match (self, k) {
            (HashData::Values(m), _) => m.get(k).cloned(),
            (HashData::Ints(m), Value::Int(k)) => m.get(k).map(|v| Value::Int(*v)),
            // An Int-keyed hash holds no other key (`1.0 == 1` is a key
            // equal to 1).
            (HashData::Ints(m), Value::Float(f)) if f.fract() == 0.0 && f.abs() < 9.2e18 => {
                m.get(&(*f as i64)).map(|v| Value::Int(*v))
            }
            (HashData::Ints(_), _) => None,
        }
    }

    pub fn contains_key(&self, k: &Value) -> bool {
        match (self, k) {
            (HashData::Values(m), _) => m.contains_key(k),
            (HashData::Ints(m), Value::Int(k)) => m.contains_key(k),
            (HashData::Ints(_), _) => self.get(k).is_some(),
        }
    }

    /// Insert or replace (keeping the key's position).
    pub fn insert(&mut self, k: Value, v: Value) {
        match (&mut *self, &k, &v) {
            (HashData::Ints(m), Value::Int(a), Value::Int(b)) => {
                m.insert(*a, *b);
            }
            (HashData::Values(m), Value::Int(a), Value::Int(b)) if m.is_empty() => {
                let mut ints = IntMap::default();
                ints.insert(*a, *b);
                *self = HashData::Ints(ints);
            }
            _ => {
                self.values_mut().insert(k, v);
            }
        }
    }

    /// Remove a key, keeping the order of the others.
    pub fn shift_remove(&mut self, k: &Value) -> Option<Value> {
        if let (HashData::Ints(m), Value::Int(a)) = (&mut *self, k) {
            return m.shift_remove(a).map(Value::Int);
        }
        if matches!(self, HashData::Ints(_)) && !self.contains_key(k) {
            return None;
        }
        self.values_mut().shift_remove(k)
    }
}
use num_bigint::BigInt;
use quarz_ir::{ClassId, FuncId, MethodId};
use smallvec::SmallVec;

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
        if items.iter().all(|v| matches!(v, Value::Int(_))) {
            return ArrayData::Ints(
                items
                    .iter()
                    .map(|v| match v {
                        Value::Int(i) => *i,
                        _ => unreachable!(),
                    })
                    .collect(),
            );
        }
        if items.iter().all(|v| matches!(v, Value::Float(_))) {
            return ArrayData::Floats(
                items
                    .iter()
                    .map(|v| match v {
                        Value::Float(f) => *f,
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
        match (&mut *self, &v) {
            (ArrayData::Ints(xs), Value::Int(i)) => xs.push(*i),
            (ArrayData::Floats(xs), Value::Float(f)) => xs.push(*f),
            (ArrayData::Values(xs), Value::Int(i)) if xs.is_empty() => {
                *self = ArrayData::Ints(vec![*i]);
            }
            (ArrayData::Values(xs), Value::Float(f)) if xs.is_empty() => {
                *self = ArrayData::Floats(vec![*f]);
            }
            (ArrayData::Values(xs), _) => xs.push(v),
            _ => self.with_values(|xs| xs.push(v)),
        }
    }

    /// `self[i] = v` for an index in range.
    pub fn set(&mut self, i: usize, v: Value) {
        match (&mut *self, &v) {
            (ArrayData::Ints(xs), Value::Int(x)) => xs[i] = *x,
            (ArrayData::Floats(xs), Value::Float(x)) => xs[i] = *x,
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
    pub fn new(class: ClassId, fields: Fields) -> Rc<Object> {
        let o = Rc::new(Object {
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
    pub unsafe fn with_fields_from(class: ClassId, src: *const Value, n: usize) -> Rc<Object> {
        let mut rc = Rc::<Object>::new_uninit();
        // SAFETY: the allocation is fresh and uniquely owned; every field
        // of `Object` is written before `assume_init`.
        unsafe {
            let p = Rc::get_mut(&mut rc).unwrap_unchecked().as_mut_ptr();
            std::ptr::write(&raw mut (*p).fields_ptr, Cell::new(std::ptr::null()));
            std::ptr::write(&raw mut (*p).nfields, Cell::new(0));
            std::ptr::write(&raw mut (*p).class, class);
            let mut fields = Fields::with_capacity(n);
            std::ptr::copy_nonoverlapping(src, fields.as_mut_ptr(), n);
            fields.set_len(n);
            std::ptr::write(&raw mut (*p).fields, RefCell::new(fields));
            std::ptr::write(&raw mut (*p).exc, RefCell::new(None));
            let rc = rc.assume_init();
            rc.bind_fields();
            rc
        }
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
    /// A task is in the middle of a write: one call goes out whole, and
    /// the other writers wait here for their turn.
    pub writing: bool,
    pub write_waiters: std::collections::VecDeque<crate::sched::TaskId>,
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
    /// The buffered descriptors, shared with the helper thread that runs
    /// an operation needing a system call (the calling task waits, the
    /// others run; see `natives::io`).
    pub io: std::sync::Arc<std::sync::Mutex<FileIo>>,
    pub readable: bool,
    pub writable: bool,
    pub closed: bool,
}

#[derive(Debug, Default)]
pub struct FileIo {
    pub reader: Option<std::io::BufReader<std::fs::File>>,
    pub writer: Option<std::io::BufWriter<std::fs::File>>,
}

#[derive(Debug)]
pub struct IoVal {
    pub kind: IoKind,
}

/// A non-local flow caught by an `ensure` handler, carried through the
/// handler's body and continued by `Resume`.
pub type FlowBox = RefCell<Option<Flow>>;

/// The layout is fixed (`repr(C, u64)`: a tag word followed by the
/// payload) so that compiled code can build and test values inline. The
/// variants without reference counting come first; see `NEEDS_DROP_FROM`.
#[derive(Clone, Debug)]
#[repr(C, u64)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    Symbol(Symbol),
    Class(ClassId),
    /// Nanoseconds.
    Duration(i64),
    /// A string of at most 15 bytes, kept in the value itself.
    Short(ShortStr),
    BigInt(Rc<BigInt>),
    /// A longer string.
    Str(Rc<str>),
    Array(Rc<ArrayData>),
    Hash(Rc<HashData>),
    Set(Rc<ValueSet>),
    Range(Rc<RangeVal>),
    Regexp(Rc<RegexpVal>),
    MatchData(Rc<MatchDataVal>),
    Object(Rc<Object>),
    Proc(Rc<Closure>),
    ArrayBuilder(Rc<RefCell<Vec<Value>>>),
    HashBuilder(Rc<RefCell<ValueMap>>),
    SetBuilder(Rc<RefCell<ValueSet>>),
    StringBuilder(Rc<RefCell<String>>),
    Channel(Rc<ChannelInner>),
    Task(Rc<TaskHandle>),
    Scope(Rc<ScopeInner>),
    Atom(Rc<RefCell<Value>>),
    Selector(Rc<RefCell<SelectorState>>),
    Enumerator(Rc<EnumeratorVal>),
    Io(Rc<IoVal>),
    Bytes(Rc<[u8]>),
    BytesBuilder(Rc<RefCell<Vec<u8>>>),
    Time(Rc<TimeVal>),
    Random(Rc<RefCell<RandomState>>),
    /// Internal: a flow in transit through an `ensure` handler.
    Flow(Rc<FlowBox>),
}

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

/// Tags below this hold no reference-counted payload.
pub const NEEDS_DROP_FROM: u64 = 8;

/// A string short enough to live in a value's payload: its length,
/// then the bytes (valid UTF-8).
#[derive(Clone, Copy)]
#[repr(C)]
pub struct ShortStr {
    len: u8,
    bytes: [u8; ShortStr::MAX],
}

impl ShortStr {
    pub const MAX: usize = 15;

    pub fn new(s: &str) -> Option<ShortStr> {
        if s.len() > ShortStr::MAX {
            return None;
        }
        let mut bytes = [0u8; ShortStr::MAX];
        bytes[..s.len()].copy_from_slice(s.as_bytes());
        Some(ShortStr {
            len: s.len() as u8,
            bytes,
        })
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: built from a `str`, so the bytes are UTF-8.
        unsafe { std::str::from_utf8_unchecked(&self.bytes[..self.len as usize]) }
    }
}

impl ShortStr {
    pub fn make_ascii_uppercase(&mut self) {
        let n = self.len as usize;
        self.bytes[..n].make_ascii_uppercase();
    }

    pub fn make_ascii_lowercase(&mut self) {
        let n = self.len as usize;
        self.bytes[..n].make_ascii_lowercase();
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

impl std::ops::Deref for ShortStr {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl std::fmt::Debug for ShortStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl Value {
    /// A copy that skips the reference count machinery for values that
    /// have none.
    #[inline]
    pub fn fast_clone(&self) -> Value {
        if (self.type_tag() as u64) < NEEDS_DROP_FROM {
            // SAFETY: the variant holds no heap payload, so a bitwise
            // copy is a complete value.
            unsafe { std::ptr::read(self) }
        } else {
            self.clone()
        }
    }

    /// `*dst = *src` without a temporary: a plain copy for values without
    /// a reference count.
    ///
    /// # Safety
    /// `dst` must point to writable space holding no live value.
    #[inline]
    pub unsafe fn clone_into(dst: *mut Value, src: &Value) {
        if (src.type_tag() as u64) < NEEDS_DROP_FROM {
            std::ptr::copy_nonoverlapping(src as *const Value, dst, 1);
        } else {
            std::ptr::write(dst, src.clone());
        }
    }

    /// Drop a value, skipping the destructor for those that need none.
    #[inline]
    pub fn fast_drop(self) {
        if (self.type_tag() as u64) < NEEDS_DROP_FROM {
            std::mem::forget(self);
        }
    }
}

/// Compiled code bumps and lowers reference counts inline, assuming the
/// layout of `Rc`'s allocation: the strong count is its first word. This
/// checks that assumption once at start-up.
pub fn check_rc_layout() {
    let a: Rc<str> = Rc::from("layout");
    let value = Value::Str(a.clone());
    // The payload's first word is the pointer `Rc` keeps: the allocation.
    let strong_of = |v: &Value| -> usize {
        // SAFETY: `Value` is `repr(C, u64)`: the tag, then the payload.
        unsafe {
            let words = v as *const Value as *const usize;
            let allocation = *words.add(1) as *const usize;
            *allocation
        }
    };
    assert_eq!(
        strong_of(&value),
        2,
        "Rc layout changed: the strong count must come first"
    );
    // The tags compiled code tests for, and the field view's place.
    assert_eq!(
        Value::Class(0).type_tag(),
        5,
        "Value layout changed: Class tag"
    );
    let object = Value::Object(Object::new(0, Fields::new()));
    assert_eq!(object.type_tag(), 16, "Value layout changed: Object tag");
    let short = Value::str("short");
    assert_eq!(short.type_tag(), 7, "Value layout changed: Short tag");
    assert!(
        (short.type_tag() as u64) < NEEDS_DROP_FROM,
        "a short string must need no release"
    );
    assert_eq!(std::mem::offset_of!(Object, fields_ptr), 0);
    assert_eq!(std::mem::offset_of!(Frame, slots_ptr), 0);
    assert_eq!(std::mem::offset_of!(Frame, nslots), 8);
    assert_eq!(std::mem::offset_of!(Frame, parent_ptr), 16);
    let b = a.clone();
    assert_eq!(
        strong_of(&value),
        3,
        "Rc layout changed: the strong count must come first"
    );
    drop(b);
    assert_eq!(
        strong_of(&value),
        2,
        "Rc layout changed: the strong count must come first"
    );
}

/// Size of a value in bytes, as compiled code lays out its registers.
pub const VALUE_SIZE: usize = 24;

const _: () = assert!(std::mem::size_of::<Value>() == VALUE_SIZE);

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

impl Value {
    /// A string value: in the value itself when short, shared on the
    /// heap otherwise.
    pub fn str(s: &str) -> Value {
        match ShortStr::new(s) {
            Some(short) => Value::Short(short),
            None => Value::Str(Rc::from(s)),
        }
    }

    /// A string value from a shared string (kept shared when long).
    pub fn str_rc(s: Rc<str>) -> Value {
        match ShortStr::new(&s) {
            Some(short) => Value::Short(short),
            None => Value::Str(s),
        }
    }

    pub fn string(s: String) -> Value {
        match ShortStr::new(&s) {
            Some(short) => Value::Short(short),
            None => Value::Str(Rc::from(s)),
        }
    }

    /// A string built by `f` in a reused buffer: one allocation (the
    /// `Rc<str>`), none for the buffer. Reentrant (a nested build gets a
    /// fresh buffer).
    pub fn build_string(f: impl FnOnce(&mut String)) -> Value {
        Value::with_scratch(|buf| {
            f(buf);
            Value::str(buf.as_str())
        })
    }

    /// Run `f` on an empty, reused buffer (reentrant: a nested call gets
    /// a fresh one).
    pub fn with_scratch<R>(f: impl FnOnce(&mut String) -> R) -> R {
        thread_local! {
            static SCRATCH: RefCell<String> = const { RefCell::new(String::new()) };
        }
        let mut buf = SCRATCH.with(|s| std::mem::take(&mut *s.borrow_mut()));
        buf.clear();
        let r = f(&mut buf);
        if buf.capacity() <= 1 << 16 {
            SCRATCH.with(|s| *s.borrow_mut() = buf);
        }
        r
    }

    pub fn array(items: Vec<Value>) -> Value {
        Value::Array(Rc::new(ArrayData::from_values(items)))
    }

    pub fn ints(items: Vec<i64>) -> Value {
        Value::Array(Rc::new(ArrayData::Ints(items)))
    }

    pub fn floats(items: Vec<f64>) -> Value {
        Value::Array(Rc::new(ArrayData::Floats(items)))
    }

    pub fn bytes(bytes: Vec<u8>) -> Value {
        Value::Bytes(Rc::from(bytes))
    }

    pub fn is_truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, Value::Nil)
    }

    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(i) => Some(*i),
            _ => None,
        }
    }

    /// The text of a string value (short or long).
    #[inline]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::Short(s) => Some(s.as_str()),
            Value::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn is_str(&self) -> bool {
        matches!(self, Value::Short(_) | Value::Str(_))
    }

    /// The discriminant (the first word of the `repr(C, u64)` layout).
    pub fn type_tag(&self) -> u8 {
        // SAFETY: `Value` is `repr(C, u64)`, so it starts with its tag.
        unsafe { *(self as *const Value as *const u64) as u8 }
    }

    /// Identity comparison (`equal?`): values without a heap payload are
    /// identical when equal, the others when they share the allocation.
    pub fn identical(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a.to_bits() == b.to_bits(),
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::Class(a), Value::Class(b)) => a == b,
            (Value::Duration(a), Value::Duration(b)) => a == b,
            (Value::BigInt(a), Value::BigInt(b)) => Rc::ptr_eq(a, b) || a == b,
            (Value::Str(a), Value::Str(b)) => Rc::ptr_eq(a, b) || a == b,
            (Value::Short(a), Value::Short(b)) => a.as_str() == b.as_str(),
            (Value::Str(a), Value::Short(b)) | (Value::Short(b), Value::Str(a)) => {
                **a == *b.as_str()
            }
            (Value::Array(a), Value::Array(b)) => Rc::ptr_eq(a, b),
            (Value::Hash(a), Value::Hash(b)) => Rc::ptr_eq(a, b),
            (Value::Set(a), Value::Set(b)) => Rc::ptr_eq(a, b),
            (Value::Range(a), Value::Range(b)) => Rc::ptr_eq(a, b),
            (Value::Regexp(a), Value::Regexp(b)) => Rc::ptr_eq(a, b),
            (Value::MatchData(a), Value::MatchData(b)) => Rc::ptr_eq(a, b),
            (Value::Object(a), Value::Object(b)) => Rc::ptr_eq(a, b),
            (Value::Proc(a), Value::Proc(b)) => Rc::ptr_eq(a, b),
            (Value::ArrayBuilder(a), Value::ArrayBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::HashBuilder(a), Value::HashBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::SetBuilder(a), Value::SetBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::StringBuilder(a), Value::StringBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::Channel(a), Value::Channel(b)) => Rc::ptr_eq(a, b),
            (Value::Task(a), Value::Task(b)) => Rc::ptr_eq(a, b),
            (Value::Scope(a), Value::Scope(b)) => Rc::ptr_eq(a, b),
            (Value::Atom(a), Value::Atom(b)) => Rc::ptr_eq(a, b),
            (Value::Selector(a), Value::Selector(b)) => Rc::ptr_eq(a, b),
            (Value::Enumerator(a), Value::Enumerator(b)) => Rc::ptr_eq(a, b),
            (Value::Io(a), Value::Io(b)) => Rc::ptr_eq(a, b),
            (Value::Bytes(a), Value::Bytes(b)) => Rc::ptr_eq(a, b) || a == b,
            (Value::BytesBuilder(a), Value::BytesBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::Time(a), Value::Time(b)) => a.ns == b.ns,
            (Value::Random(a), Value::Random(b)) => Rc::ptr_eq(a, b),
            (Value::Flow(a), Value::Flow(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

/// Structural equality for immutable values (used for hash keys and as the
/// default `==`). Mutable objects compare by identity; data types and enum
/// variants compare field-wise.
impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => {
                (*a as f64) == *b
            }
            (Value::Int(a), Value::BigInt(b)) | (Value::BigInt(b), Value::Int(a)) => {
                **b == BigInt::from(*a)
            }
            (Value::BigInt(a), Value::BigInt(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Short(a), Value::Short(b)) => a.as_str() == b.as_str(),
            (Value::Str(a), Value::Short(b)) | (Value::Short(b), Value::Str(a)) => {
                **a == *b.as_str()
            }
            (Value::Array(a), Value::Array(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y)
            }
            (Value::Hash(a), Value::Hash(b)) => match (&**a, &**b) {
                (HashData::Ints(x), HashData::Ints(y)) => {
                    x.len() == y.len() && x.iter().all(|(k, v)| y.get(k) == Some(v))
                }
                _ => {
                    let (a, b) = (a.as_map(), b.as_map());
                    a.len() == b.len() && a.iter().all(|(k, v)| b.get(k).is_some_and(|w| w == v))
                }
            },
            (Value::Set(a), Value::Set(b)) => a.len() == b.len() && a.iter().all(|x| b.contains(x)),
            (Value::Range(a), Value::Range(b)) => {
                a.lo == b.lo && a.hi == b.hi && a.exclusive == b.exclusive
            }
            (Value::Regexp(a), Value::Regexp(b)) => a.source == b.source && a.flags == b.flags,
            (Value::Object(a), Value::Object(b)) => {
                if Rc::ptr_eq(a, b) {
                    return true;
                }
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

thread_local! {
    /// Classes whose instances compare and hash structurally (data types,
    /// enum variants). Set up by the interpreter.
    pub static STRUCTURAL_CLASSES: RefCell<Vec<bool>> = const { RefCell::new(Vec::new()) };
}

pub fn is_structural(obj: &Object) -> bool {
    STRUCTURAL_CLASSES.with(|s| s.borrow().get(obj.class as usize).copied().unwrap_or(false))
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Nil => 0u8.hash(state),
            Value::Bool(b) => b.hash(state),
            // Numbers that are equal hash the same (`1 == 1.0`): an
            // integral value hashes as the integer it is, which keeps
            // the common Int key a plain integer hash.
            Value::Int(i) => {
                2u8.hash(state);
                i.hash(state);
            }
            Value::BigInt(b) => {
                2u8.hash(state);
                match i64::try_from(&**b) {
                    Ok(i) => i.hash(state),
                    Err(_) => b.hash(state),
                }
            }
            Value::Float(f) => {
                2u8.hash(state);
                if f.fract() == 0.0 && f.abs() < 9.2e18 {
                    (*f as i64).hash(state);
                } else {
                    f.to_bits().hash(state);
                }
            }
            Value::Str(s) => {
                4u8.hash(state);
                (**s).hash(state);
            }
            Value::Short(s) => {
                4u8.hash(state);
                s.as_str().hash(state);
            }
            Value::Symbol(s) => {
                5u8.hash(state);
                s.hash(state);
            }
            Value::Array(a) => {
                6u8.hash(state);
                a.len().hash(state);
                for x in a.iter() {
                    x.hash(state);
                }
            }
            Value::Hash(h) => {
                7u8.hash(state);
                h.len().hash(state);
            }
            Value::Set(s) => {
                8u8.hash(state);
                s.len().hash(state);
            }
            Value::Range(r) => {
                9u8.hash(state);
                r.lo.hash(state);
                r.hi.hash(state);
            }
            Value::Object(o) => {
                12u8.hash(state);
                o.class.hash(state);
                if is_structural(o) {
                    for f in o.fields.borrow().iter() {
                        f.hash(state);
                    }
                } else {
                    (Rc::as_ptr(o) as usize).hash(state);
                }
            }
            Value::Class(c) => {
                13u8.hash(state);
                c.hash(state);
            }
            Value::Duration(d) => {
                24u8.hash(state);
                d.hash(state);
            }
            Value::Bytes(b) => {
                27u8.hash(state);
                b.hash(state);
            }
            Value::Time(t) => {
                29u8.hash(state);
                t.ns.hash(state);
            }
            other => {
                other.type_tag().hash(state);
                // Identity for the rest.
                match other {
                    Value::Proc(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::ArrayBuilder(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::HashBuilder(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::StringBuilder(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::Channel(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::Task(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::Atom(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::BytesBuilder(p) => (Rc::as_ptr(p) as usize).hash(state),
                    Value::Random(p) => (Rc::as_ptr(p) as usize).hash(state),
                    _ => {}
                }
            }
        }
    }
}

/// Normalize a big integer back to `Int` when it fits.
pub fn int_from_big(b: BigInt) -> Value {
    use num_traits::ToPrimitive;
    match b.to_i64() {
        Some(i) => Value::Int(i),
        None => Value::BigInt(Rc::new(b)),
    }
}
