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
use num_bigint::BigInt;
use quarz_ir::{ClassId, FuncId};
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
pub struct Frame {
    pub slots: RefCell<SmallVec<[Value; 8]>>,
    pub parent: Option<Rc<Frame>>,
}

impl Frame {
    pub fn new(size: usize, parent: Option<Rc<Frame>>) -> Rc<Frame> {
        Rc::new(Frame {
            slots: RefCell::new(smallvec::smallvec![Value::Nil; size]),
            parent,
        })
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
        }
        slots[i] = value;
    }
}

/// The fields of an object, stored inline for up to four.
pub type Fields = SmallVec<[Value; 4]>;

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
    /// Exceptions: the backtrace captured when raised.
    pub backtrace: RefCell<Option<Rc<Vec<String>>>>,
    pub cause: RefCell<Option<Value>>,
}

impl Object {
    pub fn new(class: ClassId, fields: Fields) -> Rc<Object> {
        let o = Rc::new(Object {
            fields_ptr: Cell::new(std::ptr::null()),
            nfields: Cell::new(0),
            class,
            fields: RefCell::new(fields),
            backtrace: RefCell::new(None),
            cause: RefCell::new(None),
        });
        o.bind_fields();
        o
    }

    /// Point the field view at the field vector (after it was created,
    /// resized or replaced).
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
    /// `&:name`: call `name` on the first argument.
    MethodName(Rc<str>),
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
            ClosureBody::MethodName(n) => write!(f, "MethodName({n})"),
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
    BigInt(Rc<BigInt>),
    Str(Rc<str>),
    Array(Rc<Vec<Value>>),
    Hash(Rc<IndexMap<Value, Value>>),
    Set(Rc<IndexSet<Value>>),
    Range(Rc<RangeVal>),
    Regexp(Rc<RegexpVal>),
    MatchData(Rc<MatchDataVal>),
    Object(Rc<Object>),
    Proc(Rc<Closure>),
    ArrayBuilder(Rc<RefCell<Vec<Value>>>),
    HashBuilder(Rc<RefCell<IndexMap<Value, Value>>>),
    SetBuilder(Rc<RefCell<IndexSet<Value>>>),
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
pub const NEEDS_DROP_FROM: u64 = 7;

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
    assert_eq!(object.type_tag(), 15, "Value layout changed: Object tag");
    assert_eq!(std::mem::offset_of!(Object, fields_ptr), 0);
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
    pub fn str(s: &str) -> Value {
        Value::Str(Rc::from(s))
    }

    pub fn string(s: String) -> Value {
        Value::Str(Rc::from(s))
    }

    pub fn array(items: Vec<Value>) -> Value {
        Value::Array(Rc::new(items))
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

    pub fn as_str(&self) -> Option<&Rc<str>> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
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
            (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => {
                (*a as f64) == *b
            }
            (Value::Int(a), Value::BigInt(b)) | (Value::BigInt(b), Value::Int(a)) => {
                **b == BigInt::from(*a)
            }
            (Value::BigInt(a), Value::BigInt(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => a == b,
            (Value::Hash(a), Value::Hash(b)) => {
                a.len() == b.len() && a.iter().all(|(k, v)| b.get(k).is_some_and(|w| w == v))
            }
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
            Value::Int(i) => {
                2u8.hash(state);
                (*i as f64).to_bits().hash(state);
            }
            Value::BigInt(b) => {
                2u8.hash(state);
                b.hash(state);
            }
            Value::Float(f) => {
                2u8.hash(state);
                f.to_bits().hash(state);
            }
            Value::Str(s) => {
                4u8.hash(state);
                s.hash(state);
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
