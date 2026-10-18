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
use quarz_syntax::ast::Block;
use quarz_types::ClassId;
use smallvec::SmallVec;

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

/// A pointer into the AST, which outlives every value (the interpreter owns
/// the checked program for the whole run).
pub struct AstRef<T>(*const T);

impl<T> AstRef<T> {
    pub fn new(r: &T) -> AstRef<T> {
        AstRef(r as *const T)
    }

    pub fn get(&self) -> &T {
        // SAFETY: the AST is owned by the interpreter and never mutated or
        // freed while values exist.
        unsafe { &*self.0 }
    }
}

impl<T> Clone for AstRef<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for AstRef<T> {}

impl<T> std::fmt::Debug for AstRef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AstRef({:p})", self.0)
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

/// An instance of a user-defined class, data type, enum variant or
/// exception.
#[derive(Debug)]
pub struct Object {
    pub class: ClassId,
    pub fields: RefCell<Vec<Value>>,
    /// Exceptions: the backtrace captured when raised.
    pub backtrace: RefCell<Option<Rc<Vec<String>>>>,
    pub cause: RefCell<Option<Value>>,
}

/// A block implemented in Rust (used by natives that iterate).
pub type NativeBlock =
    Rc<dyn Fn(&crate::interp::Interp, crate::interp::ArgVec) -> crate::interp::EvalResult>;

/// The body a closure runs: a block from the AST, a method reference
/// (`&:name`), or a native function.
pub enum ClosureBody {
    Block(AstRef<Block>),
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
            ClosureBody::Block(b) => write!(f, "Block({b:?})"),
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
    pub frame_size: u32,
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
}

#[derive(Debug)]
pub struct IoVal {
    pub kind: IoKind,
}

#[derive(Clone, Debug)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    BigInt(Rc<BigInt>),
    Float(f64),
    Str(Rc<str>),
    Symbol(Symbol),
    Array(Rc<Vec<Value>>),
    Hash(Rc<IndexMap<Value, Value>>),
    Set(Rc<IndexSet<Value>>),
    Range(Rc<RangeVal>),
    Regexp(Rc<RegexpVal>),
    MatchData(Rc<MatchDataVal>),
    Object(Rc<Object>),
    Class(ClassId),
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
    /// Nanoseconds.
    Duration(i64),
    Enumerator(Rc<EnumeratorVal>),
    Io(Rc<IoVal>),
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

    pub fn type_tag(&self) -> u8 {
        match self {
            Value::Nil => 0,
            Value::Bool(_) => 1,
            Value::Int(_) | Value::BigInt(_) => 2,
            Value::Float(_) => 3,
            Value::Str(_) => 4,
            Value::Symbol(_) => 5,
            Value::Array(_) => 6,
            Value::Hash(_) => 7,
            Value::Set(_) => 8,
            Value::Range(_) => 9,
            Value::Regexp(_) => 10,
            Value::MatchData(_) => 11,
            Value::Object(_) => 12,
            Value::Class(_) => 13,
            Value::Proc(_) => 14,
            Value::ArrayBuilder(_) => 15,
            Value::HashBuilder(_) => 16,
            Value::SetBuilder(_) => 17,
            Value::StringBuilder(_) => 18,
            Value::Channel(_) => 19,
            Value::Task(_) => 20,
            Value::Scope(_) => 21,
            Value::Atom(_) => 22,
            Value::Selector(_) => 23,
            Value::Duration(_) => 24,
            Value::Enumerator(_) => 25,
            Value::Io(_) => 26,
        }
    }

    /// Identity comparison (`equal?`).
    pub fn identical(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a.to_bits() == b.to_bits(),
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => Rc::ptr_eq(a, b) || a == b,
            (Value::Array(a), Value::Array(b)) => Rc::ptr_eq(a, b),
            (Value::Hash(a), Value::Hash(b)) => Rc::ptr_eq(a, b),
            (Value::Object(a), Value::Object(b)) => Rc::ptr_eq(a, b),
            (Value::Class(a), Value::Class(b)) => a == b,
            (Value::Proc(a), Value::Proc(b)) => Rc::ptr_eq(a, b),
            (Value::ArrayBuilder(a), Value::ArrayBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::HashBuilder(a), Value::HashBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::StringBuilder(a), Value::StringBuilder(b)) => Rc::ptr_eq(a, b),
            (Value::Channel(a), Value::Channel(b)) => Rc::ptr_eq(a, b),
            (Value::Task(a), Value::Task(b)) => Rc::ptr_eq(a, b),
            (Value::Atom(a), Value::Atom(b)) => Rc::ptr_eq(a, b),
            (Value::Duration(a), Value::Duration(b)) => a == b,
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
