//! The runtime: method invocation, dynamic dispatch, exceptions, the task
//! run loop, and conversions used by the natives. Function bodies are QIR
//! (see `vm.rs`); compiled code uses the same runtime.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use crate::rc::Rc;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{smallvec, SmallVec};
use std::rc::Weak;
use std::time::Duration;

use quarz_ir::INLINE_LINE_FLAG;
use quarz_ir::{
    ClassId, Constant, FuncId, FuncInfo, Function, MethodId, RtClassKind, RtMethod, RtParamKind,
    RtSynth, RtType, RtWorld, Unit,
};

pub use quarz_ir::FastOp;

use crate::natives;
use crate::sched::{self, Scheduler, ScopeInner, TaskExit, TaskHandle, TaskId, TaskResult};
use crate::value::*;

/// Non-local control flow and exceptions.
#[derive(Debug)]
pub enum Flow {
    /// `break value` out of the block/loop with the tag (0 = loop).
    Break(Value, u64),
    /// `next value` in a block or loop.
    Next(Value),
    /// `return value` from the method/lambda with the tag.
    Return(Value, u64),
    Retry,
    /// A raised exception object.
    Raise(Value),
    /// `exit`.
    Exit(i32),
}

pub type EvalResult = Result<Value, Flow>;

/// Positional arguments, stored inline when there are at most four.
pub type ArgVec = SmallVec<[Value; 4]>;

pub use quarz_ir::KW_SPLAT;

/// Arguments to a native method.
#[derive(Default)]
pub struct Args<'a> {
    pub pos: ArgList<'a>,
    pub kw: Vec<(Symbol, Value)>,
    pub block: Option<Value>,
}

/// A native's positional arguments: a list it owns, or a view of the
/// caller's registers, read without counting (#988: `qz_call_static` and
/// `op_call` for a call of positional arguments only; the registers keep
/// the values, and the view lives for the call). Read as a slice; a
/// native that keeps the list itself takes `into_owned`, which copies a
/// view's values.
pub enum ArgList<'a> {
    Owned(ArgVec),
    Borrowed(&'a [Value]),
}

impl ArgList<'_> {
    /// The values, owned: the list itself, or a view's values counted.
    pub fn into_owned(self) -> ArgVec {
        match self {
            ArgList::Owned(v) => v,
            ArgList::Borrowed(s) => s.iter().cloned().collect(),
        }
    }

    /// `into_owned`, as a `Vec`.
    pub fn into_vec(self) -> Vec<Value> {
        self.into_owned().into_vec()
    }
}

impl std::ops::Deref for ArgList<'_> {
    type Target = [Value];
    #[inline(always)]
    fn deref(&self) -> &[Value] {
        match self {
            ArgList::Owned(v) => v,
            ArgList::Borrowed(s) => s,
        }
    }
}

impl<'b> IntoIterator for &'b ArgList<'_> {
    type Item = &'b Value;
    type IntoIter = std::slice::Iter<'b, Value>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl Default for ArgList<'_> {
    fn default() -> Self {
        ArgList::Owned(ArgVec::new())
    }
}

impl From<ArgVec> for ArgList<'_> {
    fn from(v: ArgVec) -> Self {
        ArgList::Owned(v)
    }
}

impl Args<'_> {
    pub fn arg(&self, i: usize) -> &Value {
        self.pos.get(i).unwrap_or(&Value::Nil)
    }

    pub fn kw(&self, interp: &Interp, name: &str) -> Option<&Value> {
        let sym = interp.intern(name);
        self.kw.iter().find(|(s, _)| *s == sym).map(|(_, v)| v)
    }
}

pub type NativeFn = fn(&Interp, &Value, Args) -> EvalResult;

/// A native taking its receiver and arguments by reference (no copies,
/// no argument list): `None` sends the call down the generic path (a
/// receiver or argument it does not handle, or a case that raises). It
/// never raises itself: it answers or declines (#795), which compiled
/// code relies on to call it with no status (`qzfc.`, `fast!`).
pub type FastNativeFn = fn(&Interp, &Value, &[&Value]) -> Option<Value>;

/// A native that takes ownership of the receiver so that it can update a
/// uniquely referenced value in place. On failure it hands the receiver
/// back so the caller can restore it.
pub type OwnedNativeFn = fn(&Interp, Value, Args) -> Result<Value, (Flow, Value)>;

/// Key of the by-name method cache: class, arity, block given, and whether
/// the witness fallback applies (`Interp::find_method`); the name is the
/// inner key, so lookups do not allocate.
type NameKey = (ClassId, usize, bool, bool);

/// `fast_binop` on two Ints: inlined where the interpreter runs a block,
/// the commonest case (None: overflow or a division by zero, for the
/// method to handle).
#[inline(always)]
pub fn int_binop(op: FastOp, x: i64, y: i64) -> Option<Value> {
    Some(match op {
        FastOp::Add => Value::Int(x.checked_add(y)?),
        FastOp::Sub => Value::Int(x.checked_sub(y)?),
        FastOp::Mul => Value::Int(x.checked_mul(y)?),
        FastOp::Div => {
            if y == 0 || (x == i64::MIN && y == -1) {
                return None;
            }
            // Floor division, as in Ruby.
            let q = x / y;
            Value::Int(if (x % y != 0) && ((x < 0) != (y < 0)) {
                q - 1
            } else {
                q
            })
        }
        FastOp::Mod => {
            if y == 0 || (x == i64::MIN && y == -1) {
                return None;
            }
            let r = x % y;
            Value::Int(if r != 0 && ((r < 0) != (y < 0)) {
                r + y
            } else {
                r
            })
        }
        FastOp::Lt => Value::Bool(x < y),
        FastOp::Le => Value::Bool(x <= y),
        FastOp::Gt => Value::Bool(x > y),
        FastOp::Ge => Value::Bool(x >= y),
        FastOp::Eq => Value::Bool(x == y),
        FastOp::Ne => Value::Bool(x != y),
        FastOp::Cmp => Value::Int(x.cmp(&y) as i64),
    })
}

/// `int_binop` into `slot` (the old value dropped), false when it gives
/// nothing: each result is built where it goes, never aside.
#[inline(always)]
pub fn int_binop_into(op: FastOp, x: i64, y: i64, slot: &mut Value) -> bool {
    #[inline(always)]
    fn int(slot: &mut Value, r: Option<i64>) -> bool {
        match r {
            Some(r) => {
                crate::vm::put(slot, Value::Int(r));
                true
            }
            None => false,
        }
    }
    #[inline(always)]
    fn bool(slot: &mut Value, b: bool) -> bool {
        crate::vm::put(slot, Value::Bool(b));
        true
    }
    match op {
        FastOp::Add => int(slot, x.checked_add(y)),
        FastOp::Sub => int(slot, x.checked_sub(y)),
        FastOp::Mul => int(slot, x.checked_mul(y)),
        FastOp::Lt => bool(slot, x < y),
        FastOp::Le => bool(slot, x <= y),
        FastOp::Gt => bool(slot, x > y),
        FastOp::Ge => bool(slot, x >= y),
        FastOp::Eq => bool(slot, x == y),
        FastOp::Ne => bool(slot, x != y),
        FastOp::Cmp => int(slot, Some(x.cmp(&y) as i64)),
        FastOp::Div | FastOp::Mod => match int_binop(op, x, y) {
            Some(v) => {
                crate::vm::put(slot, v);
                true
            }
            None => false,
        },
    }
}

/// Two numbers of which one at least is a `Float`, as floats (what
/// `fast_binop` computes with), when an `Int` among them converts
/// exactly (`exact_as_float`): its comparisons are then exact (#888);
/// `None` sends a larger one to the generic path, which compares it
/// exactly (and computes the same arithmetic).
#[inline(always)]
pub fn float_operands(a: &Value, b: &Value) -> Option<(f64, f64)> {
    match (a, b) {
        (Value::Float(x), Value::Float(y)) => Some((*x, *y)),
        (Value::Int(x), Value::Float(y)) if crate::value::exact_as_float(*x) => {
            Some((*x as f64, *y))
        }
        (Value::Float(x), Value::Int(y)) if crate::value::exact_as_float(*y) => {
            Some((*x, *y as f64))
        }
        _ => None,
    }
}

/// `fast_binop` on floats, into `slot` (see `int_binop_into`).
#[inline(always)]
pub fn float_binop_into(op: FastOp, x: f64, y: f64, slot: &mut Value) {
    use crate::vm::put;
    match op {
        FastOp::Add => put(slot, Value::Float(x + y)),
        FastOp::Sub => put(slot, Value::Float(x - y)),
        FastOp::Mul => put(slot, Value::Float(x * y)),
        FastOp::Div => put(slot, Value::Float(x / y)),
        FastOp::Mod => {
            let r = x % y;
            put(
                slot,
                Value::Float(if r != 0.0 && ((r < 0.0) != (y < 0.0)) {
                    r + y
                } else {
                    r
                }),
            )
        }
        FastOp::Lt => put(slot, Value::Bool(x < y)),
        FastOp::Le => put(slot, Value::Bool(x <= y)),
        FastOp::Gt => put(slot, Value::Bool(x > y)),
        FastOp::Ge => put(slot, Value::Bool(x >= y)),
        FastOp::Eq => put(slot, Value::Bool(x == y)),
        FastOp::Ne => put(slot, Value::Bool(x != y)),
        FastOp::Cmp => put(slot, Value::Int(float_order(x, y) as i64)),
    }
}

/// Apply an operator to two numbers directly. `None` means the generic
/// path must be taken (overflow, division by zero, other types).
#[inline]
pub fn fast_binop(op: FastOp, a: &Value, b: &Value) -> Option<Value> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => int_binop(op, *x, *y),
        (Value::Float(_), Value::Float(_))
        | (Value::Int(_), Value::Float(_))
        | (Value::Float(_), Value::Int(_)) => {
            // (An `Int` that does not convert exactly: the generic path,
            // `float_operands`.)
            let (x, y) = float_operands(a, b)?;
            Some(match op {
                FastOp::Add => Value::Float(x + y),
                FastOp::Sub => Value::Float(x - y),
                FastOp::Mul => Value::Float(x * y),
                FastOp::Div => Value::Float(x / y),
                FastOp::Mod => {
                    let r = x % y;
                    Value::Float(if r != 0.0 && ((r < 0.0) != (y < 0.0)) {
                        r + y
                    } else {
                        r
                    })
                }
                FastOp::Lt => Value::Bool(x < y),
                FastOp::Le => Value::Bool(x <= y),
                FastOp::Gt => Value::Bool(x > y),
                FastOp::Ge => Value::Bool(x >= y),
                FastOp::Eq => Value::Bool(x == y),
                FastOp::Ne => Value::Bool(x != y),
                FastOp::Cmp => Value::Int(float_order(x, y) as i64),
            })
        }
        _ => None,
    }
}

/// Whether `values` are all of one kind `Interp::native_order` orders by
/// a total order of its own, which runs no code of the program (#953):
/// strings, symbols, `Int`s, `Float`s, durations, bytes or times, each
/// alone (an empty or one-element set too). Not mixed `Int`s and
/// `Float`s (exact between them, `float_order` among floats: not shown
/// to be one total order with NaN), nor arrays (their elements may be
/// anything), nor booleans or nil (no native order: `<=>` raises for
/// them): those are sorted by `sort_fallible`.
pub(crate) fn native_kind<'v>(values: impl Iterator<Item = &'v Value>) -> bool {
    fn kind(v: &Value) -> u8 {
        match v {
            Value::Str(_) | Value::Short(_) => 1,
            Value::Symbol(_) => 2,
            Value::Int(_) => 3,
            Value::Float(_) => 4,
            Value::Duration(_) => 5,
            Value::Bytes(_) => 6,
            Value::Time(_) => 7,
            _ => 0,
        }
    }
    let mut one = None;
    for v in values {
        let k = kind(v);
        if k == 0 || *one.get_or_insert(k) != k {
            return false;
        }
    }
    true
}

/// Sort `v` by `cmp`, stably (equal ones keep their order): a merge sort
/// that stops at `cmp`'s first error and takes any answer, so a comparison
/// that raises or is not a total order (a user's block or `<=>`) cannot
/// make it panic, as the standard library's sort may (#924). On an error
/// `v` holds its elements still, in an order not specified. The elements
/// are moved, never cloned. The runtime's sorts of values go through it
/// (`Interp::sort_values`, `Array::Builder#sort_by!`).
pub(crate) fn sort_fallible<T, E>(
    v: &mut Vec<T>,
    mut cmp: impl FnMut(&T, &T) -> Result<std::cmp::Ordering, E>,
) -> Result<(), E> {
    use std::cmp::Ordering::Greater;
    // (A slot being compared always holds its element.)
    fn held<T>(x: &Option<T>) -> &T {
        x.as_ref().expect("a sorted element")
    }
    /// `a[lo..hi]` sorted, `buf[lo..hi]` its scratch: top down, so that a
    /// part is sorted whole while its values are in the cache.
    fn sort<T, E>(
        a: &mut [Option<T>],
        buf: &mut [Option<T>],
        lo: usize,
        hi: usize,
        cmp: &mut impl FnMut(&T, &T) -> Result<std::cmp::Ordering, E>,
    ) -> Result<(), E> {
        // Short runs by insertion.
        if hi - lo <= 16 {
            for k in lo + 1..hi {
                let mut j = k;
                while j > lo && cmp(held(&a[j - 1]), held(&a[j]))? == Greater {
                    a.swap(j - 1, j);
                    j -= 1;
                }
            }
            return Ok(());
        }
        let mid = lo + (hi - lo) / 2;
        sort(a, buf, lo, mid, cmp)?;
        sort(a, buf, mid, hi, cmp)?;
        // (Already in order: nothing to merge.)
        if cmp(held(&a[mid - 1]), held(&a[mid]))? != Greater {
            return Ok(());
        }
        let (mut l, mut r, mut o) = (lo, mid, lo);
        while l < mid && r < hi {
            // (The left one first unless it comes after: stable.)
            if cmp(held(&a[l]), held(&a[r]))? == Greater {
                buf[o] = a[r].take();
                r += 1;
            } else {
                buf[o] = a[l].take();
                l += 1;
            }
            o += 1;
        }
        // (What is left of either half, in order.)
        let (left, right) = a.split_at_mut(mid);
        for x in left[l..]
            .iter_mut()
            .chain(right[r - mid..hi - mid].iter_mut())
        {
            buf[o] = x.take();
            o += 1;
        }
        for (to, from) in a[lo..hi].iter_mut().zip(&mut buf[lo..hi]) {
            *to = from.take();
        }
        Ok(())
    }
    let n = v.len();
    let mut a: Vec<Option<T>> = v.drain(..).map(Some).collect();
    let mut buf: Vec<Option<T>> = (0..n).map(|_| None).collect();
    let result = sort(&mut a, &mut buf, 0, n, &mut cmp);
    // (On an error part of the elements may be in `buf`: all are kept.)
    v.extend(a.into_iter().chain(buf).flatten());
    result
}

/// `Float#<=>`: a total order, NaN after every other number (and equal to
/// itself), so that sorting an array with a NaN is well defined.
pub fn float_order(x: f64, y: f64) -> std::cmp::Ordering {
    match (x.is_nan(), y.is_nan()) {
        (false, false) => x.partial_cmp(&y).unwrap_or(std::cmp::Ordering::Equal),
        (true, true) => std::cmp::Ordering::Equal,
        (true, false) => std::cmp::Ordering::Greater,
        (false, true) => std::cmp::Ordering::Less,
    }
}

/// A function body: QIR interpreted by the VM, or machine code produced by
/// `quarz build` (which still gets its arguments through an
/// `Activation`).
pub type CompiledFn =
    unsafe extern "C" fn(*const Interp, *const crate::vm::Activation, *mut Value) -> u32;

/// Materialized constant pools, by function id.
pub type Pools = Rc<RefCell<Vec<Rc<RefCell<Vec<Value>>>>>>;

/// A constant's value, evaluated by its initializer at the first use, and
/// read without a lock after that.
#[derive(Debug, Default)]
pub struct ConstCell {
    value: std::sync::OnceLock<SharedValue>,
    init: std::sync::Mutex<ConstInit>,
}

#[derive(Debug, Default)]
enum ConstInit {
    #[default]
    Idle,
    /// The initializer runs in task `task`; the tasks in `waiters` wait
    /// for it (they would otherwise run it again).
    Running {
        task: sched::TaskRef,
        waiters: Vec<sched::TaskRef>,
    },
}

/// A lock that a panic while holding it does not make unusable (nothing
/// is left half done under the runtime's locks).
pub fn lock<T: ?Sized>(m: &std::sync::Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

/// What the running program accumulates and every worker thread of an
/// M:N scheduler is to share (it is `Send + Sync`, checked below).
pub struct Global {
    pub symbols: std::sync::RwLock<SymbolTable>,
    /// Every constant loaded so far, by id (the REPL loads more); each
    /// interpreter keeps the cells of its program in `Program::consts`.
    consts: std::sync::Mutex<Vec<std::sync::Arc<ConstCell>>>,
    /// The values of the enum variants without fields, by class.
    variant_singletons: std::sync::Mutex<HashMap<ClassId, SharedValue>>,
    /// The top-level object of each file (the `self` of its top-level
    /// statements; a function has none, docs/01 §2), by file index: one
    /// for every worker, the REPL's inputs and the compiler's
    /// compile-time runs (`Interp::unit_self`).
    unit_selfs: std::sync::Mutex<HashMap<u32, SharedValue>>,
    at_exit: std::sync::Mutex<Vec<SharedValue>>,
    stdout: std::sync::Mutex<Box<dyn std::io::Write + Send>>,
    /// The status of an `exit` in a task nobody waits for, which the root
    /// task raises as `SystemExit` where it next waits (as Ruby raises a
    /// thread's in the main thread); `NO_EXIT` for none.
    exit_request: std::sync::atomic::AtomicI64,
    /// The root task, which `exit_request` goes to.
    root: std::sync::Mutex<Option<sched::TaskRef>>,
    /// The worker threads that run the tasks.
    pub workers: std::sync::Arc<sched::Workers>,
    /// Which program of the process this is (the REPL's inputs share
    /// one), for `deinit::set_classes`.
    pub id: u64,
}

const _: () = {
    const fn shareable<T: Send + Sync>() {}
    shareable::<Global>();
};

impl Global {
    pub fn new(out: Box<dyn std::io::Write + Send>, threads: usize) -> Global {
        Global {
            workers: sched::Workers::new(threads),
            symbols: std::sync::RwLock::new(SymbolTable::default()),
            consts: std::sync::Mutex::new(Vec::new()),
            variant_singletons: std::sync::Mutex::new(HashMap::new()),
            unit_selfs: std::sync::Mutex::new(HashMap::new()),
            at_exit: std::sync::Mutex::new(Vec::new()),
            stdout: std::sync::Mutex::new(out),
            exit_request: std::sync::atomic::AtomicI64::new(NO_EXIT),
            root: std::sync::Mutex::new(None),
            id: {
                static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            },
        }
    }
}

use sched::NO_EXIT;

/// Whether two exceptions are the same object.
fn same_object(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Object(a), Value::Object(b)) => Rc::ptr_eq(a, b),
        _ => false,
    }
}

/// The name of the task `Task.timeout` runs its block in.
pub(crate) const TIMEOUT_TASK: &str = "timeout";

/// The top-level object of file `file`, whose main pseudo-class is
/// `class`, in `global`: one for all the workers, made by the first that
/// asks (a compile-time run runs no unit's top level), and made again where
/// the one kept is of another class (the REPL rolled back the input that
/// made it, whose ids the next one reuses). Immortal: the tasks the top
/// level starts may keep it.
fn unit_self_in(global: &Global, file: u32, class: ClassId) -> Value {
    let mut selfs = lock(&global.unit_selfs);
    let kept = selfs
        .get(&file)
        .is_some_and(|v| matches!(v.get(), Value::Object(o) if o.class == class));
    if !kept {
        let v = Value::Object(Object::new(class, Fields::new()));
        selfs.insert(file, SharedValue::immortal(v));
    }
    selfs[&file].get().clone()
}

/// Run-time state that outlives one interpreter instance (the REPL creates
/// an interpreter per input over the same state).
#[derive(Clone)]
pub struct SharedState {
    pub global: std::sync::Arc<Global>,
    pub sched: Rc<RefCell<Scheduler>>,
    pub next_tag: Rc<Cell<u64>>,
    pub repl_frame: Option<Rc<Frame>>,
    /// Every function loaded so far, by id (append-only).
    pub funcs: Rc<RefCell<Vec<Rc<FuncInfo>>>>,
    /// Materialized constant pools, by function id.
    pub pools: Pools,
    /// Machine-code bodies, by function id (`None` = interpret).
    pub compiled: Rc<RefCell<Vec<Option<CompiledFn>>>>,
    /// The functions' bodies, for the interpreter (`vm::BodyTable`), kept
    /// opaque: a compiled program has none and links no code for them.
    pub bodies: std::rc::Rc<std::cell::OnceCell<std::rc::Rc<dyn std::any::Any>>>,
}

impl SharedState {
    /// Forget every constant's value: each initializes again when next
    /// read. For the compiler's runs of `static` statements, after a
    /// field was added to a class whose instances a constant may hold
    /// with the old layout (docs/14 §5).
    pub fn reset_consts(&self) {
        self.reset_consts_from(0);
    }

    /// Forget the constants' values from `consts` on and the variants'
    /// shared values from `classes` on: the REPL rolled back a failed
    /// input (a `static` statement may have run), whose ids the next one
    /// reuses.
    pub fn forget(&self, consts: usize, classes: usize) {
        self.reset_consts_from(consts);
        lock(&self.global.variant_singletons).retain(|c, _| (*c as usize) < classes);
        lock(&self.global.unit_selfs)
            .retain(|_, v| matches!(v.get(), Value::Object(o) if (o.class as usize) < classes));
    }

    /// `reset_consts` for the constants from `first` on (the REPL keeps
    /// those of earlier inputs, which cannot hold an instance of a class
    /// a statement of a later one adds a field to).
    pub fn reset_consts_from(&self, first: usize) {
        for cell in lock(&self.global.consts).iter_mut().skip(first) {
            *cell = Default::default();
        }
    }

    /// State for a program run by one worker (the REPL, a helper thread).
    pub fn new(out: Box<dyn std::io::Write + Send>) -> SharedState {
        SharedState::with_threads(out, 1)
    }

    /// The same for a helper thread, or why its poller could not be made
    /// (`Scheduler::try_new`).
    pub fn try_new(out: Box<dyn std::io::Write + Send>) -> std::io::Result<SharedState> {
        let global = std::sync::Arc::new(Global::new(out, 1));
        let sched = Scheduler::try_new(0, global.workers.clone())?;
        Ok(SharedState::with_scheduler(global, 0, sched))
    }

    /// State for a program whose tasks run on `threads` workers.
    pub fn with_threads(out: Box<dyn std::io::Write + Send>, threads: usize) -> SharedState {
        let global = std::sync::Arc::new(Global::new(out, threads));
        let sched = Scheduler::new(0, global.workers.clone());
        SharedState::with_scheduler(global, 0, sched)
    }

    /// The state of worker `worker` of the program `global` belongs to,
    /// with `sched` its scheduler. Each worker numbers its tags in a range
    /// of its own: a flow's tag must not match one another worker gave out
    /// (a task's block may have been made on another worker).
    fn with_scheduler(
        global: std::sync::Arc<Global>,
        worker: u32,
        sched: Scheduler,
    ) -> SharedState {
        SharedState {
            global,
            sched: Rc::new(RefCell::new(sched)),
            next_tag: Rc::new(Cell::new((u64::from(worker) << 48) | 1)),
            repl_frame: None,
            funcs: Rc::new(RefCell::new(Vec::new())),
            pools: Rc::new(RefCell::new(Vec::new())),
            compiled: Rc::new(RefCell::new(Vec::new())),
            bodies: std::rc::Rc::new(std::cell::OnceCell::new()),
        }
    }
}

/// Ids of exception classes the runtime raises.
#[derive(Clone, Debug, Default)]
pub struct ExcClasses {
    pub runtime_error: ClassId,
    pub argument_error: ClassId,
    pub type_error: ClassId,
    pub index_error: ClassId,
    pub key_error: ClassId,
    pub zero_division: ClassId,
    pub frozen_error: ClassId,
    pub no_matching_pattern: ClassId,
    pub stop_iteration: ClassId,
    pub channel_closed: ClassId,
    pub cancelled: ClassId,
    pub timeout: ClassId,
    pub deadlock: ClassId,
    pub io_error: ClassId,
    pub system_call_error: ClassId,
    pub socket_error: ClassId,
    pub tls_error: ClassId,
    pub tls_certificate_error: ClassId,
    pub crypto_error: ClassId,
    /// `Bytes::Secret::WipedError`: a use of a wiped secret.
    pub secret_wiped: ClassId,
    pub eof_error: ClassId,
    /// `IO::LineTooLong`: a line read past its `limit:` (#1135).
    pub line_too_long: ClassId,
    pub not_implemented: ClassId,
    pub system_exit: ClassId,
    pub range_error: ClassId,
    pub float_domain_error: ClassId,
    pub overflow_error: ClassId,
    pub system_stack: ClassId,
    /// `Meta::CompileTimeError`: a compile-time run's refusals.
    pub compile_time: ClassId,
}

/// Ids of runtime value classes.
#[derive(Clone, Debug, Default)]
pub struct RtClasses {
    /// `Shareable`, whose membership `Object#shareable?` tests
    /// (`transfer::Rule::Shareable`).
    pub shareable: ClassId,
    /// `Unshareable`: a type that includes it is never Shareable, whatever
    /// its fields hold (`transfer::Rule::Shareable`).
    pub unshareable: ClassId,
    pub selector: ClassId,
    pub enumerator: ClassId,
    pub io: ClassId,
    pub tcp_socket: ClassId,
    pub tcp_server: ClassId,
    pub udp_socket: ClassId,
    pub unix_socket: ClassId,
    pub unix_server: ClassId,
    pub tls_socket: ClassId,
    pub random: ClassId,
    /// `Bytes::Secret`.
    pub secret: ClassId,
    /// `crypto`'s keys held natively (`ClassId::MAX` when not required).
    pub rsa_private_key: ClassId,
    pub aes_gcm: ClassId,
    pub file: ClassId,
    pub math: ClassId,
    pub process: ClassId,
    pub process_child: ClassId,
    pub process_status: ClassId,
    pub result_ok: ClassId,
    pub result_err: ClassId,
    pub socket_address: ClassId,
}

/// The part of the interpreter compiled code reads and writes directly
/// (by the offsets in `layout`): the call stack and the stack limit.
#[repr(C)]
pub struct Hot {
    pub stack_ptr: Cell<*mut *const crate::vm::Activation>,
    pub stack_len: Cell<usize>,
    pub stack_cap: Cell<usize>,
    /// Points at this thread's `sched::STACK_LIMIT` (which the scheduler
    /// switches with the running task).
    pub limit_ptr: *const Cell<usize>,
    /// How the last typed entry (`qz_fn_N_t`) that did not simply return
    /// its value left: it returns only the value, and a status here,
    /// which the caller reads and sets back to 0.
    pub typed_status: Cell<u32>,
}

impl Hot {
    fn new() -> Hot {
        Hot {
            // Dangling, never null: slices of length 0 are made from it.
            stack_ptr: Cell::new(std::ptr::NonNull::dangling().as_ptr()),
            stack_len: Cell::new(0),
            stack_cap: Cell::new(0),
            limit_ptr: sched::stack_limit_cell(),
            typed_status: Cell::new(0),
        }
    }
}

impl Drop for Hot {
    fn drop(&mut self) {
        let cap = self.stack_cap.get();
        if cap > 0 {
            // SAFETY: the buffer came from a `Vec` of this capacity.
            drop(unsafe { Vec::from_raw_parts(self.stack_ptr.get(), 0, cap) });
        }
    }
}

/// Method ids of the owned natives `Interp::owned_fast` handles.
pub struct OwnedIds {
    pub array_push: Option<MethodId>,
    pub array_set: Option<MethodId>,
    pub hash_put: Option<MethodId>,
    pub hash_delete: Option<MethodId>,
    pub set_add: Option<MethodId>,
    pub set_delete: Option<MethodId>,
}

impl Program {
    /// Method `id` (decoded now if a compiled program's not yet needed).
    #[inline]
    pub fn method(&self, id: MethodId) -> &RtMethod {
        match &self.lazy {
            Some(lazy) => lazy.get(id),
            None => self.world.method(id),
        }
    }

    pub fn method_count(&self) -> usize {
        match &self.lazy {
            Some(lazy) => lazy.count(),
            None => self.world.methods.len(),
        }
    }
}

/// What the runtime derives from every method when it loads a program
/// (a compiled program has it computed by its build: see
/// `crate::methods`).
struct Derived {
    natives: Vec<Option<NativeFn>>,
    fast_natives: Vec<Option<FastNativeFn>>,
    natives_owned: Vec<Option<OwnedNativeFn>>,
    owned: OwnedIds,
    positional_only: Vec<bool>,
    direct_funcs: Vec<Option<FuncId>>,
    vslots: Vec<u32>,
    nvslots: usize,
}

impl Derived {
    fn of(world: &RtWorld, lazy: Option<&crate::methods::Lazy>) -> Derived {
        let mut nvslots = 0usize;
        let mut vslot = |has: bool| {
            if has {
                nvslots += 1;
                (nvslots - 1) as u32
            } else {
                u32::MAX
            }
        };
        if let Some(lazy) = lazy {
            let n = lazy.count() as MethodId;
            let at = |which: usize| move |id: MethodId| lazy.native(id, which);
            let [array_push, array_set, hash_put, hash_delete, set_add, set_delete] = lazy.owned();
            // SAFETY: the tables hold functions of their kinds, which the
            // program's build listed by the natives' symbols.
            return Derived {
                natives: (0..n)
                    .map(|id| {
                        at(natives::PLAIN)(id)
                            .map(|p| unsafe { std::mem::transmute::<usize, NativeFn>(p) })
                    })
                    .collect(),
                fast_natives: (0..n)
                    .map(|id| {
                        at(natives::FAST)(id)
                            .map(|p| unsafe { std::mem::transmute::<usize, FastNativeFn>(p) })
                    })
                    .collect(),
                natives_owned: (0..n)
                    .map(|id| {
                        at(natives::OWNED)(id)
                            .map(|p| unsafe { std::mem::transmute::<usize, OwnedNativeFn>(p) })
                    })
                    .collect(),
                owned: OwnedIds {
                    array_push,
                    array_set,
                    hash_put,
                    hash_delete,
                    set_add,
                    set_delete,
                },
                positional_only: (0..n)
                    .map(|id| lazy.flags(id) & crate::methods::POSITIONAL != 0)
                    .collect(),
                direct_funcs: (0..n).map(|id| lazy.direct_func(id)).collect(),
                vslots: (0..n)
                    .map(|id| vslot(lazy.flags(id) & crate::methods::VSLOT != 0))
                    .collect(),
                nvslots,
            };
        }
        // Only what interprets has all the natives (`install_interpreter`).
        let all = crate::vm::INTERPRETER
            .get()
            .map(|i| (i.natives)())
            .expect("a program without its natives");
        let (plain, fast, owned_reg) = (&all.plain, &all.fast, &all.owned);
        let (plain_map, fast_map, owned_map) = (plain.map(), fast.map(), owned_reg.map());
        let natives = world
            .methods
            .iter()
            .map(|m| plain_map.get(m.native_key.as_deref()?).copied())
            .collect();
        let fast_natives = world
            .methods
            .iter()
            .map(|m| fast_map.get(m.native_key.as_deref()?).copied())
            .collect();
        let natives_owned = world
            .methods
            .iter()
            .map(|m| owned_map.get(m.native_key.as_deref()?).copied())
            .collect();
        let owned_id = |key: &str| -> Option<MethodId> {
            world
                .methods
                .iter()
                .position(|m| m.native_key.as_deref() == Some(key))
                .map(|i| i as MethodId)
        };
        let positional_only: Vec<bool> = world
            .methods
            .iter()
            .map(|m| !m.has_block && m.params.iter().all(|p| p.kind == RtParamKind::Positional))
            .collect();
        let direct_funcs: Vec<Option<FuncId>> = world
            .methods
            .iter()
            .zip(&positional_only)
            .map(|(m, &positional)| {
                let plain = positional
                    && m.native_key.is_none()
                    && matches!(m.synth, RtSynth::None)
                    && !m.is_abstract;
                if plain {
                    m.func
                } else {
                    None
                }
            })
            .collect();
        let vslots = world
            .methods
            .iter()
            .map(|m| vslot(m.dispatch() == quarz_ir::Dispatch::Virtual))
            .collect();
        Derived {
            natives,
            fast_natives,
            natives_owned,
            owned: OwnedIds {
                array_push: owned_id("Array#push"),
                array_set: owned_id("Array#set"),
                hash_put: owned_id("Hash#put"),
                hash_delete: owned_id("Hash#delete"),
                set_add: owned_id("Set#add"),
                set_delete: owned_id("Set#delete"),
            },
            positional_only,
            direct_funcs,
            vslots,
            nvslots,
        }
    }
}

#[repr(C)]
/// What the interpreter derives from the program when it loads it, and
/// never changes: the part that the worker threads of an M:N scheduler
/// are to share (it is `Send + Sync`, checked below).
pub struct Program {
    /// Its classes and so on, and, but in a compiled program, its methods
    /// (see `method`). Shared: the compile-time runs of a check and the
    /// interpreters a program's tasks load hold the same one (#1057).
    pub world: std::sync::Arc<RtWorld>,
    /// A compiled program's methods, decoded when first needed.
    pub lazy: Option<std::sync::Arc<crate::methods::Lazy>>,
    /// Compilation units in execution order.
    pub units: Vec<Unit>,
    pub natives: Vec<Option<NativeFn>>,
    /// By-reference versions of some natives, by method id.
    pub fast_natives: Vec<Option<FastNativeFn>>,
    /// The symbols of the program (`RtWorld::symbols`, #1129): what a
    /// decoded string may become (`Interp::declared_symbol`). Made at the
    /// first such lookup: a program that decodes no `Symbol` does not pay
    /// for it at start-up.
    pub declared_symbols: std::sync::OnceLock<FxHashSet<Box<str>>>,
    pub natives_owned: Vec<Option<OwnedNativeFn>>,
    /// The owned natives with an in-place fast path (`xs = xs.push(v)`).
    pub owned: OwnedIds,
    /// Per method: its parameters are positional only and it takes no
    /// block, so the arguments of a call without keywords are its
    /// parameters as they are (see `invoke`).
    pub positional_only: Vec<bool>,
    /// Per method: its function, when a call can go straight to it (a
    /// method body, not a native, accessor or abstract method, with
    /// positional parameters only): the interpreter's common call.
    pub direct_funcs: Vec<Option<FuncId>>,
    pub(crate) field_indices: Vec<FxHashMap<String, usize>>,
    /// The dispatch table's columns: for each method that some
    /// descendant of its owner overrides, its column in `Interp::vtable`
    /// (`u32::MAX` for the others).
    pub(crate) vslots: Vec<u32>,
    pub(crate) nvslots: usize,
    pub argv: Vec<String>,
    pub exc: ExcClasses,
    pub rt: RtClasses,
    /// The cells of the program's constants, by id (shared with
    /// `Global::consts`).
    pub(crate) consts: Vec<std::sync::Arc<ConstCell>>,
    /// The values of the enum variants without fields, by class id.
    pub(crate) singletons: Vec<Option<SharedValue>>,
}

const _: () = {
    const fn shareable<T: Send + Sync>() {}
    shareable::<Program>();
};

pub struct Interp {
    pub hot: Hot,
    pub program: std::sync::Arc<Program>,
    /// The frame of the REPL's top level, kept across inputs.
    pub repl_frame: Option<Rc<Frame>>,
    pub funcs: Rc<RefCell<Vec<Rc<FuncInfo>>>>,
    pub bodies: std::rc::Rc<std::cell::OnceCell<std::rc::Rc<dyn std::any::Any>>>,
    pub pools: Pools,
    pub compiled: Rc<RefCell<Vec<Option<CompiledFn>>>>,
    pub global: std::sync::Arc<Global>,
    /// This thread's copies of the symbols' names (`symbol_name`): local
    /// allocations, whose counts are plain, filled from the global table
    /// as needed.
    symbol_names: RefCell<Vec<Rc<str>>>,
    pub sched: Rc<RefCell<Scheduler>>,
    /// The dispatch table: for each class and each method that some
    /// descendant of its owner overrides (`Program::vslots[mid]` is the
    /// method's column), the method the class runs (`0`: not looked up
    /// yet, else the method id plus one).
    vtable: RefCell<Vec<u32>>,
    /// The module requirements the conformance-gated sends dispatch
    /// (`send_requirement`, #599): `Comparable#<=>` and `Enumerable#each`,
    /// found once at load (`None` when the program has none: shaken out).
    req_cmp: Option<MethodId>,
    req_each: Option<MethodId>,
    class_dispatch_cache: RefCell<FxHashMap<(ClassId, MethodId), Option<MethodId>>>,
    /// What each task block reads of the frames it was made in (see
    /// `natives::concurrency::captured_slots`).
    pub(crate) spawn_captures: RefCell<FxHashMap<FuncId, std::rc::Rc<Vec<Vec<u32>>>>>,
    /// `class_method_override` results.
    class_method_cache: RefCell<FxHashMap<(ClassId, MethodId), Option<MethodId>>>,
    /// The program image for helper threads, keyed by the number of
    /// functions loaded when it was taken.
    pub(crate) image_cache: RefCell<Option<(usize, std::sync::Arc<crate::transfer::ProgramImage>)>>,
    name_cache: RefCell<FxHashMap<NameKey, FxHashMap<String, Option<MethodId>>>>,
    /// What `case_eq`'s object arm runs for a pattern of a class: its own
    /// `===`, else its own `==`, else the default comparison
    /// (`has_user_method` for each), by class: one map lookup a `when`
    /// instead of two, the second by name (#1075, #1088). As
    /// `name_cache`, kept for the interpreter's life; not used in a
    /// compile-time run, whose `refuse_generated_over` applies to each
    /// dispatch.
    case_eq_methods: RefCell<FxHashMap<ClassId, CaseEq>>,
    next_tag: Rc<Cell<u64>>,
    /// The activations in progress, innermost last (all tasks share the
    /// vector; entries are tagged with their task). Raw pointers: an
    /// activation lives on the Rust stack for the duration of its call.
    /// The task being run by the scheduler.
    pub current_task_id: Cell<TaskId>,
    /// The exceptions the current task is handling (`Inst::Rescuing`),
    /// innermost last: the last one is its `$!`, the cause of an exception
    /// it raises.
    rescuing: RefCell<Vec<Value>>,
    /// A compile-time run's time limit (docs/14): checked where code
    /// loops and calls; `None` for a program.
    pub deadline: Cell<Option<std::time::Instant>>,
    /// The local time zone is UTC (the compile-time runs set it: a
    /// compilation must not depend on the machine's zone, docs/14 §3):
    /// what `Time.at`, `Time.local`, `Time#localtime` and a zone-less
    /// `Time.parse` give.
    pub local_utc: Cell<bool>,
    /// The declarations a compile-time run reflects on (docs/14).
    pub reflect: RefCell<Option<std::rc::Rc<dyn crate::reflect::Reflect>>>,
    /// Whether this compile-time run has generated a method: only then
    /// does a dispatch ask the run's record whether a generated method
    /// would have answered it (`refuse_generated_over`, #967).
    pub generated_any: Cell<bool>,
    /// Those of the other tasks of this worker that are suspended while
    /// handling one, swapped in when they run (`resume_task`).
    parked_rescuing: RefCell<FxHashMap<TaskId, Vec<Value>>>,
    /// Backtraces also walk the native stack for compiled frames that
    /// push no activation (typed entries of the LLVM backend).
    pub native_bt: Cell<bool>,
    /// The flow being returned from compiled code (see `vm.rs`).
    pub pending_flow: RefCell<Option<Flow>>,
    /// Register files of more than the inline 16, kept empty for the
    /// next interpreted call that needs one (an allocation per call
    /// otherwise).
    pub reg_pool: RefCell<Vec<Vec<Value>>>,
    /// Check the facts instructions trust as they run (`verify.rs`).
    pub verify: bool,
    /// The kinds of each class's fields, for those checks.
    pub(crate) verify_kinds: RefCell<Vec<Option<Vec<quarz_ir::FieldKind>>>>,
    /// Per function, the registers that may hold a counted value
    /// (`live::heap_possible`), with the blocks they were found for.
    pub(crate) verify_heap: RefCell<Vec<Option<crate::verify::Heap>>>,
    self_rc: RefCell<Weak<Interp>>,
    pub root_task: Cell<Option<TaskId>>,
}

impl Interp {
    pub fn new(module: quarz_ir::Module, argv: Vec<String>) -> std::rc::Rc<Interp> {
        Interp::with_output(
            module,
            argv,
            Box::new(std::io::BufWriter::new(std::io::stdout())),
        )
    }

    /// Create an interpreter writing standard output to `out`.
    pub fn with_output(
        module: quarz_ir::Module,
        argv: Vec<String>,
        out: Box<dyn std::io::Write + Send>,
    ) -> std::rc::Rc<Interp> {
        let state = SharedState::with_threads(out, sched::Workers::count_from_env());
        let quarz_ir::Module {
            world,
            functions,
            units,
        } = module;
        Interp::with_state(std::sync::Arc::new(world), 0, functions, units, argv, state)
    }

    /// Create an interpreter over shared run-time state, loading the
    /// functions `functions` at ids starting from `base` (the REPL creates
    /// one interpreter per input, sharing variables, tasks and output).
    pub fn with_state(
        world: std::sync::Arc<RtWorld>,
        base: FuncId,
        functions: Vec<Function>,
        units: Vec<Unit>,
        argv: Vec<String>,
        state: SharedState,
    ) -> std::rc::Rc<Interp> {
        Interp::install_interpreter();
        let (infos, bodies): (Vec<FuncInfo>, Vec<Vec<quarz_ir::Block>>) =
            functions.into_iter().map(Function::split).unzip();
        crate::vm::load_bodies(&state, base, bodies);
        Interp::with_state_lazy(world, base, infos, units, argv, state, None)
    }

    /// Load `functions` into the shared state at ids from `base`, with no
    /// interpreter made for them: a compile-time round loads its
    /// functions so, and the run's interpreter is made over the state
    /// after (#1070: once a round, not twice).
    pub fn load_functions(state: &SharedState, base: FuncId, functions: Vec<Function>) {
        Interp::install_interpreter();
        let (infos, bodies): (Vec<FuncInfo>, Vec<Vec<quarz_ir::Block>>) =
            functions.into_iter().map(Function::split).unzip();
        crate::vm::load_bodies(state, base, bodies);
        Interp::load_infos(state, base, infos);
    }

    /// The functions' infos and constant pools into the shared state, at
    /// ids from `base` (`with_state_lazy`, `load_functions`).
    fn load_infos(state: &SharedState, base: FuncId, functions: Vec<FuncInfo>) {
        let mut funcs = state.funcs.borrow_mut();
        let mut pools = state.pools.borrow_mut();
        let mut compiled = state.compiled.borrow_mut();
        assert_eq!(funcs.len(), base as usize, "functions loaded out of order");
        let mut symbols = state
            .global
            .symbols
            .write()
            .unwrap_or_else(|e| e.into_inner());
        for f in functions {
            let pool: Vec<Value> = f
                .consts
                .iter()
                .map(|c| match c {
                    Constant::Nil => Value::Nil,
                    Constant::Bool(b) => Value::Bool(*b),
                    Constant::Int(i) => Value::Int(*i),
                    Constant::BigInt { digits, base } => parse_integer(digits, *base),
                    Constant::Float(f) => Value::Float(*f),
                    Constant::Str(s) => Value::str(s),
                    Constant::Symbol(s) => Value::Symbol(symbols.intern(s)),
                    // Compiled on first use.
                    Constant::Regexp { .. } => Value::Nil,
                    Constant::Bytes(b) => Value::bytes(b.clone()),
                })
                .collect();
            funcs.push(Rc::new(f));
            pools.push(Rc::new(RefCell::new(pool)));
            compiled.push(None);
        }
    }

    /// `with_state` for a compiled program, whose methods (`world`'s are
    /// left empty) come from `lazy`.
    pub fn with_state_lazy(
        world: std::sync::Arc<RtWorld>,
        base: FuncId,
        functions: Vec<FuncInfo>,
        units: Vec<Unit>,
        argv: Vec<String>,
        state: SharedState,
        lazy: Option<std::sync::Arc<crate::methods::Lazy>>,
    ) -> std::rc::Rc<Interp> {
        let structural: Vec<bool> = world.classes.iter().map(|c| c.structural).collect();
        STRUCTURAL_CLASSES.with(|s| *s.borrow_mut() = structural);
        crate::value::register_layouts(&world.classes);

        // Load the functions.
        Interp::load_infos(&state, base, functions);

        let derived = Derived::of(&world, lazy.as_deref());
        let field_indices: Vec<FxHashMap<String, usize>> = world
            .classes
            .iter()
            .map(|c| {
                c.ivars
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (f.name.clone(), i))
                    .collect()
            })
            .collect();
        let nclasses = world.classes.len();
        let class_by_name = |name: &str| -> ClassId {
            world
                .class_by_name(name)
                .unwrap_or_else(|| panic!("prelude does not define {name}"))
        };
        // The classes of a standard library a program may not require
        // (`socket`): none of their values exist then.
        let library_class =
            |name: &str| -> ClassId { world.class_by_name(name).unwrap_or(ClassId::MAX) };
        let exc = ExcClasses {
            runtime_error: class_by_name("RuntimeError"),
            argument_error: class_by_name("ArgumentError"),
            type_error: class_by_name("TypeError"),
            index_error: class_by_name("IndexError"),
            key_error: class_by_name("KeyError"),
            zero_division: class_by_name("ZeroDivisionError"),
            frozen_error: class_by_name("FrozenError"),
            no_matching_pattern: class_by_name("NoMatchingPatternError"),
            stop_iteration: class_by_name("StopIteration"),
            channel_closed: class_by_name("Channel::Closed"),
            cancelled: class_by_name("Task::Cancelled"),
            timeout: class_by_name("Task::Timeout"),
            deadlock: class_by_name("DeadlockError"),
            io_error: class_by_name("IOError"),
            system_call_error: class_by_name("SystemCallError"),
            socket_error: library_class("SocketError"),
            tls_error: library_class("TLS::Error"),
            tls_certificate_error: library_class("TLS::CertificateError"),
            crypto_error: library_class("Crypto::Error"),
            secret_wiped: class_by_name("Bytes::Secret::WipedError"),
            eof_error: class_by_name("EOFError"),
            line_too_long: class_by_name("IO::LineTooLong"),
            not_implemented: class_by_name("NotImplementedError"),
            system_exit: class_by_name("SystemExit"),
            range_error: class_by_name("RangeError"),
            float_domain_error: class_by_name("FloatDomainError"),
            overflow_error: class_by_name("OverflowError"),
            system_stack: class_by_name("SystemStackError"),
            compile_time: class_by_name("Meta::CompileTimeError"),
        };
        let rt = RtClasses {
            shareable: class_by_name("Shareable"),
            unshareable: class_by_name("Unshareable"),
            selector: class_by_name("Channel::Selector"),
            enumerator: class_by_name("Enumerator"),
            io: class_by_name("IO"),
            tcp_socket: library_class("TCPSocket"),
            tcp_server: library_class("TCPServer"),
            udp_socket: library_class("UDPSocket"),
            unix_socket: library_class("UNIXSocket"),
            unix_server: library_class("UNIXServer"),
            tls_socket: library_class("TLSSocket"),
            random: class_by_name("Random"),
            secret: class_by_name("Bytes::Secret"),
            rsa_private_key: library_class("Crypto::RSA::PrivateKey"),
            aes_gcm: library_class("Crypto::AES::GCM"),
            file: class_by_name("File"),
            math: class_by_name("Math"),
            process: class_by_name("Process"),
            process_child: class_by_name("Process::Child"),
            process_status: class_by_name("Process::Status"),
            result_ok: class_by_name("Result::Ok"),
            result_err: class_by_name("Result::Err"),
            socket_address: library_class("Socket::Address"),
        };
        // Each unit's top-level object, made now if no worker, earlier
        // REPL input or compile-time run made it.
        for u in &units {
            unit_self_in(&state.global, u.file, u.main_class);
        }
        let consts: Vec<std::sync::Arc<ConstCell>> = {
            let mut all = lock(&state.global.consts);
            while all.len() < world.consts.len() {
                all.push(Default::default());
            }
            all[..world.consts.len()].to_vec()
        };
        // The same value for every task, and for every interpreter the
        // REPL creates.
        let singletons: Vec<Option<SharedValue>> = {
            let mut known = lock(&state.global.variant_singletons);
            world
                .classes
                .iter()
                .enumerate()
                .map(|(cid, c)| {
                    let unit = c.kind == quarz_ir::RtClassKind::Variant && c.fields.is_empty();
                    unit.then(|| {
                        let cid = cid as ClassId;
                        known
                            .entry(cid)
                            .or_insert_with(|| {
                                SharedValue::immortal(Value::Object(Object::new(
                                    cid,
                                    Fields::new(),
                                )))
                            })
                            .clone()
                    })
                })
                .collect()
        };
        let repl_frame = state.repl_frame.clone();
        let Derived {
            natives,
            fast_natives,
            natives_owned,
            owned,
            positional_only,
            direct_funcs,
            vslots,
            nvslots,
        } = derived;
        let program = std::sync::Arc::new(Program {
            declared_symbols: std::sync::OnceLock::new(),
            world,
            lazy,
            units,
            natives,
            fast_natives,
            natives_owned,
            owned,
            positional_only,
            direct_funcs,
            field_indices,
            vslots,
            nvslots,
            argv,
            exc,
            rt,
            consts,
            singletons,
        });
        let req_cmp = requirement(&program, program.world.builtin.comparable, "<=>");
        let req_each = requirement(&program, program.world.builtin.enumerable, "each");
        let interp = std::rc::Rc::new(Interp {
            hot: Hot::new(),
            program,
            repl_frame,
            funcs: state.funcs,
            bodies: state.bodies,
            pools: state.pools,
            compiled: state.compiled,
            global: state.global,
            symbol_names: RefCell::new(Vec::new()),
            sched: state.sched,
            vtable: RefCell::new(vec![0; nvslots * nclasses]),
            req_cmp,
            req_each,
            class_dispatch_cache: RefCell::new(FxHashMap::default()),
            spawn_captures: RefCell::new(FxHashMap::default()),
            class_method_cache: RefCell::new(FxHashMap::default()),
            image_cache: RefCell::new(None),
            name_cache: RefCell::new(FxHashMap::default()),
            case_eq_methods: RefCell::new(FxHashMap::default()),
            next_tag: state.next_tag,
            current_task_id: Cell::new(0),
            rescuing: RefCell::new(Vec::new()),
            deadline: Cell::new(None),
            local_utc: Cell::new(false),
            reflect: RefCell::new(None),
            generated_any: Cell::new(false),
            parked_rescuing: RefCell::new(FxHashMap::default()),
            native_bt: Cell::new(false),
            pending_flow: RefCell::new(None),
            reg_pool: RefCell::new(Vec::new()),
            verify: crate::verify::enabled(),
            verify_kinds: RefCell::new(Vec::new()),
            verify_heap: RefCell::new(Vec::new()),
            self_rc: RefCell::new(Weak::new()),
            root_task: Cell::new(None),
        });
        *interp.self_rc.borrow_mut() = std::rc::Rc::downgrade(&interp);
        let deinit: Vec<bool> = (0..interp.program.world.classes.len() as ClassId)
            .map(|c| interp.deinitializer(c).is_some())
            .collect();
        crate::deinit::set_classes(deinit, interp.global.id);
        // The `==` and `hash` each class's instances are compared and
        // hashed by as keys, from the lowering's rows (`RtClass::key_methods`,
        // `World::key_methods`, #813). Every interpreter makes its table
        // from its own world: a REPL input's, a static round's.
        let world = &interp.program.world;
        let keys: Vec<Option<crate::keys::KeyMethods>> =
            if world.classes.iter().all(|c| c.key_methods == (None, None)) {
                Vec::new()
            } else {
                world
                    .classes
                    .iter()
                    .map(|c| {
                        let (eq, hash) = c.key_methods;
                        (eq.is_some() || hash.is_some())
                            .then_some(crate::keys::KeyMethods { eq, hash })
                    })
                    .collect()
            };
        crate::keys::set(&interp, keys);
        interp
    }

    /// The `deinitialize` instances of class `cid` run when released.
    fn deinitializer(&self, cid: ClassId) -> Option<MethodId> {
        quarz_ir::deinitializer(&self.program.world.classes, cid)
    }

    /// Run the `deinitialize` of the objects released since the last
    /// time (see `crate::deinit`). An exception it raises is reported as
    /// a warning; it does not reach the code that released the object.
    #[cold]
    #[inline(never)]
    pub fn run_deinitializers(&self) {
        crate::deinit::run(|obj| {
            let Some(mid) = self.deinitializer(obj.class) else {
                return;
            };
            let recv = Value::Object(obj);
            if let Err(Flow::Raise(e)) = self.invoke(mid, recv, smallvec![], Vec::new(), None) {
                self.flush();
                eprintln!(
                    "warning: deinitialize raised {}: {}",
                    self.class_name(&e),
                    self.exception_message(&e)
                );
            }
        });
    }

    pub fn rc(&self) -> std::rc::Rc<Interp> {
        self.self_rc
            .borrow()
            .upgrade()
            .expect("interpreter dropped")
    }

    /// The symbol `name` when it is one of the program's
    /// (`Program::declared_symbols`), interned; nil otherwise, interning
    /// nothing: for a string from outside (`JSON.decode`), which must not
    /// grow the symbol table, #1129.
    pub fn declared_symbol(&self, name: &str) -> Option<Symbol> {
        let world = &self.program.world;
        self.program
            .declared_symbols
            .get_or_init(|| world.symbols.iter().map(Box::from).collect())
            .contains(name)
            .then(|| self.intern(name))
    }

    pub fn intern(&self, name: &str) -> Symbol {
        let symbols = &self.global.symbols;
        if let Some(s) = symbols
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .lookup(name)
        {
            return s;
        }
        symbols
            .write()
            .unwrap_or_else(|e| e.into_inner())
            .intern(name)
    }

    pub fn symbol_name(&self, sym: Symbol) -> Rc<str> {
        let i = sym.0 as usize;
        if let Some(n) = self.symbol_names.borrow().get(i) {
            return n.clone();
        }
        // Copy the names interned since (the table only grows).
        let table = self
            .global
            .symbols
            .read()
            .unwrap_or_else(|e| e.into_inner());
        let mut names = self.symbol_names.borrow_mut();
        for k in names.len()..table.len() {
            names.push(Rc::from(&**table.name(Symbol(k as u32))));
        }
        names[i].clone()
    }

    pub fn new_tag(&self) -> u64 {
        let t = self.next_tag.get();
        self.next_tag.set(t + 1);
        t
    }

    pub fn file_name(&self, file: u32) -> &str {
        self.program
            .world
            .file_names
            .get(file as usize)
            .map(String::as_str)
            .unwrap_or("?")
    }

    // ----- running ---------------------------------------------------------------

    /// Run the main program as the root task. Returns the exit code.
    pub fn run(self: &std::rc::Rc<Interp>) -> i32 {
        let me = self.clone();
        let body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
            let mut result = Ok(Value::Nil);
            for unit in me.program.units.iter() {
                let self_val = me.unit_self(unit.file);
                if let Err(f) = me.run_top_level(unit.body, unit.file, self_val) {
                    result = Err(f);
                    break;
                }
            }
            task_exit(&me, result)
        });
        let root = self
            .sched
            .borrow_mut()
            .spawn(body, None, "main".to_string(), 256 * 1024 * 1024);
        self.root_task.set(Some(root.id));
        self.set_root(&root);
        let code = self.pending_exit(&root, self.run_loop(&root));
        // The other workers stop with the main program.
        self.global.workers.stop();
        let code = self.run_at_exit(code);
        self.flush();
        if std::env::var_os("QUARZ_COUNT_COPIES").is_some() {
            eprintln!(
                "quarz: {} copies of shared collections",
                crate::value::copies()
            );
            eprintln!(
                "quarz: {} values moved across Task.blocking",
                crate::transfer::moved()
            );
        }
        code
    }

    /// End a session that ran pieces of a program (the REPL) with `code`:
    /// its `at_exit` blocks run, as when a program ends. The exit code.
    pub fn finish(self: &std::rc::Rc<Interp>, code: i32) -> i32 {
        let code = self.run_at_exit(code);
        self.flush();
        code
    }

    /// Run the `at_exit` blocks, the last registered first (and any they
    /// register), each as the root task of a run of its own, as Ruby does
    /// when the main program ends, also by `exit` or an exception. An
    /// exception in one is reported; a block that exits or fails sets the
    /// exit code.
    fn run_at_exit(self: &std::rc::Rc<Interp>, mut code: i32) -> i32 {
        if let Some(status) = self.take_exit_request() {
            if code == 0 {
                code = status as i32;
            }
        }
        loop {
            let Some(block) = lock(&self.global.at_exit).pop() else {
                return code;
            };
            let block = block.into_inner();
            let me = self.clone();
            let body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
                let r = me.call_block(&block, smallvec![]);
                task_exit(&me, r)
            });
            let root =
                self.sched
                    .borrow_mut()
                    .spawn(body, None, "at_exit".to_string(), 16 * 1024 * 1024);
            self.root_task.set(Some(root.id));
            self.set_root(&root);
            let c = self.pending_exit(&root, self.run_loop(&root));
            if c != 0 {
                code = c;
            }
        }
    }

    /// The shared state, for creating another interpreter over it.
    pub fn shared_state(&self) -> SharedState {
        SharedState {
            global: self.global.clone(),
            sched: self.sched.clone(),
            next_tag: self.next_tag.clone(),
            repl_frame: self.repl_frame.clone(),
            funcs: self.funcs.clone(),
            pools: self.pools.clone(),
            compiled: self.compiled.clone(),
            bodies: self.bodies.clone(),
        }
    }

    /// The top-level object of file `file` (nil for a file without one).
    pub fn unit_self(&self, file: u32) -> Value {
        match self.program.world.file_mains.get(file as usize) {
            Some(Some(class)) => unit_self_in(&self.global, file, *class),
            _ => Value::Nil,
        }
    }

    /// Evaluate REPL input: run the function `fid` in the persistent REPL
    /// frame as the top level of unit `file`. Returns the value of the
    /// last statement, or `None` after an uncaught exception (which is
    /// reported) or exit.
    pub fn run_repl(
        self: &std::rc::Rc<Interp>,
        file: u32,
        fid: FuncId,
    ) -> Result<Option<Value>, i32> {
        let me = self.clone();
        let run_body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
            let self_val = me.unit_self(file);
            let result = me.run_top_level(fid, file, self_val);
            task_exit(&me, result)
        });
        let root =
            self.sched
                .borrow_mut()
                .spawn(run_body, None, "repl".to_string(), 256 * 1024 * 1024);
        self.set_root(&root);
        let code = self.run_loop(&root);
        self.flush();
        if code != 0 && !root.is_done() {
            // Ending: an exit the root has not raised goes with it.
            let _ = root.take_exit();
            return Err(code);
        }
        // An exit from a task nobody awaited, the line ended before raising
        // (both taken: the first one wins).
        let (own, global) = (root.take_exit(), self.take_exit_request());
        if let Some(status) = own.or(global) {
            return Err(status as i32);
        }
        let result = root.result();
        match result {
            Some(TaskResult::Value(v)) => Ok(Some(v)),
            Some(TaskResult::Error(_)) => Ok(None),
            None => Err(code),
        }
    }

    /// Run a compile-time `static` statement (docs/14): the function `fid`
    /// with `self_val`, as a root task of its own (constants and blocks
    /// need one), under the deadline set. The exception it raised, or
    /// its exit status, comes back for the compiler's diagnostic.
    pub fn run_static(
        self: &std::rc::Rc<Interp>,
        fid: FuncId,
        self_val: Value,
        file: u32,
    ) -> Result<Value, StaticEnd> {
        let me = self.clone();
        let run_body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
            let result = me.run_init(fid, self_val, file);
            task_exit(&me, result)
        });
        let root = self.sched.borrow_mut().spawn(
            run_body,
            None,
            "static statement".to_string(),
            256 * 1024 * 1024,
        );
        self.set_root(&root);
        let code = self.run_loop_with(&root, false);
        self.flush();
        if let Some(status) = root.take_exit().or(self.take_exit_request()) {
            return Err(StaticEnd::Exited(status as i32));
        }
        match root.result() {
            Some(TaskResult::Value(v)) => Ok(v),
            Some(TaskResult::Error(e)) => Err(StaticEnd::Raised(e)),
            None => Err(StaticEnd::Exited(code)),
        }
    }

    /// `run_static` for a block kept from an earlier compile-time run (a
    /// class-end hook, docs/14 §5), called with `args`.
    pub fn run_static_block(
        self: &std::rc::Rc<Interp>,
        block: Value,
        args: Vec<Value>,
    ) -> Result<Value, StaticEnd> {
        let me = self.clone();
        let run_body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
            let result = me.call_block(&block, args.into_iter().collect());
            task_exit(&me, result)
        });
        let root = self.sched.borrow_mut().spawn(
            run_body,
            None,
            "class-end hook".to_string(),
            256 * 1024 * 1024,
        );
        self.set_root(&root);
        let code = self.run_loop_with(&root, false);
        self.flush();
        if let Some(status) = root.take_exit().or(self.take_exit_request()) {
            return Err(StaticEnd::Exited(status as i32));
        }
        match root.result() {
            Some(TaskResult::Value(v)) => Ok(v),
            Some(TaskResult::Error(e)) => Err(StaticEnd::Raised(e)),
            None => Err(StaticEnd::Exited(code)),
        }
    }

    pub(crate) fn run_loop(&self, root: &Rc<TaskHandle>) -> i32 {
        self.run_loop_with(root, true)
    }

    /// The run loop; `report` prints an exception the root task died with
    /// (a helper thread hands it back instead).
    pub(crate) fn run_loop_with(&self, root: &Rc<TaskHandle>, report: bool) -> i32 {
        loop {
            let next = self.sched.borrow_mut().next_step();
            match next {
                sched::Next::Run(task, co) => {
                    if let Some(code) = self.resume_task(task, co) {
                        return code;
                    }
                    if root.is_done() {
                        break;
                    }
                }
                sched::Next::Spawn(requests) => self.adopt_tasks(requests),
                sched::Next::Exit(code) => return code,
                sched::Next::Stop => return 0,
                sched::Next::Idle => {
                    if root.is_done() {
                        break;
                    }
                    // Deadlock: no runnable tasks, no timers.
                    self.flush();
                    let waiting = self.sched.borrow().waiting_tasks();
                    eprintln!(
                        "DeadlockError: all tasks are blocked ({})",
                        waiting.join(", ")
                    );
                    return 1;
                }
            }
        }
        match root.result() {
            Some(TaskResult::Error(exc)) => {
                if report {
                    self.flush();
                    self.report_uncaught(&exc);
                }
                1
            }
            _ => 0,
        }
    }

    /// Cancel the tasks still running (a `Task.blocking` block's, once it
    /// returned) and run them until they end, so that their `ensure`
    /// clauses run and none is left for a later run on this interpreter;
    /// tasks they spawn meanwhile too. Tasks that never end (waiting
    /// uncancellably forever) are left. The code of one that ended the
    /// program (`Flow::Exit`), if any.
    pub(crate) fn cancel_leftovers(&self) -> Option<i32> {
        loop {
            let left = self.sched.borrow().live_tasks();
            if left.is_empty() {
                return None;
            }
            for t in &left {
                if !t.cancel_requested() {
                    self.cancel_task(t);
                }
            }
            let next = self.sched.borrow_mut().next_step();
            match next {
                sched::Next::Run(task, co) => {
                    if let Some(code) = self.resume_task(task, co) {
                        return Some(code);
                    }
                }
                sched::Next::Spawn(requests) => self.adopt_tasks(requests),
                sched::Next::Exit(code) => return Some(code),
                sched::Next::Stop | sched::Next::Idle => return None,
            }
        }
    }

    pub fn flush(&self) {
        use std::io::Write;
        let _ = lock(&self.global.stdout).flush();
    }

    fn report_uncaught(&self, exc: &Value) {
        let class_name = self.class_name(exc);
        let message = self.exception_message(exc);
        eprintln!("{class_name}: {message}");
        if let Value::Object(o) = exc {
            if let Some(bt) = o.backtrace() {
                for frame in bt.iter() {
                    eprintln!("    from {frame}");
                }
            }
        }
    }

    // ----- tasks -------------------------------------------------------------------

    pub fn current_task(&self) -> Rc<TaskHandle> {
        self.sched.borrow().current_task()
    }

    /// Start a task running `closure` (marked shared: it may run on
    /// another worker), on the worker `Workers::place` picks; a
    /// `Task.timeout` block's on this one.
    pub fn spawn_task(
        &self,
        closure: Value,
        scope: Option<Rc<ScopeInner>>,
        name: &str,
    ) -> Rc<TaskHandle> {
        let (here, workers) = {
            let s = self.sched.borrow();
            (s.worker, s.workers.clone())
        };
        // A `Task.timeout` block is its caller's code, which may hold what
        // is not Shareable: it runs on the caller's worker.
        let target = if name == TIMEOUT_TASK {
            here
        } else {
            workers.place(here)
        };
        // Where its `exit`s go: its spawner's sink; the task of a
        // `Task.timeout` block is one itself (the block is its caller's).
        let sink = {
            let s = self.sched.borrow();
            s.current
                .and_then(|id| TaskHandle::children_sink(s.task(id)))
        };
        let is_sink = name == TIMEOUT_TASK;
        // In a `Task.__contain` block: listed there, and its tasks too.
        // The task of a `Task.timeout` block and a scope's child are their
        // spawner's own code, which ends with it: they take the container
        // (for what they spawn) but are not listed, unless the scope has
        // ended (it waits for nobody then; checked once the child is in
        // it, under the same lock as the scope's end).
        let container = if sched::CONTAINERS.load(std::sync::atomic::Ordering::Acquire) != 0 {
            let s = self.sched.borrow();
            s.current.and_then(|id| s.task(id).container())
        } else {
            None
        };
        let contain = |handle: &Rc<TaskHandle>| {
            if let Some(c) = &container {
                let listed = !is_sink && handle.scope.as_ref().is_none_or(|s| s.is_ended());
                // Set first: a task listed is one the block's end may let
                // go (`set_container(None)`), which must win.
                handle.set_container(Some(c.clone()));
                if listed && !c.add(handle.clone()) {
                    handle.set_container(None);
                }
            }
        };
        // A worker that cannot start leaves the task here.
        let target = if target != here && !self.start_worker(target) {
            here
        } else {
            target
        };
        if target == here {
            let body = self.task_body(closure);
            let handle = self.sched.borrow_mut().spawn_with(
                body,
                scope,
                name.to_string(),
                sched::TASK_STACK,
                sink,
                is_sink,
            );
            contain(&handle);
            return handle;
        }
        let handle = TaskHandle::with_sink(
            target,
            workers.reserve_id(target),
            scope,
            name.to_string(),
            sink,
            is_sink,
        );
        contain(&handle);
        workers.post_spawn(
            target,
            sched::SpawnRequest {
                handle: crate::rc::SendRc::new(handle.clone()),
                block: SharedValue::new(closure),
            },
        );
        handle
    }

    /// Run one task until it suspends or ends; `Some(code)` to end the
    /// program.
    fn resume_task(&self, task: Rc<TaskHandle>, mut co: sched::TaskCoroutine) -> Option<i32> {
        self.current_task_id.set(task.id);
        // The exceptions it was handling when it was suspended, if any.
        let parked = {
            let mut p = self.parked_rescuing.borrow_mut();
            if p.is_empty() {
                None
            } else {
                p.remove(&task.id)
            }
        };
        if let Some(stack) = parked {
            *self.rescuing.borrow_mut() = stack;
        }
        let result = sched::resume(&task, &mut co);
        let stack = {
            let mut r = self.rescuing.borrow_mut();
            (!r.is_empty()).then(|| std::mem::take(&mut *r))
        };
        if let Some(stack) = stack {
            if matches!(result, corosensei::CoroutineResult::Yield(())) {
                self.parked_rescuing.borrow_mut().insert(task.id, stack);
            } else {
                // Ended (by a jump out of a handler): they go.
                drop(stack);
            }
        }
        self.sched.borrow_mut().after_resume(task, co, result)
    }

    /// Start the tasks other workers placed on this one.
    fn adopt_tasks(&self, requests: Vec<sched::SpawnRequest>) {
        for r in requests {
            let body = self.task_body(r.block.into_inner());
            self.sched
                .borrow_mut()
                .adopt(r.handle.into_inner(), body, sched::TASK_STACK);
        }
    }

    /// Start worker `w`'s thread, unless it runs already: an interpreter
    /// of its own over the program (built on that thread, whose stack
    /// limit and thread-local state it uses) and the same global state,
    /// running the tasks placed there until the program ends. Whether it
    /// runs (`Workers::start`).
    fn start_worker(&self, w: u32) -> bool {
        let global = self.global.clone();
        let workers = global.workers.clone();
        workers.start(w, |poller| self.spawn_worker(global, w, poller))
    }

    fn spawn_worker(
        &self,
        global: std::sync::Arc<Global>,
        w: u32,
        poller: std::sync::Arc<sched::Poller>,
    ) -> std::io::Result<()> {
        sched::set_multi_threaded();
        let image = self.image();
        let argv = self.program.argv.clone();
        let native_bt = self.native_bt.get();
        std::thread::Builder::new()
            .name(format!("quarz-worker-{w}"))
            .spawn(move || {
                // A panic here would leave the worker's tasks unfinished
                // and the others waiting for them: it ends the program.
                sched::exit_on_panic(move || {
                    Interp::worker_main(global, w, poller, image, argv, native_bt)
                })
            })
            .map(|_| ())
    }

    /// The body of worker `w`'s thread (see `start_worker`).
    fn worker_main(
        global: std::sync::Arc<Global>,
        w: u32,
        poller: std::sync::Arc<sched::Poller>,
        image: std::sync::Arc<crate::transfer::ProgramImage>,
        argv: Vec<String>,
        native_bt: bool,
    ) {
        let sched = Scheduler::with_poller(w, global.workers.clone(), poller);
        let state = SharedState::with_scheduler(global, w, sched);
        let interp = image.load(argv, state);
        interp.native_bt.set(native_bt);
        {
            let mut compiled = interp.compiled.borrow_mut();
            for (i, f) in image.compiled.iter().enumerate() {
                if i < compiled.len() {
                    compiled[i] = *f;
                }
            }
        }
        interp.run_worker();
        // The program is ending: its tasks are not unwound.
        std::mem::forget(interp);
    }

    /// A worker's loop: run the tasks placed on it until the program ends.
    fn run_worker(&self) {
        loop {
            let next = self.sched.borrow_mut().next_step();
            match next {
                sched::Next::Run(task, co) => {
                    let _ = self.resume_task(task, co);
                }
                sched::Next::Spawn(requests) => self.adopt_tasks(requests),
                sched::Next::Stop | sched::Next::Exit(_) | sched::Next::Idle => return,
            }
        }
    }

    /// A task's body: call `closure`, and turn how it ends into the
    /// task's result.
    fn task_body(&self, closure: Value) -> Box<dyn FnOnce() -> TaskExit> {
        let me = self.rc();
        Box::new(move || {
            // Cancelled before it started: its block does not run.
            let r = match me.check_cancel(&me.current_task()) {
                Ok(()) => me.call_block(&closure, smallvec![]),
                Err(e) => Err(e),
            };
            match r {
                Ok(v) => TaskExit::Result(TaskResult::Value(v)),
                // An `exit` nothing rescued in the task: like any exception,
                // the task's result, raised again by `await` or its scope.
                // It also goes to the task's sink (the root, or the
                // `Task.timeout` block it was spawned under), which raises it
                // where it next waits, as Ruby raises a thread's in the main
                // thread (a scope's owner the sink, it takes it once); but
                // not from `Task.timeout`'s task, whose block is its caller's.
                Err(Flow::Raise(e)) if me.exception_is_a(&e, me.program.exc.system_exit) => {
                    let task = me.current_task();
                    if task.name != TIMEOUT_TASK {
                        me.request_exit(me.exit_status(&e) as i64);
                    }
                    TaskExit::Result(TaskResult::Error(e))
                }
                Err(Flow::Raise(e)) => TaskExit::Result(TaskResult::Error(e)),
                Err(Flow::Exit(c)) => TaskExit::Exit(c),
                Err(other) => {
                    let e = me
                        .make_exception(me.program.exc.runtime_error, &stray_flow_message(&other));
                    TaskExit::Result(TaskResult::Error(e))
                }
            }
        })
    }

    /// Block the current task until woken, then check for cancellation.
    pub fn park(&self) -> Result<(), Flow> {
        let task = self.current_task();
        self.check_cancel(&task)?;
        task.set_state(sched::TaskState::Waiting);
        sched::suspend_raw();
        self.check_cancel(&task)
    }

    pub fn check_cancel(&self, task: &TaskHandle) -> Result<(), Flow> {
        if task.cancel_due() {
            task.note_cancel_delivered();
            return Err(self.raise(self.program.exc.cancelled, "task cancelled"));
        }
        match self.own_exit(task) {
            Some(exit) => Err(exit),
            None => Ok(()),
        }
    }

    /// The `SystemExit` of an `exit` delivered to `task` as a sink (or, for
    /// the run's root, one no live sink took), taking it.
    fn own_exit(&self, task: &TaskHandle) -> Option<Flow> {
        // None delivered anywhere: nothing to look at (each is counted
        // before it is stored, and its sink woken after).
        if sched::PENDING_EXITS.load(std::sync::atomic::Ordering::Acquire) == 0 {
            return None;
        }
        let status = match task.take_exit() {
            Some(status) => status,
            None => {
                let global = &self.global.exit_request;
                if global.load(std::sync::atomic::Ordering::Acquire) == NO_EXIT
                    || *lock(&self.global.root) != Some(task.task_ref())
                {
                    return None;
                }
                let mut status = self.take_exit_request()?;
                // The root waiting in `Task.timeout`: the block takes it.
                if let Some(d) = task.live_delegate() {
                    match d.deliver_exit(status) {
                        Ok(()) => {
                            self.wake_ref(d.task_ref());
                            return None;
                        }
                        Err(s) => status = s,
                    }
                }
                status
            }
        };
        Some(Flow::Raise(crate::natives::system_exit(
            self, status, "exit",
        )))
    }

    /// An `exit` from the current task, which ended in `SystemExit`: its
    /// sink (or the nearest one still running) raises it where it next
    /// waits; with none, the run's root, or the program ends with its
    /// status if the root ended first.
    fn request_exit(&self, mut status: i64) {
        let mut next = self.current_task().live_sink();
        while let Some(sink) = next {
            let target = sink.live_delegate().unwrap_or_else(|| sink.clone());
            // Checked again once stored: one that finished meanwhile gives
            // it back, and the next sink up takes it.
            match target.deliver_exit(status) {
                Ok(()) => {
                    self.wake_ref(target.task_ref());
                    return;
                }
                Err(s) => status = s,
            }
            // A delegate that just finished: its sink takes it.
            if !Rc::ptr_eq(&target, &sink) {
                match sink.deliver_exit(status) {
                    Ok(()) => {
                        self.wake_ref(sink.task_ref());
                        return;
                    }
                    Err(s) => status = s,
                }
            }
            next = sink.live_sink();
        }
        sched::PENDING_EXITS.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
        if self
            .global
            .exit_request
            .compare_exchange(
                NO_EXIT,
                status,
                std::sync::atomic::Ordering::AcqRel,
                std::sync::atomic::Ordering::Acquire,
            )
            .is_err()
        {
            sched::PENDING_EXITS.fetch_sub(1, std::sync::atomic::Ordering::AcqRel);
        }
        if let Some(root) = *lock(&self.global.root) {
            self.wake_ref(root);
        }
    }

    /// The run's root task: a sink, and the one an exit no live sink takes
    /// goes to.
    pub(crate) fn set_root(&self, root: &TaskHandle) {
        root.make_sink();
        *lock(&self.global.root) = Some(root.task_ref());
    }

    /// The exit code of a run whose root task ended with `code`, or the
    /// status of an exit the root task ended before raising.
    pub(crate) fn pending_exit(&self, root: &TaskHandle, code: i32) -> i32 {
        match root.take_exit().or_else(|| self.take_exit_request()) {
            Some(status) if code == 0 => status as i32,
            _ => code,
        }
    }

    /// The status of an exit no sink took and nothing raised yet, taking
    /// it.
    pub(crate) fn take_exit_request(&self) -> Option<i64> {
        match self
            .global
            .exit_request
            .swap(NO_EXIT, std::sync::atomic::Ordering::AcqRel)
        {
            NO_EXIT => None,
            status => {
                sched::PENDING_EXITS.fetch_sub(1, std::sync::atomic::Ordering::AcqRel);
                Some(status)
            }
        }
    }

    /// Wait until the descriptor `fd` of the IO state `st` is readable
    /// (or writable), parking the task. The task is listed among the
    /// descriptor's waiters meanwhile, which closing it wakes on
    /// whatever worker it waits.
    pub fn wait_io<T: Watched>(
        &self,
        st: &IoCell<T>,
        fd: std::os::fd::RawFd,
        writable: bool,
    ) -> Result<(), Flow> {
        self.wait_io_held(st, st.borrow_mut(), fd, writable)
    }

    /// `wait_io` for a caller holding the state's lock (`held`), which
    /// found nothing to take: the wait is registered before the lock is
    /// released, so that another task that takes the lock next and
    /// leaves bytes in the buffer finds this one among the waiters and
    /// wakes it (a wake that comes before the park is not lost: another
    /// worker's is posted and delivered once this worker suspends the
    /// task, and this worker runs nothing else before it).
    ///
    /// A state closed meanwhile is not waited on: `close` took the waiters
    /// to wake and dropped the descriptor before this registration, so no
    /// wake would come (#1134: a writer that released the lock at
    /// `WouldBlock`, a TLS pump, ...). It returns at once, and the
    /// caller's loop finds the state closed as if the close had come
    /// first.
    pub fn wait_io_held<T: Watched>(
        &self,
        st: &IoCell<T>,
        mut held: crate::value::IoGuard<'_, T>,
        fd: std::os::fd::RawFd,
        writable: bool,
    ) -> Result<(), Flow> {
        if held.closed() {
            return Ok(());
        }
        let me = self.sched.borrow().current_ref();
        let w = held.watch();
        w.waiters.push(me);
        let serial = w.serial;
        self.sched.borrow_mut().wait_fd(fd, serial, writable, me.id);
        drop(held);
        let r = self.park();
        self.sched.borrow_mut().unwait_fd(fd, me.id);
        st.borrow_mut().watch().waiters.retain(|t| *t != me);
        r
    }

    /// Run a blocking job on another thread, parking the task until it
    /// finishes (file IO, child processes, `Task.blocking`).
    pub fn block_on<T: Send + 'static>(
        &self,
        job: impl FnOnce() -> T + Send + 'static,
    ) -> Result<T, Flow> {
        self.block_on_kind(sched::JobKind::General, job)
    }

    /// `block_on` in `kind`'s pool (`JobKind::Lookup` for name
    /// resolution). No helper to run it: a `SystemCallError`, where the
    /// process used to end (#1128). The task cancelled while the job
    /// waits for a helper: the job is dropped unrun.
    pub fn block_on_kind<T: Send + 'static>(
        &self,
        kind: sched::JobKind,
        job: impl FnOnce() -> T + Send + 'static,
    ) -> Result<T, Flow> {
        use std::sync::mpsc::TryRecvError;
        let id = self.current_task().id;
        let (rx, dropped) = self.sched.borrow_mut().offload(id, kind, job);
        loop {
            match rx.try_recv() {
                Ok(Ok(v)) => return Ok(v),
                Ok(Err(e)) => {
                    return Err(self.raise(
                        self.program.exc.system_call_error,
                        &format!("start a helper thread: {e}"),
                    ))
                }
                Err(TryRecvError::Disconnected) => {
                    return Err(self.raise(self.program.exc.runtime_error, "background job failed"))
                }
                Err(TryRecvError::Empty) => {
                    if let Err(flow) = self.park() {
                        dropped.store(true, std::sync::atomic::Ordering::Release);
                        return Err(flow);
                    }
                }
            }
        }
    }

    /// Run `f` out of reach of the current task's cancellation (`Task.uncancellable`,
    /// and the waits of a scope or `Task.timeout` for children it has
    /// cancelled): its waits do not raise `Task::Cancelled`.
    pub fn uncancellable<R>(&self, f: impl FnOnce() -> R) -> R {
        let task = self.current_task();
        task.set_uncancellable(true);
        let r = f();
        task.set_uncancellable(false);
        r
    }

    /// Let the other tasks run, then raise a cancellation or an exit
    /// request that came meanwhile: `Task.yield` is a cancellation point,
    /// as Kotlin's `yield()`.
    pub fn yield_now(&self) -> Result<(), Flow> {
        self.sched.borrow_mut().requeue_current();
        sched::suspend_raw();
        self.check_cancel_current()
    }

    /// `check_cancel` for the current task, without taking a reference to
    /// it (`Task.yield` may be called often).
    pub fn check_cancel_current(&self) -> Result<(), Flow> {
        // Nothing cancelled yet and no exit delivered: nothing to look up.
        if !sched::ANY_CANCELLED.load(std::sync::atomic::Ordering::Acquire)
            && sched::PENDING_EXITS.load(std::sync::atomic::Ordering::Acquire) == 0
        {
            return Ok(());
        }
        // Nothing for the current task: no need to take a reference to it.
        let quiet = {
            let s = self.sched.borrow();
            let task = s.task(s.current.expect("no current task"));
            !task.cancel_due()
                && task.exit_request.load(std::sync::atomic::Ordering::Acquire) == NO_EXIT
                && (self
                    .global
                    .exit_request
                    .load(std::sync::atomic::Ordering::Acquire)
                    == NO_EXIT
                    || *lock(&self.global.root) != Some(task.task_ref()))
        };
        if quiet {
            return Ok(());
        }
        self.check_cancel(&self.current_task())
    }

    pub fn wake(&self, id: TaskId) {
        self.sched.borrow_mut().wake(id);
    }

    /// Wake a task, whichever worker runs it.
    pub fn wake_ref(&self, r: sched::TaskRef) {
        self.sched.borrow_mut().wake_ref(r);
    }

    /// Park the task for `d`. Woken before then (a scope's owner is when
    /// a child fails), it parks again; leaving early (cancelled), it
    /// cancels its timer, which would otherwise wake its next wait.
    pub fn sleep(&self, d: Duration) -> Result<(), Flow> {
        let id = self.sched.borrow().current_ref().id;
        let timer = self.sched.borrow_mut().add_timer(d, id);
        while self.sched.borrow().timer_pending(timer) {
            if let Err(e) = self.park() {
                self.sched.borrow_mut().cancel_timer(timer);
                return Err(e);
            }
        }
        Ok(())
    }

    /// Wait for a task to finish and return its result (re-raising its
    /// exception).
    pub fn await_task(&self, task: &Rc<TaskHandle>) -> EvalResult {
        loop {
            if task.is_done() {
                // A sink awaiting a task done with an `exit` it has not
                // raised yet: that exit, once (not also the task's result).
                if sched::PENDING_EXITS.load(std::sync::atomic::Ordering::Acquire) != 0 {
                    if let Some(exit) = self.own_exit(&self.current_task()) {
                        return Err(exit);
                    }
                }
                return match task.result() {
                    Some(TaskResult::Value(v)) => Ok(v),
                    Some(TaskResult::Error(e)) => Err(Flow::Raise(e)),
                    None => Ok(Value::Nil),
                };
            }
            {
                // The task sets itself done under this lock: it is done
                // now, or it will wake this one.
                let mut joiners = sched::lock(&task.joiners);
                if task.is_done() {
                    continue;
                }
                let me = self.sched.borrow().current_ref();
                // Woken by something else, it may be listed already.
                if !joiners.contains(&me) {
                    joiners.push(me);
                }
            }
            if let Err(e) = self.park() {
                let me = self.sched.borrow().current_ref();
                sched::lock(&task.joiners).retain(|t| *t != me);
                return Err(e);
            }
        }
    }

    pub fn cancel_task(&self, task: &Rc<TaskHandle>) {
        if task.is_done() {
            return;
        }
        task.set_cancel_requested();
        self.wake_ref(task.task_ref());
    }

    // ----- exceptions ------------------------------------------------------------------

    pub fn make_exception(&self, class: ClassId, message: &str) -> Value {
        let n = self.program.world.class(class).fields.len().max(1);
        let mut fields: Fields = smallvec![Value::Nil; n];
        fields[0] = Value::str(message);
        let bt = self.capture_backtrace();
        Value::Object({
            let o = Object::new(class, fields);
            o.init_exc(ExcInfo::new(Some(Rc::new(bt)), self.rescued()));
            o
        })
    }

    /// The current task's `$!`: the exception it is handling, innermost.
    pub fn rescued(&self) -> Option<Value> {
        self.rescuing.borrow().last().cloned()
    }

    /// The current task starts handling `exc` (`Inst::Rescuing`).
    pub fn start_rescuing(&self, exc: Value) {
        self.rescuing.borrow_mut().push(exc);
    }

    /// The current task ends handling `exc`, and those it started since
    /// (left by a jump that did not end them).
    pub fn end_rescuing(&self, exc: &Value) {
        let ended: Vec<Value> = {
            let mut r = self.rescuing.borrow_mut();
            // The usual case: the innermost.
            if r.last().is_some_and(|e| same_object(e, exc)) {
                let last = r.pop();
                drop(r);
                drop(last);
                return;
            }
            match r.iter().rposition(|e| same_object(e, exc)) {
                Some(at) => r.split_off(at),
                None => return,
            }
        };
        // Dropped after the borrow: an exception's release may run code.
        drop(ended);
    }

    /// The innermost frames of the current task's call stack, as
    /// `file:line:in name` (deep recursion is cut off).
    pub fn capture_backtrace(&self) -> Vec<String> {
        let stack = self.call_stack();
        let task = self.current_task_id.get();
        let funcs = self.funcs.borrow();
        // The frames, innermost first: the activations of this task
        // (those the native unwinder also sees are left to it), merged
        // by stack position with the compiled frames it reports.
        let mut entries: Vec<(usize, FuncId, u32)> = stack
            .iter()
            .filter_map(|p| {
                // SAFETY: entries are removed before their activation ends.
                let act = unsafe { &**p };
                (act.task == task && !act.native.get())
                    .then(|| (act.sp.get(), act.fid, act.line.get()))
            })
            .collect();
        if self.native_bt.get() {
            entries.extend(native_frames());
            // Deeper frames have lower addresses; the activation stack
            // keeps its own order where addresses are unknown.
            entries.sort_by_key(|e| std::cmp::Reverse(e.0));
            entries.reverse();
        } else {
            entries.reverse();
        }
        let mut frames = 0;
        let mut bt = Vec::new();
        for (_, fid, line) in entries {
            frames += 1;
            if frames > 32 {
                continue;
            }
            let f = &funcs[fid as usize];
            let mut line = line;
            // Code inlined from another function: its frame, then the
            // caller's at the line of the call.
            while line & INLINE_LINE_FLAG != 0 {
                let Some(o) = f.inlined.get((line & !INLINE_LINE_FLAG) as usize) else {
                    break;
                };
                let callee = &funcs[o.callee as usize];
                bt.push(format!(
                    "{}:{}:in {}",
                    self.file_name(callee.file),
                    o.line,
                    callee.name
                ));
                line = o.call_line;
            }
            bt.push(format!("{}:{}:in {}", self.file_name(f.file), line, f.name));
        }
        if frames > 32 {
            bt.push(format!("... {} more frames", frames - 32));
        }
        bt
    }

    pub fn raise(&self, class: ClassId, message: &str) -> Flow {
        Flow::Raise(self.make_exception(class, message))
    }

    pub fn err_arg(&self, message: &str) -> Flow {
        self.raise(self.program.exc.argument_error, message)
    }

    /// An `Int` result that does not fit in 64 bits.
    pub fn err_overflow(&self) -> Flow {
        self.raise(
            self.program.exc.overflow_error,
            "arithmetic overflow (an Integer holds any size)",
        )
    }

    /// `b` as an `Int`, or `OverflowError`.
    pub fn int_of_big(&self, b: &num_bigint::BigInt) -> EvalResult {
        fit_int(b).ok_or_else(|| self.err_overflow())
    }

    pub fn err_type(&self, message: &str) -> Flow {
        self.raise(self.program.exc.type_error, message)
    }

    pub fn err_runtime(&self, message: &str) -> Flow {
        self.raise(self.program.exc.runtime_error, message)
    }

    /// A compile-time run's refusal (a method with no body yet, a native
    /// acting on the outside world, the time limit): a
    /// `Meta::CompileTimeError`, which no `rescue` short of `rescue
    /// Exception` takes (#959).
    pub fn err_compile_time(&self, message: &str) -> Flow {
        self.raise(self.program.exc.compile_time, message)
    }

    /// A compile-time run past its time limit raises (docs/14 §5).
    #[inline]
    pub fn check_deadline(&self) -> Result<(), Flow> {
        match self.deadline.get() {
            Some(d) if std::time::Instant::now() > d => {
                Err(self.err_compile_time("compile-time evaluation took too long"))
            }
            _ => Ok(()),
        }
    }

    pub fn err_index(&self, message: &str) -> Flow {
        self.raise(self.program.exc.index_error, message)
    }

    pub fn exception_message(&self, exc: &Value) -> String {
        match exc {
            Value::Object(o) => match o.field(0).as_ref().and_then(|v| v.as_str()) {
                Some(s) => s.to_string(),
                None => self.class_name(exc),
            },
            _ => String::new(),
        }
    }

    /// Whether an exception object is an instance of a class.
    pub fn exception_is_a(&self, exc: &Value, class: ClassId) -> bool {
        match exc {
            Value::Object(o) => self.program.world.class_is_a(o.class, class),
            _ => false,
        }
    }

    /// A `SystemExit`'s status.
    pub fn exit_status(&self, e: &Value) -> i32 {
        let Value::Object(o) = e else {
            return 1;
        };
        match self
            .field_index(o.class, "status")
            .map(|i| self.logical_get(o, i))
        {
            Some(Value::Int(s)) => s as i32,
            _ => 0,
        }
    }

    /// `raise` with the usual argument forms.
    pub fn eval_raise(&self, args: ArgVec) -> EvalResult {
        let mut it = args.into_iter();
        let first = it.next().unwrap_or(Value::Nil);
        let exc = match first {
            Value::Class(cid) => {
                let msg = match it.next() {
                    Some(m) => self.to_s(&m)?.to_string(),
                    None => self.program.world.class(cid).name.clone(),
                };
                self.make_exception(cid, &msg)
            }
            Value::Str(s) => self.make_exception(self.program.exc.runtime_error, &s),
            Value::Short(s) => self.make_exception(self.program.exc.runtime_error, s.as_str()),
            // Raised before: its first backtrace stays.
            Value::Object(o) => Value::Object(crate::natives::raised(
                o,
                || self.capture_backtrace(),
                self.rescued(),
            )),
            other => {
                return Err(self.err_type(&format!("cannot raise {}", self.class_name(&other))))
            }
        };
        Err(Flow::Raise(exc))
    }

    // ----- classes ---------------------------------------------------------------------

    pub fn class_of(&self, v: &Value) -> ClassId {
        let b = &self.program.world.builtin;
        match v {
            Value::Nil => b.nil,
            Value::Bool(_) => b.bool_,
            Value::Int(_) => b.int,
            Value::BigInt(_) => b.integer,
            Value::Float(_) => b.float,
            Value::Str(_) | Value::Short(_) => b.string,
            Value::Symbol(_) => b.symbol,
            Value::Array(_) => b.array,
            Value::Hash(_) => b.hash,
            Value::Set(_) => b.set,
            Value::Range(_) => b.range,
            Value::Regexp(_) => b.regexp,
            Value::MatchData(m) if m.data.is_some() => b.bytes_match_data,
            Value::MatchData(_) => b.match_data,
            Value::Object(o) => o.class,
            // A cog's root module is a `Cog` (docs/10 §6).
            Value::Class(c) if self.program.world.class(*c).cog.is_some() => b.cog,
            Value::Class(_) => b.class_,
            Value::Proc(_) => b.proc_,
            Value::ArrayBuilder(_) => b.array_builder,
            Value::HashBuilder(_) => b.hash_builder,
            Value::SetBuilder(_) => b.set_builder,
            Value::StringBuilder(_) => b.string_builder,
            Value::Channel(_) => b.channel,
            Value::Task(_) => b.task,
            Value::Scope(_) => b.scope,
            Value::Atom(_) => b.atom,
            Value::Selector(_) => self.program.rt.selector,
            Value::Duration(_) => b.duration,
            Value::Enumerator(_) => self.program.rt.enumerator,
            // (A socket's class is the library's, `std/socket.qz`, `tls.qz`;
            // a program that did not load it, which a native may still
            // hand a socket, `Signal.reader`'s, sees an `IO`, #1187.)
            Value::Io(io) => {
                let c = match &io.kind {
                    IoKind::Socket(st) => {
                        let s = st.borrow();
                        if s.pipe.is_some() {
                            self.program.rt.io
                        } else if s.unix {
                            self.program.rt.unix_socket
                        } else {
                            self.program.rt.tcp_socket
                        }
                    }
                    IoKind::Listener(st) => {
                        if st.borrow().unix {
                            self.program.rt.unix_server
                        } else {
                            self.program.rt.tcp_server
                        }
                    }
                    IoKind::Udp(_) => self.program.rt.udp_socket,
                    IoKind::Tls(_) => self.program.rt.tls_socket,
                    IoKind::Child(_) => self.program.rt.process_child,
                    _ => self.program.rt.io,
                };
                if c == u32::MAX {
                    self.program.rt.io
                } else {
                    c
                }
            }
            Value::Bytes(_) => b.bytes,
            Value::BytesBuilder(_) => b.bytes_builder,
            Value::Time(_) => b.time,
            Value::Random(_) => self.program.rt.random,
            Value::Secret(s) => match &**s {
                crate::value::SecretVal::Bytes(_) => self.program.rt.secret,
                crate::value::SecretVal::Key(k) => match k.kind() {
                    crate::value::KeyKind::RsaPrivate => self.program.rt.rsa_private_key,
                    crate::value::KeyKind::Aes => self.program.rt.aes_gcm,
                },
            },
            Value::Flow(_) => b.object,
        }
    }

    pub fn class_name(&self, v: &Value) -> String {
        self.program.world.class(self.class_of(v)).name.clone()
    }

    /// The index of declared field `name` of `cid` (see `logical_get`).
    pub fn field_index(&self, cid: ClassId, name: &str) -> Option<usize> {
        self.program.field_indices[cid as usize].get(name).copied()
    }

    /// Declared field `i` of `o`: its physical field, or, for a data
    /// value held in place, that value rebuilt from its physical fields.
    pub fn logical_get(&self, o: &Object, i: usize) -> Value {
        let class = self.program.world.class(o.class);
        let Some(iv) = class.ivars.get(i) else {
            return Value::Nil;
        };
        let slot = iv.slot as usize;
        match iv.flat {
            None => o.field(slot).unwrap_or(Value::Nil),
            Some(d) => {
                let n = self.program.world.class(d).fields.len();
                let vals: Fields = (slot..slot + n)
                    .map(|k| o.field(k).unwrap_or(Value::Nil))
                    .collect();
                Value::Object(Object::new(d, vals))
            }
        }
    }
    /// `with` on data value `o` whose type's body has its own
    /// `initialize` taking the fields (`init`, `RtClass::with_init`): that
    /// `initialize` given the keywords' values, moved, and the receiver's
    /// other fields, in declaration order. No copy of the receiver is made
    /// for it to read them back from (#1024).
    #[inline(never)]
    fn data_with_init(
        &self,
        m: &RtMethod,
        o: &Rc<Object>,
        init: MethodId,
        kw: Vec<(Symbol, Value)>,
    ) -> EvalResult {
        let n = self.program.world.class(o.class).ivars.len();
        let mut args: ArgVec = smallvec![Value::Nil; n];
        // (The fields given, a bit each for the first 64, the rest
        // listed: a keyword naming none is ignored, as the copy's
        // `logical_set` ignores it; the checker refuses one given twice.)
        let mut given: u64 = 0;
        let mut far: SmallVec<[usize; 2]> = SmallVec::new();
        for (sym, v) in kw {
            let name = self.symbol_name(sym);
            if let Some(i) = m.params.iter().position(|p| *p.name == *name) {
                if let Some(a) = args.get_mut(i) {
                    *a = v;
                    if i < 64 {
                        given |= 1 << i;
                    } else {
                        far.push(i);
                    }
                }
            }
        }
        for (i, a) in args.iter_mut().enumerate() {
            let is_given = if i < 64 {
                given & (1 << i) != 0
            } else {
                far.contains(&i)
            };
            if !is_given {
                *a = self.logical_get(o, i);
            }
        }
        self.construct(o.class, Some(init), args, Vec::new(), None)
    }

    /// Store `v` into declared field `i` of `o` (a data value held in
    /// place is copied field by field).
    pub fn logical_set(&self, o: &Object, i: usize, v: Value) {
        let class = self.program.world.class(o.class);
        let Some(iv) = class.ivars.get(i) else {
            return;
        };
        let slot = iv.slot as usize;
        match iv.flat {
            None => o.set_field(slot, v),
            Some(d) => {
                let n = self.program.world.class(d).fields.len();
                let Value::Object(src) = &v else {
                    return;
                };
                for k in 0..n {
                    if let Some(x) = src.field(k) {
                        if slot + k < o.field_count() {
                            o.set_field(slot + k, x);
                        }
                    }
                }
            }
        }
    }

    /// The values of all declared fields of `o`.
    pub fn logical_values(&self, o: &Object) -> Vec<Value> {
        let n = self.program.world.class(o.class).ivars.len();
        (0..n).map(|i| self.logical_get(o, i)).collect()
    }

    /// The physical fields of a `class` object from its declared
    /// fields' values.
    pub fn flatten_values(&self, class: ClassId, values: Vec<Value>) -> Fields {
        let info = self.program.world.class(class);
        let mut out: Fields = smallvec![Value::Nil; info.fields.len()];
        for (iv, v) in info.ivars.iter().zip(values) {
            let slot = iv.slot as usize;
            match iv.flat {
                None => {
                    if slot < out.len() {
                        out[slot] = v;
                    }
                }
                Some(d) => {
                    let n = self.program.world.class(d).fields.len();
                    if let Value::Object(src) = &v {
                        for k in 0..n.min(src.field_count()) {
                            if slot + k < out.len() {
                                out[slot + k] = src.field(k).unwrap_or(Value::Nil);
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// `value.is_a?(type)`: type arguments only for the elements of
    /// built-in collections and tuples (`RtType::Elems`).
    pub fn is_a(&self, v: &Value, ty: &RtType) -> bool {
        match ty {
            RtType::Nothing => false,
            RtType::Class(cid) => self.program.world.class_is_a(self.class_of(v), *cid),
            RtType::Elems(cid, args) => {
                let any = RtType::Any;
                let arg = |i: usize| args.get(i).unwrap_or(&any);
                self.program.world.class_is_a(self.class_of(v), *cid)
                    && match v {
                        Value::Array(a) => a.iter().all(|x| self.is_a(&x, arg(0))),
                        Value::Set(s) => s.iter().all(|x| self.is_a(x, arg(0))),
                        Value::Hash(h) => h
                            .as_map()
                            .iter()
                            .all(|(k, x)| self.is_a(k, arg(0)) && self.is_a(x, arg(1))),
                        // An endless end is nil.
                        Value::Range(r) => [&r.lo, &r.hi]
                            .iter()
                            .all(|x| x.is_nil() || self.is_a(x, arg(0))),
                        _ => true,
                    }
            }
            RtType::ClassObject => matches!(v, Value::Class(_)),
            RtType::ClassOf(cid) => {
                matches!(v, Value::Class(c) if self.program.world.class_is_a(*c, *cid))
            }
            RtType::Union(ms) => ms.iter().any(|m| self.is_a(v, m)),
            RtType::Tuple(ts) => matches!(v, Value::Array(a)
                if a.len() == ts.len()
                    && (ts.iter().all(|t| *t == RtType::Any)
                        || a.iter().zip(ts).all(|(x, t)| self.is_a(&x, t)))),
            RtType::Proc => matches!(v, Value::Proc(_)),
            RtType::Any => true,
        }
    }

    pub fn variant_singleton(&self, cid: ClassId) -> Value {
        if let Some(Some(v)) = self.program.singletons.get(cid as usize) {
            return v.get().clone();
        }
        lock(&self.global.variant_singletons)
            .entry(cid)
            .or_insert_with(|| {
                SharedValue::immortal(Value::Object(Object::new(cid, Fields::new())))
            })
            .get()
            .clone()
    }

    /// Register an `at_exit` block (any task may; they run at the end).
    pub fn add_at_exit(&self, block: Value) {
        lock(&self.global.at_exit).push(SharedValue::new(block));
    }

    /// The value of a constant, evaluating its initializer on first use.
    pub fn const_value(&self, cid: u32) -> EvalResult {
        let cell = &self.program.consts[cid as usize];
        if let Some(v) = cell.value.get() {
            return Ok(v.get().clone());
        }
        let info = &self.program.world.consts[cid as usize];
        let Some(init) = info.init else {
            return Ok(Value::Nil);
        };
        // Run the initializer once: a task that finds another one
        // running it waits (it may suspend: IO, `sleep`).
        loop {
            let me = self.sched.borrow().current_ref();
            let mut state = lock(&cell.init);
            if let Some(v) = cell.value.get() {
                return Ok(v.get().clone());
            }
            match &mut *state {
                ConstInit::Running { task, .. } if *task == me => {
                    drop(state);
                    return Err(self.raise(
                        self.program.exc.runtime_error,
                        &format!("constant `{}` is used by its own initializer", info.name),
                    ));
                }
                ConstInit::Running { waiters, .. } => {
                    if !waiters.contains(&me) {
                        waiters.push(me);
                    }
                    drop(state);
                    if let Err(e) = self.park() {
                        if let ConstInit::Running { waiters, .. } = &mut *lock(&cell.init) {
                            waiters.retain(|t| *t != me);
                        }
                        return Err(e);
                    }
                }
                ConstInit::Idle => {
                    *state = ConstInit::Running {
                        task: me,
                        waiters: Vec::new(),
                    };
                    break;
                }
            }
        }
        let self_val = match info.owner {
            Some(o) => Value::Class(o),
            None => self.unit_self(info.file),
        };
        let r = self.run_init(init, self_val, info.file);
        // A constant is visible from every task. One whose initializer
        // failed is evaluated again at its next use.
        if let Ok(v) = &r {
            let _ = cell.value.set(SharedValue::immortal(v.clone()));
        }
        let running = std::mem::take(&mut *lock(&cell.init));
        if let ConstInit::Running { waiters, .. } = running {
            for w in waiters {
                self.wake_ref(w);
            }
        }
        r
    }

    // ----- dispatch --------------------------------------------------------------------

    /// Find the implementation of a statically resolved method for the
    /// receiver's run-time class (subclass overrides). A class method
    /// called on a class object not below its owner (one no check saw,
    /// docs/05 §3) is a TypeError.
    pub fn resolve_dynamic(&self, recv: &Value, mid: MethodId) -> Result<MethodId, Flow> {
        let found = self.resolve_dynamic_here(recv, mid)?;
        if self.generated_any.get() {
            self.refuse_generated_over(recv, found)?;
        }
        Ok(found)
    }

    /// In a compile-time run that has generated methods: a call that
    /// found `found` for `recv` where a method this statement generated
    /// would have answered it, had the class's statements run, is
    /// refused as a call by name to a class whose statements have not all
    /// run is (#967, docs/14 §7): the generated method has no body until
    /// then. It would have answered when it is of `found`'s name and side,
    /// of a class `recv` is, below `found`'s owner (or, a class method on
    /// a class object, standing in for a method of `Type`), and may take
    /// `found`'s calls: as many positional parameters as `found` takes
    /// (none optional), or, a keyword-form method, when `found` may be
    /// called with no positional argument. Neither the parameters' types
    /// nor the keywords' names are compared: an approximation that may
    /// refuse a generated overload, never accept a call a generated method
    /// would have answered (a generated method has no defaults: one that
    /// takes `found`'s calls has exactly its positional count, or is of the
    /// keyword form when `found` takes none).
    pub fn refuse_generated_over(&self, recv: &Value, found: MethodId) -> Result<(), Flow> {
        let Some(reflect) = self.reflect.borrow().clone() else {
            return Ok(());
        };
        let m = self.program.method(found);
        let world = &self.program.world;
        let (min, max) = m.positional_arity();
        // (A class object takes class methods in place of `Type`'s.)
        let (class, singleton, type_method) = match recv {
            Value::Class(c) => (*c, true, !m.singleton),
            _ => (self.class_of(recv), false, false),
        };
        for (a, a_singleton, params) in reflect.generated_named(&m.name) {
            // (The keyword form takes keywords only: any call that passes
            // no positional argument, refused whatever the keywords.)
            let takes = match params {
                Some(n) => min == n && max == n,
                None => min == 0,
            };
            if a_singleton == singleton
                && takes
                && world.class_is_a(class, a)
                && (type_method || (a != m.owner && world.class_is_a(a, m.owner)))
            {
                return Err(self.err_compile_time(&format!(
                    "`{}` of `{}` has no body at compile time: a method the runtime calls by name is lowered once the class's `static` statements ran, or when a call resolves to it (docs/14)",
                    m.name,
                    world.class(a).name
                )));
            }
        }
        Ok(())
    }

    /// A compile-time run generated instance method `name` into `class`:
    /// when it is `==` (or `hash`), the instances of `class` and of the
    /// classes below it that compare (hash) in Rust, by identity (no such
    /// method of their own in `RtClass::key_methods`), are compared
    /// (hashed) by calling `Object#==` (`Object#hash`) from then on
    /// (`crate::keys`), so that a table holding one asks
    /// `refuse_generated_over` as any other dispatch does (#967). A class
    /// with its own keeps it. Nothing is looked up: the rows stay the
    /// lowering's, and identity is what `Object`'s methods are.
    pub fn generated_key_method(&self, class: ClassId, singleton: bool, name: &str) {
        if singleton || !matches!(name, "==" | "hash") {
            return;
        }
        let world = &self.program.world;
        let object = world.class(world.builtin.object);
        let own = |n: &str| {
            object.methods.get(n).and_then(|ids| {
                ids.iter()
                    .copied()
                    .find(|&m| self.program.method(m).owner == world.builtin.object)
            })
        };
        // (Only the generated one: the other keeps hashing or comparing
        // as before, in Rust, so that a table built before agrees.)
        let by = own(name);
        for c in 0..world.classes.len() as ClassId {
            if !world.class_is_a(c, class) {
                continue;
            }
            let mut methods = crate::keys::of(c).unwrap_or_default();
            if name == "==" {
                methods.eq = methods.eq.or(by);
            } else {
                methods.hash = methods.hash.or(by);
            }
            crate::keys::add(c, methods);
        }
    }

    fn resolve_dynamic_here(&self, recv: &Value, mid: MethodId) -> Result<MethodId, Flow> {
        let m = self.program.method(mid);
        if m.singleton {
            let class_side = m.dispatch() == quarz_ir::Dispatch::ClassSide;
            // A class method some subclass overrides: the class it is
            // called on decides.
            return match recv {
                Value::Class(cid) if class_side && *cid != m.owner => {
                    // (The cache holds keys only: a hit needs no check.)
                    if let Some(found) = self.class_method_cache.borrow().get(&(*cid, mid)) {
                        return Ok(found.unwrap_or(mid));
                    }
                    // (A key of `RtWorld::class_override_rows`: `cid` has
                    // the owner among its ancestors, every conformance, an
                    // extension's too, #504.)
                    let method = |id: MethodId| self.program.method(id);
                    if !self
                        .program
                        .world
                        .in_class_override_rows(&method, *cid, mid)
                    {
                        let what = format!(
                            "{} given to a call of `{}.{}`, a class no check saw",
                            self.program.world.class(*cid).name,
                            self.program.world.class(m.owner).name,
                            m.name
                        );
                        if crate::verify::enabled() {
                            self.violated(what);
                            unreachable!()
                        }
                        return Err(self.err_type(&format!(
                            "cannot cast {} to a receiver `{}` was checked for",
                            self.program.world.class(*cid).name,
                            m.name
                        )));
                    }
                    Ok(self.class_method_override(*cid, mid).unwrap_or(mid))
                }
                _ => Ok(mid),
            };
        }
        if m.is_extension {
            return Ok(mid);
        }
        // Nothing overrides it, and the receiver is not a class object
        // (whose own class methods may stand in for a module's): the
        // method is the one.
        if self.program.vslots[mid as usize] == u32::MAX && !matches!(recv, Value::Class(_)) {
            return Ok(mid);
        }
        if let Value::Class(cid) = recv {
            // A method of `Type` running on a class object: a class method
            // of its signature (the class's, a superclass's or an included
            // module's) overrides it.
            if let Some(found) = self.class_side_override(*cid, mid) {
                return Ok(found);
            }
        }
        let cid = self.class_of(recv);
        let slot = self.program.vslots[mid as usize];
        if slot == u32::MAX {
            // Nothing overrides it: the method is the one.
            return Ok(mid);
        }
        let at = cid as usize * self.program.nvslots + slot as usize;
        if let Some(&hit) = self.vtable.borrow().get(at) {
            if hit != 0 {
                return Ok(hit - 1);
            }
        }
        let method = |id: MethodId| self.program.method(id);
        let found = self.program.world.dispatch_target(&method, cid, mid);
        if let Some(cell) = self.vtable.borrow_mut().get_mut(at) {
            *cell = found + 1;
        }
        Ok(found)
    }

    /// The implementation of `Type`'s method `mid` for the class object
    /// `cid`: a class method of the class (or a superclass) of its
    /// signature, or of a module it includes (docs/01 §6), as the row of
    /// `RtWorld::class_override_rows` gives it (`World::class_method_target`);
    /// `None` for `mid` itself.
    fn class_side_override(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        if let Some(found) = self.class_dispatch_cache.borrow().get(&(cid, mid)) {
            return *found;
        }
        // (The row for a key, `RtWorld::in_class_override_rows`: a method
        // outside the set has nothing on the class object to take its
        // place, #681's option (a).)
        let world = &self.program.world;
        let method = |id: MethodId| self.program.method(id);
        let found = if world.in_class_override_rows(&method, cid, mid) {
            let by = world.class_override_row(cid, mid).unwrap_or_else(|| {
                panic!(
                    "internal error: no class override row for `{}` on `{}`",
                    self.program.method(mid).name,
                    world.class(cid).name
                )
            });
            (by != mid).then_some(by)
        } else {
            None
        };
        self.class_dispatch_cache
            .borrow_mut()
            .insert((cid, mid), found);
        found
    }

    /// The class method of `cid` (or of a superclass below the owner of
    /// `mid`) that overrides the class method `mid`: the row of
    /// `RtWorld::class_override_rows` (`World::class_method_target`, #681's
    /// option (a)). The call is a key (`resolve_dynamic` checks it): no row
    /// is an internal error. Cached per class.
    fn class_method_override(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        if let Some(found) = self.class_method_cache.borrow().get(&(cid, mid)) {
            return *found;
        }
        let world = &self.program.world;
        let by = world.class_override_row(cid, mid).unwrap_or_else(|| {
            panic!(
                "internal error: no class override row for `{}` on `{}`",
                self.program.method(mid).name,
                world.class(cid).name
            )
        });
        let found = (by != mid).then_some(by);
        self.class_method_cache
            .borrow_mut()
            .insert((cid, mid), found);
        found
    }

    /// The witness of abstract method `abs` for class `cid` that a call by
    /// name reaches (`find_method`): the row of `RtWorld::witness_rows`.
    /// Every key `find_method` passes is one `RtWorld::in_witness_rows`
    /// admits (a module's requirement on a class whose values exist): an
    /// abstract class's requirement is implemented before it in the lookup
    /// (#687's option 1), so a call by name never stops at one; a key
    /// outside the rows, or one with no row, is an internal error.
    fn witness_for(&self, cid: ClassId, abs: MethodId) -> Option<MethodId> {
        let world = &self.program.world;
        let method = |id: MethodId| self.program.method(id);
        if !world.in_witness_rows(&method, cid, abs) {
            panic!(
                "internal error: `{}` on `{}` reached an abstract class's requirement by name (#687: implemented before it in the lookup)",
                self.program.method(abs).name,
                world.class(cid).name
            )
        }
        world.witness_row(cid, abs).unwrap_or_else(|| {
            panic!(
                "internal error: no witness row for `{}` on `{}`",
                self.program.method(abs).name,
                world.class(cid).name
            )
        })
    }

    /// Find a method by name on a class (first match in resolution order
    /// that accepts `argc` positional arguments), in `RtClass::lookup`: the
    /// modules of scoped and conditional extensions are not searched, so
    /// none of their methods is found by name (docs/01 §7) — except an
    /// abstract method of such a module, which resolves through the
    /// witness its conformance recorded (the witness rows), conformance holding
    /// wherever the value goes (natives calling `each` or `<=>` by name on
    /// a class conforming to `Enumerable` or `Comparable` through a scoped
    /// extension).
    ///
    /// `witness`: whether that fallback to a witness applies: only where
    /// the call is gated by the receiver's conformance (a bound, or a call
    /// the checker typed on that receiver), since a scoped or conditional
    /// extension's witness must not run outside it. Every caller, with its
    /// gate (keep this list complete when adding one):
    ///
    /// `true`, through `send`/`send_kw` (`send_with(.., true)`):
    /// - `ops.rs` `CallOp::Send` and compound-assignment operators: a call
    ///   the checker typed on the receiver (and the lowering's own by-name
    ///   calls: `__snapshot`/`__copy_captures`, attribute writers in a
    ///   multiple assignment, found by name on the receiver's own class);
    /// - `vm.rs` `BoundMethod` (`.:name`, the checker's method reference),
    ///   the block fast path's fallback (`&:name`, typed for the block's
    ///   parameter), interpolation's `<<` on a non-builder (typed);
    /// - `Enumerator#each` (`enumerator_each`): the source method of an
    ///   enumerator, a built-in's or an `Enumerable` native's (`times`,
    ///   `Range#each`, `Array#each`, `map`, `each_slice`, `to_enum`, ...);
    /// - `steps.rs` `next`: on an `Enumerator` subclass (typed);
    ///   `rewind`: only after `has_user_method` (`false`) found it;
    /// - `Process::Output#success?`: `status` of a `Process::Output`.
    ///
    /// Not here: the sends of a module's requirement, which dispatch it
    /// as a typed call does (`send_requirement`, #599): `each` on an
    /// `Enumerable` (`natives::collect`, `Enumerable#each_with_index_pairs`)
    /// and `<=>` through `compare` (`compare_with(.., true)`), the element
    /// type bounded by `Comparable`: `Enumerable#sort`/`min`/`max`/`minmax`
    /// (`extension Enumerable[T <: Comparable[T]]`), `Array#<=>`
    /// (`extension Array[T <: Comparable[T]]`), `Array::Builder#sort!`
    /// without a block (`extension Array::Builder[T <: Comparable[T]]`,
    /// #560), `Array::Builder#sort_by!`
    /// (`U <: Comparable[U]`), `Enumerable#sort_pairs` (`K <: Comparable[K]`,
    /// for `sort_by`'s keys, #579), `Comparable#clamp` (`self` conforms);
    /// `Symbol#<=>` and numbers' `<=>` reach only symbols and numbers.
    ///
    /// `false`: `has_user_method`, natives' optional hooks on any value
    /// (`to_s`, `inspect`, `==` in `values_equal`, `JSON.generate`'s
    /// `to_json`, `Enumerator#rewind`'s `rewind`); `range_covers`
    /// (`Range[T]` takes any `T`, #559); the hash-key probe of
    /// `==`/`hash`; the block fast path's first lookup.
    pub fn find_method(
        &self,
        cid: ClassId,
        name: &str,
        argc: usize,
        with_block: bool,
        witness: bool,
    ) -> Option<MethodId> {
        let key = (cid, argc, with_block, witness);
        if let Some(found) = self.name_cache.borrow().get(&key).and_then(|m| m.get(name)) {
            return *found;
        }
        let mut found = None;
        let mut fallback = None;
        // (By name: `lookup`, which leaves out the modules of scoped and
        // conditional extensions; `ancestors` is membership, docs/01 §7.)
        'outer: for anc in &self.program.world.class(cid).lookup {
            let anc = *anc;
            // A file's top-level `def`s are functions, which nothing finds
            // by name on its top-level object (docs/01 §1).
            if self.program.world.class(anc).kind == quarz_ir::RtClassKind::Main {
                continue;
            }
            let mut ext_lists: Vec<Vec<MethodId>> = Vec::new();
            let mut lists: Vec<&Vec<MethodId>> = Vec::new();
            // Always-active extensions on this ancestor come first (a
            // module's extension applies only where `using` makes it
            // visible, which is resolved statically).
            for ext in &self.program.world.extensions {
                if ext.always_active && ext.target == anc {
                    if let Some(ids) = ext.methods.get(name) {
                        // (A send by name on a value: the instance side; an
                        // extension keeps both sides in one table, #590.)
                        ext_lists.push(
                            ids.iter()
                                .copied()
                                .filter(|i| !self.program.method(*i).singleton)
                                .collect(),
                        );
                    }
                }
            }
            lists.extend(ext_lists.iter());
            if let Some(ids) = self.program.world.class(anc).methods.get(name) {
                lists.push(ids);
            }
            for ids in lists {
                for id in ids {
                    let m = self.program.method(*id);
                    let (min, max) = m.positional_arity();
                    if min <= argc && argc <= max && (m.has_block == with_block) {
                        found = Some(*id);
                        break 'outer;
                    }
                    fallback.get_or_insert(*id);
                }
            }
        }
        // Not found by name: an abstract method of a module only an
        // extension's include brings (in `ancestors`, not in `lookup`),
        // when a witness implements it for the class; nothing else.
        if found.is_none() && witness {
            let rc = self.program.world.class(cid);
            'mods: for anc in &rc.ancestors {
                if rc.lookup.contains(anc) {
                    continue;
                }
                let Some(ids) = self.program.world.class(*anc).methods.get(name) else {
                    continue;
                };
                for id in ids {
                    let m = self.program.method(*id);
                    let (min, max) = m.positional_arity();
                    if m.is_abstract
                        && min <= argc
                        && argc <= max
                        && m.has_block == with_block
                        && self.witness_for(cid, *id).is_some()
                    {
                        found = Some(*id);
                        break 'mods;
                    }
                }
            }
        }
        // An abstract method (a module's) that an extension implements for
        // the class: conformance holds wherever the value goes.
        if let Some(abs) = found.filter(|m| self.program.method(*m).is_abstract) {
            if let Some(i) = self.witness_for(cid, abs) {
                found = Some(i);
            }
        }
        let result = found.or(fallback);
        self.name_cache
            .borrow_mut()
            .entry(key)
            .or_default()
            .insert(name.to_string(), result);
        result
    }

    /// `Enumerable#each`, the requirement `natives::collect` dispatches.
    pub(crate) fn req_each(&self) -> Option<MethodId> {
        self.req_each
    }

    /// A conformance-gated send of a module's requirement (#599): `<=>`
    /// on an element bounded by `Comparable` (`compare`), `each` on an
    /// `Enumerable` (`natives::collect`, `each_with_index_pairs`). It
    /// dispatches the requirement `req` as a call typed through the module
    /// does (`resolve_dynamic`, the row of `RtWorld::override_rows`), not
    /// the first method of the name in `RtClass::lookup`. A receiver whose
    /// class is not a key of the rows for `req` is an internal error
    /// (`check_gated_key`, on the first dispatch for the class, before the
    /// vtable cell is filled): the gate (a bound on `Comparable`, an
    /// `Enumerable` receiver) admits none.
    /// So is a missing requirement (`req` is `None`): `shake` drops it only
    /// when no class with values includes the module, and a gated send is
    /// then never reached with an object (built-in values compare inline).
    pub(crate) fn send_requirement(
        &self,
        recv: &Value,
        req: Option<MethodId>,
        name: &str,
        args: ArgVec,
        block: Option<Value>,
    ) -> EvalResult {
        let cid = self.class_of(recv);
        let Some(req) = req else {
            panic!(
                "internal error: a gated `{name}` on `{}` with no requirement shipped",
                self.program.world.class(cid).name
            );
        };
        // (A filled dispatch cell for the class: what a typed call reads,
        // and nothing more. The key-set test runs once, when the cell is
        // first filled for the class.)
        let slot = self.program.vslots[req as usize];
        if slot != u32::MAX {
            let at = cid as usize * self.program.nvslots + slot as usize;
            // (The cell copied out, so that the borrow ends before the
            // call: a dispatch inside the method may fill another cell,
            // #790.)
            let hit = self.vtable.borrow().get(at).copied().unwrap_or(0);
            if hit != 0 {
                return self.invoke(hit - 1, recv.clone(), args, Vec::new(), block);
            }
        }
        let method = |id: MethodId| self.program.method(id);
        check_gated_key(&self.program.world, &method, cid, req, name);
        let mid = self.resolve_dynamic(recv, req)?;
        self.invoke(mid, recv.clone(), args, Vec::new(), block)
    }

    /// Call a method by name with dynamic lookup (used by `&:sym`,
    /// enumerators, `to_s`, operators in compound assignment).
    pub fn send(&self, recv: &Value, name: &str, args: ArgVec, block: Option<Value>) -> EvalResult {
        self.send_kw(recv, name, args, Vec::new(), block)
    }

    /// `send` with keyword arguments.
    pub fn send_kw(
        &self,
        recv: &Value,
        name: &str,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
    ) -> EvalResult {
        self.send_with(recv, name, args, kw, block, true)
    }

    /// `send_kw`, saying whether the witness fallback applies
    /// (`find_method`).
    fn send_with(
        &self,
        recv: &Value,
        name: &str,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
        witness: bool,
    ) -> EvalResult {
        let cid = self.class_of(recv);
        let Some(mid) = self.find_method(cid, name, args.len(), block.is_some(), witness) else {
            return Err(self.raise(
                self.program.exc.runtime_error,
                &format!(
                    "undefined method `{name}` for {}",
                    self.program.world.class(cid).name
                ),
            ));
        };
        if self.generated_any.get() {
            self.refuse_generated_over(recv, mid)?;
        }
        self.invoke(mid, recv.clone(), args, kw, block)
    }

    /// Whether the receiver's class defines `name` itself (not via Object's
    /// native default).
    /// (In a compile-time run, a method this statement generated that
    /// would answer is refused: `refuse_generated_over`.)
    pub fn has_user_method(
        &self,
        recv: &Value,
        name: &str,
        argc: usize,
    ) -> Result<Option<MethodId>, Flow> {
        let cid = self.class_of(recv);
        let Some(mid) = self.find_method(cid, name, argc, false, false) else {
            return Ok(None);
        };
        if self.generated_any.get() {
            self.refuse_generated_over(recv, mid)?;
        }
        let m = self.program.method(mid);
        if m.owner == self.program.world.builtin.object && m.native_key.is_some() {
            return Ok(None);
        }
        Ok(Some(mid))
    }

    // ----- invocation --------------------------------------------------------------------

    /// Under `QUARZ_VERIFY` (the facts check, `verify::enabled`): what
    /// native `mid` returned is of its declared result
    /// (`RtMethod::result_test`, #1187), else a violation naming the
    /// native, the declared type and the value's class. A native serving
    /// several overloads of its name finds the one it serves from its
    /// arguments, which no entry knows: it is checked against the union
    /// of their results (`RtMethod::result_union`), which accepts more.
    #[inline(always)]
    pub(crate) fn check_native_result(&self, mid: MethodId, v: &Value) {
        // (`verify` is `verify::enabled()`, read once: a field load in a
        // release build, where the check is off.)
        if self.verify && self.program.world.native_results {
            self.check_native_result_now(mid, v);
        }
    }

    #[cold]
    #[inline(never)]
    fn check_native_result_now(&self, mid: MethodId, v: &Value) {
        let m = self.program.method(mid);
        let Some(key) = m.native_key.as_deref() else {
            return;
        };
        let test = m.result_union.as_ref().or(m.result_test.as_ref());
        let Some(test) = test else {
            self.violated(format!("native `{key}` has no test of its declared result"));
            return;
        };
        if !self.is_a(v, test) {
            self.violated(format!(
                "native `{key}` returned a value of class {}, but its declared result is {}",
                self.class_name(v),
                m.ret.as_deref().unwrap_or("its declared type")
            ));
        }
    }

    /// A native `mid` called with its receiver and positional arguments
    /// borrowed (`ArgList::Borrowed`, #988): what `invoke` does for a
    /// native, without an argument list. The caller keeps the values for
    /// the call (a view of its registers).
    #[inline]
    pub fn invoke_native_borrowed(
        &self,
        mid: MethodId,
        native: NativeFn,
        recv: &Value,
        args: &[Value],
    ) -> EvalResult {
        crate::keys::check()?;
        if self.deadline.get().is_some() {
            self.check_deadline()?;
            if let Some(key) = self.program.method(mid).native_key.as_deref() {
                if !crate::natives::compile_time_allowed(key) {
                    return Err(
                        self.err_compile_time(&format!("`{key}` cannot run at compile time"))
                    );
                }
            }
        }
        let r = native(
            self,
            recv,
            Args {
                pos: ArgList::Borrowed(args),
                kw: Vec::new(),
                block: None,
            },
        );
        if let Ok(v) = &r {
            self.check_native_result(mid, v);
        }
        r
    }

    pub fn invoke(
        &self,
        mid: MethodId,
        recv: Value,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
    ) -> EvalResult {
        // What a key's own `==` or `hash` raised is raised before any more
        // Quarz code runs (`crate::keys`; their own calls check first).
        crate::keys::check()?;
        if self.deadline.get().is_some() {
            self.check_deadline()?;
        }
        let m = self.program.method(mid);
        if let Some(native) = self.program.natives[mid as usize] {
            // A compile-time run refuses the natives that act on the
            // outside world, whatever the analysis before it missed.
            if self.deadline.get().is_some() {
                if let Some(key) = m.native_key.as_deref() {
                    if !crate::natives::compile_time_allowed(key) {
                        return Err(
                            self.err_compile_time(&format!("`{key}` cannot run at compile time"))
                        );
                    }
                }
            }
            // A native reads its arguments by position: those passed by
            // keyword take their places (docs/01 §9).
            let (args, kw) = if kw.is_empty() {
                (args, kw)
            } else {
                self.native_positions(m, args, kw)?
            };
            let r = native(
                self,
                &recv,
                Args {
                    pos: args.into(),
                    kw,
                    block,
                },
            );
            if let Ok(v) = &r {
                self.check_native_result(mid, v);
            }
            return r;
        }
        match &m.synth {
            RtSynth::FieldGet(idx) => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("field access on a non-object"));
                };
                return Ok(self.logical_get(o, *idx as usize));
            }
            RtSynth::FieldSet(idx) => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("field access on a non-object"));
                };
                let v = args.into_iter().next().unwrap_or(Value::Nil);
                self.logical_set(o, *idx as usize, v.clone());
                return Ok(v);
            }
            RtSynth::DataInit => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("data initialization on a non-object"));
                };
                let values = self.bind_data_args(mid, &recv, args, kw)?;
                o.set_fields(self.flatten_values(o.class, values));
                return Ok(Value::Nil);
            }
            RtSynth::DataWith => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("`with` on a non-object"));
                };
                // The body's `initialize` taking the fields builds the
                // value, as `new` would (docs/01 §4): the one the checker
                // found (`RtClass::with_init`, #536 step 6).
                if let Some(init) = self.program.world.class(o.class).with_init {
                    return self.data_with_init(m, o, init, kw);
                }
                let copy = Object::new(o.class, o.fields());
                for (sym, v) in kw {
                    let name = self.symbol_name(sym);
                    if let Some(i) = m.params.iter().position(|p| *p.name == *name) {
                        self.logical_set(&copy, i, v);
                    }
                }
                return Ok(Value::Object(copy));
            }
            RtSynth::DataToH => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("`to_h` on a non-object"));
                };
                let mut map = ValueMap::default();
                let class = self.program.world.class(o.class);
                for (i, f) in class.ivars.iter().enumerate() {
                    map.insert(Value::Symbol(self.intern(&f.name)), self.logical_get(o, i));
                }
                return Ok(Value::Hash(Rc::new(crate::value::HashData::from(map))));
            }
            RtSynth::None => {}
        }
        if m.native_key.is_some() {
            return Err(self.raise(
                self.program.exc.not_implemented,
                &format!(
                    "native method `{}` is not implemented",
                    m.native_key.as_deref().unwrap_or("")
                ),
            ));
        }
        // An abstract method reached at run time: nothing implements it for
        // the receiver's class, which the checker refuses, so a check missed
        // it (#630; #555, #600). A violation under `QUARZ_VERIFY`, else a
        // `TypeError` that says so, as for a class no check saw
        // (`resolve_dynamic`); not `NotImplementedError`, which is for what
        // this platform does not implement.
        if m.is_abstract {
            // (The documented exception, #509: a `Type[M]` value holding the
            // module or the abstract class itself, whose abstract class
            // method nothing implements; a catchable `TypeError` that says
            // so, until #510 makes such a value impossible.)
            if let Value::Class(cid) = &recv {
                let c = self.program.world.class(*cid);
                if m.singleton && (c.kind == quarz_ir::RtClassKind::Module || c.is_abstract) {
                    let what = if c.kind == quarz_ir::RtClassKind::Module {
                        "the module"
                    } else {
                        "the abstract class"
                    };
                    return Err(self.err_type(&format!(
                        "abstract class method `{}` called on {what} `{}` itself: a `Type` value holding it has no implementation (#510)",
                        m.name, c.name
                    )));
                }
            }
            // (A compile-time run on a class whose conformance waits for
            // its statements, docs/14 §5: the implementation may be one a
            // statement still to run generates, #801. An error at the
            // statement, whatever `QUARZ_VERIFY` says.)
            let cid = match &recv {
                Value::Class(c) => *c,
                other => self.class_of(other),
            };
            if self.program.world.deferred_conformance.contains(&cid) {
                let world = &self.program.world;
                return Err(self.err_runtime(&format!(
                    "`{}` of `{}` is not implemented yet: `{}`'s conformance to `{}` waits for its class's `static` statements, and none has generated `{}` so far (docs/14 §5)",
                    m.name,
                    world.class(cid).name,
                    world.class(cid).name,
                    world.class(m.owner).name,
                    m.name
                )));
            }
            let what = format!(
                "abstract method `{}` called on {}, which no check saw implemented",
                m.name,
                self.class_name(&recv)
            );
            if crate::verify::enabled() {
                self.violated(what);
                unreachable!()
            }
            return Err(self.err_type(&what));
        }
        let Some(fid) = m.func else {
            if self.deadline.get().is_some() {
                // A compile-time run: a body not lowered is a bug of the
                // compiler, not a nil (docs/14).
                return Err(self.err_compile_time(&format!(
                    "`{}` of `{}` has no body at compile time: a method the runtime calls by name is lowered once the class's `static` statements ran, or when a call resolves to it (docs/14)",
                    m.name,
                    self.program.world.class(m.owner).name
                )));
            }
            return Ok(Value::Nil);
        };
        // Positional parameters only: the arguments are bound as they
        // are (the checker has matched their number; extra ones are
        // dropped, as `bind_params` does).
        let (bound, provided) = if kw.is_empty() && self.program.positional_only[mid as usize] {
            let mut args = args;
            args.truncate(m.params.len());
            let n = args.len();
            let provided = if n >= 64 { u64::MAX } else { (1u64 << n) - 1 };
            (args, provided)
        } else {
            self.bind_params(mid, &recv, args, kw, block.clone())?
        };
        self.run_method(mid, fid, recv, bound, provided, block)
    }

    /// Invoke with an owned receiver (`x = x.push(v)`): natives that update
    /// in place get the sole reference. On error the receiver is returned.
    /// `x = x.meth(args)` for the common collection updates: apply the
    /// update to the value in `slot` (in place when it is unshared)
    /// without the generic owned-call machinery. Returns whether it
    /// applied; when it did not, nothing was changed.
    #[inline]
    pub fn owned_fast(&self, mid: MethodId, slot: &mut Value, args: &[&Value]) -> bool {
        let o = &self.program.owned;
        let m = Some(mid);
        match (slot, args) {
            (Value::Array(a), [v]) if m == o.array_push => {
                crate::value::unique_mut(a).push((*v).clone());
                true
            }
            (Value::Array(a), [Value::Int(i), v]) if m == o.array_set => {
                let n = a.len() as i64;
                let i = if *i < 0 { n + *i } else { *i };
                if i < 0 || i >= n {
                    return false;
                }
                crate::value::unique_mut(a).set(i as usize, (*v).clone());
                true
            }
            // A key with its own `==` or `hash` goes to the native, which
            // looks it up before changing anything (`crate::keys`).
            (Value::Hash(_), [k, ..]) | (Value::Set(_), [k])
                if crate::keys::is_custom(k)
                    && (m == o.hash_put
                        || m == o.hash_delete
                        || m == o.set_add
                        || m == o.set_delete) =>
            {
                false
            }
            (Value::Hash(h), [k, v]) if m == o.hash_put => {
                crate::value::unique_mut(h).insert((*k).clone(), (*v).clone());
                true
            }
            (Value::Hash(h), [k]) if m == o.hash_delete => {
                crate::value::unique_mut(h).shift_remove(k);
                true
            }
            (Value::Set(s), [v]) if m == o.set_add => {
                crate::value::unique_mut(s).insert((*v).clone());
                true
            }
            (Value::Set(s), [v]) if m == o.set_delete => {
                crate::value::unique_mut(s).shift_remove(v);
                true
            }
            _ => false,
        }
    }

    pub fn invoke_owned(
        &self,
        mid: MethodId,
        recv: Value,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
    ) -> Result<Value, (Flow, Value)> {
        let mid = match self.resolve_dynamic(&recv, mid) {
            Ok(mid) => mid,
            Err(flow) => return Err((flow, recv)),
        };
        if let Some(native) = self.program.natives_owned[mid as usize] {
            // (As `invoke` binds them for a native.)
            let (args, kw) = if kw.is_empty() {
                (args, kw)
            } else {
                match self.native_positions(self.program.method(mid), args, kw) {
                    Ok(bound) => bound,
                    Err(e) => return Err((e, recv)),
                }
            };
            let r = native(
                self,
                recv,
                Args {
                    pos: args.into(),
                    kw,
                    block: None,
                },
            );
            if let Ok(v) = &r {
                self.check_native_result(mid, v);
            }
            return r;
        }
        match self.invoke(mid, recv.clone(), args, kw, None) {
            Ok(v) => Ok(v),
            Err(e) => Err((e, recv)),
        }
    }

    /// Bind the arguments of a data constructor to its fields, running
    /// field defaults for the missing ones.
    fn bind_data_args(
        &self,
        mid: MethodId,
        recv: &Value,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
    ) -> Result<Vec<Value>, Flow> {
        let m = self.program.method(mid);
        let n = m.params.len();
        let mut values = vec![Value::Nil; n];
        let mut set = vec![false; n];
        for (i, a) in args.into_iter().enumerate() {
            if i < n {
                values[i] = a;
                set[i] = true;
            }
        }
        for (sym, v) in kw {
            let name = self.symbol_name(sym);
            if let Some(i) = m.params.iter().position(|p| *p.name == *name) {
                values[i] = v;
                set[i] = true;
            }
        }
        let class = self.program.world.class(m.owner);
        for (i, p) in m.params.iter().enumerate() {
            if !set[i] && p.has_default {
                if let Some(default) = class.ivars.get(i).and_then(|f| f.default) {
                    values[i] = self.run_init(default, recv.clone(), class.file)?;
                }
            }
        }
        Ok(values)
    }

    /// For a native: the keyword arguments that name positional
    /// parameters, moved to their positions, a skipped optional parameter
    /// before one taking its literal default (`RtParam::default`); the
    /// other keywords stay keywords.
    fn native_positions(
        &self,
        m: &quarz_ir::RtMethod,
        mut args: ArgVec,
        mut kw: Vec<(Symbol, Value)>,
    ) -> Result<(ArgVec, Vec<(Symbol, Value)>), Flow> {
        let positional: Vec<&quarz_ir::RtParam> = m
            .params
            .iter()
            .take_while(|p| p.kind == RtParamKind::Positional)
            .collect();
        for (i, p) in positional.iter().enumerate() {
            let Some(k) = kw
                .iter()
                .position(|(s, _)| *self.symbol_name(*s) == *p.name)
            else {
                continue;
            };
            if i < args.len() {
                continue;
            }
            for skipped in &positional[args.len()..i] {
                let value = match &skipped.default {
                    Some(Constant::Nil) => Value::Nil,
                    Some(Constant::Bool(b)) => Value::Bool(*b),
                    Some(Constant::Int(n)) => Value::Int(*n),
                    Some(Constant::Float(f)) => Value::Float(*f),
                    Some(Constant::Symbol(s)) => Value::Symbol(self.intern(s)),
                    _ => {
                        return Err(self.err_runtime(&format!(
                            "`{}` takes `{}` by keyword, but its parameter `{}` before it has no literal default to pass",
                            m.name, p.name, skipped.name
                        )))
                    }
                };
                args.push(value);
            }
            args.push(kw.remove(k).1);
        }
        Ok((args, kw))
    }

    /// Bind call arguments to parameter slots: positional parameters take
    /// positional arguments in order, keyword arguments go by name, the
    /// block comes last. Returns the slots and a mask of the ones that
    /// were passed (defaults are evaluated by the body).
    fn bind_params(
        &self,
        mid: MethodId,
        recv: &Value,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
    ) -> Result<(ArgVec, u64), Flow> {
        let m = self.program.method(mid);
        let n = m.params.len();
        let mut values: ArgVec = smallvec![Value::Nil; n + usize::from(m.has_block)];
        // The parameters given: `provided`, the activation's mask, has a
        // bit for the first 64 (a method declares no default past them,
        // #1002); `Given` records every one, for the keyword binding
        // below and a method generated with `keywords:`, which may have
        // any number of keywords. (Past 64 only: nothing allocated for
        // a method of 64 parameters or fewer.)
        let mut given = Given::new(n + usize::from(m.has_block));
        let mut args = args.into_iter();
        for (i, p) in m.params.iter().enumerate() {
            match p.kind {
                RtParamKind::Positional => {
                    if let Some(a) = args.next() {
                        values[i] = a;
                        given.set(i);
                    }
                }
                RtParamKind::Rest => {
                    let rest: Vec<Value> = args.by_ref().collect();
                    values[i] = Value::array(rest);
                    given.set(i);
                }
                _ => {}
            }
        }
        if !kw.is_empty() {
            let mut kwrest: Vec<(Symbol, Value)> = Vec::new();
            for (sym, v) in kw {
                let name = self.symbol_name(sym);
                // A `**hash` argument: its entries go to `**kw` only.
                if *name == *KW_SPLAT {
                    if let Value::Hash(h) = &v {
                        for (k, x) in h.as_map().iter() {
                            if let Value::Symbol(s) = k {
                                kwrest.push((*s, x.clone()));
                            }
                        }
                    }
                    continue;
                }
                let found = quarz_ir::keyword_param(&m.params, &name);
                match found {
                    Some(i) if !given.get(i) => {
                        values[i] = v;
                        given.set(i);
                    }
                    _ => kwrest.push((sym, v)),
                }
            }
            for (i, p) in m.params.iter().enumerate() {
                if p.kind == RtParamKind::KeywordRest && !given.get(i) {
                    let mut map = ValueMap::default();
                    for (sym, v) in kwrest.drain(..) {
                        map.insert(Value::Symbol(sym), v);
                    }
                    values[i] = Value::Hash(Rc::new(crate::value::HashData::from(map)));
                    given.set(i);
                }
            }
        } else {
            for (i, p) in m.params.iter().enumerate() {
                if p.kind == RtParamKind::KeywordRest {
                    values[i] =
                        Value::Hash(Rc::new(crate::value::HashData::from(ValueMap::default())));
                    given.set(i);
                }
            }
        }
        if m.has_block {
            if let Some(b) = block {
                values[n] = b;
                given.set(n);
            }
        }
        // A method generated with `keywords:` (docs/14 §5): its body takes
        // the hash of the keywords given, in the order of its parameters.
        if m.keyword_hash {
            let mut map = ValueMap::default();
            for (i, p) in m.params.iter().enumerate() {
                if given.get(i) {
                    let v = std::mem::replace(&mut values[i], Value::Nil);
                    map.insert(Value::Symbol(self.intern(&p.name)), v);
                }
            }
            let hash = Value::Hash(Rc::new(crate::value::HashData::from(map)));
            return Ok((smallvec![hash], 1));
        }
        let _ = recv;
        Ok((values, given.low))
    }

    /// For `new` on a class method's receiver: the class the receiver
    /// names (`class` or a subclass) and the `initialize` to run: the one
    /// the checker chose for the subclass (`RtClass::inherited_inits`,
    /// recorded for every subclass the method's `new` can build, #536
    /// step 6). A subclass without a record is an internal error, unless
    /// a compile-time run reached a pair the check refused (`reflect`,
    /// #870), which stops the run. (A compiled program has no
    /// reflection: only the compile-time runner installs one.)
    pub fn receiver_class_init(
        &self,
        recv: &Value,
        class: ClassId,
        init: Option<MethodId>,
    ) -> Result<(ClassId, Option<MethodId>), Flow> {
        let cid = match recv {
            Value::Class(c) => *c,
            _ => class,
        };
        if cid == class {
            return Ok((cid, init));
        }
        let info = self.program.world.class(cid);
        match info.inherited_inits.iter().find(|(i, _)| *i == init) {
            Some((_, chosen)) => Ok((cid, *chosen)),
            None => {
                let refused = self
                    .reflect
                    .borrow()
                    .as_ref()
                    .and_then(|r| r.refused_construction(cid, init));
                if let Some(why) = refused {
                    return Err(self.err_runtime(&why));
                }
                Err(self.err_runtime(&format!(
                "internal error: no inherited constructor recorded for `{}` from `{}`'s `new`; please report",
                    info.name,
                    self.program.world.class(class).name
                )))
            }
        }
    }

    /// Run the field defaults of `value`, a new object of a class (not a
    /// data type), in order (`construct`; compiled code's inline
    /// construction runs them itself, `gen::field_defaults`, #1000).
    pub fn field_defaults(&self, value: &Value) -> Result<(), Flow> {
        let Value::Object(obj) = value else {
            return Err(self.err_type("field defaults of a non-object"));
        };
        let info = self.program.world.class(obj.class);
        for (i, f) in info.ivars.iter().enumerate() {
            if let Some(d) = f.default {
                let v = self.run_init(d, value.clone(), info.file)?;
                self.logical_set(obj, i, v);
            }
        }
        Ok(())
    }

    /// Allocate an instance and run its initializer.
    pub fn construct(
        &self,
        class: ClassId,
        init: Option<MethodId>,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
    ) -> EvalResult {
        let info = self.program.world.class(class);
        // A value the runtime makes itself is no object of its class
        // (`RtClass::built_by_runtime`, `World::built_by_runtime`): the
        // checker refuses `new` on such a class, written or reached through
        // a module's or a witness's `new` (the inherited-constructor rule),
        // so reaching it here is a checker bug, an internal error (not
        // #509's TypeError, which is for a case left to run time).
        if info.built_by_runtime {
            return Err(self.err_type(&format!(
                "internal error: a checker bug: `new` reached `{}`, a class the runtime builds",
                info.name
            )));
        }
        // A data constructor given every physical field: copied in.
        if let Some(i) = init {
            if self.program.method(i).synth == RtSynth::DataInit
                && kw.is_empty()
                && block.is_none()
                && args.len() == info.fields.len()
                && matches!(info.kind, RtClassKind::Data | RtClassKind::Variant)
            {
                let fields: Fields = args.into_iter().collect();
                return Ok(Value::Object(Object::new(class, fields)));
            }
        }
        let obj = Object::with_nil_fields(class, info.fields.len());
        let value = Value::Object(obj.clone());
        let made = (|| {
            // Field defaults (data types evaluate them in their constructor).
            if !matches!(info.kind, RtClassKind::Data | RtClassKind::Variant) {
                self.field_defaults(&value)?;
            }
            if let Some(init) = init {
                self.invoke(init, value.clone(), args, kw, block)?;
            }
            Ok(())
        })();
        if let Err(flow) = made {
            // Failing before the object was usable (docs/03 §4), as a
            // Swift `init` before its first phase ends: nothing has seen
            // it, and its `deinitialize`, which may read any field, does
            // not run (the fields assigned are released as they go).
            if !obj.is_usable() {
                obj.set_deinitialized();
            }
            return Err(flow);
        }
        Ok(value)
    }

    // ----- blocks --------------------------------------------------------------------------

    /// A block implemented in Rust.
    pub fn native_block(&self, f: impl Fn(&Interp, ArgVec) -> EvalResult + 'static) -> Value {
        let tag = self.new_tag();
        Value::Proc(Rc::new(Closure {
            body: ClosureBody::Native(std::rc::Rc::new(f)),
            frame: None,
            self_val: Value::Nil,
            destructure: None,
            is_lambda: true,
            tag,
            method_block: None,
            method_tag: tag,
            file: 0,
            shareable: false,
        }))
    }

    /// Run a call that received a block, turning `break` into the call's
    /// value.
    pub fn catch_break(&self, block: &Option<Value>, r: EvalResult) -> EvalResult {
        match (r, block) {
            (Err(Flow::Break(v, t)), Some(Value::Proc(c))) if c.tag == t => Ok(v),
            (r, _) => r,
        }
    }

    // ----- regexps and comparisons -------------------------------------------------------

    pub fn make_regexp(&self, source: &str, flags: &str) -> EvalResult {
        match RegexpVal::new(source, flags) {
            Ok(regex) => Ok(Value::Regexp(Rc::new(regex))),
            Err(e) => Err(self.raise(
                self.program.exc.argument_error,
                &format!("invalid regexp /{source}/: {e}"),
            )),
        }
    }

    /// `pattern === v` (docs/01 §11, #1075): the one test of `when` and a
    /// value pattern of `case/in` (`Inst::CaseEq`, on the VM and through
    /// `qz_op_case_eq` in compiled code). A built-in pattern takes its
    /// arm, the same function its prelude `===` native runs (`Type#===`
    /// `case_eq_class`, `Range#===` `range_covers`, `Regexp#===`
    /// `case_eq_regexp`), with no method looked
    /// up: a program can change none of them. An object of a class with
    /// its own `===` is asked; any other value is compared with `==`
    /// (`Object#===`), a class's own `==` included, and so is a procedure:
    /// one is called only where the pattern's static type is a procedure
    /// type, which the lowering makes a call (`Output::proc_patterns`,
    /// #1085), never by the value's class here.
    pub fn case_eq(&self, pattern: &Value, v: &Value) -> Result<bool, Flow> {
        match pattern {
            Value::Class(cid) => Ok(self.case_eq_class(*cid, v)),
            Value::Range(r) => self.range_covers(r, v),
            Value::Regexp(re) => self.case_eq_regexp(re, v),
            // (`values_equal`'s two tails, its lookup cached.)
            Value::Object(_) => match self.object_case_eq(pattern)? {
                CaseEq::Own(mid) => Ok(self
                    .invoke(mid, pattern.clone(), smallvec![v.clone()], vec![], None)?
                    .is_truthy()),
                CaseEq::Eq(mid) => self.eq_by(mid, pattern, v),
                CaseEq::Default => self.builtin_eq(pattern, v),
            },
            _ => self.values_equal(pattern, v),
        }
    }

    /// What an object pattern runs (`CaseEq`): its class's own `===`,
    /// else its own `==` (`values_equal`'s), else the default, each by
    /// `has_user_method`; cached by class outside a compile-time run
    /// (`case_eq_methods`).
    fn object_case_eq(&self, pattern: &Value) -> Result<CaseEq, Flow> {
        let find = || -> Result<CaseEq, Flow> {
            Ok(match self.has_user_method(pattern, "===", 1)? {
                Some(mid) => CaseEq::Own(mid),
                None => match self.user_eq(pattern)? {
                    Some(mid) => CaseEq::Eq(mid),
                    None => CaseEq::Default,
                },
            })
        };
        if self.generated_any.get() {
            return find();
        }
        let cid = self.class_of(pattern);
        if let Some(found) = self.case_eq_methods.borrow().get(&cid) {
            return Ok(*found);
        }
        let found = find()?;
        self.case_eq_methods.borrow_mut().insert(cid, found);
        Ok(found)
    }

    /// `Type#===`: whether `v` is an instance of the class or a subclass.
    pub fn case_eq_class(&self, cid: ClassId, v: &Value) -> bool {
        self.program.world.class_is_a(self.class_of(v), cid)
    }

    /// `Regexp#===`: whether the regexp matches `v`, a string or bytes
    /// (any other value does not match).
    pub fn case_eq_regexp(&self, re: &RegexpVal, v: &Value) -> Result<bool, Flow> {
        Ok(match v {
            Value::Bytes(b) => re.for_bytes().map_err(|e| self.err_arg(e))?.is_match(b),
            _ => v.as_str().is_some_and(|s| re.regex.is_match(s.as_bytes())),
        })
    }

    pub fn range_covers(&self, r: &RangeVal, v: &Value) -> Result<bool, Flow> {
        use std::cmp::Ordering;
        if !r.lo.is_nil() {
            match self.compare_with(&r.lo, v, true) {
                Ok(Ordering::Greater) => return Ok(false),
                Ok(_) => {}
                Err(_) => return Ok(false),
            }
        }
        if !r.hi.is_nil() {
            match self.compare_with(v, &r.hi, true) {
                Ok(Ordering::Greater) => return Ok(false),
                Ok(Ordering::Equal) if r.exclusive => return Ok(false),
                Ok(_) => {}
                Err(_) => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Apply a binary operator by name with fast paths for numbers.
    pub fn binary_op(&self, lhs: &Value, name: &str, rhs: Value) -> EvalResult {
        if let Some(op) = FastOp::from_name(name) {
            if let Some(v) = fast_binop(op, lhs, &rhs) {
                return Ok(v);
            }
        }
        self.send(lhs, name, smallvec![rhs], None)
    }

    // ----- conversions ---------------------------------------------------------------------------

    /// Append `v`'s `to_s` to `buf` (numbers and strings without a
    /// temporary).
    pub fn append_to_s(&self, buf: &mut String, v: &Value) -> Result<(), Flow> {
        match v {
            Value::Str(s) => buf.push_str(s),
            Value::Short(s) => buf.push_str(s.as_str()),
            Value::Int(i) => {
                let mut digits = [0u8; 20];
                buf.push_str(crate::value::format_int(&mut digits, *i));
            }
            Value::Nil => {}
            Value::Bool(b) => buf.push_str(if *b { "true" } else { "false" }),
            _ => buf.push_str(&self.to_s(v)?),
        }
        Ok(())
    }

    /// `v.to_s`: borrowed from a string value, built otherwise.
    pub fn to_s<'a>(&self, v: &'a Value) -> Result<Cow<'a, str>, Flow> {
        match v {
            Value::Str(s) => Ok(Cow::Borrowed(s)),
            Value::Short(s) => Ok(Cow::Borrowed(s.as_str())),
            Value::Object(_) => {
                if let Some(mid) = self.has_user_method(v, "to_s", 0)? {
                    let r = self.invoke(mid, v.clone(), smallvec![], vec![], None)?;
                    return Ok(Cow::Owned(self.to_s(&r)?.into_owned()));
                }
                Ok(Cow::Owned(self.object_to_s(v)?))
            }
            _ => Ok(Cow::Owned(self.format_value(v, false)?)),
        }
    }

    /// The default `to_s` of an object, as in Ruby: an exception's
    /// message, a `data` value or variant formatted as the default
    /// `inspect` does, and other objects' class name only. It never
    /// calls a user-defined `inspect`, which may call `to_s`.
    pub(crate) fn object_to_s(&self, v: &Value) -> Result<String, Flow> {
        let Value::Object(o) = v else {
            return self.format_value(v, false);
        };
        let class = self.program.world.class(o.class);
        if class.is_exception {
            return Ok(self.exception_message(v));
        }
        match class.kind {
            RtClassKind::Data | RtClassKind::Variant | RtClassKind::Main => {
                self.format_value(v, true)
            }
            _ => Ok(format!("#<{}>", class.name)),
        }
    }

    pub fn inspect(&self, v: &Value) -> Result<String, Flow> {
        if let Value::Object(_) = v {
            if let Some(mid) = self.has_user_method(v, "inspect", 0)? {
                let r = self.invoke(mid, v.clone(), smallvec![], vec![], None)?;
                return Ok(self.to_s(&r)?.to_string());
            }
        }
        self.format_value(v, true)
    }

    pub(crate) fn format_value(&self, v: &Value, inspect: bool) -> Result<String, Flow> {
        // A value nested too deeply: raised before the stack runs out
        // (#437).
        if crate::sched::stack_exhausted() {
            return Err(self.too_deep("inspect"));
        }
        Ok(match v {
            Value::Nil => {
                if inspect {
                    "nil".to_string()
                } else {
                    String::new()
                }
            }
            Value::Bool(b) => b.to_string(),
            Value::Int(i) => i.to_string(),
            Value::BigInt(b) => b.to_string(),
            Value::Float(f) => format_float(*f),
            Value::Str(_) | Value::Short(_) => {
                let s = v.as_str().unwrap_or("");
                if inspect {
                    inspect_str(s)
                } else {
                    s.to_string()
                }
            }
            Value::Symbol(s) => {
                let name = self.symbol_name(*s);
                if inspect {
                    if name.chars().all(|c| {
                        c.is_alphanumeric() || c == '_' || c == '?' || c == '!' || c == '='
                    }) && !name.is_empty()
                    {
                        format!(":{name}")
                    } else {
                        format!(":{}", inspect_quoted(&name, true))
                    }
                } else {
                    name.to_string()
                }
            }
            Value::Array(a) => {
                let mut parts = Vec::new();
                for x in a.iter() {
                    parts.push(self.inspect(&x)?);
                }
                format!("[{}]", parts.join(", "))
            }
            // A copy, as the other builders': an element's `inspect` may
            // change the builder, which a held borrow would refuse (#925).
            Value::ArrayBuilder(a) => {
                let mut parts = Vec::new();
                let items = a.borrow().clone();
                for x in items.iter() {
                    parts.push(self.inspect(x)?);
                }
                format!("[{}]", parts.join(", "))
            }
            Value::Hash(h) => self.format_hash(h.as_map().iter())?,
            // A copy: an element's `inspect` may change the builder.
            Value::HashBuilder(h) => {
                let m = h.borrow().clone();
                self.format_hash(m.iter())?
            }
            Value::Set(s) => {
                let mut parts = Vec::new();
                for x in s.iter() {
                    parts.push(self.inspect(x)?);
                }
                format!("Set[{}]", parts.join(", "))
            }
            Value::SetBuilder(s) => {
                let mut parts = Vec::new();
                let members = s.borrow().clone();
                for x in members.iter() {
                    parts.push(self.inspect(x)?);
                }
                format!("Set[{}]", parts.join(", "))
            }
            // As Ruby's: `to_s` shows the bounds' `to_s` (`nil` as
            // nothing), `inspect` their `inspect`, leaving out a missing
            // bound unless both are.
            Value::Range(r) => {
                let bound = |b: &Value, other: &Value| -> Result<String, Flow> {
                    if !inspect {
                        Ok(self.to_s(b)?.into_owned())
                    } else if b.is_nil() && !other.is_nil() {
                        Ok(String::new())
                    } else {
                        self.inspect(b)
                    }
                };
                format!(
                    "{}{}{}",
                    bound(&r.lo, &r.hi)?,
                    if r.exclusive { "..." } else { ".." },
                    bound(&r.hi, &r.lo)?
                )
            }
            Value::Regexp(r) => crate::value::regexp_literal(&r.source, &r.flags),
            // `to_s` (and interpolation) is the match, as in Ruby (a
            // Bytes match as Bytes shows itself).
            Value::MatchData(m) if !inspect => {
                let (st, en) = m.groups[0].unwrap_or((0, 0));
                match &m.data {
                    Some(data) => crate::natives::bytes::inspect_bytes(&data[st..en]),
                    None => m.text[st..en].to_string(),
                }
            }
            Value::MatchData(m) => {
                let group = |k: usize| -> String {
                    match (m.groups.get(k).copied().flatten(), &m.data) {
                        (Some((s, e)), Some(data)) => {
                            crate::natives::bytes::inspect_bytes(&data[s..e])
                        }
                        (Some((s, e)), None) => inspect_str(&m.text[s..e]),
                        (None, _) => "nil".to_string(),
                    }
                };
                let class = if m.data.is_some() {
                    "Bytes::MatchData"
                } else {
                    "MatchData"
                };
                let mut out = format!("#<{class} {}", group(0));
                for k in 1..m.groups.len() {
                    let label = m
                        .names
                        .iter()
                        .find(|(_, idx)| *idx == k)
                        .map(|(n, _)| n.clone())
                        .unwrap_or_else(|| k.to_string());
                    out.push_str(&format!(" {label}:{}", group(k)));
                }
                out.push('>');
                out
            }
            Value::Object(o) => {
                let class = self.program.world.class(o.class);
                if class.is_exception {
                    return Ok(format!("#<{}: {}>", class.name, self.exception_message(v)));
                }
                match class.kind {
                    RtClassKind::Data | RtClassKind::Variant => {
                        if class.ivars.is_empty() {
                            return Ok(class.name.clone());
                        }
                        let mut parts = Vec::new();
                        for (f, val) in class.ivars.iter().zip(self.logical_values(o)) {
                            parts.push(format!("{}: {}", f.name, self.inspect(&val)?));
                        }
                        format!("{}({})", class.name, parts.join(", "))
                    }
                    RtClassKind::Main => "main".to_string(),
                    _ => {
                        let mut parts = Vec::new();
                        for (f, val) in class.ivars.iter().zip(self.logical_values(o)) {
                            parts.push(format!("@{}={}", f.name, self.inspect(&val)?));
                        }
                        if parts.is_empty() {
                            format!("#<{}>", class.name)
                        } else {
                            format!("#<{} {}>", class.name, parts.join(", "))
                        }
                    }
                }
            }
            Value::Class(c) => self.program.world.class(*c).name.clone(),
            Value::Proc(_) => "#<Proc>".to_string(),
            Value::StringBuilder(s) => {
                if inspect {
                    inspect_str(&s.borrow())
                } else {
                    s.borrow().clone()
                }
            }
            Value::Channel(c) => format!("#<Channel capacity={}>", c.capacity),
            Value::Task(t) => format!("#<Task {}>", t.id),
            Value::Scope(_) => "#<Task::Scope>".to_string(),
            Value::Atom(a) => {
                let v = sched::lock(a).clone();
                format!("#<Atom {}>", self.inspect(&v)?)
            }
            Value::Selector(_) => "#<Channel::Selector>".to_string(),
            Value::Duration(ns) => format_duration(*ns),
            Value::Enumerator(e) => format!("#<Enumerator {}>", e.method),
            Value::Io(io) => match &io.kind {
                IoKind::Stdin => "#<IO:<STDIN>>".to_string(),
                IoKind::Stdout => "#<IO:<STDOUT>>".to_string(),
                IoKind::Stderr => "#<IO:<STDERR>>".to_string(),
                IoKind::File(f) => {
                    let f = f.borrow();
                    format!(
                        "#<File:{}{}>",
                        f.path,
                        if f.closed { " (closed)" } else { "" }
                    )
                }
                IoKind::Socket(_) | IoKind::Listener(_) | IoKind::Udp(_) | IoKind::Tls(_) => {
                    natives::net::inspect_socket(self, io)
                }
                IoKind::Child(st) => natives::process::inspect_child(st),
            },
            Value::Random(r) => format!("#<Random seed={}>", r.borrow().seed),
            // Nothing of it, not even its size (#963).
            Value::Secret(s) => match &**s {
                crate::value::SecretVal::Bytes(_) => "#<Bytes::Secret>".to_string(),
                // The size, never the key.
                crate::value::SecretVal::Key(k) => match k.kind() {
                    crate::value::KeyKind::RsaPrivate => {
                        format!("#<Crypto::RSA::PrivateKey {} bits>", k.bits())
                    }
                    crate::value::KeyKind::Aes => format!("#<Crypto::AES::GCM {} bits>", k.bits()),
                },
            },
            Value::Bytes(b) => natives::bytes::inspect_bytes(b),
            Value::BytesBuilder(b) => natives::bytes::inspect_bytes(&b.borrow()),
            Value::Time(t) => natives::time::time_to_s(t, inspect),
            Value::Flow(_) => "#<Flow>".to_string(),
        })
    }

    fn format_hash<'a>(
        &self,
        iter: impl Iterator<Item = (&'a Value, &'a Value)>,
    ) -> Result<String, Flow> {
        let mut parts = Vec::new();
        for (k, v) in iter {
            let key = match k {
                Value::Symbol(s) => {
                    let name = self.symbol_name(*s);
                    if name
                        .chars()
                        .all(|c| c.is_alphanumeric() || c == '_' || c == '?' || c == '!')
                    {
                        format!("{name}: ")
                    } else {
                        format!("{} => ", self.inspect(k)?)
                    }
                }
                _ => format!("{} => ", self.inspect(k)?),
            };
            parts.push(format!("{key}{}", self.inspect(v)?));
        }
        Ok(format!("{{{}}}", parts.join(", ")))
    }

    /// `a == b` with user-defined equality.
    pub fn values_equal(&self, a: &Value, b: &Value) -> Result<bool, Flow> {
        match self.user_eq(a)? {
            Some(mid) => self.eq_by(mid, a, b),
            None => self.builtin_eq(a, b),
        }
    }

    /// `values_equal`'s lookup: `a`'s class's own `==`, for an object.
    pub(crate) fn user_eq(&self, a: &Value) -> Result<Option<MethodId>, Flow> {
        if let Value::Object(_) = a {
            return self.has_user_method(a, "==", 1);
        }
        Ok(None)
    }

    /// `a == b` by `a`'s own `==`, `mid` (`user_eq`).
    pub(crate) fn eq_by(&self, mid: MethodId, a: &Value, b: &Value) -> Result<bool, Flow> {
        let r = self.invoke(mid, a.clone(), smallvec![b.clone()], vec![], None)?;
        Ok(r.is_truthy())
    }

    /// `a == b` when `a` has no `==` of its own (`user_eq`).
    pub(crate) fn builtin_eq(&self, a: &Value, b: &Value) -> Result<bool, Flow> {
        // An element's or field's own `==` (`crate::keys`) may raise.
        let eq = a == b;
        crate::keys::check()?;
        Ok(eq)
    }

    /// `a == b` by the default equality (`Object#==`), not a class's own
    /// for `a`: its elements' and fields' own still apply (`crate::keys`).
    pub fn values_equal_default(&self, a: &Value, b: &Value) -> Result<bool, Flow> {
        let eq = a.default_eq(b);
        crate::keys::check()?;
        Ok(eq)
    }

    /// A `SystemStackError` for a walk over a value nested too deeply to
    /// `what` (`inspect`, `compare`) before the native stack runs out.
    pub(crate) fn too_deep(&self, what: &str) -> Flow {
        self.raise(
            self.program.exc.system_stack,
            &format!("a value nested too deeply to {what}"),
        )
    }

    /// `a <=> b` as an ordering, raising when incomparable.
    pub fn compare(&self, a: &Value, b: &Value) -> Result<std::cmp::Ordering, Flow> {
        self.compare_with(a, b, true)
    }

    /// The order of two built-in values `compare_with` orders natively:
    /// numbers (an `Int` and a `Float` exactly, #888; NaN as
    /// `float_order` orders it), strings, symbols (by name), durations,
    /// bytes, times. `None` for any other pair, which a `<=>` decides.
    #[inline]
    fn native_order(&self, a: &Value, b: &Value) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;
        Some(match (a, b) {
            (Value::Int(x), Value::Int(y)) => x.cmp(y),
            (Value::Float(x), Value::Float(y)) => float_order(*x, *y),
            // (Exactly, #888; NaN ordered as `float_order` orders it.)
            (Value::Int(x), Value::Float(y)) => {
                crate::value::cmp_int_float(*x, *y).unwrap_or_else(|| float_order(*x as f64, *y))
            }
            (Value::Float(x), Value::Int(y)) => crate::value::cmp_int_float(*y, *x)
                .map(Ordering::reverse)
                .unwrap_or_else(|| float_order(*x, *y as f64)),
            (Value::Str(_) | Value::Short(_), Value::Str(_) | Value::Short(_)) => {
                a.as_str().unwrap_or("").cmp(b.as_str().unwrap_or(""))
            }
            (Value::Symbol(x), Value::Symbol(y)) => self.symbol_name(*x).cmp(&self.symbol_name(*y)),
            (Value::Duration(x), Value::Duration(y)) => x.cmp(y),
            (Value::Bytes(x), Value::Bytes(y)) => x.cmp(y),
            (Value::Time(x), Value::Time(y)) => x.ns.cmp(&y.ns),
            _ => return None,
        })
    }

    /// Sort `items` as `compare` orders them (a sort without a block):
    /// with the standard library's stable sort where every one is of one
    /// kind `native_order` orders (`native_kind`), whose order is total
    /// and runs no code of the program, so that it can neither raise nor
    /// be inconsistent (#953); with `sort_values` otherwise (#924).
    pub fn sort_compared(&self, items: &mut Vec<Value>) -> Result<(), Flow> {
        if native_kind(items.iter()) {
            items.sort_by(|a, b| {
                self.native_order(a, b)
                    .expect("a native order for one kind of built-in value")
            });
            return Ok(());
        }
        self.sort_values(items, |a, b| self.compare(a, b))
    }

    /// `sort_compared` by `key` of each item (`sort_by`'s pairs): the
    /// keys compared, the items moved with them.
    pub fn sort_compared_by(
        &self,
        items: &mut Vec<Value>,
        key: impl Fn(&Value) -> Value,
    ) -> Result<(), Flow> {
        let mut keyed: Vec<(Value, Value)> = items.drain(..).map(|v| (key(&v), v)).collect();
        let result = if native_kind(keyed.iter().map(|(k, _)| k)) {
            keyed.sort_by(|(a, _), (b, _)| {
                self.native_order(a, b)
                    .expect("a native order for one kind of built-in value")
            });
            Ok(())
        } else {
            sort_fallible(&mut keyed, |(a, _), (b, _)| self.compare(a, b))
        };
        items.extend(keyed.into_iter().map(|(_, item)| item));
        result
    }

    /// `compare`, saying whether a `<=>` found by name may be a witness
    /// (`find_method`): `true` for the sorting natives, whose element type
    /// is bounded by `Comparable` (the checker allows them only on
    /// conforming values), and for `range_covers` (`Range[T <:
    /// Comparable[T]]`, #559); `false` for a comparison by name.
    pub(crate) fn compare_with(
        &self,
        a: &Value,
        b: &Value,
        witness: bool,
    ) -> Result<std::cmp::Ordering, Flow> {
        use std::cmp::Ordering;
        if crate::sched::stack_exhausted() {
            return Err(self.too_deep("compare"));
        }
        // (An object's order is its `<=>`'s: the built-ins' first.)
        if !matches!(a, Value::Object(_)) {
            if let Some(o) = self.native_order(a, b) {
                return Ok(o);
            }
        }
        if let (Value::Array(x), Value::Array(y)) = (a, b) {
            for (p, q) in x.iter().zip(y.iter()) {
                let o = self.compare_with(&p, &q, witness)?;
                if o != Ordering::Equal {
                    return Ok(o);
                }
            }
            return Ok(x.len().cmp(&y.len()));
        }
        let r = if witness {
            self.send_requirement(a, self.req_cmp, "<=>", smallvec![b.clone()], None)?
        } else {
            self.send_with(a, "<=>", smallvec![b.clone()], Vec::new(), None, false)?
        };
        match r {
            Value::Int(i) => Ok(i.cmp(&0)),
            _ => Err(self.err_arg(&format!(
                "comparison of {} with {} failed",
                self.class_name(a),
                self.class_name(b)
            ))),
        }
    }

    /// Sort with a fallible comparator: stably (`sort_fallible`), stopping
    /// at the first error, which is returned with `items` holding its
    /// values still, in an order not specified. Any comparison is taken,
    /// a total order or not (an inconsistent block gives some
    /// permutation), never a panic (#924).
    pub fn sort_values(
        &self,
        items: &mut Vec<Value>,
        cmp: impl FnMut(&Value, &Value) -> Result<std::cmp::Ordering, Flow>,
    ) -> Result<(), Flow> {
        sort_fallible(items, cmp)
    }

    pub fn write_out(&self, s: &str) {
        self.write_out_bytes(s.as_bytes());
    }

    pub fn write_out_bytes(&self, bytes: &[u8]) {
        use std::io::Write;
        let _ = lock(&self.global.stdout).write_all(bytes);
    }
}

/// The error for a `return` or `break` that reached a task's top: its
/// block ran after the method (or call) it would leave had returned
/// (a kept block called later), or in another task.
fn stray_flow_message(flow: &Flow) -> String {
    match flow {
        Flow::Return(..) => {
            "`return` from a block whose method or lambda has already returned (or that runs in another task)".to_string()
        }
        Flow::Break(..) => {
            "`break` from a block whose call has already returned (or that runs in another task)".to_string()
        }
        other => format!("unexpected control flow: {other:?}"),
    }
}

/// How a compile-time run ended other than normally (`Interp::run_static`).
pub enum StaticEnd {
    Raised(Value),
    Exited(i32),
}

/// Convert the result of a task body into its exit.
pub(crate) fn task_exit(interp: &Interp, result: EvalResult) -> TaskExit {
    match result {
        Ok(v) => TaskExit::Result(TaskResult::Value(v)),
        // A `SystemExit` nothing rescued ends the program with its status,
        // from any task (as Ruby's `exit` in a thread), after the `ensure`
        // clauses it passed.
        Err(Flow::Raise(e)) if interp.exception_is_a(&e, interp.program.exc.system_exit) => {
            TaskExit::Exit(interp.exit_status(&e))
        }
        Err(Flow::Raise(e)) => TaskExit::Result(TaskResult::Error(e)),
        Err(Flow::Exit(c)) => TaskExit::Exit(c),
        Err(Flow::Return(v, 0)) => TaskExit::Result(TaskResult::Value(v)),
        Err(other) => {
            let e = interp.make_exception(
                interp.program.exc.runtime_error,
                &stray_flow_message(&other),
            );
            TaskExit::Result(TaskResult::Error(e))
        }
    }
}

/// Parse an integer literal (digits without prefix/underscores) in a base.
/// An `Integer` literal's value.
pub fn parse_integer(digits: &str, base: u8) -> Value {
    use num_bigint::BigInt;
    use num_traits::Num;
    let (neg, digits) = match digits.strip_prefix('-') {
        Some(d) => (true, d),
        None => (false, digits),
    };
    let b = BigInt::from_str_radix(digits, base as u32).unwrap_or_default();
    integer(if neg { -b } else { b })
}

/// Format a float the way Ruby does: shortest round-trip digits, always
/// with a decimal point, exponent notation below 1e-4 and from 1e16.
pub fn format_float(f: f64) -> String {
    if f.is_nan() {
        return "NaN".to_string();
    }
    if f.is_infinite() {
        return if f > 0.0 {
            "Infinity".to_string()
        } else {
            "-Infinity".to_string()
        };
    }
    if f == 0.0 {
        return if f.is_sign_negative() {
            "-0.0".to_string()
        } else {
            "0.0".to_string()
        };
    }
    // Shortest representation in scientific form, e.g. "1.5e-7".
    let sci = format!("{f:e}");
    let (mantissa, exp) = sci.split_once('e').unwrap_or((&sci, "0"));
    let exp: i32 = exp.parse().unwrap_or(0);
    if !(-4..16).contains(&exp) {
        let mantissa = if mantissa.contains('.') {
            mantissa.to_string()
        } else {
            format!("{mantissa}.0")
        };
        let sign = if exp < 0 { '-' } else { '+' };
        return format!("{mantissa}e{sign}{:02}", exp.abs());
    }
    let s = format!("{f}");
    if s.contains('.') {
        s
    } else {
        format!("{s}.0")
    }
}

pub fn format_duration(ns: i64) -> String {
    if ns % 1_000_000_000 == 0 {
        format!("{}s", ns / 1_000_000_000)
    } else if ns % 1_000_000 == 0 {
        format!("{}ms", ns / 1_000_000)
    } else {
        format!("{}ns", ns)
    }
}

pub fn inspect_str(s: &str) -> String {
    inspect_quoted(s, false)
}

/// A string as `inspect` quotes it: other control characters as Ruby
/// shows them, `\u0001` in a String and `\x01` in a Symbol.
pub(crate) fn inspect_quoted(s: &str, symbol: bool) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\x1b' => out.push_str("\\e"),
            '\x07' => out.push_str("\\a"),
            '\x08' => out.push_str("\\b"),
            '\x0b' => out.push_str("\\v"),
            '\x0c' => out.push_str("\\f"),
            '#' => out.push('#'),
            c if symbol && ((c as u32) < 0x20 || c == '\x7f') => {
                out.push_str(&format!("\\x{:02X}", c as u32))
            }
            c if c.is_control() => out.push_str(&format!("\\u{:04X}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// The compiled frames the native unwinder finds on this task's stack
/// (see `native_bt`), innermost first.
fn native_frames() -> Vec<(usize, FuncId, u32)> {
    crate::native_bt::frames()
}

/// A conformance-gated send's first dispatch for class `cid` and
/// requirement `req` (`Interp::send_requirement`): the class must be a key of
/// the witness rows for it (`RtWorld::in_witness_rows`), which the gate (a
/// `Comparable` bound, an `Enumerable` receiver) guarantees; otherwise an
/// internal error.
pub fn check_gated_key<'m>(
    world: &quarz_ir::RtWorld,
    method: &dyn Fn(MethodId) -> &'m RtMethod,
    cid: ClassId,
    req: MethodId,
    name: &str,
) {
    if !world.in_witness_rows(method, cid, req) {
        panic!(
            "internal error: a gated `{name}` on `{}`, not a key of the witness rows",
            world.class(cid).name
        );
    }
}

/// The abstract method `name` the prelude module `module` declares (a
/// requirement a gated send dispatches, `Interp::send_requirement`):
/// `None` when `shake` dropped it (its name cleared), which happens only
/// when no class with values includes the module, so that no gated send
/// can reach one.
fn requirement(program: &Program, module: ClassId, name: &str) -> Option<MethodId> {
    program
        .world
        .class(module)
        .methods
        .get(name)?
        .iter()
        .copied()
        .find(|&m| {
            let m = program.method(m);
            m.owner == module && m.name == name && m.is_abstract
        })
}

/// The parameters a call gave (`Interp::bind_params`): the first 64 as the
/// activation's `provided` mask, the others in a list of their own, empty
/// for a method of 64 parameters or fewer.
struct Given {
    low: u64,
    high: Vec<bool>,
}

impl Given {
    fn new(n: usize) -> Given {
        Given {
            low: 0,
            high: vec![false; n.saturating_sub(64)],
        }
    }

    fn set(&mut self, i: usize) {
        if i < 64 {
            self.low |= 1u64 << i;
        } else {
            self.high[i - 64] = true;
        }
    }

    fn get(&self, i: usize) -> bool {
        if i < 64 {
            self.low & (1u64 << i) != 0
        } else {
            self.high[i - 64]
        }
    }
}

#[cfg(test)]
mod sort_tests {
    use super::sort_fallible;

    /// `sort_fallible` of the indices `0..n` by `cmp`.
    fn sort_indices<E>(
        n: usize,
        mut cmp: impl FnMut(usize, usize) -> Result<Ordering, E>,
    ) -> Result<Vec<usize>, E> {
        let mut v: Vec<usize> = (0..n).collect();
        sort_fallible(&mut v, |a, b| cmp(*a, *b)).map(|()| v)
    }
    use std::cmp::Ordering;

    /// A small deterministic generator for the inputs.
    fn values(n: usize, seed: u64, range: u64) -> Vec<u64> {
        let mut x = seed;
        (0..n)
            .map(|_| {
                x = x
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                (x >> 33) % range
            })
            .collect()
    }

    #[test]
    fn sorts_as_the_standard_stable_sort() {
        for n in [0, 1, 2, 15, 16, 17, 33, 100, 1000, 4097] {
            for range in [3, 1000] {
                let v = values(n, n as u64 + range, range);
                let order = sort_indices(n, |a, b| Ok::<_, ()>(v[a].cmp(&v[b]))).unwrap();
                let mut want: Vec<usize> = (0..n).collect();
                want.sort_by(|&a, &b| v[a].cmp(&v[b]));
                assert_eq!(order, want, "n={n} range={range}");
            }
        }
    }

    #[test]
    fn stops_at_the_first_error() {
        let v = values(500, 7, 50);
        let mut calls = 0;
        let r = sort_indices(v.len(), |a, b| {
            calls += 1;
            if calls == 123 {
                Err("stop")
            } else {
                Ok(v[a].cmp(&v[b]))
            }
        });
        assert_eq!(r, Err("stop"));
        assert_eq!(calls, 123);
        // Stopped in a merge (past the 16-element runs' insertions): the
        // values are all kept.
        let mut w: Vec<u64> = values(500, 9, 50);
        let mut sorted_w = w.clone();
        sorted_w.sort_unstable();
        let mut calls = 0;
        let r = sort_fallible(&mut w, |a, b| {
            calls += 1;
            if calls == 2000 {
                Err(())
            } else {
                Ok(a.cmp(b))
            }
        });
        assert_eq!(r, Err(()));
        w.sort_unstable();
        assert_eq!(w, sorted_w);
    }

    /// #953: the standard library's sort only for values of one kind
    /// `native_order` orders totally.
    #[test]
    fn a_native_kind_is_one_kind_of_built_in_value() {
        use super::native_kind;
        use crate::value::Value;
        let strs = [
            Value::string("b".to_string()),
            Value::string("a".to_string()),
        ];
        assert!(native_kind(strs.iter()));
        assert!(native_kind([Value::Int(1), Value::Int(2)].iter()));
        assert!(native_kind([].iter()));
        // Mixed numbers, and booleans or nil: not.
        assert!(!native_kind([Value::Int(1), Value::Float(2.0)].iter()));
        assert!(!native_kind([Value::Bool(true), Value::Bool(false)].iter()));
        assert!(!native_kind([Value::Nil].iter()));
        assert!(!native_kind([strs[0].clone(), Value::Int(1)].iter()));
    }

    #[test]
    fn takes_an_order_that_is_not_total() {
        for n in [20, 300, 3000] {
            let mut c = 0u64;
            let order = sort_indices(n, |_, _| {
                c += 1;
                Ok::<_, ()>(match (c * 7) % 3 {
                    0 => Ordering::Less,
                    1 => Ordering::Equal,
                    _ => Ordering::Greater,
                })
            })
            .unwrap();
            let mut seen = order.clone();
            seen.sort_unstable();
            assert_eq!(seen, (0..n).collect::<Vec<_>>(), "a permutation");
        }
    }
}

/// What `Interp::case_eq` runs for an object pattern of a class
/// (`Interp::case_eq_methods`, #1088).
#[derive(Clone, Copy, Debug)]
enum CaseEq {
    /// The class's own `===`.
    Own(MethodId),
    /// No `===` of its own: its own `==`, which `Object#===` calls.
    Eq(MethodId),
    /// Neither: the default comparison (`Value`'s `==`).
    Default,
}
