//! The runtime: method invocation, dynamic dispatch, exceptions, the task
//! run loop, and conversions used by the natives. Function bodies are QIR
//! (see `vm.rs`); compiled code uses the same runtime.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use crate::rc::Rc;
use rustc_hash::FxHashMap;
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

/// Arguments to a native method.
#[derive(Default)]
pub struct Args {
    pub pos: ArgVec,
    pub kw: Vec<(Symbol, Value)>,
    pub block: Option<Value>,
}

impl Args {
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
/// receiver or argument it does not handle, or a case that raises).
pub type FastNativeFn = fn(&Interp, &Value, &[&Value]) -> Option<EvalResult>;

/// A native that takes ownership of the receiver so that it can update a
/// uniquely referenced value in place. On failure it hands the receiver
/// back so the caller can restore it.
pub type OwnedNativeFn = fn(&Interp, Value, Args) -> Result<Value, (Flow, Value)>;

/// Key of the by-name method cache: class, arity, block given (the name
/// is the inner key, so lookups do not allocate).
type NameKey = (ClassId, usize, bool);

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
/// `fast_binop` computes with).
#[inline(always)]
pub fn float_operands(a: &Value, b: &Value) -> Option<(f64, f64)> {
    match (a, b) {
        (Value::Float(x), Value::Float(y)) => Some((*x, *y)),
        (Value::Int(x), Value::Float(y)) => Some((*x as f64, *y)),
        (Value::Float(x), Value::Int(y)) => Some((*x, *y as f64)),
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
            let x = match a {
                Value::Int(i) => *i as f64,
                Value::Float(f) => *f,
                _ => return None,
            };
            let y = match b {
                Value::Int(i) => *i as f64,
                Value::Float(f) => *f,
                _ => return None,
            };
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
    /// The top-level object of each file (the `self` of its top level and
    /// of its top-level `def`s), by file index: one for every worker, the
    /// REPL's inputs and the compiler's compile-time runs
    /// (`Interp::unit_self_of`).
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
/// made it, whose ids the next one reuses). Immortal: every task calling a
/// top-level `def` of the file uses it.
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
    pub eof_error: ClassId,
    pub not_implemented: ClassId,
    pub system_exit: ClassId,
    pub range_error: ClassId,
    pub float_domain_error: ClassId,
    pub overflow_error: ClassId,
    pub system_stack: ClassId,
}

/// Ids of runtime value classes.
#[derive(Clone, Debug, Default)]
pub struct RtClasses {
    pub selector: ClassId,
    pub enumerator: ClassId,
    pub io: ClassId,
    pub tcp_socket: ClassId,
    pub tcp_server: ClassId,
    pub udp_socket: ClassId,
    pub unix_socket: ClassId,
    pub unix_server: ClassId,
    pub random: ClassId,
    pub file: ClassId,
    pub math: ClassId,
    pub process: ClassId,
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
            .map(|m| vslot(m.overridden && !m.singleton && !m.is_extension))
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
    /// (see `method`).
    pub world: RtWorld,
    /// A compiled program's methods, decoded when first needed.
    pub lazy: Option<std::sync::Arc<crate::methods::Lazy>>,
    /// Compilation units in execution order.
    pub units: Vec<Unit>,
    pub natives: Vec<Option<NativeFn>>,
    /// By-reference versions of some natives, by method id.
    pub fast_natives: Vec<Option<FastNativeFn>>,
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
    /// The top-level objects this interpreter has used, by file index: a
    /// copy of `Global::unit_selfs`'s, read without its lock
    /// (`Interp::unit_self_of`).
    unit_selfs: RefCell<Vec<Value>>,
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
    /// The declarations a compile-time run reflects on (docs/14).
    pub reflect: RefCell<Option<std::rc::Rc<dyn crate::reflect::Reflect>>>,
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
        Interp::with_state(world, 0, functions, units, argv, state)
    }

    /// Create an interpreter over shared run-time state, loading the
    /// functions `functions` at ids starting from `base` (the REPL creates
    /// one interpreter per input, sharing variables, tasks and output).
    pub fn with_state(
        world: RtWorld,
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

    /// `with_state` for a compiled program, whose methods (`world`'s are
    /// left empty) come from `lazy`.
    pub fn with_state_lazy(
        world: RtWorld,
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
        {
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
            eof_error: class_by_name("EOFError"),
            not_implemented: class_by_name("NotImplementedError"),
            system_exit: class_by_name("SystemExit"),
            range_error: class_by_name("RangeError"),
            float_domain_error: class_by_name("FloatDomainError"),
            overflow_error: class_by_name("OverflowError"),
            system_stack: class_by_name("SystemStackError"),
        };
        let rt = RtClasses {
            selector: class_by_name("Selector"),
            enumerator: class_by_name("Enumerator"),
            io: class_by_name("IO"),
            tcp_socket: library_class("TCPSocket"),
            tcp_server: library_class("TCPServer"),
            udp_socket: library_class("UDPSocket"),
            unix_socket: library_class("UNIXSocket"),
            unix_server: library_class("UNIXServer"),
            random: class_by_name("Random"),
            file: class_by_name("File"),
            math: class_by_name("Math"),
            process: class_by_name("Process"),
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
        let interp = std::rc::Rc::new(Interp {
            hot: Hot::new(),
            program,
            repl_frame,
            unit_selfs: RefCell::new(Vec::new()),
            funcs: state.funcs,
            bodies: state.bodies,
            pools: state.pools,
            compiled: state.compiled,
            global: state.global,
            symbol_names: RefCell::new(Vec::new()),
            sched: state.sched,
            vtable: RefCell::new(vec![0; nvslots * nclasses]),
            class_dispatch_cache: RefCell::new(FxHashMap::default()),
            spawn_captures: RefCell::new(FxHashMap::default()),
            class_method_cache: RefCell::new(FxHashMap::default()),
            image_cache: RefCell::new(None),
            name_cache: RefCell::new(FxHashMap::default()),
            next_tag: state.next_tag,
            current_task_id: Cell::new(0),
            rescuing: RefCell::new(Vec::new()),
            deadline: Cell::new(None),
            reflect: RefCell::new(None),
            parked_rescuing: RefCell::new(FxHashMap::default()),
            native_bt: Cell::new(false),
            pending_flow: RefCell::new(None),
            reg_pool: RefCell::new(Vec::new()),
            verify: crate::verify::enabled(),
            verify_kinds: RefCell::new(Vec::new()),
            self_rc: RefCell::new(Weak::new()),
            root_task: Cell::new(None),
        });
        *interp.self_rc.borrow_mut() = std::rc::Rc::downgrade(&interp);
        let deinit: Vec<bool> = (0..interp.program.world.classes.len() as ClassId)
            .map(|c| interp.deinitializer(c).is_some())
            .collect();
        crate::deinit::set_classes(deinit, interp.global.id);
        // A class's own `==` and `hash` (not a native's: the prelude's
        // compare in Rust), by which hashes and sets compare its instances.
        // Only the classes below one that declares a `==` or `hash` with a
        // body are looked at (most programs have none: start-up pays a
        // scan of the classes' method tables).
        let world = &interp.program.world;
        let owners: Vec<ClassId> = (0..world.classes.len() as ClassId)
            .filter(|&c| world.class(c).declares_eq_hash)
            .collect();
        // The class's own: neither a native nor an extension's (which
        // takes no part in dynamic dispatch, docs/01-syntax.md §7).
        let own = |c: ClassId, name: &str, argc: usize| {
            interp.find_method(c, name, argc, false).filter(|m| {
                let m = interp.program.method(*m);
                m.native_key.is_none() && !m.is_extension
            })
        };
        let keys: Vec<Option<crate::keys::KeyMethods>> = if owners.is_empty() {
            Vec::new()
        } else {
            (0..world.classes.len() as ClassId)
                .map(|c| {
                    if !world.class(c).ancestors.iter().any(|a| owners.contains(a)) {
                        return None;
                    }
                    let k = crate::keys::KeyMethods {
                        eq: own(c, "==", 1),
                        hash: own(c, "hash", 0),
                    };
                    (k.eq.is_some() || k.hash.is_some()).then_some(k)
                })
                .collect()
        };
        crate::keys::set(&interp, keys);
        interp
    }

    /// The `deinitialize` instances of class `cid` run when released.
    fn deinitializer(&self, cid: ClassId) -> Option<MethodId> {
        let world = &self.program.world;
        world.class(cid).ancestors.iter().find_map(|a| {
            world
                .class(*a)
                .methods
                .get("deinitialize")
                .and_then(|ms| ms.first().copied())
        })
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
            Some(Some(class)) => self.unit_self_of(file, *class),
            _ => Value::Nil,
        }
    }

    /// The top-level object of file `file`, whose main pseudo-class is
    /// `class` (`unit_self_in`), from this interpreter's copy: a call of
    /// a top-level `def` takes no lock.
    pub fn unit_self_of(&self, file: u32, class: ClassId) -> Value {
        let mut mine = self.unit_selfs.borrow_mut();
        if let Some(v @ Value::Object(o)) = mine.get(file as usize) {
            if o.class == class {
                return v.clone();
            }
        }
        let v = unit_self_in(&self.global, file, class);
        if mine.len() <= file as usize {
            mine.resize(file as usize + 1, Value::Nil);
        }
        mine[file as usize] = v.clone();
        v
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
                // and the others waiting for them: it ends the program,
                // as one on the main thread does (the hook has printed
                // it).
                let run = std::panic::AssertUnwindSafe(move || {
                    Interp::worker_main(global, w, poller, image, argv, native_bt)
                });
                if std::panic::catch_unwind(run).is_err() {
                    std::process::exit(101);
                }
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
                    let e = me.make_exception(
                        me.program.exc.runtime_error,
                        &format!("unexpected control flow in task: {other:?}"),
                    );
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
        let me = self.sched.borrow().current_ref();
        let serial = {
            let mut s = st.borrow_mut();
            let w = s.watch();
            w.waiters.push(me);
            w.serial
        };
        self.sched.borrow_mut().wait_fd(fd, serial, writable, me.id);
        let r = self.park();
        self.sched.borrow_mut().unwait_fd(fd, me.id);
        st.borrow_mut().watch().waiters.retain(|t| *t != me);
        r
    }

    /// Run a blocking job on another thread, parking the task until it
    /// finishes (file IO, name resolution, child processes).
    pub fn block_on<T: Send + 'static>(
        &self,
        job: impl FnOnce() -> T + Send + 'static,
    ) -> Result<T, Flow> {
        use std::sync::mpsc::TryRecvError;
        let id = self.current_task().id;
        let rx = self.sched.borrow_mut().offload(id, job);
        loop {
            match rx.try_recv() {
                Ok(v) => return Ok(v),
                Err(TryRecvError::Disconnected) => {
                    return Err(self.raise(self.program.exc.runtime_error, "background job failed"))
                }
                Err(TryRecvError::Empty) => self.park()?,
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

    /// A compile-time run past its time limit raises (docs/14 §5).
    #[inline]
    pub fn check_deadline(&self) -> Result<(), Flow> {
        match self.deadline.get() {
            Some(d) if std::time::Instant::now() > d => {
                Err(self.err_runtime("compile-time evaluation took too long"))
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
            Value::Io(io) => match &io.kind {
                IoKind::Socket(st) => {
                    if st.borrow().unix {
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
                _ => self.program.rt.io,
            },
            Value::Bytes(_) => b.bytes,
            Value::BytesBuilder(_) => b.bytes_builder,
            Value::Time(_) => b.time,
            Value::Random(_) => self.program.rt.random,
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
    /// receiver's run-time class (subclass overrides).
    pub fn resolve_dynamic(&self, recv: &Value, mid: MethodId) -> MethodId {
        let m = self.program.method(mid);
        if m.singleton {
            // A class method some subclass overrides: the class it is
            // called on decides.
            return match recv {
                Value::Class(cid) if m.overridden && *cid != m.owner => {
                    self.class_method_override(*cid, mid).unwrap_or(mid)
                }
                _ => mid,
            };
        }
        if m.is_extension {
            return mid;
        }
        // Nothing overrides it, and the receiver is not a class object
        // (whose own class methods may stand in for a module's): the
        // method is the one.
        if self.program.vslots[mid as usize] == u32::MAX && !matches!(recv, Value::Class(_)) {
            return mid;
        }
        if let Value::Class(cid) = recv {
            // A module method running on a class object (`extend`): the
            // class's own `def self.` methods override the module's.
            if let Some(found) = self.class_side_override(*cid, mid) {
                return found;
            }
        }
        let cid = self.class_of(recv);
        if cid == m.owner {
            return mid;
        }
        let slot = self.program.vslots[mid as usize];
        if slot == u32::MAX {
            // Nothing overrides it: the method is the one.
            return mid;
        }
        let at = cid as usize * self.program.nvslots + slot as usize;
        if let Some(&hit) = self.vtable.borrow().get(at) {
            if hit != 0 {
                return hit - 1;
            }
        }
        let found = self.find_override(cid, mid).unwrap_or(mid);
        if let Some(cell) = self.vtable.borrow_mut().get_mut(at) {
            *cell = found + 1;
        }
        found
    }

    /// The implementation of a module instance method `mid` for the class
    /// object `cid`: a singleton method of the class (or a superclass), or
    /// a concrete method of another module the class extends.
    fn class_side_override(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        if let Some(found) = self.class_dispatch_cache.borrow().get(&(cid, mid)) {
            return *found;
        }
        let m = self.program.method(mid);
        let (min, max) = m.positional_arity();
        // A class method of the same name that accepts less is an
        // overload, not an override.
        let accepts = |c: MethodId| {
            let cm = self.program.method(c);
            let (cmin, cmax) = cm.positional_arity();
            !cm.is_abstract
                && cm.has_block == m.has_block
                && cmin <= max
                && cmax >= min
                && (c == mid || self.same_signature(c, mid) || cm.overrides.contains(&mid))
        };
        let mut found = None;
        let mut cur = Some(cid);
        'chain: while let Some(c) = cur {
            let class = self.program.world.class(c);
            if let Some(ids) = class.singleton_methods.get(&m.name) {
                if let Some(id) = ids.iter().copied().find(|id| accepts(*id)) {
                    found = Some(id);
                    break;
                }
            }
            for module in &class.extends {
                for anc in &self.program.world.class(*module).ancestors {
                    if let Some(ids) = self.program.world.class(*anc).methods.get(&m.name) {
                        if let Some(id) = ids.iter().copied().find(|id| accepts(*id)) {
                            found = Some(id);
                            break 'chain;
                        }
                    }
                }
            }
            cur = class.superclass;
        }
        let found = found.filter(|f| *f != mid);
        self.class_dispatch_cache
            .borrow_mut()
            .insert((cid, mid), found);
        found
    }

    /// The class method of `cid` (or of a superclass below the owner of
    /// `mid`) that overrides the class method `mid`.
    fn class_method_override(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        if let Some(found) = self.class_method_cache.borrow().get(&(cid, mid)) {
            return *found;
        }
        let m = self.program.method(mid);
        let mut found = None;
        let mut cur = Some(cid);
        while let Some(c) = cur {
            if c == m.owner {
                break;
            }
            let class = self.program.world.class(c);
            if let Some(ids) = class.singleton_methods.get(&m.name) {
                if let Some(id) = ids.iter().copied().find(|id| {
                    self.same_signature(*id, mid)
                        || self.program.method(*id).overrides.contains(&mid)
                }) {
                    found = Some(id);
                    break;
                }
            }
            cur = class.superclass;
        }
        self.class_method_cache
            .borrow_mut()
            .insert((cid, mid), found);
        found
    }

    /// The extension's method that implements abstract method `abs` for
    /// class `anc` itself (`RtWorld::ext_impls`): the one an extension that
    /// makes it conform (`include`) gives, else the one found where the
    /// class was declared.
    fn ext_impl(&self, anc: ClassId, abs: MethodId) -> Option<MethodId> {
        let world = &self.program.world;
        let m = self.program.method(abs);
        // (Of the extension's methods of the name, one that takes what the
        // abstract method's callers pass, as the checker's `implements`; an
        // overload of another arity is not it.)
        let (amin, amax) = m.positional_arity();
        let takes = |i: MethodId| {
            let c = self.program.method(i);
            let (cmin, cmax) = c.positional_arity();
            !c.is_abstract && c.has_block == m.has_block && cmin <= amin && cmax >= amax
        };
        for ext in &world.extensions {
            if ext.target == anc && world.extension_dispatches(ext, m.owner) {
                if let Some(ids) = ext.methods.get(&m.name) {
                    let exact = ids
                        .iter()
                        .find(|i| takes(**i) && self.same_signature(**i, abs));
                    if let Some(i) = exact.or_else(|| ids.iter().find(|i| takes(**i))) {
                        return Some(*i);
                    }
                }
            }
        }
        world
            .ext_impls
            .iter()
            .find(|(c, a, _)| *c == anc && *a == abs)
            .map(|(_, _, i)| *i)
    }

    /// A method of `cid` (or of an ancestor before the owner of `mid`)
    /// that overrides `mid`: same name, and the same signature when the
    /// name is overloaded.
    fn find_override(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        let m = self.program.method(mid);
        let (min, max) = m.positional_arity();
        for anc in &self.program.world.class(cid).ancestors {
            let anc = *anc;
            if anc == m.owner {
                return None;
            }
            // An abstract method an extension implements for this class
            // (its conformance), unless the class defines its own.
            let own = self.program.world.class(anc).methods.contains_key(&m.name);
            if m.is_abstract && !own {
                if let Some(i) = self.ext_impl(anc, mid) {
                    return Some(i);
                }
            }
            let mut candidates: Vec<MethodId> = Vec::new();
            for ext in &self.program.world.extensions {
                if ext.target == anc && self.program.world.extension_dispatches(ext, m.owner) {
                    if let Some(ids) = ext.methods.get(&m.name) {
                        candidates.extend(ids);
                    }
                }
            }
            if let Some(ids) = self.program.world.class(anc).methods.get(&m.name) {
                candidates.extend(ids);
            }
            candidates.retain(|c| {
                let cm = self.program.method(*c);
                let (cmin, cmax) = cm.positional_arity();
                cm.has_block == m.has_block && cmin <= max && cmax >= min
            });
            if candidates.is_empty() {
                continue;
            }
            if let Some(exact) = candidates.iter().find(|c| self.same_signature(**c, mid)) {
                return Some(*exact);
            }
            // An override whose parameter types are written differently
            // (instantiated generics, wider types). A method of the same
            // name that accepts less is an overload: keep looking.
            if let Some(o) = candidates
                .iter()
                .find(|c| self.program.method(**c).overrides.contains(&mid))
            {
                return Some(*o);
            }
        }
        None
    }

    fn same_signature(&self, a: MethodId, b: MethodId) -> bool {
        let (a, b) = (self.program.method(a), self.program.method(b));
        a.params.len() == b.params.len()
            && a.params.iter().zip(&b.params).all(|(p, q)| {
                p.kind == q.kind
                    && (p.kind != RtParamKind::KeywordOnly || p.name == q.name)
                    && (p.ty == q.ty || p.ty.is_none() || q.ty.is_none())
            })
    }

    /// Find a method by name on a class (first match in resolution order
    /// that accepts `argc` positional arguments).
    pub fn find_method(
        &self,
        cid: ClassId,
        name: &str,
        argc: usize,
        with_block: bool,
    ) -> Option<MethodId> {
        let key = (cid, argc, with_block);
        if let Some(found) = self.name_cache.borrow().get(&key).and_then(|m| m.get(name)) {
            return *found;
        }
        let mut found = None;
        let mut fallback = None;
        'outer: for anc in &self.program.world.class(cid).ancestors {
            let anc = *anc;
            let mut lists: Vec<&Vec<MethodId>> = Vec::new();
            // Always-active extensions on this ancestor come first (a
            // module's extension applies only where `using` makes it
            // visible, which is resolved statically).
            for ext in &self.program.world.extensions {
                if ext.always_active && ext.target == anc {
                    if let Some(ids) = ext.methods.get(name) {
                        lists.push(ids);
                    }
                }
            }
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
        // An abstract method (a module's) that an extension implements for
        // the class: conformance holds wherever the value goes.
        if let Some(abs) = found.filter(|m| self.program.method(*m).is_abstract) {
            let owner = self.program.method(abs).owner;
            for anc in &self.program.world.class(cid).ancestors {
                if *anc == owner {
                    break;
                }
                if let Some(i) = self.ext_impl(*anc, abs) {
                    found = Some(i);
                    break;
                }
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
        let cid = self.class_of(recv);
        let Some(mid) = self.find_method(cid, name, args.len(), block.is_some()) else {
            return Err(self.raise(
                self.program.exc.runtime_error,
                &format!(
                    "undefined method `{name}` for {}",
                    self.program.world.class(cid).name
                ),
            ));
        };
        self.invoke(mid, recv.clone(), args, kw, block)
    }

    /// Whether the receiver's class defines `name` itself (not via Object's
    /// native default).
    pub fn has_user_method(&self, recv: &Value, name: &str, argc: usize) -> Option<MethodId> {
        let cid = self.class_of(recv);
        let mid = self.find_method(cid, name, argc, false)?;
        let m = self.program.method(mid);
        if m.owner == self.program.world.builtin.object && m.native_key.is_some() {
            return None;
        }
        Some(mid)
    }

    // ----- invocation --------------------------------------------------------------------

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
                            self.err_runtime(&format!("`{key}` cannot run at compile time"))
                        );
                    }
                }
            }
            return native(
                self,
                &recv,
                Args {
                    pos: args,
                    kw,
                    block,
                },
            );
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
                let copy = Object::new(o.class, o.fields());
                for (sym, v) in kw {
                    let name = self.symbol_name(sym);
                    if let Some(i) = m.params.iter().position(|p| *p.name == *name) {
                        self.logical_set(&copy, i, v);
                    }
                }
                // The body's `initialize` taking the fields builds the
                // value, as `new` would (docs/01 §4).
                let class = self.program.world.class(o.class);
                let own_init = class.methods.get("initialize").and_then(|ids| {
                    ids.iter().copied().find(|i| {
                        let im = self.program.method(*i);
                        im.synth != RtSynth::DataInit
                            && im.params.len() == class.ivars.len()
                            && im.params.iter().zip(&class.ivars).all(|(p, f)| {
                                p.kind == RtParamKind::Positional
                                    && p.name == f.name
                                    && (p.ty == f.ty || p.ty.is_none() || f.ty.is_none())
                            })
                    })
                });
                if let Some(init) = own_init {
                    let args: ArgVec = (0..class.ivars.len())
                        .map(|i| self.logical_get(&copy, i))
                        .collect();
                    return self.construct(o.class, Some(init), args, Vec::new(), None);
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
        if m.is_abstract {
            return Err(self.raise(
                self.program.exc.not_implemented,
                &format!(
                    "abstract method `{}` called on {}",
                    m.name,
                    self.class_name(&recv)
                ),
            ));
        }
        let Some(fid) = m.func else {
            if self.deadline.get().is_some() {
                // A compile-time run: a body not lowered is a bug of the
                // compiler, not a nil (docs/14).
                return Err(self.err_runtime(&format!(
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
        let mid = self.resolve_dynamic(&recv, mid);
        if let Some(native) = self.program.natives_owned[mid as usize] {
            return native(
                self,
                recv,
                Args {
                    pos: args,
                    kw,
                    block: None,
                },
            );
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
        let mut provided = 0u64;
        let bit = |i: usize| if i < 64 { 1u64 << i } else { 0 };
        let mut args = args.into_iter();
        for (i, p) in m.params.iter().enumerate() {
            match p.kind {
                RtParamKind::Positional => {
                    if let Some(a) = args.next() {
                        values[i] = a;
                        provided |= bit(i);
                    }
                }
                RtParamKind::Rest => {
                    let rest: Vec<Value> = args.by_ref().collect();
                    values[i] = Value::array(rest);
                    provided |= bit(i);
                }
                _ => {}
            }
        }
        if !kw.is_empty() {
            let mut kwrest: Vec<(Symbol, Value)> = Vec::new();
            for (sym, v) in kw {
                let name = self.symbol_name(sym);
                let found = m.params.iter().position(|p| {
                    *p.name == *name
                        && matches!(p.kind, RtParamKind::Positional | RtParamKind::KeywordOnly)
                });
                match found {
                    Some(i) if provided & bit(i) == 0 => {
                        values[i] = v;
                        provided |= bit(i);
                    }
                    _ => kwrest.push((sym, v)),
                }
            }
            for (i, p) in m.params.iter().enumerate() {
                if p.kind == RtParamKind::KeywordRest && provided & bit(i) == 0 {
                    let mut map = ValueMap::default();
                    for (sym, v) in kwrest.drain(..) {
                        map.insert(Value::Symbol(sym), v);
                    }
                    values[i] = Value::Hash(Rc::new(crate::value::HashData::from(map)));
                    provided |= bit(i);
                }
            }
        } else {
            for (i, p) in m.params.iter().enumerate() {
                if p.kind == RtParamKind::KeywordRest {
                    values[i] =
                        Value::Hash(Rc::new(crate::value::HashData::from(ValueMap::default())));
                    provided |= bit(i);
                }
            }
        }
        if m.has_block {
            if let Some(b) = block {
                values[n] = b;
                provided |= bit(n);
            }
        }
        let _ = recv;
        Ok((values, provided))
    }

    /// Allocate an instance and run its initializer.
    /// For `new` on a class method's receiver: the class the receiver
    /// names (`class` or a subclass) and the `initialize` to run, the
    /// nearest one declared between it and `class`, else `init`.
    pub fn receiver_class_init(
        &self,
        recv: &Value,
        class: ClassId,
        init: Option<MethodId>,
    ) -> (ClassId, Option<MethodId>) {
        let cid = match recv {
            Value::Class(c) => *c,
            _ => class,
        };
        if cid == class {
            return (cid, init);
        }
        for anc in &self.program.world.class(cid).ancestors {
            if *anc == class {
                break;
            }
            // A module's `initialize` makes only a class with no fields
            // to assign (docs/01 §3), as the checker has it.
            if self.program.world.class(*anc).kind == RtClassKind::Module
                && !self.program.world.class(cid).module_init
            {
                continue;
            }
            if let Some(ids) = self.program.world.class(*anc).methods.get("initialize") {
                let pick = init
                    .and_then(|i| {
                        ids.iter().copied().find(|id| {
                            self.same_signature(*id, i)
                                || self.program.method(*id).overrides.contains(&i)
                        })
                    })
                    .or_else(|| ids.first().copied());
                return (cid, pick);
            }
        }
        (cid, init)
    }

    pub fn construct(
        &self,
        class: ClassId,
        init: Option<MethodId>,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
    ) -> EvalResult {
        let info = self.program.world.class(class);
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
        let obj = Object::new(class, smallvec![Value::Nil; info.fields.len()]);
        let value = Value::Object(obj.clone());
        let made = (|| {
            // Field defaults (data types evaluate them in their constructor).
            if !matches!(info.kind, RtClassKind::Data | RtClassKind::Variant) {
                for (i, f) in info.ivars.iter().enumerate() {
                    if let Some(d) = f.default {
                        let v = self.run_init(d, value.clone(), info.file)?;
                        self.logical_set(&obj, i, v);
                    }
                }
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

    /// `===` for `case/when`.
    pub fn case_eq(&self, pattern: &Value, v: &Value) -> Result<bool, Flow> {
        match pattern {
            Value::Class(cid) => Ok(self.program.world.class_is_a(self.class_of(v), *cid)),
            Value::Range(r) => self.range_covers(r, v),
            Value::Regexp(re) => Ok(match v {
                Value::Bytes(b) => re.for_bytes().map_err(|e| self.err_arg(e))?.is_match(b),
                _ => v.as_str().is_some_and(|s| re.regex.is_match(s.as_bytes())),
            }),
            Value::Proc(_) => Ok(self.call_block(pattern, smallvec![v.clone()])?.is_truthy()),
            _ => self.values_equal(pattern, v),
        }
    }

    pub fn range_covers(&self, r: &RangeVal, v: &Value) -> Result<bool, Flow> {
        use std::cmp::Ordering;
        if !r.lo.is_nil() {
            match self.compare(&r.lo, v) {
                Ok(Ordering::Greater) => return Ok(false),
                Ok(_) => {}
                Err(_) => return Ok(false),
            }
        }
        if !r.hi.is_nil() {
            match self.compare(v, &r.hi) {
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
                if let Some(mid) = self.has_user_method(v, "to_s", 0) {
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
            if let Some(mid) = self.has_user_method(v, "inspect", 0) {
                let r = self.invoke(mid, v.clone(), smallvec![], vec![], None)?;
                return Ok(self.to_s(&r)?.to_string());
            }
        }
        self.format_value(v, true)
    }

    pub(crate) fn format_value(&self, v: &Value, inspect: bool) -> Result<String, Flow> {
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
            Value::ArrayBuilder(a) => {
                let mut parts = Vec::new();
                for x in a.borrow().iter() {
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
            Value::Scope(_) => "#<Scope>".to_string(),
            Value::Atom(a) => {
                let v = sched::lock(a).clone();
                format!("#<Atom {}>", self.inspect(&v)?)
            }
            Value::Selector(_) => "#<Selector>".to_string(),
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
                IoKind::Socket(_) | IoKind::Listener(_) | IoKind::Udp(_) => {
                    natives::net::inspect_socket(self, io)
                }
            },
            Value::Random(r) => format!("#<Random seed={}>", r.borrow().seed),
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
        if let Value::Object(_) = a {
            if let Some(mid) = self.has_user_method(a, "==", 1) {
                let r = self.invoke(mid, a.clone(), smallvec![b.clone()], vec![], None)?;
                return Ok(r.is_truthy());
            }
        }
        // An element's or field's own `==` (`crate::keys`) may raise.
        let eq = a == b;
        crate::keys::check()?;
        Ok(eq)
    }

    /// `a <=> b` as an ordering, raising when incomparable.
    pub fn compare(&self, a: &Value, b: &Value) -> Result<std::cmp::Ordering, Flow> {
        use std::cmp::Ordering;
        match (a, b) {
            (Value::Int(x), Value::Int(y)) => return Ok(x.cmp(y)),
            (Value::Float(x), Value::Float(y)) => return Ok(float_order(*x, *y)),
            (Value::Int(x), Value::Float(y)) => return Ok(float_order(*x as f64, *y)),
            (Value::Float(x), Value::Int(y)) => return Ok(float_order(*x, *y as f64)),
            (Value::Str(_) | Value::Short(_), Value::Str(_) | Value::Short(_)) => {
                return Ok(a.as_str().unwrap_or("").cmp(b.as_str().unwrap_or("")))
            }
            (Value::Symbol(x), Value::Symbol(y)) => {
                return Ok(self.symbol_name(*x).cmp(&self.symbol_name(*y)))
            }
            (Value::Duration(x), Value::Duration(y)) => return Ok(x.cmp(y)),
            (Value::Bytes(x), Value::Bytes(y)) => return Ok(x.cmp(y)),
            (Value::Time(x), Value::Time(y)) => return Ok(x.ns.cmp(&y.ns)),
            (Value::Array(x), Value::Array(y)) => {
                for (p, q) in x.iter().zip(y.iter()) {
                    let o = self.compare(&p, &q)?;
                    if o != Ordering::Equal {
                        return Ok(o);
                    }
                }
                return Ok(x.len().cmp(&y.len()));
            }
            _ => {}
        }
        let r = self.send(a, "<=>", smallvec![b.clone()], None)?;
        match r {
            Value::Int(i) => Ok(i.cmp(&0)),
            _ => Err(self.err_arg(&format!(
                "comparison of {} with {} failed",
                self.class_name(a),
                self.class_name(b)
            ))),
        }
    }

    /// Sort with a fallible comparator.
    pub fn sort_values(
        &self,
        items: &mut [Value],
        mut cmp: impl FnMut(&Value, &Value) -> Result<std::cmp::Ordering, Flow>,
    ) -> Result<(), Flow> {
        let mut error = None;
        items.sort_by(|a, b| {
            if error.is_some() {
                return std::cmp::Ordering::Equal;
            }
            match cmp(a, b) {
                Ok(o) => o,
                Err(e) => {
                    error = Some(e);
                    std::cmp::Ordering::Equal
                }
            }
        });
        match error {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    pub fn write_out(&self, s: &str) {
        self.write_out_bytes(s.as_bytes());
    }

    pub fn write_out_bytes(&self, bytes: &[u8]) {
        use std::io::Write;
        let _ = lock(&self.global.stdout).write_all(bytes);
    }
}

/// Convert the result of a task body into its exit.
/// How a compile-time run ended other than normally (`Interp::run_static`).
pub enum StaticEnd {
    Raised(Value),
    Exited(i32),
}

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
                &format!("unexpected control flow: {other:?}"),
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
