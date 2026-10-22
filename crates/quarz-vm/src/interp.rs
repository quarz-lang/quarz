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
    ClassId, Constant, FuncId, Function, MethodId, RtClassKind, RtParamKind, RtSynth, RtType,
    RtWorld, Unit,
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

/// Apply an operator to two numbers directly. `None` means the generic
/// path must be taken (overflow, division by zero, other types).
#[inline]
pub fn fast_binop(op: FastOp, a: &Value, b: &Value) -> Option<Value> {
    use std::cmp::Ordering;
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
                FastOp::Cmp => Value::Int(x.partial_cmp(&y).unwrap_or(Ordering::Equal) as i64),
            })
        }
        _ => None,
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
    at_exit: std::sync::Mutex<Vec<SharedValue>>,
    stdout: std::sync::Mutex<Box<dyn std::io::Write + Send>>,
    /// The worker threads that run the tasks.
    pub workers: std::sync::Arc<sched::Workers>,
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
            at_exit: std::sync::Mutex::new(Vec::new()),
            stdout: std::sync::Mutex::new(out),
        }
    }
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
    pub funcs: Rc<RefCell<Vec<Rc<Function>>>>,
    /// Materialized constant pools, by function id.
    pub pools: Pools,
    /// Machine-code bodies, by function id (`None` = interpret).
    pub compiled: Rc<RefCell<Vec<Option<CompiledFn>>>>,
}

impl SharedState {
    /// State for a program run by one worker (the REPL, a helper thread).
    pub fn new(out: Box<dyn std::io::Write + Send>) -> SharedState {
        SharedState::with_threads(out, 1)
    }

    /// State for a program whose tasks run on `threads` workers.
    pub fn with_threads(out: Box<dyn std::io::Write + Send>, threads: usize) -> SharedState {
        SharedState::for_worker(std::sync::Arc::new(Global::new(out, threads)), 0)
    }

    /// The state of worker `worker` of the program `global` belongs to.
    /// Each worker numbers its tags in a range of its own: a flow's tag
    /// must not match one another worker gave out (a task's block may
    /// have been made on another worker).
    pub fn for_worker(global: std::sync::Arc<Global>, worker: u32) -> SharedState {
        let workers = global.workers.clone();
        SharedState {
            global,
            sched: Rc::new(RefCell::new(Scheduler::new(worker, workers))),
            next_tag: Rc::new(Cell::new((u64::from(worker) << 48) | 1)),
            repl_frame: None,
            funcs: Rc::new(RefCell::new(Vec::new())),
            pools: Rc::new(RefCell::new(Vec::new())),
            compiled: Rc::new(RefCell::new(Vec::new())),
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
    pub eof_error: ClassId,
    pub not_implemented: ClassId,
    pub system_exit: ClassId,
    pub range_error: ClassId,
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

#[repr(C)]
/// What the interpreter derives from the program when it loads it, and
/// never changes: the part that the worker threads of an M:N scheduler
/// are to share (it is `Send + Sync`, checked below).
pub struct Program {
    pub world: RtWorld,
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
    /// The `self` object of each unit's top level, by file index.
    unit_selfs: Vec<Value>,
    /// The frame of the REPL's top level, kept across inputs.
    pub repl_frame: Option<Rc<Frame>>,
    pub funcs: Rc<RefCell<Vec<Rc<Function>>>>,
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
    /// Backtraces also walk the native stack for compiled frames that
    /// push no activation (typed entries of the LLVM backend).
    pub native_bt: Cell<bool>,
    /// The flow being returned from compiled code (see `vm.rs`).
    pub pending_flow: RefCell<Option<Flow>>,
    /// Register files of more than the inline 16, kept empty for the
    /// next interpreted call that needs one (an allocation per call
    /// otherwise).
    pub reg_pool: RefCell<Vec<Vec<Value>>>,
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
        let structural: Vec<bool> = world.classes.iter().map(|c| c.structural).collect();
        STRUCTURAL_CLASSES.with(|s| *s.borrow_mut() = structural);

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
                        Constant::BigInt { digits, base } => parse_int(digits, *base),
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

        let registry = natives::registry();
        let natives: Vec<Option<NativeFn>> = world
            .methods
            .iter()
            .map(|m| {
                m.native_key
                    .as_deref()
                    .and_then(|k| registry.get(k).copied())
            })
            .collect();
        let fast_registry = natives::fast_registry();
        let fast_natives: Vec<Option<FastNativeFn>> = world
            .methods
            .iter()
            .map(|m| {
                m.native_key
                    .as_deref()
                    .and_then(|k| fast_registry.get(k).copied())
            })
            .collect();
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
        let mut nvslots = 0usize;
        let vslots: Vec<u32> = world
            .methods
            .iter()
            .map(|m| {
                if m.overridden && !m.singleton && !m.is_extension {
                    nvslots += 1;
                    (nvslots - 1) as u32
                } else {
                    u32::MAX
                }
            })
            .collect();
        let owned_registry = natives::owned_registry();
        let natives_owned: Vec<Option<OwnedNativeFn>> = world
            .methods
            .iter()
            .map(|m| {
                m.native_key
                    .as_deref()
                    .and_then(|k| owned_registry.get(k).copied())
            })
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
        let owned = OwnedIds {
            array_push: owned_id("Array#push"),
            array_set: owned_id("Array#set"),
            hash_put: owned_id("Hash#put"),
            hash_delete: owned_id("Hash#delete"),
            set_add: owned_id("Set#add"),
            set_delete: owned_id("Set#delete"),
        };
        let class_by_name = |name: &str| -> ClassId {
            world
                .class_by_name(name)
                .unwrap_or_else(|| panic!("prelude does not define {name}"))
        };
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
            eof_error: class_by_name("EOFError"),
            not_implemented: class_by_name("NotImplementedError"),
            system_exit: class_by_name("SystemExit"),
            range_error: class_by_name("RangeError"),
            system_stack: class_by_name("SystemStackError"),
        };
        let rt = RtClasses {
            selector: class_by_name("Selector"),
            enumerator: class_by_name("Enumerator"),
            io: class_by_name("IO"),
            tcp_socket: class_by_name("TCPSocket"),
            tcp_server: class_by_name("TCPServer"),
            udp_socket: class_by_name("UDPSocket"),
            unix_socket: class_by_name("UNIXSocket"),
            unix_server: class_by_name("UNIXServer"),
            random: class_by_name("Random"),
            file: class_by_name("File"),
            math: class_by_name("Math"),
            process: class_by_name("Process"),
            result_ok: class_by_name("Result::Ok"),
            result_err: class_by_name("Result::Err"),
        };
        let n_files = world
            .file_names
            .len()
            .max(units.iter().map(|u| u.file as usize + 1).max().unwrap_or(0));
        let mut unit_selfs = vec![Value::Nil; n_files];
        for u in &units {
            // Every task calling a top-level method uses it: immortal, so
            // that workers do not contend for its count.
            let v = Value::Object(Object::new(u.main_class, Fields::new()));
            v.make_immortal();
            unit_selfs[u.file as usize] = v;
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
        let program = std::sync::Arc::new(Program {
            world,
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
            unit_selfs,
            repl_frame,
            funcs: state.funcs,
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
            native_bt: Cell::new(false),
            pending_flow: RefCell::new(None),
            reg_pool: RefCell::new(Vec::new()),
            self_rc: RefCell::new(Weak::new()),
            root_task: Cell::new(None),
        });
        *interp.self_rc.borrow_mut() = std::rc::Rc::downgrade(&interp);
        interp
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
                let self_val = me.unit_selfs[unit.file as usize].clone();
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
        let code = self.run_loop(&root);
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

    /// Run the `at_exit` blocks, the last registered first (and any they
    /// register), each as the root task of a run of its own, as Ruby does
    /// when the main program ends, also by `exit` or an exception. An
    /// exception in one is reported; a block that exits or fails sets the
    /// exit code.
    fn run_at_exit(self: &std::rc::Rc<Interp>, mut code: i32) -> i32 {
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
            let c = self.run_loop(&root);
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
            let self_val = me
                .unit_selfs
                .get(file as usize)
                .cloned()
                .unwrap_or(Value::Nil);
            let result = me.run_top_level(fid, file, self_val);
            task_exit(&me, result)
        });
        let root =
            self.sched
                .borrow_mut()
                .spawn(run_body, None, "repl".to_string(), 256 * 1024 * 1024);
        let code = self.run_loop(&root);
        self.flush();
        if code != 0 && !root.is_done() {
            return Err(code);
        }
        let result = root.result();
        match result {
            Some(TaskResult::Value(v)) => Ok(Some(v)),
            Some(TaskResult::Error(_)) => Ok(None),
            None => Err(code),
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

    /// Spawn a task running the closure.
    /// Start a task running `closure` (marked shared: it may run on
    /// another worker), on the worker `Workers::place` picks.
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
        let target = workers.place(here);
        if target == here {
            let body = self.task_body(closure);
            return self
                .sched
                .borrow_mut()
                .spawn(body, scope, name.to_string(), sched::TASK_STACK);
        }
        self.start_worker(target);
        let handle = TaskHandle::new(target, workers.reserve_id(target), scope, name.to_string());
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
        let result = sched::resume(&task, &mut co);
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
    /// running the tasks placed there until the program ends.
    fn start_worker(&self, w: u32) {
        let global = self.global.clone();
        if !global.workers.claim_start(w) {
            return;
        }
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
                    Interp::worker_main(global, w, image, argv, native_bt)
                });
                if std::panic::catch_unwind(run).is_err() {
                    std::process::exit(101);
                }
            })
            .expect("start a worker thread");
    }

    /// The body of worker `w`'s thread (see `start_worker`).
    fn worker_main(
        global: std::sync::Arc<Global>,
        w: u32,
        image: std::sync::Arc<crate::transfer::ProgramImage>,
        argv: Vec<String>,
        native_bt: bool,
    ) {
        let state = SharedState::for_worker(global, w);
        let interp = Interp::with_state(
            image.world.clone(),
            0,
            image.functions.clone(),
            image.units.clone(),
            argv,
            state,
        );
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
            let r = me.call_block(&closure, smallvec![]);
            match r {
                Ok(v) => TaskExit::Result(TaskResult::Value(v)),
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
        if task.take_cancel() {
            return Err(self.raise(self.program.exc.cancelled, "task cancelled"));
        }
        Ok(())
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

    pub fn yield_now(&self) {
        self.sched.borrow_mut().requeue_current();
        sched::suspend_raw();
    }

    pub fn wake(&self, id: TaskId) {
        self.sched.borrow_mut().wake(id);
    }

    /// Wake a task, whichever worker runs it.
    pub fn wake_ref(&self, r: sched::TaskRef) {
        self.sched.borrow_mut().wake_ref(r);
    }

    pub fn sleep(&self, d: Duration) -> Result<(), Flow> {
        let id = self.current_task().id;
        self.sched.borrow_mut().add_timer(d, id);
        self.park()
    }

    /// Wait for a task to finish and return its result (re-raising its
    /// exception).
    pub fn await_task(&self, task: &Rc<TaskHandle>) -> EvalResult {
        loop {
            if task.is_done() {
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
                joiners.push(self.sched.borrow().current_ref());
            }
            self.park()?;
        }
    }

    pub fn cancel_task(&self, task: &Rc<TaskHandle>) {
        if task.is_done() {
            return;
        }
        task.set_cancel_requested(true);
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
            o.init_exc(
                ExcInfo {
                    backtrace: Some(Rc::new(bt)),
                    cause: None,
                },
                false,
            );
            o
        })
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

    pub fn err_type(&self, message: &str) -> Flow {
        self.raise(self.program.exc.type_error, message)
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
            Value::Object(o) => {
                // Raised before: its first backtrace stays.
                if o.exc_info().is_none() {
                    let bt = self.capture_backtrace();
                    let info = ExcInfo {
                        backtrace: Some(Rc::new(bt)),
                        cause: None,
                    };
                    o.init_exc(info, Rc::is_shared(&o));
                }
                Value::Object(o)
            }
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
            Value::Int(_) | Value::BigInt(_) => b.int,
            Value::Float(_) => b.float,
            Value::Str(_) | Value::Short(_) => b.string,
            Value::Symbol(_) => b.symbol,
            Value::Array(_) => b.array,
            Value::Hash(_) => b.hash,
            Value::Set(_) => b.set,
            Value::Range(_) => b.range,
            Value::Regexp(_) => b.regexp,
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
                // SAFETY: a short read, copying values.
                let vals: Fields = unsafe { o.fields_ref() }
                    .get(slot..slot + n)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_else(|| smallvec![Value::Nil; n]);
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
                // SAFETY: a short write copying values; `src` is a value
                // of class `d`, so not `o` itself.
                let (fields, src_fields) = unsafe { (o.fields_mut(), src.fields_ref()) };
                for k in 0..n {
                    if let (Some(dst), Some(x)) = (fields.get_mut(slot + k), src_fields.get(k)) {
                        *dst = x.clone();
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
                        // SAFETY: a short read, copying values.
                        for (k, x) in unsafe { src.fields_ref() }.iter().take(n).enumerate() {
                            if slot + k < out.len() {
                                out[slot + k] = x.clone();
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// `value.is_a?(type)`, ignoring type arguments.
    pub fn is_a(&self, v: &Value, ty: &RtType) -> bool {
        match ty {
            RtType::Nothing => false,
            RtType::Class(cid) => self.program.world.class_is_a(self.class_of(v), *cid),
            RtType::ClassObject => matches!(v, Value::Class(_)),
            RtType::Union(ms) => ms.iter().any(|m| self.is_a(v, m)),
            RtType::Tuple(n) => matches!(v, Value::Array(a) if a.len() == *n as usize),
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
                    waiters.push(me);
                    drop(state);
                    self.park()?;
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
            None => self
                .unit_selfs
                .get(info.file as usize)
                .cloned()
                .unwrap_or(Value::Nil),
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
        let m = self.program.world.method(mid);
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
        let m = self.program.world.method(mid);
        let (min, max) = m.positional_arity();
        // A class method of the same name that accepts less is an
        // overload, not an override.
        let accepts = |c: MethodId| {
            let cm = self.program.world.method(c);
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
        let m = self.program.world.method(mid);
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
                        || self.program.world.method(*id).overrides.contains(&mid)
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

    /// A method of `cid` (or of an ancestor before the owner of `mid`)
    /// that overrides `mid`: same name, and the same signature when the
    /// name is overloaded.
    fn find_override(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        let m = self.program.world.method(mid);
        let (min, max) = m.positional_arity();
        for anc in &self.program.world.class(cid).ancestors {
            let anc = *anc;
            if anc == m.owner {
                return None;
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
                let cm = self.program.world.method(*c);
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
                .find(|c| self.program.world.method(**c).overrides.contains(&mid))
            {
                return Some(*o);
            }
        }
        None
    }

    fn same_signature(&self, a: MethodId, b: MethodId) -> bool {
        let (a, b) = (self.program.world.method(a), self.program.world.method(b));
        a.params.len() == b.params.len()
            && a.params.iter().zip(&b.params).all(|(p, q)| {
                p.kind == q.kind && (p.ty == q.ty || p.ty.is_none() || q.ty.is_none())
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
                    let m = self.program.world.method(*id);
                    let (min, max) = m.positional_arity();
                    if min <= argc && argc <= max && (m.has_block == with_block) {
                        found = Some(*id);
                        break 'outer;
                    }
                    fallback.get_or_insert(*id);
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
        let m = self.program.world.method(mid);
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
        let m = self.program.world.method(mid);
        if let Some(native) = self.program.natives[mid as usize] {
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
                crate::value::unique_mut(s).shift_remove(*v);
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
        let m = self.program.world.method(mid);
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
        let m = self.program.world.method(mid);
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
            if let Some(ids) = self.program.world.class(*anc).methods.get("initialize") {
                let pick = init
                    .and_then(|i| {
                        ids.iter().copied().find(|id| {
                            self.same_signature(*id, i)
                                || self.program.world.method(*id).overrides.contains(&i)
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
            if self.program.world.methods[i as usize].synth == RtSynth::DataInit
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
        let mut pattern = String::new();
        let mut inline = String::new();
        if flags.contains('i') {
            inline.push('i');
        }
        if flags.contains('m') {
            inline.push('s');
        }
        if flags.contains('x') {
            inline.push('x');
        }
        if !inline.is_empty() {
            pattern.push_str(&format!("(?{inline})"));
        }
        // Ruby's `\A`/`\z` are the same; `\h` is a hex digit.
        pattern.push_str(&source.replace("\\h", "[0-9a-fA-F]"));
        match regex::Regex::new(&pattern) {
            Ok(regex) => Ok(Value::Regexp(Rc::new(RegexpVal {
                regex,
                source: source.to_string(),
                flags: flags.to_string(),
            }))),
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
            Value::Regexp(re) => Ok(v.as_str().is_some_and(|s| re.regex.is_match(s))),
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
            Value::Object(o) => {
                if let Some(mid) = self.has_user_method(v, "to_s", 0) {
                    let r = self.invoke(mid, v.clone(), smallvec![], vec![], None)?;
                    return Ok(Cow::Owned(self.to_s(&r)?.into_owned()));
                }
                if self.program.world.is_exception_class(o.class) {
                    return Ok(Cow::Owned(self.exception_message(v)));
                }
                Ok(Cow::Owned(self.inspect(v)?))
            }
            _ => Ok(Cow::Owned(self.format_value(v, false)?)),
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

    fn format_value(&self, v: &Value, inspect: bool) -> Result<String, Flow> {
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
                        format!(":{}", inspect_str(&name))
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
            Value::HashBuilder(h) => self.format_hash(h.borrow().iter())?,
            Value::Set(s) => {
                let mut parts = Vec::new();
                for x in s.iter() {
                    parts.push(self.inspect(x)?);
                }
                format!("Set[{}]", parts.join(", "))
            }
            Value::SetBuilder(s) => {
                let mut parts = Vec::new();
                for x in s.borrow().iter() {
                    parts.push(self.inspect(x)?);
                }
                format!("Set[{}]", parts.join(", "))
            }
            Value::Range(r) => format!(
                "{}{}{}",
                self.inspect(&r.lo)?,
                if r.exclusive { "..." } else { ".." },
                self.inspect(&r.hi)?
            ),
            Value::Regexp(r) => format!("/{}/{}", r.source, r.flags),
            Value::MatchData(m) => {
                let group = |k: usize| -> String {
                    match m.groups.get(k).copied().flatten() {
                        Some((s, e)) => inspect_str(&m.text[s..e]),
                        None => "nil".to_string(),
                    }
                };
                let mut out = format!("#<MatchData {}", group(0));
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
        Ok(a == b)
    }

    /// `a <=> b` as an ordering, raising when incomparable.
    pub fn compare(&self, a: &Value, b: &Value) -> Result<std::cmp::Ordering, Flow> {
        use std::cmp::Ordering;
        match (a, b) {
            (Value::Int(x), Value::Int(y)) => return Ok(x.cmp(y)),
            (Value::Float(x), Value::Float(y)) => {
                return Ok(x.partial_cmp(y).unwrap_or(Ordering::Equal))
            }
            (Value::Int(x), Value::Float(y)) => {
                return Ok((*x as f64).partial_cmp(y).unwrap_or(Ordering::Equal))
            }
            (Value::Float(x), Value::Int(y)) => {
                return Ok(x.partial_cmp(&(*y as f64)).unwrap_or(Ordering::Equal))
            }
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
pub(crate) fn task_exit(interp: &Interp, result: EvalResult) -> TaskExit {
    match result {
        Ok(v) => TaskExit::Result(TaskResult::Value(v)),
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
pub fn parse_int(digits: &str, base: u8) -> Value {
    let (neg, digits) = match digits.strip_prefix('-') {
        Some(d) => (true, d),
        None => (false, digits),
    };
    match i64::from_str_radix(digits, base as u32) {
        Ok(v) => Value::Int(if neg { -v } else { v }),
        Err(_) => {
            use num_bigint::BigInt;
            use num_traits::Num;
            let b = BigInt::from_str_radix(digits, base as u32).unwrap_or_default();
            int_from_big(if neg { -b } else { b })
        }
    }
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
            '#' => out.push('#'),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\x{:02X}", c as u32)),
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
