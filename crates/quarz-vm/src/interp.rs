//! The runtime: method invocation, dynamic dispatch, exceptions, the task
//! run loop, and conversions used by the natives. Function bodies are QIR
//! (see `vm.rs`); compiled code uses the same runtime.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use rustc_hash::FxHashMap;
use smallvec::{smallvec, SmallVec};
use std::rc::{Rc, Weak};
use std::time::Duration;

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

/// A native that takes ownership of the receiver so that it can update a
/// uniquely referenced value in place. On failure it hands the receiver
/// back so the caller can restore it.
pub type OwnedNativeFn = fn(&Interp, Value, Args) -> Result<Value, (Flow, Value)>;

/// Key of the by-name method cache: class, arity, block given (the name
/// is the inner key, so lookups do not allocate).
type NameKey = (ClassId, usize, bool);

/// Apply an operator to two numbers directly. `None` means the generic
/// path must be taken (overflow, division by zero, other types).
#[inline]
pub fn fast_binop(op: FastOp, a: &Value, b: &Value) -> Option<Value> {
    use std::cmp::Ordering;
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => {
            let (x, y) = (*x, *y);
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

/// Run-time state that outlives one interpreter instance (the REPL creates
/// an interpreter per input over the same state).
#[derive(Clone)]
pub struct SharedState {
    pub symbols: Rc<RefCell<SymbolTable>>,
    pub consts: Rc<RefCell<Vec<Option<Value>>>>,
    pub variant_singletons: Rc<RefCell<HashMap<ClassId, Value>>>,
    pub sched: Rc<RefCell<Scheduler>>,
    pub next_tag: Rc<Cell<u64>>,
    pub at_exit: Rc<RefCell<Vec<Value>>>,
    pub stdout: Rc<RefCell<Box<dyn std::io::Write>>>,
    pub repl_frame: Option<Rc<Frame>>,
    /// Every function loaded so far, by id (append-only).
    pub funcs: Rc<RefCell<Vec<Rc<Function>>>>,
    /// Materialized constant pools, by function id.
    pub pools: Pools,
    /// Machine-code bodies, by function id (`None` = interpret).
    pub compiled: Rc<RefCell<Vec<Option<CompiledFn>>>>,
}

impl SharedState {
    pub fn new(out: Box<dyn std::io::Write>) -> SharedState {
        SharedState {
            symbols: Rc::new(RefCell::new(SymbolTable::default())),
            consts: Rc::new(RefCell::new(Vec::new())),
            variant_singletons: Rc::new(RefCell::new(HashMap::new())),
            sched: Rc::new(RefCell::new(Scheduler::new())),
            next_tag: Rc::new(Cell::new(1)),
            at_exit: Rc::new(RefCell::new(Vec::new())),
            stdout: Rc::new(RefCell::new(out)),
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
    pub file: ClassId,
    pub math: ClassId,
    pub process: ClassId,
    pub result_ok: ClassId,
    pub result_err: ClassId,
}

pub struct Interp {
    pub world: RtWorld,
    /// Compilation units in execution order.
    pub units: Vec<Unit>,
    /// The `self` object of each unit's top level, by file index.
    unit_selfs: Vec<Value>,
    /// The frame of the REPL's top level, kept across inputs.
    pub repl_frame: Option<Rc<Frame>>,
    pub funcs: Rc<RefCell<Vec<Rc<Function>>>>,
    pub pools: Pools,
    pub compiled: Rc<RefCell<Vec<Option<CompiledFn>>>>,
    pub symbols: Rc<RefCell<SymbolTable>>,
    consts: Rc<RefCell<Vec<Option<Value>>>>,
    variant_singletons: Rc<RefCell<HashMap<ClassId, Value>>>,
    pub natives: Vec<Option<NativeFn>>,
    pub natives_owned: Vec<Option<OwnedNativeFn>>,
    field_indices: Vec<FxHashMap<String, usize>>,
    pub sched: Rc<RefCell<Scheduler>>,
    dispatch_cache: RefCell<FxHashMap<(ClassId, MethodId), MethodId>>,
    name_cache: RefCell<FxHashMap<NameKey, FxHashMap<String, Option<MethodId>>>>,
    next_tag: Rc<Cell<u64>>,
    pub argv: Vec<String>,
    pub exc: ExcClasses,
    pub rt: RtClasses,
    /// The activations in progress, innermost last (all tasks share the
    /// vector; entries are tagged with their task). Raw pointers: an
    /// activation lives on the Rust stack for the duration of its call.
    pub call_stack: RefCell<Vec<*const crate::vm::Activation>>,
    /// The task being run by the scheduler.
    pub current_task_id: Cell<TaskId>,
    pub at_exit: Rc<RefCell<Vec<Value>>>,
    pub stdout: Rc<RefCell<Box<dyn std::io::Write>>>,
    /// The flow being returned from compiled code (see `vm.rs`).
    pub pending_flow: RefCell<Option<Flow>>,
    self_rc: RefCell<Weak<Interp>>,
    pub root_task: Cell<Option<TaskId>>,
}

impl Interp {
    pub fn new(module: quarz_ir::Module, argv: Vec<String>) -> Rc<Interp> {
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
        out: Box<dyn std::io::Write>,
    ) -> Rc<Interp> {
        let state = SharedState::new(out);
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
    ) -> Rc<Interp> {
        let structural: Vec<bool> = world.classes.iter().map(|c| c.structural).collect();
        STRUCTURAL_CLASSES.with(|s| *s.borrow_mut() = structural);

        // Load the functions.
        {
            let mut funcs = state.funcs.borrow_mut();
            let mut pools = state.pools.borrow_mut();
            let mut compiled = state.compiled.borrow_mut();
            assert_eq!(funcs.len(), base as usize, "functions loaded out of order");
            let mut symbols = state.symbols.borrow_mut();
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
        let field_indices: Vec<FxHashMap<String, usize>> = world
            .classes
            .iter()
            .map(|c| {
                c.fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (f.name.clone(), i))
                    .collect()
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
            unit_selfs[u.file as usize] = Value::Object(Rc::new(Object {
                class: u.main_class,
                fields: RefCell::new(Fields::new()),
                backtrace: RefCell::new(None),
                cause: RefCell::new(None),
            }));
        }
        let n_consts = world.consts.len();
        {
            let mut consts = state.consts.borrow_mut();
            if consts.len() < n_consts {
                consts.resize(n_consts, None);
            }
        }
        let repl_frame = state.repl_frame.clone();
        let interp = Rc::new(Interp {
            world,
            units,
            unit_selfs,
            repl_frame,
            funcs: state.funcs,
            pools: state.pools,
            compiled: state.compiled,
            symbols: state.symbols,
            consts: state.consts,
            variant_singletons: state.variant_singletons,
            natives,
            natives_owned,
            field_indices,
            sched: state.sched,
            dispatch_cache: RefCell::new(FxHashMap::default()),
            name_cache: RefCell::new(FxHashMap::default()),
            next_tag: state.next_tag,
            argv,
            exc,
            rt,
            call_stack: RefCell::new(Vec::new()),
            current_task_id: Cell::new(0),
            at_exit: state.at_exit,
            stdout: state.stdout,
            pending_flow: RefCell::new(None),
            self_rc: RefCell::new(Weak::new()),
            root_task: Cell::new(None),
        });
        *interp.self_rc.borrow_mut() = Rc::downgrade(&interp);
        interp
    }

    pub fn rc(&self) -> Rc<Interp> {
        self.self_rc
            .borrow()
            .upgrade()
            .expect("interpreter dropped")
    }

    pub fn intern(&self, name: &str) -> Symbol {
        self.symbols.borrow_mut().intern(name)
    }

    pub fn symbol_name(&self, sym: Symbol) -> Rc<str> {
        self.symbols.borrow().name(sym).clone()
    }

    pub fn new_tag(&self) -> u64 {
        let t = self.next_tag.get();
        self.next_tag.set(t + 1);
        t
    }

    pub fn file_name(&self, file: u32) -> &str {
        self.world
            .file_names
            .get(file as usize)
            .map(String::as_str)
            .unwrap_or("?")
    }

    // ----- running ---------------------------------------------------------------

    /// Run the main program as the root task. Returns the exit code.
    pub fn run(self: &Rc<Interp>) -> i32 {
        let me = self.clone();
        let body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
            let mut result = Ok(Value::Nil);
            for unit in me.units.iter() {
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
        self.flush();
        code
    }

    /// The shared state, for creating another interpreter over it.
    pub fn shared_state(&self) -> SharedState {
        SharedState {
            symbols: self.symbols.clone(),
            consts: self.consts.clone(),
            variant_singletons: self.variant_singletons.clone(),
            sched: self.sched.clone(),
            next_tag: self.next_tag.clone(),
            at_exit: self.at_exit.clone(),
            stdout: self.stdout.clone(),
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
    pub fn run_repl(self: &Rc<Interp>, file: u32, fid: FuncId) -> Result<Option<Value>, i32> {
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
        let result = root.result.borrow().clone();
        match result {
            Some(TaskResult::Value(v)) => Ok(Some(v)),
            Some(TaskResult::Error(_)) => Ok(None),
            None => Err(code),
        }
    }

    fn run_loop(&self, root: &Rc<TaskHandle>) -> i32 {
        loop {
            let next = self.sched.borrow_mut().next_runnable();
            let Some((id, mut co)) = next else {
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
            };
            let task = self.sched.borrow().task(id).clone();
            self.current_task_id.set(id);
            let result = sched::resume(&task, &mut co);
            let exit = self.sched.borrow_mut().after_resume(id, co, result);
            if let Some(code) = exit {
                return code;
            }
            if root.is_done() {
                break;
            }
        }
        match root.result.borrow().clone() {
            Some(TaskResult::Error(exc)) => {
                self.flush();
                self.report_uncaught(&exc);
                1
            }
            _ => 0,
        }
    }

    pub fn flush(&self) {
        use std::io::Write;
        let _ = self.stdout.borrow_mut().flush();
    }

    fn report_uncaught(&self, exc: &Value) {
        let class_name = self.class_name(exc);
        let message = self.exception_message(exc);
        eprintln!("{class_name}: {message}");
        if let Value::Object(o) = exc {
            if let Some(bt) = o.backtrace.borrow().as_ref() {
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
    pub fn spawn_task(
        &self,
        closure: Value,
        scope: Option<Rc<ScopeInner>>,
        name: &str,
    ) -> Rc<TaskHandle> {
        let me = self.rc();
        let body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
            let r = me.call_block(&closure, smallvec![]);
            match r {
                Ok(v) => TaskExit::Result(TaskResult::Value(v)),
                Err(Flow::Raise(e)) => TaskExit::Result(TaskResult::Error(e)),
                Err(Flow::Exit(c)) => TaskExit::Exit(c),
                Err(other) => {
                    let e = me.make_exception(
                        me.exc.runtime_error,
                        &format!("unexpected control flow in task: {other:?}"),
                    );
                    TaskExit::Result(TaskResult::Error(e))
                }
            }
        });
        self.sched
            .borrow_mut()
            .spawn(body, scope, name.to_string(), 16 * 1024 * 1024)
    }

    /// Block the current task until woken, then check for cancellation.
    pub fn park(&self) -> Result<(), Flow> {
        let task = self.current_task();
        self.check_cancel(&task)?;
        task.state.set(sched::TaskState::Waiting);
        sched::suspend_raw();
        self.check_cancel(&task)
    }

    pub fn check_cancel(&self, task: &TaskHandle) -> Result<(), Flow> {
        if task.cancel_requested.get() {
            task.cancel_requested.set(false);
            return Err(self.raise(self.exc.cancelled, "task cancelled"));
        }
        Ok(())
    }

    pub fn yield_now(&self) {
        self.sched.borrow_mut().requeue_current();
        sched::suspend_raw();
    }

    pub fn wake(&self, id: TaskId) {
        self.sched.borrow_mut().wake(id);
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
                return match task.result.borrow().clone() {
                    Some(TaskResult::Value(v)) => Ok(v),
                    Some(TaskResult::Error(e)) => Err(Flow::Raise(e)),
                    None => Ok(Value::Nil),
                };
            }
            let me = self.current_task().id;
            task.joiners.borrow_mut().push(me);
            self.park()?;
        }
    }

    pub fn cancel_task(&self, task: &Rc<TaskHandle>) {
        if task.is_done() {
            return;
        }
        task.cancel_requested.set(true);
        self.wake(task.id);
    }

    // ----- exceptions ------------------------------------------------------------------

    pub fn make_exception(&self, class: ClassId, message: &str) -> Value {
        let n = self.world.class(class).fields.len().max(1);
        let mut fields: Fields = smallvec![Value::Nil; n];
        fields[0] = Value::str(message);
        let bt = self.capture_backtrace();
        Value::Object(Rc::new(Object {
            class,
            fields: RefCell::new(fields),
            backtrace: RefCell::new(Some(Rc::new(bt))),
            cause: RefCell::new(None),
        }))
    }

    /// The innermost frames of the current task's call stack, as
    /// `file:line:in name` (deep recursion is cut off).
    pub fn capture_backtrace(&self) -> Vec<String> {
        let stack = self.call_stack.borrow();
        let task = self.current_task_id.get();
        let funcs = self.funcs.borrow();
        let mut frames = 0;
        let mut bt = Vec::new();
        for p in stack.iter().rev() {
            // SAFETY: entries are removed before their activation ends.
            let act = unsafe { &**p };
            if act.task != task {
                continue;
            }
            frames += 1;
            if frames > 32 {
                continue;
            }
            let f = &funcs[act.fid as usize];
            bt.push(format!(
                "{}:{}:in {}",
                self.file_name(f.file),
                act.line.get(),
                f.name
            ));
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
        self.raise(self.exc.argument_error, message)
    }

    pub fn err_type(&self, message: &str) -> Flow {
        self.raise(self.exc.type_error, message)
    }

    pub fn err_index(&self, message: &str) -> Flow {
        self.raise(self.exc.index_error, message)
    }

    pub fn exception_message(&self, exc: &Value) -> String {
        match exc {
            Value::Object(o) => match o.fields.borrow().first() {
                Some(Value::Str(s)) => s.to_string(),
                _ => self.class_name(exc),
            },
            _ => String::new(),
        }
    }

    /// Whether an exception object is an instance of a class.
    pub fn exception_is_a(&self, exc: &Value, class: ClassId) -> bool {
        match exc {
            Value::Object(o) => self.world.class_is_a(o.class, class),
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
                    None => self.world.class(cid).name.clone(),
                };
                self.make_exception(cid, &msg)
            }
            Value::Str(s) => self.make_exception(self.exc.runtime_error, &s),
            Value::Object(o) => {
                if o.backtrace.borrow().is_none() {
                    let bt = self.capture_backtrace();
                    *o.backtrace.borrow_mut() = Some(Rc::new(bt));
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
        let b = &self.world.builtin;
        match v {
            Value::Nil => b.nil,
            Value::Bool(_) => b.bool_,
            Value::Int(_) | Value::BigInt(_) => b.int,
            Value::Float(_) => b.float,
            Value::Str(_) => b.string,
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
            Value::Selector(_) => self.rt.selector,
            Value::Duration(_) => b.duration,
            Value::Enumerator(_) => self.rt.enumerator,
            Value::Io(_) => self.rt.io,
            Value::Bytes(_) => b.bytes,
            Value::BytesBuilder(_) => b.bytes_builder,
            Value::Time(_) => b.time,
            Value::Flow(_) => b.object,
        }
    }

    pub fn class_name(&self, v: &Value) -> String {
        self.world.class(self.class_of(v)).name.clone()
    }

    pub fn field_index(&self, cid: ClassId, name: &str) -> Option<usize> {
        self.field_indices[cid as usize].get(name).copied()
    }

    /// `value.is_a?(type)`, ignoring type arguments.
    pub fn is_a(&self, v: &Value, ty: &RtType) -> bool {
        match ty {
            RtType::Nothing => false,
            RtType::Class(cid) => self.world.class_is_a(self.class_of(v), *cid),
            RtType::ClassObject => matches!(v, Value::Class(_)),
            RtType::Union(ms) => ms.iter().any(|m| self.is_a(v, m)),
            RtType::Tuple(n) => matches!(v, Value::Array(a) if a.len() == *n as usize),
            RtType::Proc => matches!(v, Value::Proc(_)),
            RtType::Any => true,
        }
    }

    pub fn variant_singleton(&self, cid: ClassId) -> Value {
        if let Some(v) = self.variant_singletons.borrow().get(&cid) {
            return v.clone();
        }
        let v = Value::Object(Rc::new(Object {
            class: cid,
            fields: RefCell::new(Fields::new()),
            backtrace: RefCell::new(None),
            cause: RefCell::new(None),
        }));
        self.variant_singletons.borrow_mut().insert(cid, v.clone());
        v
    }

    /// The value of a constant, evaluating its initializer on first use.
    pub fn const_value(&self, cid: u32) -> EvalResult {
        if let Some(v) = self.consts.borrow()[cid as usize].clone() {
            return Ok(v);
        }
        let info = &self.world.consts[cid as usize];
        let Some(init) = info.init else {
            return Ok(Value::Nil);
        };
        let self_val = match info.owner {
            Some(o) => Value::Class(o),
            None => self
                .unit_selfs
                .get(info.file as usize)
                .cloned()
                .unwrap_or(Value::Nil),
        };
        let v = self.run_init(init, self_val, info.file)?;
        self.consts.borrow_mut()[cid as usize] = Some(v.clone());
        Ok(v)
    }

    // ----- dispatch --------------------------------------------------------------------

    /// Find the implementation of a statically resolved method for the
    /// receiver's run-time class (subclass overrides).
    pub fn resolve_dynamic(&self, recv: &Value, mid: MethodId) -> MethodId {
        let m = self.world.method(mid);
        if m.singleton || m.is_extension {
            return mid;
        }
        let cid = self.class_of(recv);
        if cid == m.owner {
            return mid;
        }
        if let Some(found) = self.dispatch_cache.borrow().get(&(cid, mid)) {
            return *found;
        }
        let found = self.find_override(cid, mid).unwrap_or(mid);
        self.dispatch_cache.borrow_mut().insert((cid, mid), found);
        found
    }

    /// A method of `cid` (or of an ancestor before the owner of `mid`)
    /// that overrides `mid`: same name, and the same signature when the
    /// name is overloaded.
    fn find_override(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        let m = self.world.method(mid);
        let (min, max) = m.positional_arity();
        for anc in &self.world.class(cid).ancestors {
            let anc = *anc;
            if anc == m.owner {
                return None;
            }
            let mut candidates: Vec<MethodId> = Vec::new();
            for ext in &self.world.extensions {
                if ext.target == anc {
                    if let Some(ids) = ext.methods.get(&m.name) {
                        candidates.extend(ids);
                    }
                }
            }
            if let Some(ids) = self.world.class(anc).methods.get(&m.name) {
                candidates.extend(ids);
            }
            candidates.retain(|c| {
                let cm = self.world.method(*c);
                let (cmin, cmax) = cm.positional_arity();
                cm.has_block == m.has_block && cmin <= max && cmax >= min
            });
            if candidates.is_empty() {
                continue;
            }
            if let Some(exact) = candidates.iter().find(|c| self.same_signature(**c, mid)) {
                return Some(*exact);
            }
            if m.overloaded {
                // An override of one of the other overloads.
                continue;
            }
            return candidates
                .iter()
                .find(|c| self.world.method(**c).positional_arity() == (min, max))
                .or(candidates.first())
                .copied();
        }
        None
    }

    fn same_signature(&self, a: MethodId, b: MethodId) -> bool {
        let (a, b) = (self.world.method(a), self.world.method(b));
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
        'outer: for anc in &self.world.class(cid).ancestors {
            let anc = *anc;
            let mut lists: Vec<&Vec<MethodId>> = Vec::new();
            // Always-active extensions on this ancestor come first.
            for ext in &self.world.extensions {
                if ext.target == anc {
                    if let Some(ids) = ext.methods.get(name) {
                        lists.push(ids);
                    }
                }
            }
            if let Some(ids) = self.world.class(anc).methods.get(name) {
                lists.push(ids);
            }
            for ids in lists {
                for id in ids {
                    let m = self.world.method(*id);
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
        let cid = self.class_of(recv);
        let Some(mid) = self.find_method(cid, name, args.len(), block.is_some()) else {
            return Err(self.raise(
                self.exc.runtime_error,
                &format!(
                    "undefined method `{name}` for {}",
                    self.world.class(cid).name
                ),
            ));
        };
        self.invoke(mid, recv.clone(), args, Vec::new(), block)
    }

    /// Whether the receiver's class defines `name` itself (not via Object's
    /// native default).
    pub fn has_user_method(&self, recv: &Value, name: &str, argc: usize) -> Option<MethodId> {
        let cid = self.class_of(recv);
        let mid = self.find_method(cid, name, argc, false)?;
        let m = self.world.method(mid);
        if m.owner == self.world.builtin.object && m.native_key.is_some() {
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
        let m = self.world.method(mid);
        if let Some(native) = self.natives[mid as usize] {
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
                return Ok(o
                    .fields
                    .borrow()
                    .get(*idx as usize)
                    .cloned()
                    .unwrap_or(Value::Nil));
            }
            RtSynth::FieldSet(idx) => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("field access on a non-object"));
                };
                let v = args.into_iter().next().unwrap_or(Value::Nil);
                let mut fields = o.fields.borrow_mut();
                let idx = *idx as usize;
                if idx >= fields.len() {
                    fields.resize(idx + 1, Value::Nil);
                }
                fields[idx] = v.clone();
                return Ok(v);
            }
            RtSynth::DataInit => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("data initialization on a non-object"));
                };
                let values = self.bind_data_args(mid, &recv, args, kw)?;
                *o.fields.borrow_mut() = Fields::from_vec(values);
                return Ok(Value::Nil);
            }
            RtSynth::DataWith => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("`with` on a non-object"));
                };
                let mut fields = o.fields.borrow().clone();
                for (sym, v) in kw {
                    let name = self.symbol_name(sym);
                    if let Some(i) = m.params.iter().position(|p| *p.name == *name) {
                        if i < fields.len() {
                            fields[i] = v;
                        }
                    }
                }
                return Ok(Value::Object(Rc::new(Object {
                    class: o.class,
                    fields: RefCell::new(fields),
                    backtrace: RefCell::new(None),
                    cause: RefCell::new(None),
                })));
            }
            RtSynth::DataToH => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("`to_h` on a non-object"));
                };
                let mut map = indexmap::IndexMap::new();
                let class = self.world.class(o.class);
                for (f, v) in class.fields.iter().zip(o.fields.borrow().iter()) {
                    map.insert(Value::Symbol(self.intern(&f.name)), v.clone());
                }
                return Ok(Value::Hash(Rc::new(map)));
            }
            RtSynth::None => {}
        }
        if m.native_key.is_some() {
            return Err(self.raise(
                self.exc.not_implemented,
                &format!(
                    "native method `{}` is not implemented",
                    m.native_key.as_deref().unwrap_or("")
                ),
            ));
        }
        if m.is_abstract {
            return Err(self.raise(
                self.exc.not_implemented,
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
        let (bound, provided) = self.bind_params(mid, &recv, args, kw, block.clone())?;
        self.run_method(mid, fid, recv, bound, provided, block)
    }

    /// Invoke with an owned receiver (`x = x.push(v)`): natives that update
    /// in place get the sole reference. On error the receiver is returned.
    pub fn invoke_owned(
        &self,
        mid: MethodId,
        recv: Value,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
    ) -> Result<Value, (Flow, Value)> {
        let mid = self.resolve_dynamic(&recv, mid);
        if let Some(native) = self.natives_owned[mid as usize] {
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
        let m = self.world.method(mid);
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
        let class = self.world.class(m.owner);
        for (i, p) in m.params.iter().enumerate() {
            if !set[i] && p.has_default {
                if let Some(default) = class.fields.get(i).and_then(|f| f.default) {
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
        let m = self.world.method(mid);
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
                    let mut map = indexmap::IndexMap::new();
                    for (sym, v) in kwrest.drain(..) {
                        map.insert(Value::Symbol(sym), v);
                    }
                    values[i] = Value::Hash(Rc::new(map));
                    provided |= bit(i);
                }
            }
        } else {
            for (i, p) in m.params.iter().enumerate() {
                if p.kind == RtParamKind::KeywordRest {
                    values[i] = Value::Hash(Rc::new(indexmap::IndexMap::new()));
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
    pub fn construct(
        &self,
        class: ClassId,
        init: Option<MethodId>,
        args: ArgVec,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
    ) -> EvalResult {
        let info = self.world.class(class);
        let obj = Rc::new(Object {
            class,
            fields: RefCell::new(smallvec![Value::Nil; info.fields.len()]),
            backtrace: RefCell::new(None),
            cause: RefCell::new(None),
        });
        let value = Value::Object(obj.clone());
        // Field defaults (data types evaluate them in their constructor).
        if !matches!(info.kind, RtClassKind::Data | RtClassKind::Variant) {
            for (i, f) in info.fields.iter().enumerate() {
                if let Some(d) = f.default {
                    let v = self.run_init(d, value.clone(), info.file)?;
                    obj.fields.borrow_mut()[i] = v;
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
            body: ClosureBody::Native(Rc::new(f)),
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
                self.exc.argument_error,
                &format!("invalid regexp /{source}/: {e}"),
            )),
        }
    }

    /// `===` for `case/when`.
    pub fn case_eq(&self, pattern: &Value, v: &Value) -> Result<bool, Flow> {
        match pattern {
            Value::Class(cid) => Ok(self.world.class_is_a(self.class_of(v), *cid)),
            Value::Range(r) => self.range_covers(r, v),
            Value::Regexp(re) => Ok(match v {
                Value::Str(s) => re.regex.is_match(s),
                _ => false,
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

    pub fn to_s(&self, v: &Value) -> Result<Rc<str>, Flow> {
        match v {
            Value::Str(s) => Ok(s.clone()),
            Value::Object(o) => {
                if let Some(mid) = self.has_user_method(v, "to_s", 0) {
                    let r = self.invoke(mid, v.clone(), smallvec![], vec![], None)?;
                    return self.to_s(&r);
                }
                if self.world.is_exception_class(o.class) {
                    return Ok(Rc::from(self.exception_message(v).as_str()));
                }
                Ok(Rc::from(self.inspect(v)?.as_str()))
            }
            _ => Ok(Rc::from(self.format_value(v, false)?.as_str())),
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
            Value::Str(s) => {
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
                    parts.push(self.inspect(x)?);
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
            Value::Hash(h) => self.format_hash(h.iter())?,
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
            Value::MatchData(m) => format!(
                "#<MatchData {:?}>",
                &m.text[m.groups[0].map(|(s, e)| s..e).unwrap_or(0..0)]
            ),
            Value::Object(o) => {
                let class = self.world.class(o.class);
                if class.is_exception {
                    return Ok(format!("#<{}: {}>", class.name, self.exception_message(v)));
                }
                match class.kind {
                    RtClassKind::Data | RtClassKind::Variant => {
                        if class.fields.is_empty() {
                            return Ok(class.name.clone());
                        }
                        let mut parts = Vec::new();
                        for (f, val) in class.fields.iter().zip(o.fields.borrow().iter()) {
                            parts.push(format!("{}: {}", f.name, self.inspect(val)?));
                        }
                        format!("{}({})", class.name, parts.join(", "))
                    }
                    RtClassKind::Main => "main".to_string(),
                    _ => {
                        let mut parts = Vec::new();
                        for (f, val) in class.fields.iter().zip(o.fields.borrow().iter()) {
                            parts.push(format!("@{}={}", f.name, self.inspect(val)?));
                        }
                        if parts.is_empty() {
                            format!("#<{}>", class.name)
                        } else {
                            format!("#<{} {}>", class.name, parts.join(", "))
                        }
                    }
                }
            }
            Value::Class(c) => self.world.class(*c).name.clone(),
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
            Value::Atom(a) => format!("#<Atom {}>", self.inspect(&a.borrow())?),
            Value::Selector(_) => "#<Selector>".to_string(),
            Value::Duration(ns) => format_duration(*ns),
            Value::Enumerator(e) => format!("#<Enumerator {}>", e.method),
            Value::Io(_) => "#<IO>".to_string(),
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
            (Value::Str(x), Value::Str(y)) => return Ok(x.cmp(y)),
            (Value::Symbol(x), Value::Symbol(y)) => {
                return Ok(self.symbol_name(*x).cmp(&self.symbol_name(*y)))
            }
            (Value::Duration(x), Value::Duration(y)) => return Ok(x.cmp(y)),
            (Value::Bytes(x), Value::Bytes(y)) => return Ok(x.cmp(y)),
            (Value::Time(x), Value::Time(y)) => return Ok(x.ns.cmp(&y.ns)),
            (Value::Array(x), Value::Array(y)) => {
                for (p, q) in x.iter().zip(y.iter()) {
                    let o = self.compare(p, q)?;
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
        use std::io::Write;
        let _ = self.stdout.borrow_mut().write_all(s.as_bytes());
    }
}

/// Convert the result of a task body into its exit.
fn task_exit(interp: &Interp, result: EvalResult) -> TaskExit {
    match result {
        Ok(v) => TaskExit::Result(TaskResult::Value(v)),
        Err(Flow::Raise(e)) => TaskExit::Result(TaskResult::Error(e)),
        Err(Flow::Exit(c)) => TaskExit::Exit(c),
        Err(Flow::Return(v, 0)) => TaskExit::Result(TaskResult::Value(v)),
        Err(other) => {
            let e = interp.make_exception(
                interp.exc.runtime_error,
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
