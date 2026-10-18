//! The interpreter: method invocation, dynamic dispatch, exceptions, the
//! task run loop, and conversions used by the natives.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::{Rc, Weak};
use std::time::Duration;

use quarz_syntax::ast::{Block, ParamKind};
use quarz_types::{CallTarget, Checked, ClassId, ClassKind, MethodId, Output, Synth, Type, World};

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

/// Arguments to a native method.
pub struct Args {
    pub pos: Vec<Value>,
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

/// Key of the by-name method cache: class, name, arity, block given.
type NameKey = (ClassId, String, usize, bool);

/// Which construct a `break` exits.
#[derive(Clone, Copy, Debug)]
pub enum Breakable {
    None,
    Loop,
    Block(u64),
}

/// Evaluation context of a method body or block body.
#[derive(Clone)]
pub struct Ctx {
    pub self_val: Value,
    pub frame: Rc<Frame>,
    /// The block passed to the enclosing method (for `yield`).
    pub block: Option<Value>,
    pub method_tag: u64,
    pub breakable: Breakable,
    pub method: Option<MethodId>,
    /// Source file index of the code being evaluated.
    pub file: u32,
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
    pub world: World,
    pub out: Output,
    /// Compilation units in execution order.
    pub units: Vec<quarz_types::CheckedUnit>,
    /// The `self` object of each unit's top level, by file index.
    unit_selfs: Vec<Value>,
    /// Display names by file index (0 = the prelude).
    pub file_names: Vec<String>,
    pub symbols: RefCell<SymbolTable>,
    consts: RefCell<Vec<Option<Value>>>,
    variant_singletons: RefCell<HashMap<ClassId, Value>>,
    pub natives: Vec<Option<NativeFn>>,
    pub natives_owned: Vec<Option<OwnedNativeFn>>,
    pub sched: RefCell<Scheduler>,
    dispatch_cache: RefCell<HashMap<(ClassId, MethodId), MethodId>>,
    name_cache: RefCell<HashMap<NameKey, Option<MethodId>>>,
    regexp_cache: RefCell<HashMap<u32, Value>>,
    next_tag: Cell<u64>,
    pub argv: Vec<String>,
    pub exc: ExcClasses,
    pub rt: RtClasses,
    pub call_stack: RefCell<Vec<Rc<str>>>,
    pub at_exit: RefCell<Vec<Value>>,
    pub stdout: RefCell<Box<dyn std::io::Write>>,
    self_rc: RefCell<Weak<Interp>>,
    pub root_task: Cell<Option<TaskId>>,
}

impl Interp {
    pub fn new(checked: Checked, argv: Vec<String>) -> Rc<Interp> {
        Interp::with_output(
            checked,
            argv,
            Box::new(std::io::BufWriter::new(std::io::stdout())),
        )
    }

    /// Create an interpreter writing standard output to `out`.
    pub fn with_output(
        checked: Checked,
        argv: Vec<String>,
        out: Box<dyn std::io::Write>,
    ) -> Rc<Interp> {
        let Checked {
            world,
            output,
            units,
        } = checked;
        let structural: Vec<bool> = world
            .classes
            .iter()
            .map(|c| matches!(c.kind, ClassKind::Data | ClassKind::Variant))
            .collect();
        STRUCTURAL_CLASSES.with(|s| *s.borrow_mut() = structural);

        let registry = natives::registry();
        let natives: Vec<Option<NativeFn>> = world
            .methods
            .iter()
            .map(|m| {
                if m.is_native && m.synth == Synth::None {
                    registry.get(m.native_key(&world).as_str()).copied()
                } else {
                    None
                }
            })
            .collect();
        let owned_registry = natives::owned_registry();
        let natives_owned: Vec<Option<OwnedNativeFn>> = world
            .methods
            .iter()
            .map(|m| {
                if m.is_native && m.synth == Synth::None {
                    owned_registry.get(m.native_key(&world).as_str()).copied()
                } else {
                    None
                }
            })
            .collect();
        let class_by_name = |name: &str| -> ClassId {
            let mut cur: Option<ClassId> = None;
            for part in name.split("::") {
                let member = match cur {
                    Some(c) => world.class(c).members.get(part).copied(),
                    None => world.top.get(part).copied(),
                };
                match member {
                    Some(quarz_types::Member::Class(id)) => cur = Some(id),
                    _ => panic!("prelude does not define {name}"),
                }
            }
            cur.unwrap()
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
        let mut unit_selfs = vec![Value::Nil; units.len() + 1];
        let mut file_names = vec!["<prelude>".to_string(); units.len() + 1];
        for u in &units {
            unit_selfs[u.file as usize] = Value::Object(Rc::new(Object {
                class: u.main_class,
                fields: RefCell::new(Vec::new()),
                backtrace: RefCell::new(None),
                cause: RefCell::new(None),
            }));
            file_names[u.file as usize] = u.name.clone();
        }
        let n_consts = world.consts.len();
        let interp = Rc::new(Interp {
            world,
            out: output,
            units,
            unit_selfs,
            file_names,
            symbols: RefCell::new(SymbolTable::default()),
            consts: RefCell::new(vec![None; n_consts]),
            variant_singletons: RefCell::new(HashMap::new()),
            natives,
            natives_owned,
            sched: RefCell::new(Scheduler::new()),
            dispatch_cache: RefCell::new(HashMap::new()),
            name_cache: RefCell::new(HashMap::new()),
            regexp_cache: RefCell::new(HashMap::new()),
            next_tag: Cell::new(1),
            argv,
            exc,
            rt,
            call_stack: RefCell::new(Vec::new()),
            at_exit: RefCell::new(Vec::new()),
            stdout: RefCell::new(out),
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

    // ----- running ---------------------------------------------------------------

    /// Run the main program as the root task. Returns the exit code.
    pub fn run(self: &Rc<Interp>) -> i32 {
        let me = self.clone();
        let body: Box<dyn FnOnce() -> TaskExit> = Box::new(move || {
            let mut result = Ok(Value::Nil);
            'units: for unit in me.units.iter() {
                let size = me
                    .out
                    .unit_frame_sizes
                    .get(unit.file as usize)
                    .copied()
                    .unwrap_or(0);
                let ctx = Ctx {
                    self_val: me.unit_selfs[unit.file as usize].clone(),
                    frame: Frame::new(size as usize + 8, None),
                    block: None,
                    method_tag: 0,
                    breakable: Breakable::None,
                    method: None,
                    file: unit.file,
                };
                for e in unit.body.iter() {
                    match me.eval(e, &ctx) {
                        Ok(_) => {}
                        Err(f) => {
                            result = Err(f);
                            break 'units;
                        }
                    }
                }
            }
            match result {
                Ok(v) => TaskExit::Result(TaskResult::Value(v)),
                Err(Flow::Raise(e)) => TaskExit::Result(TaskResult::Error(e)),
                Err(Flow::Exit(c)) => TaskExit::Exit(c),
                Err(Flow::Return(_, 0)) => TaskExit::Result(TaskResult::Value(Value::Nil)),
                Err(other) => {
                    let e = me.make_exception(
                        me.exc.runtime_error,
                        &format!("unexpected control flow: {other:?}"),
                    );
                    TaskExit::Result(TaskResult::Error(e))
                }
            }
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
            let r = me.call_block(&closure, vec![]);
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
        let n = self.world.all_fields(class).len().max(1);
        let mut fields = vec![Value::Nil; n];
        fields[0] = Value::str(message);
        let bt = self.capture_backtrace();
        Value::Object(Rc::new(Object {
            class,
            fields: RefCell::new(fields),
            backtrace: RefCell::new(Some(Rc::new(bt))),
            cause: RefCell::new(None),
        }))
    }

    /// The innermost frames of the call stack (deep recursion is cut
    /// off).
    pub fn capture_backtrace(&self) -> Vec<String> {
        let stack = self.call_stack.borrow();
        let mut bt: Vec<String> = stack.iter().rev().take(32).map(|s| s.to_string()).collect();
        if stack.len() > 32 {
            bt.push(format!("... {} more frames", stack.len() - 32));
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
        }
    }

    pub fn class_name(&self, v: &Value) -> String {
        self.world.class(self.class_of(v)).name.clone()
    }

    /// `value.is_a?(type)`, ignoring type arguments.
    pub fn is_a(&self, v: &Value, ty: &Type) -> bool {
        match ty {
            Type::Nothing => false,
            Type::Class(cid, _) => self.world.class_is_a(self.class_of(v), *cid),
            Type::ClassObject(_, _) => matches!(v, Value::Class(_)),
            Type::Union(ms) => ms.iter().any(|m| self.is_a(v, m)),
            Type::Tuple(ts) => matches!(v, Value::Array(a) if a.len() == ts.len()),
            Type::Proc(_, _) => matches!(v, Value::Proc(_)),
            Type::Param(_) | Type::Var(_) => true,
        }
    }

    pub fn variant_singleton(&self, cid: ClassId) -> Value {
        if let Some(v) = self.variant_singletons.borrow().get(&cid) {
            return v.clone();
        }
        let v = Value::Object(Rc::new(Object {
            class: cid,
            fields: RefCell::new(Vec::new()),
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
        let info = self.world.consts[cid as usize].clone();
        let Some(value) = info.value else {
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
        let ctx = Ctx {
            self_val,
            frame: Frame::new(8, None),
            block: None,
            method_tag: self.new_tag(),
            breakable: Breakable::None,
            method: None,
            file: info.file,
        };
        let v = self.eval(&value, &ctx)?;
        self.consts.borrow_mut()[cid as usize] = Some(v.clone());
        Ok(v)
    }

    // ----- dispatch --------------------------------------------------------------------

    /// Find the implementation of a statically resolved method for the
    /// receiver's run-time class (subclass overrides).
    pub fn resolve_dynamic(&self, recv: &Value, mid: MethodId) -> MethodId {
        let m = self.world.method(mid);
        if m.singleton || m.extension.is_some() {
            return mid;
        }
        let cid = self.class_of(recv);
        if cid == m.owner {
            return mid;
        }
        if let Some(found) = self.dispatch_cache.borrow().get(&(cid, mid)) {
            return *found;
        }
        let (min, max) = m.positional_arity();
        let found = self
            .find_method(cid, &m.name, min, m.block.is_some())
            .filter(|f| {
                let (fmin, fmax) = self.world.method(*f).positional_arity();
                fmin <= max && fmax >= min
            })
            .unwrap_or(mid);
        self.dispatch_cache.borrow_mut().insert((cid, mid), found);
        found
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
        let key = (cid, name.to_string(), argc, with_block);
        if let Some(found) = self.name_cache.borrow().get(&key) {
            return *found;
        }
        let mut found = None;
        let mut fallback = None;
        for (anc, _) in self.world.ancestors(cid, &[]) {
            // Always-active extensions on this ancestor.
            for ext_id in self.world.active_extension_ids() {
                let ext = &self.world.extensions[ext_id as usize];
                if ext.target != anc {
                    continue;
                }
                if let Some(ids) = ext.methods.get(name) {
                    for id in ids {
                        let m = self.world.method(*id);
                        let (min, max) = m.positional_arity();
                        if min <= argc && argc <= max && (m.block.is_some() == with_block) {
                            found = Some(*id);
                            break;
                        }
                        fallback.get_or_insert(*id);
                    }
                }
                if found.is_some() {
                    break;
                }
            }
            if found.is_some() {
                break;
            }
            if let Some(ids) = self.world.class(anc).methods.get(name) {
                for id in ids {
                    let m = self.world.method(*id);
                    let (min, max) = m.positional_arity();
                    if min <= argc && argc <= max && (m.block.is_some() == with_block) {
                        found = Some(*id);
                        break;
                    }
                    fallback.get_or_insert(*id);
                }
            }
            if found.is_some() {
                break;
            }
        }
        let result = found.or(fallback);
        self.name_cache.borrow_mut().insert(key, result);
        result
    }

    /// Call a method by name with dynamic lookup (used by `&:sym`,
    /// enumerators, `to_s`, operators in compound assignment).
    pub fn send(
        &self,
        recv: &Value,
        name: &str,
        args: Vec<Value>,
        block: Option<Value>,
    ) -> EvalResult {
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
        if m.owner == self.world.builtin.object && m.is_native {
            return None;
        }
        Some(mid)
    }

    // ----- invocation --------------------------------------------------------------------

    pub fn invoke(
        &self,
        mid: MethodId,
        recv: Value,
        args: Vec<Value>,
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
            Synth::FieldGet(name) => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("field access on a non-object"));
                };
                let idx = self.world.field_index(o.class, name).unwrap_or(0);
                return Ok(o.fields.borrow().get(idx).cloned().unwrap_or(Value::Nil));
            }
            Synth::FieldSet(name) => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("field access on a non-object"));
                };
                let idx = self.world.field_index(o.class, name).unwrap_or(0);
                let v = args.into_iter().next().unwrap_or(Value::Nil);
                let mut fields = o.fields.borrow_mut();
                if idx >= fields.len() {
                    fields.resize(idx + 1, Value::Nil);
                }
                fields[idx] = v.clone();
                return Ok(v);
            }
            Synth::DataInit => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("data initialization on a non-object"));
                };
                let values = self.bind_data_args(m.params.len(), &m.params, args, kw)?;
                *o.fields.borrow_mut() = values;
                return Ok(Value::Nil);
            }
            Synth::DataWith => {
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
            Synth::DataToH => {
                let Value::Object(o) = &recv else {
                    return Err(self.err_type("`to_h` on a non-object"));
                };
                let mut map = indexmap::IndexMap::new();
                for (f, v) in self
                    .world
                    .all_fields(o.class)
                    .iter()
                    .zip(o.fields.borrow().iter())
                {
                    map.insert(Value::Symbol(self.intern(&f.0.name)), v.clone());
                }
                return Ok(Value::Hash(Rc::new(map)));
            }
            Synth::None => {}
        }
        if m.is_native {
            return Err(self.raise(
                self.exc.not_implemented,
                &format!(
                    "native method `{}` is not implemented",
                    m.native_key(&self.world)
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
        let Some(def) = &m.body else {
            return Ok(Value::Nil);
        };
        if sched::stack_exhausted() {
            return Err(self.raise(self.exc.system_stack, "stack level too deep"));
        }
        let frame = Frame::new(m.frame_size as usize + 1, None);
        let tag = self.new_tag();
        let ctx = Ctx {
            self_val: recv.clone(),
            frame: frame.clone(),
            block: block.clone(),
            method_tag: tag,
            breakable: Breakable::None,
            method: Some(mid),
            file: m.file,
        };
        self.bind_params(&ctx, mid, args, kw, block)?;
        self.call_stack.borrow_mut().push(Rc::from(
            format!("{}#{}", self.world.class(m.owner).name, m.name).as_str(),
        ));
        let body = def.body.as_deref().unwrap_or(&[]);
        let r = self.eval_body(body, &ctx);
        self.call_stack.borrow_mut().pop();
        match r {
            Err(Flow::Return(v, t)) if t == tag => Ok(v),
            r => r,
        }
    }

    /// Invoke with an owned receiver (`x = x.push(v)`): natives that update
    /// in place get the sole reference. On error the receiver is returned.
    pub fn invoke_owned(
        &self,
        mid: MethodId,
        recv: Value,
        args: Vec<Value>,
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

    fn bind_data_args(
        &self,
        n: usize,
        params: &[quarz_types::ParamInfo],
        args: Vec<Value>,
        kw: Vec<(Symbol, Value)>,
    ) -> Result<Vec<Value>, Flow> {
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
            if let Some(i) = params.iter().position(|p| *p.name == *name) {
                values[i] = v;
                set[i] = true;
            }
        }
        for (i, p) in params.iter().enumerate() {
            if !set[i] {
                if let Some(d) = &p.default {
                    let ctx = Ctx {
                        self_val: Value::Nil,
                        frame: Frame::new(4, None),
                        block: None,
                        method_tag: 0,
                        breakable: Breakable::None,
                        method: None,
                        file: 0,
                    };
                    values[i] = self.eval(d, &ctx)?;
                }
            }
        }
        Ok(values)
    }

    /// Bind call arguments to the parameter slots of a new frame.
    fn bind_params(
        &self,
        ctx: &Ctx,
        mid: MethodId,
        args: Vec<Value>,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
    ) -> Result<(), Flow> {
        let m = self.world.method(mid);
        let frame = &ctx.frame;
        let mut args = args.into_iter();
        let mut kw = kw;
        let mut rest: Vec<Value> = Vec::new();
        let mut set = vec![false; m.params.len()];
        // Positional parameters take positional arguments in order.
        for (i, p) in m.params.iter().enumerate() {
            match p.kind {
                ParamKind::Positional => {
                    if let Some(a) = args.next() {
                        frame.set(0, i as u32, a);
                        set[i] = true;
                    }
                }
                ParamKind::Rest => {
                    rest.extend(args.by_ref());
                    frame.set(0, i as u32, Value::array(std::mem::take(&mut rest)));
                    set[i] = true;
                }
                _ => {}
            }
        }
        // Keyword arguments by name.
        let mut kwrest: Vec<(Symbol, Value)> = Vec::new();
        for (sym, v) in kw.drain(..) {
            let name = self.symbol_name(sym);
            let found = m.params.iter().position(|p| {
                *p.name == *name && matches!(p.kind, ParamKind::Positional | ParamKind::KeywordOnly)
            });
            match found {
                Some(i) if !set[i] => {
                    frame.set(0, i as u32, v);
                    set[i] = true;
                }
                _ => kwrest.push((sym, v)),
            }
        }
        for (i, p) in m.params.iter().enumerate() {
            if set[i] {
                continue;
            }
            match p.kind {
                ParamKind::KeywordRest => {
                    let mut map = indexmap::IndexMap::new();
                    for (sym, v) in kwrest.drain(..) {
                        map.insert(Value::Symbol(sym), v);
                    }
                    frame.set(0, i as u32, Value::Hash(Rc::new(map)));
                }
                ParamKind::Block => {}
                _ => match &p.default {
                    Some(d) => {
                        let v = self.eval(d, ctx)?;
                        frame.set(0, i as u32, v);
                    }
                    None => frame.set(0, i as u32, Value::Nil),
                },
            }
        }
        if m.block.is_some() {
            frame.set(0, m.params.len() as u32, block.unwrap_or(Value::Nil));
        }
        // `def initialize(@x: Int)`.
        for (i, p) in m.params.iter().enumerate() {
            if p.assigns_ivar {
                if let Value::Object(o) = &ctx.self_val {
                    if let Some(idx) = self.world.field_index(o.class, &p.name) {
                        let v = frame.get(0, i as u32);
                        let mut fields = o.fields.borrow_mut();
                        if idx >= fields.len() {
                            fields.resize(idx + 1, Value::Nil);
                        }
                        fields[idx] = v;
                    }
                }
            }
        }
        Ok(())
    }

    /// Allocate an instance and run its initializer.
    pub fn construct(
        &self,
        class: ClassId,
        init: Option<MethodId>,
        args: Vec<Value>,
        kw: Vec<(Symbol, Value)>,
        block: Option<Value>,
    ) -> EvalResult {
        let fields = self.world.all_fields(class);
        let obj = Rc::new(Object {
            class,
            fields: RefCell::new(vec![Value::Nil; fields.len()]),
            backtrace: RefCell::new(None),
            cause: RefCell::new(None),
        });
        let value = Value::Object(obj.clone());
        // Field defaults.
        let has_defaults = fields.iter().any(|(f, _)| f.default.is_some());
        if has_defaults
            && !matches!(
                self.world.class(class).kind,
                ClassKind::Data | ClassKind::Variant
            )
        {
            let ctx = Ctx {
                self_val: value.clone(),
                frame: Frame::new(8, None),
                block: None,
                method_tag: self.new_tag(),
                breakable: Breakable::None,
                method: None,
                file: self.world.class(class).file,
            };
            for (i, (f, _)) in fields.iter().enumerate() {
                if let Some(d) = &f.default {
                    let v = self.eval(d, &ctx)?;
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

    /// Create the closure for a block written at a call site.
    pub fn make_block(&self, block: &Block, call_id: u32, ctx: &Ctx) -> Value {
        Value::Proc(Rc::new(Closure {
            body: ClosureBody::Block(AstRef::new(block)),
            frame: Some(ctx.frame.clone()),
            self_val: ctx.self_val.clone(),
            frame_size: self.out.frame_sizes.get(&call_id).copied().unwrap_or(0),
            destructure: self.out.block_destructure.get(&call_id).copied(),
            is_lambda: false,
            tag: self.new_tag(),
            method_block: ctx.block.clone(),
            method_tag: ctx.method_tag,
            file: ctx.file,
        }))
    }

    /// Call a block/procedure value with arguments. `next` yields the
    /// block's value; `break` propagates to the call that received it.
    pub fn call_block(&self, proc: &Value, mut args: Vec<Value>) -> EvalResult {
        let Value::Proc(closure) = proc else {
            return Err(self.err_type("not a procedure"));
        };
        match &closure.body {
            ClosureBody::MethodName(name) => {
                if args.is_empty() {
                    return Err(self.err_arg("block needs an argument"));
                }
                let recv = args.remove(0);
                self.send(&recv, name, args, None)
            }
            ClosureBody::BoundMethod { recv, name } => self.send(recv, name, args, None),
            ClosureBody::Native(f) => f(self, args),
            ClosureBody::Block(block) => {
                if sched::stack_exhausted() {
                    return Err(self.raise(self.exc.system_stack, "stack level too deep"));
                }
                let block = block.get();
                let frame = Frame::new(closure.frame_size as usize + 1, closure.frame.clone());
                // Destructure a single array argument over several parameters.
                if let Some(n) = closure.destructure {
                    if args.len() == 1 {
                        if let Value::Array(a) = &args[0] {
                            let items: Vec<Value> = a.iter().cloned().collect();
                            let mut items = items;
                            items.resize(n.max(items.len()), Value::Nil);
                            args = items;
                        }
                    }
                }
                let mut it = args.into_iter();
                let mut slot = 0u32;
                for p in &block.params.list {
                    match p.kind {
                        ParamKind::Block => continue,
                        ParamKind::Rest => {
                            let rest: Vec<Value> = it.by_ref().collect();
                            frame.set(0, slot, Value::array(rest));
                        }
                        _ => {
                            let v = it.next().unwrap_or(Value::Nil);
                            frame.set(0, slot, v);
                        }
                    }
                    slot += 1;
                }
                let ctx = Ctx {
                    self_val: closure.self_val.clone(),
                    frame,
                    block: closure.method_block.clone(),
                    method_tag: if closure.is_lambda {
                        closure.tag
                    } else {
                        closure.method_tag
                    },
                    breakable: if closure.is_lambda {
                        Breakable::None
                    } else {
                        Breakable::Block(closure.tag)
                    },
                    method: None,
                    file: closure.file,
                };
                match self.eval_body(&block.body, &ctx) {
                    Ok(v) => Ok(v),
                    Err(Flow::Next(v)) => Ok(v),
                    Err(Flow::Return(v, t)) if closure.is_lambda && t == closure.tag => Ok(v),
                    Err(Flow::Break(v, t)) if closure.is_lambda && t == closure.tag => Ok(v),
                    Err(e) => Err(e),
                }
            }
        }
    }

    /// A block implemented in Rust.
    pub fn native_block(&self, f: impl Fn(&Interp, Vec<Value>) -> EvalResult + 'static) -> Value {
        let tag = self.new_tag();
        Value::Proc(Rc::new(Closure {
            body: ClosureBody::Native(Rc::new(f)),
            frame: None,
            self_val: Value::Nil,
            frame_size: 0,
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

    // ----- conversions ---------------------------------------------------------------------------

    pub fn to_s(&self, v: &Value) -> Result<Rc<str>, Flow> {
        match v {
            Value::Str(s) => Ok(s.clone()),
            Value::Object(o) => {
                if let Some(mid) = self.has_user_method(v, "to_s", 0) {
                    let r = self.invoke(mid, v.clone(), vec![], vec![], None)?;
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
                let r = self.invoke(mid, v.clone(), vec![], vec![], None)?;
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
                if self.world.is_exception_class(o.class) {
                    return Ok(format!("#<{}: {}>", class.name, self.exception_message(v)));
                }
                match class.kind {
                    ClassKind::Data | ClassKind::Variant => {
                        let fields = self.world.all_fields(o.class);
                        if fields.is_empty() {
                            return Ok(class.name.clone());
                        }
                        let mut parts = Vec::new();
                        for (f, val) in fields.iter().zip(o.fields.borrow().iter()) {
                            parts.push(format!("{}: {}", f.0.name, self.inspect(val)?));
                        }
                        format!("{}({})", class.name, parts.join(", "))
                    }
                    ClassKind::Main => "main".to_string(),
                    _ => {
                        let fields = self.world.all_fields(o.class);
                        let mut parts = Vec::new();
                        for (f, val) in fields.iter().zip(o.fields.borrow().iter()) {
                            parts.push(format!("@{}={}", f.0.name, self.inspect(val)?));
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
                let r = self.invoke(mid, a.clone(), vec![b.clone()], vec![], None)?;
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
        let r = self.send(a, "<=>", vec![b.clone()], None)?;
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

    pub fn regexp_cached(&self, id: u32) -> Option<Value> {
        self.regexp_cache.borrow().get(&id).cloned()
    }

    pub fn cache_regexp(&self, id: u32, v: Value) {
        self.regexp_cache.borrow_mut().insert(id, v);
    }

    pub fn write_out(&self, s: &str) {
        use std::io::Write;
        let _ = self.stdout.borrow_mut().write_all(s.as_bytes());
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

/// Look up a call target recorded by the checker.
pub fn call_target(out: &Output, id: u32) -> Option<&CallTarget> {
    out.calls.get(&id)
}
