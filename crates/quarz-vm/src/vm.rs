//! The QIR interpreter: activation records and the execution of
//! instructions. Compiled code (`quarz build`) shares the instruction
//! semantics through `exec_inst`.

use crate::rc::Rc;
use std::cell::{Cell, RefCell};

use quarz_ir::*;
use smallvec::{smallvec, SmallVec};

use crate::interp::{
    float_binop_into, float_operands, int_binop_into, ArgVec, EvalResult, Flow, Interp, SharedState,
};
use crate::sched;
use crate::value::MethodCache;
use crate::value::*;

/// The interpreter, installed by what interprets
/// (`Interp::install_interpreter`). A compiled program never installs
/// it, and so links neither it nor the functions' bodies.
pub(crate) struct Interpreter {
    /// Run a function without compiled code.
    pub run: fn(&Interp, FuncId, &Activation) -> EvalResult,
    /// The bodies an interpreter has loaded, for another thread to
    /// `import` into its state.
    pub export: fn(&Interp) -> Option<Bodies>,
    pub import: fn(&SharedState, &Bodies),
    /// All the natives (a compiled program has a table of those it uses).
    pub natives: fn() -> crate::natives::Natives,
}

pub(crate) static INTERPRETER: std::sync::OnceLock<Interpreter> = std::sync::OnceLock::new();

/// Functions' bodies on their way to another thread (what they are is
/// the interpreter's business: see `Interpreter`).
pub type Bodies = std::sync::Arc<dyn std::any::Any + Send + Sync>;

/// The bodies of a program's functions, by id (`SharedState::bodies`).
type BodyTable = RefCell<Vec<std::rc::Rc<[Block]>>>;

fn body_table(cell: &std::cell::OnceCell<std::rc::Rc<dyn std::any::Any>>) -> &BodyTable {
    let table = cell.get_or_init(|| std::rc::Rc::new(BodyTable::default()));
    debug_assert!(table.is::<BodyTable>());
    // SAFETY: only this function fills the cell, with a `BodyTable`
    // (checked without `downcast_ref`'s virtual call: this runs on every
    // interpreted call).
    unsafe { &*(std::rc::Rc::as_ptr(table) as *const BodyTable) }
}

/// Load the bodies of the functions from `base` on (those below stay).
pub(crate) fn load_bodies(
    state: &SharedState,
    base: FuncId,
    bodies: impl IntoIterator<Item = Vec<Block>>,
) {
    let mut table = body_table(&state.bodies).borrow_mut();
    table.truncate(base as usize);
    table.extend(bodies.into_iter().map(std::rc::Rc::from));
}

fn export_bodies(rt: &Interp) -> Option<Bodies> {
    let table = body_table(&rt.bodies).borrow();
    let list: Vec<Vec<Block>> = table.iter().map(|b| b.to_vec()).collect();
    Some(std::sync::Arc::new(list))
}

fn import_bodies(state: &SharedState, bodies: &Bodies) {
    if let Some(list) = bodies.downcast_ref::<Vec<Vec<Block>>>() {
        load_bodies(state, 0, list.iter().cloned());
    }
}

/// The context a function body runs in. `repr(C)`: compiled code builds
/// and reads it by the offsets in `layout`.
#[repr(C)]
pub struct Activation {
    pub fid: FuncId,
    /// The task running it (call stacks are kept per task).
    pub task: crate::sched::TaskId,
    /// Source line of the instruction being executed (for backtraces).
    pub line: Cell<u32>,
    pub file: u32,
    pub self_val: Value,
    /// The heap frame for captured variables (this function's own, or
    /// the one a block shares with its creator).
    pub frame: Option<Rc<Frame>>,
    /// The block passed to the call (`Nil` when none).
    pub block: Value,
    /// Identifies this method activation for `return` from its blocks.
    pub method_tag: u64,
    pub closure_tag: u64,
    /// Bit `i` set: parameter `i` was given (for `HasArg`).
    pub provided: u64,
    /// The parameter view: `nargs` values at `args_ptr` (in `args`, or in
    /// a compiled caller's argument area).
    pub args_ptr: Cell<*const Value>,
    pub nargs: Cell<u32>,
    /// Where the activation lives: activations are built on the native
    /// stack (a local of the interpreter, or an area of a compiled
    /// caller's frame), so their addresses order them among the frames
    /// the native unwinder reports (see `Interp::capture_backtrace`).
    pub sp: Cell<usize>,
    /// The frame is also visible to the native unwinder (a typed entry
    /// that materialized its activation): backtraces take it from there.
    pub native: Cell<bool>,
    /// The call owns the values of the parameter view (a list built for
    /// it, or a compiled caller's argument area it releases after the
    /// call), so `Arg` moves a parameter out of it: the callee holds the
    /// only reference a moved argument has, and can update it in place.
    /// False when the view borrows someone else's values (a native
    /// handing a block an array's elements).
    pub args_owned: Cell<bool>,
    /// The block's caller, built on the first `yield` and reused.
    pub yield_caller: YieldCache,
}

/// A lazily built `BlockCaller` for an activation's block: null until
/// the first `yield`, `GENERIC` when the block needs the general path.
#[repr(transparent)]
pub struct YieldCache(Cell<*mut BlockCaller>);

impl Default for YieldCache {
    fn default() -> Self {
        YieldCache(Cell::new(std::ptr::null_mut()))
    }
}

impl YieldCache {
    const GENERIC: *mut BlockCaller = std::ptr::dangling_mut::<BlockCaller>();

    /// The cached caller, building it on first use.
    pub fn get_or_init(&self, build: impl FnOnce() -> Option<BlockCaller>) -> Option<&BlockCaller> {
        let p = self.0.get();
        if p.is_null() {
            let p = match build() {
                Some(c) => Box::into_raw(Box::new(c)),
                None => Self::GENERIC,
            };
            self.0.set(p);
        }
        let p = self.0.get();
        if p == Self::GENERIC {
            None
        } else {
            // SAFETY: a non-null, non-sentinel pointer came from `Box::into_raw`
            // above and is freed only by `drop`.
            Some(unsafe { &*p })
        }
    }
}

impl Drop for YieldCache {
    fn drop(&mut self) {
        let p = self.0.get();
        if !p.is_null() && p != Self::GENERIC {
            // SAFETY: see `get_or_init`.
            drop(unsafe { Box::from_raw(p) });
        }
    }
}

/// A block prepared for repeated calls (natives that iterate, `yield`):
/// its activation is built once, and each call only points the
/// parameter view at the arguments. Only blocks with a compiled or QIR
/// body, positional parameters and no frame of their own qualify.
pub struct BlockCaller {
    interp: *const Interp,
    kind: CallerKind,
}

enum CallerKind {
    /// A block with a body: its activation, built once.
    Func {
        closure: Rc<Closure>,
        fid: FuncId,
        act: Activation,
        compiled: Option<crate::interp::CompiledFn>,
        nparams: usize,
    },
    /// `&:name`: the method is called on the first argument.
    Named { closure: Rc<Closure> },
}

impl Interp {
    /// A reusable caller for `proc`, or `None` when it needs the general
    /// path (`call_block`).
    pub fn block_caller(&self, proc: &Value) -> Option<BlockCaller> {
        let Value::Proc(closure) = proc else {
            return None;
        };
        let fid = match closure.body {
            ClosureBody::Func(fid) => fid,
            ClosureBody::MethodName(..) => {
                return Some(BlockCaller {
                    interp: self,
                    kind: CallerKind::Named {
                        closure: closure.clone(),
                    },
                });
            }
            _ => return None,
        };
        if closure.destructure.is_some() {
            return None;
        }
        let (frame_size, nparams, file) = {
            let funcs = self.funcs.borrow();
            let f = &funcs[fid as usize];
            if f.frame_size > 0
                || f.param_kinds.len() >= 64
                || !f
                    .param_kinds
                    .iter()
                    .all(|k| matches!(k, RtParamKind::Positional | RtParamKind::KeywordOnly))
            {
                return None;
            }
            (f.frame_size, f.param_kinds.len(), closure.file)
        };
        debug_assert_eq!(frame_size, 0);
        let act = Activation {
            fid,
            task: self.current_task_id.get(),
            line: Cell::new(0),
            self_val: closure.self_val.fast_clone(),
            frame: closure.frame.clone(),
            block: closure
                .method_block
                .as_ref()
                .map_or(Value::Nil, |b| b.fast_clone()),
            method_tag: if closure.is_lambda {
                closure.tag
            } else {
                closure.method_tag
            },
            closure_tag: closure.tag,
            file,
            provided: (1u64 << nparams) - 1,
            args_ptr: Cell::new(std::ptr::null()),
            nargs: Cell::new(0),
            yield_caller: Default::default(),
            sp: Cell::new(0),
            native: Cell::new(false),
            args_owned: Cell::new(false),
        };
        let compiled = self.compiled.borrow().get(fid as usize).copied().flatten();
        Some(BlockCaller {
            interp: self,
            kind: CallerKind::Func {
                closure: closure.clone(),
                fid,
                act,
                compiled,
                nparams,
            },
        })
    }

    /// `recv.name(*args)` for a `&:name` proc: the method found for the
    /// last (receiver class, argument count) is cached in the proc, and a
    /// by-reference native is called without an argument list.
    pub fn call_named(
        &self,
        recv: &Value,
        args: &[Value],
        name: &str,
        cache: Option<&MethodCache>,
        method: Option<MethodId>,
    ) -> EvalResult {
        let cid = self.class_of(recv);
        let argc = args.len();
        // The method the checker resolved for the block's parameter type
        // is dispatched as a call would be (an extension method visible
        // there, or a module's method a value conforms to through an
        // extension, is not found by name).
        let mid = match (method, cache.and_then(Cell::get)) {
            (Some(m), _) => self.resolve_dynamic(recv, m),
            (None, Some((c, n, mid))) if c == cid && n == argc => mid,
            _ => match self.find_method(cid, name, argc, false) {
                Some(mid) => {
                    if let Some(cache) = cache {
                        cache.set(Some((cid, argc, mid)));
                    }
                    mid
                }
                None => return self.send(recv, name, args.iter().cloned().collect(), None),
            },
        };
        if argc <= 3 {
            if let Some(fast) = self.program.fast_natives[mid as usize] {
                let refs: SmallVec<[&Value; 3]> = args.iter().collect();
                if let Some(r) = fast(self, recv, &refs) {
                    return r;
                }
            }
        }
        self.invoke(
            mid,
            recv.clone(),
            args.iter().cloned().collect(),
            Vec::new(),
            None,
        )
    }
}

/// The method cache of an `&:name` procedure, unless the procedure is
/// shared: tasks on other threads may call it at once, and the cache is
/// a plain cell (the method is then looked up each time).
fn own_cache<'a>(
    closure: &crate::rc::Rc<Closure>,
    cache: &'a MethodCache,
) -> Option<&'a MethodCache> {
    (!crate::rc::Rc::is_shared(closure)).then_some(cache)
}

impl BlockCaller {
    /// Call the block with `args` (padded with nil or cut to the block's
    /// parameters).
    pub fn call(&self, args: &[Value]) -> EvalResult {
        crate::keys::check()?;
        // SAFETY: a caller never outlives the interpreter that made it.
        let interp = unsafe { &*self.interp };
        let (closure, fid, act, compiled, nparams) = match &self.kind {
            CallerKind::Func {
                closure,
                fid,
                act,
                compiled,
                nparams,
            } => (closure, *fid, act, *compiled, *nparams),
            CallerKind::Named { closure } => {
                let ClosureBody::MethodName(name, cache, method) = &closure.body else {
                    unreachable!()
                };
                let Some((recv, rest)) = args.split_first() else {
                    return Err(interp.err_arg("block needs an argument"));
                };
                return interp.call_named(recv, rest, name, own_cache(closure, cache), *method);
            }
        };
        if sched::stack_exhausted() {
            return Err(interp.raise(interp.program.exc.system_stack, "stack level too deep"));
        }
        let padded: ArgVec;
        let view: &[Value] = if args.len() == nparams {
            args
        } else {
            let mut v: ArgVec = args.iter().take(nparams).map(|a| a.fast_clone()).collect();
            while v.len() < nparams {
                v.push(Value::Nil);
            }
            padded = v;
            &padded
        };
        act.args_ptr.set(view.as_ptr());
        act.nargs.set(view.len() as u32);
        interp.push_call(act);
        let r = match compiled {
            Some(f) => {
                let mut out = Value::Nil;
                // SAFETY: `f` is the compiled body of `fid` (see `run_compiled`).
                let status = unsafe { f(interp, act, &mut out) };
                if status == crate::ffi::STATUS_OK {
                    Ok(out)
                } else {
                    Err(interp.take_flow(status))
                }
            }
            None => interp.run_func_inner(fid, act),
        };
        interp.pop_call_stack(act);
        match r {
            Ok(v) => Ok(v),
            Err(Flow::Next(v)) => Ok(v),
            Err(Flow::Return(v, t)) if closure.is_lambda && t == closure.tag => Ok(v),
            Err(Flow::Break(v, t)) if closure.is_lambda && t == closure.tag => Ok(v),
            Err(e) => Err(e),
        }
    }
}

impl Activation {
    pub fn has_arg(&self, i: u32) -> bool {
        i >= 64 || self.provided & (1u64 << i) != 0
    }

    /// Point the parameter view at `args`, which must outlive the
    /// activation.
    pub fn bind(&self, args: &[Value]) {
        self.args_ptr.set(args.as_ptr());
        self.nargs.set(args.len() as u32);
    }

    /// Point the parameter view at `args`, owned by this call: `Arg`
    /// moves its values out.
    pub fn bind_owned(&self, args: &mut [Value]) {
        self.args_ptr.set(args.as_mut_ptr());
        self.nargs.set(args.len() as u32);
        self.args_owned.set(true);
    }

    /// Parameter `i` for `Arg`: moved out of the view when the call owns
    /// it (each parameter is read once, at entry), else copied; nil when
    /// absent.
    pub fn take_arg(&self, i: u32) -> Value {
        let n = self.nargs.get();
        if i >= n {
            return Value::Nil;
        }
        if self.args_owned.get() {
            // SAFETY: an owned view (`bind_owned`, or a compiled caller's
            // area set by `qz_enter`) points at `n` live values this call
            // may take: the owner releases what is left, nil included.
            unsafe {
                std::ptr::replace(
                    (self.args_ptr.get() as *mut Value).add(i as usize),
                    Value::Nil,
                )
            }
        } else {
            self.params()[i as usize].clone()
        }
    }

    pub fn params(&self) -> &[Value] {
        let n = self.nargs.get() as usize;
        if n == 0 {
            return &[];
        }
        // SAFETY: `bind` (or `qz_enter`) pointed the view at `n` live
        // values that outlive the activation.
        unsafe { std::slice::from_raw_parts(self.args_ptr.get(), n) }
    }

    pub fn arg(&self, i: u32) -> Option<&Value> {
        self.params().get(i as usize)
    }
}

/// How one step of a block ended.
enum Step {
    /// Continue with the block.
    Jump(BlockId),
    Done(EvalResult),
}

impl Interp {
    pub fn func(&self, id: FuncId) -> Rc<FuncInfo> {
        self.funcs.borrow()[id as usize].clone()
    }

    /// Run a function to completion (its machine code when it has some).
    #[inline(always)]
    pub fn run_func(&self, fid: FuncId, act: &Activation) -> EvalResult {
        self.push_call(act);
        let r = self.run_func_inner(fid, act);
        self.pop_call_stack(act);
        // Objects released in the call are finalized now (when it
        // returns: an exception on its way out leaves them to the next
        // return, as compiled code does).
        if r.is_ok() && crate::deinit::pending() {
            self.run_deinitializers();
        }
        r
    }

    #[inline(always)]
    fn run_func_inner(&self, fid: FuncId, act: &Activation) -> EvalResult {
        if let Some(r) = self.run_compiled(fid, act) {
            return r;
        }
        match INTERPRETER.get() {
            Some(i) => (i.run)(self, fid, act),
            None => panic!("{} is not compiled", self.func(fid).name),
        }
    }

    /// Install the interpreter, which runs the functions without compiled
    /// code. Only what interprets calls this.
    pub fn install_interpreter() {
        let _ = INTERPRETER.set(Interpreter {
            run: |rt, fid, act| {
                let table = body_table(&rt.bodies).borrow();
                rt.interpret(&table[fid as usize], fid, act)
            },
            export: export_bodies,
            import: import_bodies,
            natives: crate::natives::all,
        });
    }

    fn interpret(&self, blocks: &[Block], fid: FuncId, act: &Activation) -> EvalResult {
        let funcs = self.funcs.borrow();
        let f = &funcs[fid as usize];
        let pools = self.pools.borrow();
        let pool = &pools[fid as usize];
        let n = f.nregs as usize;
        let mut regs: SmallVec<[Value; 16]> = if n <= 16 {
            SmallVec::new()
        } else {
            // Exactly the size needed (growing it by doubling, the files
            // of a deep recursion come out larger and unevenly placed,
            // measurably slower).
            let mut v = self.reg_pool.borrow_mut().pop().unwrap_or_default();
            v.reserve_exact(n);
            SmallVec::from_vec(v)
        };
        // Nil in every register, without a capacity check per push.
        // SAFETY: there is room for `n` (the inline 16, or the pooled
        // vector reserved above); each is written before the length
        // covers it.
        unsafe {
            let p = regs.as_mut_ptr();
            for i in 0..n {
                p.add(i).write(Value::Nil);
            }
            regs.set_len(n);
        }
        let mut pending: Option<Flow> = None;
        let r = self.run_blocks(f, blocks, pool, act, &mut regs, &mut pending);
        release_regs(&mut regs);
        if regs.spilled() {
            let v = regs.into_vec();
            let mut pool = self.reg_pool.borrow_mut();
            if pool.len() < 64 {
                pool.push(v);
            }
        }
        r
    }

    /// Remove `act` from the call stack. Tasks interleave on one stack,
    /// so the entry is usually, but not always, the last one.
    pub(crate) fn pop_call_stack(&self, act: &Activation) {
        let p = act as *const Activation;
        let len = self.hot.stack_len.get();
        // SAFETY: `len` entries of the buffer are initialized.
        let stack = unsafe { std::slice::from_raw_parts_mut(self.hot.stack_ptr.get(), len) };
        if stack.last() == Some(&p) {
            self.hot.stack_len.set(len - 1);
        } else if let Some(i) = stack.iter().rposition(|e| *e == p) {
            stack.copy_within(i + 1.., i);
            self.hot.stack_len.set(len - 1);
        }
    }

    /// Push an activation on the call stack (compiled code does this
    /// inline when there is room).
    #[inline]
    pub fn push_call(&self, act: &Activation) {
        act.sp.set(act as *const Activation as usize);
        let act = act as *const Activation;
        let len = self.hot.stack_len.get();
        if len == self.hot.stack_cap.get() {
            self.grow_call_stack();
        }
        // SAFETY: `len < cap` now.
        unsafe { *self.hot.stack_ptr.get().add(len) = act };
        self.hot.stack_len.set(len + 1);
    }

    #[cold]
    fn grow_call_stack(&self) {
        let len = self.hot.stack_len.get();
        let cap = self.hot.stack_cap.get();
        let new_cap = (cap * 2).max(256);
        let mut buf: Vec<*const Activation> = Vec::with_capacity(new_cap);
        // SAFETY: the old buffer holds `len` initialized entries.
        unsafe {
            buf.extend_from_slice(std::slice::from_raw_parts(self.hot.stack_ptr.get(), len));
            buf.set_len(0);
            if cap > 0 {
                drop(Vec::from_raw_parts(self.hot.stack_ptr.get(), 0, cap));
            }
        }
        let mut buf = std::mem::ManuallyDrop::new(buf);
        self.hot.stack_ptr.set(buf.as_mut_ptr());
        self.hot.stack_cap.set(new_cap);
    }

    /// The call stack, innermost last.
    pub fn call_stack(&self) -> &[*const Activation] {
        // SAFETY: `stack_len` entries of the buffer are initialized.
        unsafe { std::slice::from_raw_parts(self.hot.stack_ptr.get(), self.hot.stack_len.get()) }
    }

    /// Run the function's blocks from the entry to the end of the
    /// function (blocks follow one another here rather than through the
    /// caller: a step between blocks is a jump).
    #[allow(clippy::too_many_arguments)]
    fn run_blocks(
        &self,
        f: &FuncInfo,
        blocks: &[Block],
        pool: &RefCell<Vec<Value>>,
        act: &Activation,
        regs: &mut [Value],
        pending: &mut Option<Flow>,
    ) -> EvalResult {
        let mut block: BlockId = 0;
        let mut start = 0;
        'blocks: loop {
            let b = &blocks[block as usize];
            for (i, inst) in b.insts.iter().enumerate().skip(start) {
                // The commonest instructions that cannot fail, here rather
                // than through `exec_inst` (a large frame for one store).
                // They raise nothing, so the line is not needed either.
                match inst {
                    Inst::LoadConst { dst, idx } => {
                        // SAFETY: the pool is only borrowed mutably inside
                        // `constant` (to cache a regexp), never while the
                        // block loop reads it here.
                        let consts: &Vec<Value> = unsafe { &*pool.as_ptr() };
                        let c = &consts[*idx as usize];
                        let v = match c {
                            Value::Int(i) => Value::Int(*i),
                            Value::Float(x) => Value::Float(*x),
                            Value::Bool(b) => Value::Bool(*b),
                            Value::Nil => Value::Nil,
                            other => other.clone(),
                        };
                        if !v.is_nil()
                            || !matches!(f.consts[*idx as usize], Constant::Regexp { .. })
                        {
                            put(&mut regs[*dst as usize], v);
                            continue;
                        }
                    }
                    Inst::Move { dst, src } => {
                        let v = regs[*src as usize].clone();
                        put(&mut regs[*dst as usize], v);
                        continue;
                    }
                    Inst::Take { dst, src } => {
                        let v = std::mem::replace(&mut regs[*src as usize], Value::Nil);
                        put(&mut regs[*dst as usize], v);
                        continue;
                    }
                    Inst::Arg { dst, index } => {
                        put(&mut regs[*dst as usize], act.take_arg(*index));
                        continue;
                    }
                    Inst::SelfRef { dst } => {
                        put(&mut regs[*dst as usize], act.self_val.clone());
                        continue;
                    }
                    Inst::ClearRegs { from, to } => {
                        for r in &mut regs[*from as usize..*to as usize] {
                            put(r, Value::Nil);
                        }
                        continue;
                    }
                    Inst::Release { src } => {
                        put(&mut regs[*src as usize], Value::Nil);
                        if crate::deinit::pending() {
                            self.run_deinitializers();
                        }
                        continue;
                    }
                    Inst::IsNil { dst, src } => {
                        let v = Value::Bool(regs[*src as usize].is_nil());
                        put(&mut regs[*dst as usize], v);
                        continue;
                    }
                    Inst::BinOp {
                        dst, op, lhs, rhs, ..
                    } => {
                        // Two Ints, the commonest case, computed here and
                        // written straight into the register: a value built
                        // aside and copied in is read back before its stores
                        // are done, which costs more than the arithmetic.
                        if let (Value::Int(x), Value::Int(y)) =
                            (&regs[*lhs as usize], &regs[*rhs as usize])
                        {
                            let (x, y) = (*x, *y);
                            if int_binop_into(*op, x, y, &mut regs[*dst as usize]) {
                                continue;
                            }
                        } else if let Some((x, y)) =
                            float_operands(&regs[*lhs as usize], &regs[*rhs as usize])
                        {
                            float_binop_into(*op, x, y, &mut regs[*dst as usize]);
                            continue;
                        }
                    }
                    _ => {}
                }
                act.line.set(b.lines[i]);
                if let Err(flow) = self.exec_inst(f, pool, act, regs, pending, inst) {
                    match self.unwind(b, flow, pending) {
                        Step::Jump(h) => {
                            block = h;
                            start = 0;
                            continue 'blocks;
                        }
                        Step::Done(r) => return r,
                    }
                }
            }
            start = 0;
            let step = match &b.term {
                Term::Jump(t) => {
                    block = *t;
                    continue 'blocks;
                }
                Term::Branch { cond, then, els } => {
                    block = if regs[*cond as usize].is_truthy() {
                        *then
                    } else {
                        *els
                    };
                    continue 'blocks;
                }
                // The function ends here: its result is moved out.
                Term::Return(r) => {
                    return Ok(std::mem::replace(&mut regs[*r as usize], Value::Nil));
                }
                _ => {
                    act.line.set(b.term_line);
                    match &b.term {
                        Term::Raise(r) => {
                            self.unwind(b, Flow::Raise(regs[*r as usize].clone()), pending)
                        }
                        Term::BreakOut(r) => self.unwind(
                            b,
                            Flow::Break(regs[*r as usize].clone(), act.closure_tag),
                            pending,
                        ),
                        Term::ReturnOut(r) => self.unwind(
                            b,
                            Flow::Return(regs[*r as usize].clone(), act.method_tag),
                            pending,
                        ),
                        Term::Resume(r) => match &regs[*r as usize] {
                            Value::Flow(fb) => match fb.borrow_mut().take() {
                                Some(flow) => self.unwind(b, flow, pending),
                                None => Step::Done(Ok(Value::Nil)),
                            },
                            _ => Step::Done(Ok(Value::Nil)),
                        },
                        _ => Step::Done(Err(self.raise(
                            self.program.exc.runtime_error,
                            "internal error: unreachable code executed (in a compiled program, \
                             possibly a function the build dropped as unreachable: \
                             QUARZ_NO_SHAKE=1 at build time keeps them)",
                        ))),
                    }
                }
            };
            match step {
                Step::Jump(h) => block = h,
                Step::Done(r) => return r,
            }
        }
    }

    /// Route a flow leaving `b` to its handler, or out of the function.
    fn unwind(&self, b: &quarz_ir::Block, flow: Flow, pending: &mut Option<Flow>) -> Step {
        match b.handler {
            Some(h) if h.kind == HandlerKind::Ensure || matches!(flow, Flow::Raise(_)) => {
                *pending = Some(flow);
                Step::Jump(h.block)
            }
            _ => Step::Done(Err(flow)),
        }
    }

    pub(crate) fn frame<'a>(&self, act: &'a Activation) -> &'a Rc<Frame> {
        act.frame
            .as_ref()
            .expect("function without a frame uses one")
    }

    /// Materialize constant `idx` of the function (regexps are compiled on
    /// first use, since they may be invalid).
    pub(crate) fn constant(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        idx: u32,
    ) -> EvalResult {
        let v = pool.borrow()[idx as usize].clone();
        if !v.is_nil() {
            return Ok(v);
        }
        if let Constant::Regexp { source, flags } = &f.consts[idx as usize] {
            let v = self.make_regexp(source, flags)?;
            pool.borrow_mut()[idx as usize] = v.clone();
            return Ok(v);
        }
        Ok(v)
    }

    pub(crate) fn symbol_const(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        idx: u32,
    ) -> Symbol {
        match &pool.borrow()[idx as usize] {
            Value::Symbol(s) => *s,
            _ => match &f.consts[idx as usize] {
                Constant::Symbol(name) | Constant::Str(name) => self.intern(name),
                _ => self.intern(""),
            },
        }
    }

    /// The string of an `Interpolate`: every piece is written into one
    /// reused buffer (a number is formatted there, not through a
    /// temporary string).
    /// `Inst::Interpolate`: a new string, or (`into`) the text appended
    /// to a `String::Builder`, which is the result. The text is built in
    /// a reused buffer first (a `to_s` may run user code, even code
    /// that appends to the same builder), then copied in.
    pub fn interpolate_inst(
        &self,
        f: &FuncInfo,
        regs: &[Value],
        parts: impl Iterator<Item = StrPiece> + Clone,
        into: Option<Reg>,
    ) -> EvalResult {
        let Some(b) = into else {
            return self.interpolate(f, regs, parts);
        };
        let target = &regs[b as usize];
        if !matches!(target, Value::StringBuilder(_)) {
            // Not a builder after all: `<<` by name.
            let s = self.interpolate(f, regs, parts)?;
            return self.send(target, "<<", smallvec![s], None);
        }
        self.append_interpolation(f, regs, parts, b)?;
        Ok(regs[b as usize].clone())
    }

    /// Append the interpolation to the `String::Builder` in `regs[b]`.
    pub fn append_interpolation(
        &self,
        f: &FuncInfo,
        regs: &[Value],
        parts: impl Iterator<Item = StrPiece> + Clone,
        b: Reg,
    ) -> Result<(), Flow> {
        let Value::StringBuilder(sb) = &regs[b as usize] else {
            unreachable!("append_interpolation on a non-builder")
        };
        // Strings, integers, nil and booleans are written straight into
        // the builder (their text runs no user code).
        let plain = parts.clone().all(|p| match p {
            StrPiece::Lit(_) => true,
            StrPiece::Val(r) => matches!(
                regs[r as usize],
                Value::Str(_) | Value::Short(_) | Value::Int(_) | Value::Nil | Value::Bool(_)
            ),
        });
        if plain {
            let mut buf = sb.borrow_mut();
            for p in parts {
                match p {
                    StrPiece::Lit(idx) => buf.push_str(self.str_const(f, idx)),
                    StrPiece::Val(r) => self.append_to_s(&mut buf, &regs[r as usize])?,
                }
            }
            return Ok(());
        }
        let mut failed = None;
        Value::with_scratch(|s| {
            for p in parts {
                match p {
                    StrPiece::Lit(idx) => s.push_str(self.str_const(f, idx)),
                    StrPiece::Val(r) => {
                        if let Err(e) = self.append_to_s(s, &regs[r as usize]) {
                            failed = Some(e);
                            return;
                        }
                    }
                }
            }
            sb.borrow_mut().push_str(s);
        });
        match failed {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    pub fn interpolate(
        &self,
        f: &FuncInfo,
        regs: &[Value],
        parts: impl Iterator<Item = StrPiece>,
    ) -> EvalResult {
        let mut failed = None;
        let v = Value::build_string(|s| {
            for p in parts {
                match p {
                    StrPiece::Lit(idx) => s.push_str(self.str_const(f, idx)),
                    StrPiece::Val(r) => {
                        if let Err(e) = self.append_to_s(s, &regs[r as usize]) {
                            failed = Some(e);
                            return;
                        }
                    }
                }
            }
        });
        match failed {
            Some(e) => Err(e),
            None => Ok(v),
        }
    }

    pub(crate) fn str_const<'f>(&self, f: &'f FuncInfo, idx: u32) -> &'f str {
        match &f.consts[idx as usize] {
            Constant::Str(s) | Constant::Symbol(s) => s,
            _ => "",
        }
    }

    /// Positional arguments of a call (expanding a splat array).
    pub(crate) fn call_args(&self, regs: &[Value], args: &[Reg], splat: bool) -> ArgVec {
        if splat {
            return match &regs[args[0] as usize] {
                Value::Array(a) => a.iter().collect(),
                other => smallvec![other.clone()],
            };
        }
        args.iter().map(|r| regs[*r as usize].clone()).collect()
    }

    pub(crate) fn call_kwargs(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        regs: &[Value],
        kw: &[(u32, Reg)],
        kw_splat: Option<Reg>,
    ) -> Vec<(Symbol, Value)> {
        if kw.is_empty() && kw_splat.is_none() {
            return Vec::new();
        }
        let mut out: Vec<(Symbol, Value)> = kw
            .iter()
            .map(|(k, r)| (self.symbol_const(f, pool, *k), regs[*r as usize].clone()))
            .collect();
        if let Some(h) = kw_splat {
            if let Value::Hash(h) = &regs[h as usize] {
                for (k, v) in h.as_map().iter() {
                    if let Value::Symbol(s) = k {
                        out.push((*s, v.clone()));
                    }
                }
            }
        }
        out
    }

    #[allow(clippy::too_many_arguments)]
    pub fn exec_inst(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        act: &Activation,
        regs: &mut [Value],
        pending: &mut Option<Flow>,
        inst: &Inst,
    ) -> Result<(), Flow> {
        match inst {
            Inst::LoadConst { dst, idx } => self.op_load_const(f, pool, regs, *dst, *idx)?,
            Inst::Move { dst, src } => {
                let v = regs[*src as usize].clone();
                regs[*dst as usize] = v;
            }
            Inst::Take { dst, src } => {
                let v = std::mem::replace(&mut regs[*src as usize], Value::Nil);
                regs[*dst as usize] = v;
            }
            Inst::SelfRef { dst } => regs[*dst as usize] = act.self_val.clone(),
            Inst::Arg { dst, index } => {
                regs[*dst as usize] = act.take_arg(*index);
            }
            Inst::HasArg { dst, index } => self.op_has_arg(act, regs, *dst, *index),
            Inst::BlockParam { dst } => {
                regs[*dst as usize] = act.block.clone();
            }
            Inst::FrameGet { dst, depth, slot } => {
                regs[*dst as usize] = self.frame(act).get(*depth, *slot);
            }
            Inst::FrameSet { depth, slot, src } => {
                let v = regs[*src as usize].clone();
                self.frame(act).set(*depth, *slot, v);
            }
            Inst::FieldGet {
                dst, obj, index, ..
            } => {
                if let (Value::Object(o), true) = (&regs[*obj as usize], obj != dst) {
                    let o: *const Object = &**o;
                    let slot: *mut Value = &mut regs[*dst as usize];
                    // SAFETY: the register holding the object is another
                    // one, which keeps it alive while `slot` is written.
                    if unsafe { (*o).field_into(*index as usize, slot) } {
                        return Ok(());
                    }
                }
                let v = match &regs[*obj as usize] {
                    Value::Object(o) => o.field(*index as usize).unwrap_or(Value::Nil),
                    _ => {
                        return Err(self.raise(
                            self.program.exc.runtime_error,
                            "instance variable access outside of an object",
                        ))
                    }
                };
                regs[*dst as usize] = v;
            }
            Inst::FieldSet {
                obj, index, src, ..
            } => {
                let v = regs[*src as usize].clone();
                match &regs[*obj as usize] {
                    Value::Object(o) => o.set_field(*index as usize, v),
                    _ => {
                        return Err(self.raise(
                            self.program.exc.runtime_error,
                            "instance variable access outside of an object",
                        ))
                    }
                }
            }
            Inst::FieldGetByName {
                dst,
                found,
                obj,
                name,
            } => self.op_field_get_by_name(f, regs, *dst, *found, *obj, *name),
            Inst::ConstGet { dst, id } => self.op_const_get(regs, *dst, *id)?,
            Inst::ClassRef { dst, class } => regs[*dst as usize] = Value::Class(*class),
            Inst::VariantSingleton { dst, class } => self.op_variant_singleton(regs, *dst, *class),
            Inst::Call {
                dst,
                kind,
                recv,
                args,
                splat,
                kw,
                kw_splat,
                block,
                moved,
            } => self.op_call(
                f,
                pool,
                act,
                regs,
                crate::ops::CallOps {
                    dst: *dst,
                    kind: crate::ops::CallOp::of(kind),
                    recv: *recv,
                    args,
                    splat: *splat,
                    kw,
                    kw_splat: *kw_splat,
                    block: *block,
                    moved: *moved,
                },
            )?,
            Inst::OwnedCall {
                dst,
                method,
                recv,
                args,
                kw,
                unused,
            } => self.op_owned_call(
                f,
                pool,
                act,
                regs,
                crate::ops::OwnedOps {
                    dst: *dst,
                    method: *method,
                    recv: *recv,
                    args,
                    kw,
                    unused: *unused,
                },
            )?,
            Inst::IsNil { dst, src } => {
                regs[*dst as usize] = Value::Bool(regs[*src as usize].is_nil());
            }
            Inst::BinOp {
                dst,
                op,
                lhs,
                rhs,
                method,
            } => self.op_binop(regs, *dst, *op, *lhs, *rhs, *method)?,
            Inst::Not { dst, src } => {
                regs[*dst as usize] = Value::Bool(!regs[*src as usize].is_truthy());
            }
            Inst::CaseEq {
                dst,
                pattern,
                value,
            } => self.op_case_eq(regs, *dst, *pattern, *value)?,
            Inst::Equal { dst, a, b } => self.op_equal(regs, *dst, *a, *b)?,
            Inst::ClassIs { dst, src, class } => {
                let r = matches!(&regs[*src as usize], Value::Object(o) if o.class == *class);
                regs[*dst as usize] = Value::Bool(r);
            }
            Inst::ClassIsA { dst, src, class } => self.op_class_is_a(regs, *dst, *src, *class),
            Inst::IsA { dst, src, ty } => self.op_is_a(regs, *dst, *src, ty),
            Inst::As {
                dst,
                src,
                ty,
                optional,
                name,
            } => self.op_as(regs, *dst, *src, ty, *optional, name)?,
            Inst::MakeBlock {
                dst,
                func,
                destructure,
                is_lambda,
            } => self.op_make_block(act, regs, *dst, *func, *destructure, *is_lambda),
            Inst::MethodRef { dst, recv, name } => {
                self.op_method_ref(f, act, regs, *dst, *recv, *name)
            }
            Inst::SymbolProc { dst, name, method } => {
                self.op_symbol_proc(f, act, regs, *dst, *name, *method)
            }
            Inst::MakeArray { dst, items } => {
                self.op_make_array(regs, *dst, items.iter().map(|i| (i.reg, i.splat)))
            }
            Inst::MakeHash { dst, items } => {
                self.op_make_hash(regs, *dst, items.iter().copied())?
            }
            Inst::MakeRange {
                dst,
                lo,
                hi,
                exclusive,
            } => self.op_make_range(regs, *dst, *lo, *hi, *exclusive),
            Inst::MakeRegexp { dst, source, flags } => {
                self.op_make_regexp(regs, *dst, *source, flags)?
            }
            Inst::Interpolate { dst, parts, into } => {
                regs[*dst as usize] =
                    self.interpolate_inst(f, regs, parts.iter().copied(), *into)?;
            }
            Inst::ToSym { dst, src } => self.op_to_sym(regs, *dst, *src)?,
            Inst::IsArray { dst, src } => self.op_is_array(regs, *dst, *src),
            Inst::IsHash { dst, src } => self.op_is_hash(regs, *dst, *src),
            Inst::IsObject { dst, src } => self.op_is_object(regs, *dst, *src),
            Inst::ToArray { dst, src } => self.op_to_array(regs, *dst, *src),
            Inst::Len { dst, src } => self.op_len(regs, *dst, *src),
            Inst::ArrayGet { dst, arr, index } => self.op_array_get(regs, *dst, *arr, *index),
            Inst::ArrayGetReg {
                dst, arr, index, ..
            } => self.op_array_get_reg(regs, *dst, *arr, *index),
            Inst::ArrayWords { dst, arr, float } => {
                self.op_array_words(regs, *dst, *arr, *float)?
            }
            Inst::ArrayIndex {
                dst, arr, index, ..
            } => self.op_array_index(regs, *dst, *arr, *index)?,
            Inst::ArrayGetWord {
                dst, arr, index, ..
            } => self.op_array_get_reg(regs, *dst, *arr, *index),
            Inst::ArraySlice {
                dst,
                arr,
                from,
                drop_last,
            } => self.op_array_slice(regs, *dst, *arr, *from, *drop_last),
            Inst::ArraySliceReg { dst, arr, from, to } => {
                self.op_array_slice_reg(regs, *dst, *arr, *from, *to)
            }
            Inst::ObjectFields { dst, src } => self.op_object_fields(regs, *dst, *src),
            Inst::HashGetSym {
                dst,
                found,
                hash,
                key,
            } => self.op_hash_get_sym(f, pool, regs, *dst, *found, *hash, *key),
            Inst::ArrayPush { arr, src } | Inst::ArrayPushWord { arr, src, .. } => {
                self.op_array_push(regs, *arr, *src)?
            }
            Inst::ArrayNewWords {
                dst,
                capacity,
                float,
            } => self.op_array_new_words(regs, *dst, *capacity, *float),
            Inst::HashRest { dst, hash, keys } => {
                self.op_hash_rest(f, pool, regs, *dst, *hash, keys.iter().copied())
            }
            Inst::CatchException { dst } => self.op_catch_exception(regs, pending, *dst)?,
            Inst::CatchAny { dst } => self.op_catch_any(regs, pending, *dst),
            Inst::ClearRegs { from, to } => {
                for r in &mut regs[*from as usize..*to as usize] {
                    *r = Value::Nil;
                }
            }
            Inst::Release { src } => {
                regs[*src as usize] = Value::Nil;
                if crate::deinit::pending() {
                    self.run_deinitializers();
                }
            }
            Inst::Rescuing { src, enter } => self.op_rescuing(regs, *src, *enter),
            Inst::NoMatch { src, is_assert } => {
                return Err(self.op_no_match(regs, *src, *is_assert))
            }
        }
        Ok(())
    }

    // ----- calling functions ---------------------------------------------------------------

    /// Call a block/procedure value with arguments. `next` yields the
    /// block's value; `break` propagates to the call that received it.
    pub fn call_block(&self, proc: &Value, args: ArgVec) -> EvalResult {
        self.call_block_on(proc, None, args)
    }

    /// Call a block, with `self` replaced by `recv` when given (a block
    /// with a receiver, run by `instance_exec`).
    pub fn call_block_on(&self, proc: &Value, recv: Option<Value>, mut args: ArgVec) -> EvalResult {
        // What a key's own `==` or `hash` raised is raised before any more
        // Quarz code runs (`crate::keys`).
        crate::keys::check()?;
        let Value::Proc(closure) = proc else {
            return Err(self.err_type("not a procedure"));
        };
        match &closure.body {
            ClosureBody::MethodName(name, cache, method) => {
                if args.is_empty() {
                    return Err(self.err_arg("block needs an argument"));
                }
                let recv = args.remove(0);
                self.call_named(&recv, &args, name, own_cache(closure, cache), *method)
            }
            ClosureBody::BoundMethod { recv, name } => self.send(recv, name, args, None),
            ClosureBody::Native(f) => f(self, args),
            ClosureBody::Func(fid) => {
                if sched::stack_exhausted() {
                    return Err(self.raise(self.program.exc.system_stack, "stack level too deep"));
                }
                let funcs = self.funcs.borrow();
                let f = &funcs[*fid as usize];
                let frame = if f.frame_size > 0 {
                    Some(Frame::new(f.frame_size as usize, closure.frame.clone()))
                } else {
                    closure.frame.clone()
                };
                // Destructure a single array argument over several parameters.
                if let Some(n) = closure.destructure {
                    if args.len() == 1 {
                        if let Value::Array(a) = &args[0] {
                            let mut items: ArgVec = a.iter().collect();
                            items.resize(n.max(items.len()), Value::Nil);
                            args = items;
                        }
                    }
                }
                let file = closure.file;
                let nparams = f.param_kinds.len();
                // The common shape: positional parameters, one argument
                // each. The arguments are the bound list as they are.
                let simple = args.len() == nparams
                    && nparams < 64
                    && f.param_kinds
                        .iter()
                        .all(|k| matches!(k, RtParamKind::Positional | RtParamKind::KeywordOnly));
                let (mut bound, provided) = if simple {
                    (args, (1u64 << nparams) - 1)
                } else {
                    let mut bound: ArgVec = ArgVec::with_capacity(nparams);
                    let mut provided = 0u64;
                    let mut it = args.into_iter();
                    for (i, kind) in f.param_kinds.iter().enumerate() {
                        match kind {
                            RtParamKind::Rest => {
                                let rest: Vec<Value> = it.by_ref().collect();
                                bound.push(Value::array(rest));
                                provided |= 1 << i.min(63);
                            }
                            RtParamKind::Block => bound.push(Value::Nil),
                            _ => match it.next() {
                                Some(v) => {
                                    bound.push(v);
                                    provided |= 1 << i.min(63);
                                }
                                None => bound.push(Value::Nil),
                            },
                        }
                    }
                    (bound, provided)
                };
                let act = Activation {
                    fid: *fid,
                    task: self.current_task_id.get(),
                    line: Cell::new(0),
                    self_val: match recv {
                        Some(v) => v,
                        None => closure.self_val.fast_clone(),
                    },
                    frame,
                    block: closure
                        .method_block
                        .as_ref()
                        .map_or(Value::Nil, |b| b.fast_clone()),
                    method_tag: if closure.is_lambda {
                        closure.tag
                    } else {
                        closure.method_tag
                    },
                    closure_tag: closure.tag,
                    file,
                    provided,
                    args_ptr: Cell::new(std::ptr::null()),
                    nargs: Cell::new(0),
                    yield_caller: Default::default(),
                    sp: Cell::new(0),
                    native: Cell::new(false),
                    args_owned: Cell::new(false),
                };
                act.bind_owned(&mut bound);
                let r = match self.run_func(*fid, &act) {
                    Ok(v) => Ok(v),
                    Err(Flow::Next(v)) => Ok(v),
                    Err(Flow::Return(v, t)) if closure.is_lambda && t == closure.tag => Ok(v),
                    Err(Flow::Break(v, t)) if closure.is_lambda && t == closure.tag => Ok(v),
                    Err(e) => Err(e),
                };
                // Take the activation apart without destructors for the
                // values that need none.
                let Activation {
                    self_val,
                    frame,
                    block,
                    ..
                } = act;
                self_val.fast_drop();
                block.fast_drop();
                drop(frame);
                drop(bound);
                r
            }
        }
    }

    /// Run a constant initializer or field default with the given `self`.
    pub fn run_init(&self, fid: FuncId, self_val: Value, file: u32) -> EvalResult {
        let f = self.func(fid);
        let frame = if f.frame_size > 0 {
            Some(Frame::new(f.frame_size as usize, None))
        } else {
            None
        };
        let act = Activation {
            fid,
            task: self.current_task_id.get(),
            line: Cell::new(0),
            self_val,
            frame,
            block: Value::Nil,
            method_tag: self.new_tag(),
            closure_tag: 0,
            file,
            provided: 0,
            args_ptr: Cell::new(std::ptr::null()),
            nargs: Cell::new(0),
            yield_caller: Default::default(),
            sp: Cell::new(0),
            native: Cell::new(false),
            args_owned: Cell::new(false),
        };
        self.run_func(fid, &act)
    }

    /// Run a method body (parameters already bound).
    pub fn run_method(
        &self,
        _mid: MethodId,
        fid: FuncId,
        recv: Value,
        mut args: ArgVec,
        provided: u64,
        block: Option<Value>,
    ) -> EvalResult {
        if sched::stack_exhausted() {
            return Err(self.raise(self.program.exc.system_stack, "stack level too deep"));
        }
        let (frame_size, file) = {
            let funcs = self.funcs.borrow();
            let f = &funcs[fid as usize];
            (f.frame_size, f.file)
        };
        let frame = if frame_size > 0 {
            Some(Frame::new(frame_size as usize, None))
        } else {
            None
        };
        let tag = self.new_tag();
        let act = Activation {
            fid,
            task: self.current_task_id.get(),
            line: Cell::new(0),
            self_val: recv,
            frame,
            block: block.unwrap_or(Value::Nil),
            method_tag: tag,
            closure_tag: 0,
            file,
            provided,
            args_ptr: Cell::new(std::ptr::null()),
            nargs: Cell::new(0),
            yield_caller: Default::default(),
            sp: Cell::new(0),
            native: Cell::new(false),
            args_owned: Cell::new(false),
        };
        act.bind_owned(&mut args);
        let r = self.run_func(fid, &act);
        match r {
            Err(Flow::Return(v, t)) if t == tag => Ok(v),
            r => r,
        }
    }

    /// Run a unit's top level (or a REPL input in the persistent frame).
    pub(crate) fn run_top_level(&self, fid: FuncId, file: u32, self_val: Value) -> EvalResult {
        let f = self.func(fid);
        let frame = match f.kind {
            FuncKind::Repl => Some(
                self.repl_frame
                    .clone()
                    .unwrap_or_else(|| Frame::new(16, None)),
            ),
            _ if f.frame_size > 0 => Some(Frame::new(f.frame_size as usize, None)),
            _ => None,
        };
        let act = Activation {
            fid,
            task: self.current_task_id.get(),
            line: Cell::new(0),
            self_val,
            frame,
            block: Value::Nil,
            method_tag: 0,
            closure_tag: 0,
            file,
            provided: 0,
            args_ptr: Cell::new(std::ptr::null()),
            nargs: Cell::new(0),
            yield_caller: Default::default(),
            sp: Cell::new(0),
            native: Cell::new(false),
            args_owned: Cell::new(false),
        };
        self.run_func(fid, &act)
    }
}

/// Positional arguments stored inline (re-exported for natives).
pub type Args4 = SmallVec<[Value; 4]>;

/// Empty a register file: only the values holding a reference are
/// released one by one (most registers hold nil or a number).
fn release_regs(regs: &mut SmallVec<[Value; 16]>) {
    for r in regs.iter_mut() {
        if !matches!(
            r,
            Value::Nil
                | Value::Bool(_)
                | Value::Int(_)
                | Value::Float(_)
                | Value::Symbol(_)
                | Value::Class(_)
                | Value::Duration(_)
                | Value::Short(_)
        ) {
            *r = Value::Nil;
        }
    }
    // SAFETY: every element is now a variant without drop glue, so
    // forgetting them leaks nothing.
    unsafe { regs.set_len(0) };
}

/// `*slot = v`, without calling into the drop glue when the old value
/// holds no reference (a register usually holds nil or a number).
#[inline(always)]
pub(crate) fn put(slot: &mut Value, v: Value) {
    if matches!(
        slot,
        Value::Nil
            | Value::Bool(_)
            | Value::Int(_)
            | Value::Float(_)
            | Value::Symbol(_)
            | Value::Class(_)
            | Value::Duration(_)
            | Value::Short(_)
    ) {
        // SAFETY: the old value has no drop glue, so overwriting it
        // without dropping leaks nothing.
        unsafe { std::ptr::write(slot, v) }
    } else {
        *slot = v;
    }
}
