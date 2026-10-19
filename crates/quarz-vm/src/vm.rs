//! The QIR interpreter: activation records and the execution of
//! instructions. Compiled code (`quarz build`) shares the instruction
//! semantics through `exec_inst`.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use quarz_ir::*;
use smallvec::{smallvec, SmallVec};

use crate::interp::{fast_binop, ArgVec, EvalResult, Flow, Interp};
use crate::sched;
use crate::value::*;

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
    closure: Rc<Closure>,
    fid: FuncId,
    act: Activation,
    compiled: Option<crate::interp::CompiledFn>,
    nparams: usize,
}

impl Interp {
    /// A reusable caller for `proc`, or `None` when it needs the general
    /// path (`call_block`).
    pub fn block_caller(&self, proc: &Value) -> Option<BlockCaller> {
        let Value::Proc(closure) = proc else {
            return None;
        };
        let ClosureBody::Func(fid) = closure.body else {
            return None;
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
        };
        let compiled = self.compiled.borrow().get(fid as usize).copied().flatten();
        Some(BlockCaller {
            interp: self,
            closure: closure.clone(),
            fid,
            act,
            compiled,
            nparams,
        })
    }
}

impl BlockCaller {
    /// Call the block with `args` (padded with nil or cut to the block's
    /// parameters).
    pub fn call(&self, args: &[Value]) -> EvalResult {
        // SAFETY: a caller never outlives the interpreter that made it.
        let interp = unsafe { &*self.interp };
        if sched::stack_exhausted() {
            return Err(interp.raise(interp.exc.system_stack, "stack level too deep"));
        }
        let padded: ArgVec;
        let view: &[Value] = if args.len() == self.nparams {
            args
        } else {
            let mut v: ArgVec = args
                .iter()
                .take(self.nparams)
                .map(|a| a.fast_clone())
                .collect();
            while v.len() < self.nparams {
                v.push(Value::Nil);
            }
            padded = v;
            &padded
        };
        self.act.args_ptr.set(view.as_ptr());
        self.act.nargs.set(view.len() as u32);
        let act = &self.act;
        interp.push_call(act as *const Activation);
        let r = match self.compiled {
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
            None => interp.run_func_inner(self.fid, act),
        };
        interp.pop_call_stack(act);
        let closure = &self.closure;
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
    pub fn func(&self, id: FuncId) -> Rc<Function> {
        self.funcs.borrow()[id as usize].clone()
    }

    /// Run a function to completion (its machine code when it has some).
    #[inline(always)]
    pub fn run_func(&self, fid: FuncId, act: &Activation) -> EvalResult {
        self.push_call(act as *const Activation);
        let r = self.run_func_inner(fid, act);
        self.pop_call_stack(act);
        r
    }

    #[inline(always)]
    fn run_func_inner(&self, fid: FuncId, act: &Activation) -> EvalResult {
        if let Some(r) = self.run_compiled(fid, act) {
            return r;
        }
        let funcs = self.funcs.borrow();
        let f = &funcs[fid as usize];
        let pools = self.pools.borrow();
        let pool = &pools[fid as usize];
        let mut regs: SmallVec<[Value; 16]> = smallvec![Value::Nil; f.nregs as usize];
        let mut pending: Option<Flow> = None;
        let mut block = 0;
        loop {
            match self.run_block(f, fid, pool, act, &mut regs, &mut pending, block) {
                Step::Jump(b) => block = b,
                Step::Done(r) => return r,
            }
        }
    }

    /// Continue a function in the interpreter from instruction `inst` of
    /// `block`, on the registers compiled code was using (it gives up on
    /// a speculation it cannot keep, such as an Int growing into a
    /// BigInt). The registers are the caller's to release afterwards.
    pub fn run_func_from(
        &self,
        fid: FuncId,
        act: &Activation,
        regs: &mut [Value],
        block: BlockId,
        inst: usize,
    ) -> EvalResult {
        let funcs = self.funcs.borrow();
        let f = &funcs[fid as usize];
        let pools = self.pools.borrow();
        let pool = &pools[fid as usize];
        let mut pending: Option<Flow> = None;
        let mut block = block;
        let mut start = inst;
        loop {
            match self.run_block_from(f, fid, pool, act, regs, &mut pending, block, start) {
                Step::Jump(b) => {
                    block = b;
                    start = 0;
                }
                Step::Done(r) => return r,
            }
        }
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
    pub fn push_call(&self, act: *const Activation) {
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

    #[allow(clippy::too_many_arguments)]
    fn run_block(
        &self,
        f: &Function,
        fid: FuncId,
        pool: &RefCell<Vec<Value>>,
        act: &Activation,
        regs: &mut [Value],
        pending: &mut Option<Flow>,
        block: BlockId,
    ) -> Step {
        self.run_block_from(f, fid, pool, act, regs, pending, block, 0)
    }

    /// Run a block from its instruction `start` on.
    #[allow(clippy::too_many_arguments)]
    fn run_block_from(
        &self,
        f: &Function,
        fid: FuncId,
        pool: &RefCell<Vec<Value>>,
        act: &Activation,
        regs: &mut [Value],
        pending: &mut Option<Flow>,
        block: BlockId,
        start: usize,
    ) -> Step {
        let b = &f.blocks[block as usize];
        for (i, inst) in b.insts.iter().enumerate().skip(start) {
            act.line.set(b.lines[i]);
            if let Err(flow) = self.exec_inst(f, fid, pool, act, regs, pending, inst) {
                return self.unwind(b, flow, pending);
            }
        }
        act.line.set(b.term_line);
        match &b.term {
            Term::Jump(t) => Step::Jump(*t),
            Term::Branch { cond, then, els } => {
                if regs[*cond as usize].is_truthy() {
                    Step::Jump(*then)
                } else {
                    Step::Jump(*els)
                }
            }
            Term::Return(r) => Step::Done(Ok(regs[*r as usize].clone())),
            Term::Raise(r) => self.unwind(b, Flow::Raise(regs[*r as usize].clone()), pending),
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
            Term::Unreachable => Step::Done(Err(self.raise(
                self.exc.runtime_error,
                "internal error: unreachable code executed",
            ))),
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

    fn frame<'a>(&self, act: &'a Activation) -> &'a Rc<Frame> {
        act.frame
            .as_ref()
            .expect("function without a frame uses one")
    }

    /// Materialize constant `idx` of the function (regexps are compiled on
    /// first use, since they may be invalid).
    fn constant(&self, f: &Function, pool: &RefCell<Vec<Value>>, idx: u32) -> EvalResult {
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

    fn symbol_const(&self, f: &Function, pool: &RefCell<Vec<Value>>, idx: u32) -> Symbol {
        match &pool.borrow()[idx as usize] {
            Value::Symbol(s) => *s,
            _ => match &f.consts[idx as usize] {
                Constant::Symbol(name) | Constant::Str(name) => self.intern(name),
                _ => self.intern(""),
            },
        }
    }

    fn str_const<'f>(&self, f: &'f Function, idx: u32) -> &'f str {
        match &f.consts[idx as usize] {
            Constant::Str(s) | Constant::Symbol(s) => s,
            _ => "",
        }
    }

    /// Positional arguments of a call (expanding a splat array).
    fn call_args(&self, regs: &[Value], args: &[Reg], splat: bool) -> ArgVec {
        if splat {
            return match &regs[args[0] as usize] {
                Value::Array(a) => a.iter().collect(),
                other => smallvec![other.clone()],
            };
        }
        args.iter().map(|r| regs[*r as usize].clone()).collect()
    }

    fn call_kwargs(
        &self,
        f: &Function,
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
                for (k, v) in h.iter() {
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
        f: &Function,
        fid: FuncId,
        pool: &RefCell<Vec<Value>>,
        act: &Activation,
        regs: &mut [Value],
        pending: &mut Option<Flow>,
        inst: &Inst,
    ) -> Result<(), Flow> {
        match inst {
            Inst::LoadConst { dst, idx } => {
                regs[*dst as usize] = self.constant(f, pool, *idx)?;
            }
            Inst::Move { dst, src } => {
                let v = regs[*src as usize].clone();
                regs[*dst as usize] = v;
            }
            Inst::SelfRef { dst } => regs[*dst as usize] = act.self_val.clone(),
            Inst::Arg { dst, index } => {
                regs[*dst as usize] = act.arg(*index).cloned().unwrap_or(Value::Nil);
            }
            Inst::HasArg { dst, index } => {
                regs[*dst as usize] = Value::Bool(act.has_arg(*index));
            }
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
                let v = match &regs[*obj as usize] {
                    Value::Object(o) => o
                        .fields
                        .borrow()
                        .get(*index as usize)
                        .cloned()
                        .unwrap_or(Value::Nil),
                    _ => {
                        return Err(self.raise(
                            self.exc.runtime_error,
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
                    Value::Object(o) => {
                        let mut fields = o.fields.borrow_mut();
                        let idx = *index as usize;
                        if idx >= fields.len() {
                            fields.resize(idx + 1, Value::Nil);
                        }
                        fields[idx] = v;
                    }
                    _ => {
                        return Err(self.raise(
                            self.exc.runtime_error,
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
            } => {
                let name = self.str_const(f, *name);
                let (v, ok) = match &regs[*obj as usize] {
                    Value::Object(o) => match self.field_index(o.class, name) {
                        Some(i) => (
                            o.fields.borrow().get(i).cloned().unwrap_or(Value::Nil),
                            true,
                        ),
                        None => (Value::Nil, false),
                    },
                    _ => (Value::Nil, false),
                };
                regs[*dst as usize] = v;
                regs[*found as usize] = Value::Bool(ok);
            }
            Inst::ConstGet { dst, id } => regs[*dst as usize] = self.const_value(*id)?,
            Inst::ClassRef { dst, class } => regs[*dst as usize] = Value::Class(*class),
            Inst::VariantSingleton { dst, class } => {
                regs[*dst as usize] = self.variant_singleton(*class);
            }
            Inst::Call {
                dst,
                kind,
                recv,
                args,
                splat,
                kw,
                kw_splat,
                block,
            } => {
                // A native with a by-reference version takes the
                // receiver and arguments from the registers directly.
                if let CallKind::Method(mid) = kind {
                    if !*splat
                        && kw.is_empty()
                        && kw_splat.is_none()
                        && block.is_none()
                        && args.len() <= 3
                    {
                        let recv_ref = match recv {
                            Some(r) => &regs[*r as usize],
                            None => &act.self_val,
                        };
                        let mid = self.resolve_dynamic(recv_ref, *mid);
                        if let Some(fast) = self.fast_natives[mid as usize] {
                            let result = {
                                let refs: SmallVec<[&Value; 3]> =
                                    args.iter().map(|r| &regs[*r as usize]).collect();
                                fast(self, recv_ref, &refs)
                            };
                            if let Some(r) = result {
                                let v = r?;
                                regs[*dst as usize] = v;
                                return Ok(());
                            }
                        }
                    }
                }
                let recv = match recv {
                    Some(r) => regs[*r as usize].clone(),
                    None => act.self_val.clone(),
                };
                let pos = self.call_args(regs, args, *splat);
                let kw = self.call_kwargs(f, pool, regs, kw, *kw_splat);
                let block = block.map(|b| regs[b as usize].clone());
                let r = match kind {
                    CallKind::Method(mid) => {
                        let mid = self.resolve_dynamic(&recv, *mid);
                        let r = self.invoke(mid, recv, pos, kw, block.clone());
                        self.catch_break(&block, r)
                    }
                    CallKind::Send(name) => {
                        let r = self.send_kw(&recv, name, pos, kw, block.clone());
                        self.catch_break(&block, r)
                    }
                    CallKind::Construct { class, init } => {
                        let r = self.construct(*class, *init, pos, kw, block.clone());
                        self.catch_break(&block, r)
                    }
                    CallKind::ProcCall => {
                        let r = self.call_block(&recv, pos);
                        self.catch_break(&block, r)
                    }
                    CallKind::Yield => {
                        if act.block.is_nil() {
                            Err(self.raise(self.exc.runtime_error, "no block given (yield)"))
                        } else {
                            self.call_block(&act.block, pos)
                        }
                    }
                    CallKind::Super(mid) => {
                        let r = self.invoke(*mid, recv, pos, kw, block.clone());
                        self.catch_break(&block, r)
                    }
                    CallKind::Raise => self.eval_raise(pos),
                };
                regs[*dst as usize] = r?;
            }
            Inst::OwnedCall {
                dst,
                method,
                recv,
                args,
                kw,
            } => {
                if kw.is_empty() && args.len() <= 2 {
                    // The arguments by reference: the fast paths clone
                    // only what they keep.
                    let argv: SmallVec<[Value; 2]> =
                        args.iter().map(|r| regs[*r as usize].clone()).collect();
                    let refs: SmallVec<[&Value; 2]> = argv.iter().collect();
                    match recv {
                        VarLoc::Reg(r) => {
                            if self.owned_fast(*method, &mut regs[*r as usize], &refs) {
                                regs[*dst as usize] = regs[*r as usize].clone();
                                return Ok(());
                            }
                        }
                        VarLoc::Field { obj, index } => {
                            if let Value::Object(o) = &regs[*obj as usize] {
                                let mut fields = o.fields.borrow_mut();
                                if let Some(slot) = fields.get_mut(*index as usize) {
                                    if self.owned_fast(*method, slot, &refs) {
                                        let v = slot.clone();
                                        drop(fields);
                                        regs[*dst as usize] = v;
                                        return Ok(());
                                    }
                                }
                            }
                        }
                        VarLoc::Frame { .. } => {}
                    }
                }
                let pos = self.call_args(regs, args, false);
                let kw = self.call_kwargs(f, pool, regs, kw, None);
                let take_field = |obj: Reg, index: u32| -> Value {
                    match &regs[obj as usize] {
                        Value::Object(o) => o
                            .fields
                            .borrow_mut()
                            .get_mut(index as usize)
                            .map(|s| std::mem::replace(s, Value::Nil))
                            .unwrap_or(Value::Nil),
                        _ => Value::Nil,
                    }
                };
                let put_field = |regs: &[Value], obj: Reg, index: u32, v: Value| {
                    if let Value::Object(o) = &regs[obj as usize] {
                        if let Some(s) = o.fields.borrow_mut().get_mut(index as usize) {
                            *s = v;
                        }
                    }
                };
                let old = match recv {
                    VarLoc::Reg(r) => std::mem::replace(&mut regs[*r as usize], Value::Nil),
                    VarLoc::Frame { depth, slot } => {
                        let fr = self.frame(act);
                        let old = fr.get(*depth, *slot);
                        fr.set(*depth, *slot, Value::Nil);
                        old
                    }
                    VarLoc::Field { obj, index } => take_field(*obj, *index),
                };
                match self.invoke_owned(*method, old, pos, kw) {
                    Ok(v) => {
                        match recv {
                            VarLoc::Reg(r) => regs[*r as usize] = v.clone(),
                            VarLoc::Frame { depth, slot } => {
                                self.frame(act).set(*depth, *slot, v.clone())
                            }
                            VarLoc::Field { obj, index } => {
                                put_field(regs, *obj, *index, v.clone())
                            }
                        }
                        regs[*dst as usize] = v;
                    }
                    Err((e, old)) => {
                        match recv {
                            VarLoc::Reg(r) => regs[*r as usize] = old,
                            VarLoc::Frame { depth, slot } => {
                                self.frame(act).set(*depth, *slot, old)
                            }
                            VarLoc::Field { obj, index } => put_field(regs, *obj, *index, old),
                        }
                        return Err(e);
                    }
                }
            }
            Inst::IsNil { dst, src } => {
                regs[*dst as usize] = Value::Bool(regs[*src as usize].is_nil());
            }
            Inst::BinOp {
                dst,
                op,
                lhs,
                rhs,
                method,
            } => {
                let v = match fast_binop(*op, &regs[*lhs as usize], &regs[*rhs as usize]) {
                    Some(v) => v,
                    None => {
                        let l = regs[*lhs as usize].clone();
                        let r = regs[*rhs as usize].clone();
                        match method {
                            Some(mid) => {
                                let mid = self.resolve_dynamic(&l, *mid);
                                self.invoke(mid, l, smallvec![r], Vec::new(), None)?
                            }
                            None => self.send(&l, op.name(), smallvec![r], None)?,
                        }
                    }
                };
                regs[*dst as usize] = v;
            }
            Inst::Not { dst, src } => {
                regs[*dst as usize] = Value::Bool(!regs[*src as usize].is_truthy());
            }
            Inst::CaseEq {
                dst,
                pattern,
                value,
            } => {
                let r = self.case_eq(&regs[*pattern as usize], &regs[*value as usize])?;
                regs[*dst as usize] = Value::Bool(r);
            }
            Inst::Equal { dst, a, b } => {
                let r = self.values_equal(&regs[*a as usize], &regs[*b as usize])?;
                regs[*dst as usize] = Value::Bool(r);
            }
            Inst::ClassIsA { dst, src, class } => {
                let r = self
                    .world
                    .class_is_a(self.class_of(&regs[*src as usize]), *class);
                regs[*dst as usize] = Value::Bool(r);
            }
            Inst::IsA { dst, src, ty } => {
                let r = self.is_a(&regs[*src as usize], ty);
                regs[*dst as usize] = Value::Bool(r);
            }
            Inst::As {
                dst,
                src,
                ty,
                optional,
                name,
            } => {
                let v = regs[*src as usize].clone();
                regs[*dst as usize] = if self.is_a(&v, ty) {
                    v
                } else if *optional {
                    Value::Nil
                } else {
                    return Err(
                        self.err_type(&format!("cannot cast {} to {name}", self.class_name(&v)))
                    );
                };
            }
            Inst::MakeBlock {
                dst,
                func,
                destructure,
                is_lambda,
            } => {
                let tag = self.new_tag();
                regs[*dst as usize] = Value::Proc(Rc::new(Closure {
                    body: ClosureBody::Func(*func),
                    frame: act.frame.clone(),
                    self_val: act.self_val.clone(),
                    destructure: destructure.map(|n| n as usize),
                    is_lambda: *is_lambda,
                    tag,
                    method_block: (!act.block.is_nil()).then(|| act.block.clone()),
                    method_tag: if *is_lambda { tag } else { act.method_tag },
                    file: act.file,
                }));
            }
            Inst::MethodRef { dst, recv, name } => {
                let tag = self.new_tag();
                regs[*dst as usize] = Value::Proc(Rc::new(Closure {
                    body: ClosureBody::BoundMethod {
                        recv: regs[*recv as usize].clone(),
                        name: Rc::from(self.str_const(f, *name)),
                    },
                    frame: None,
                    self_val: Value::Nil,
                    destructure: None,
                    is_lambda: true,
                    tag,
                    method_block: None,
                    method_tag: tag,
                    file: act.file,
                }));
            }
            Inst::SymbolProc { dst, name } => {
                let tag = self.new_tag();
                regs[*dst as usize] = Value::Proc(Rc::new(Closure {
                    body: ClosureBody::MethodName(
                        Rc::from(self.str_const(f, *name)),
                        Cell::new(None),
                    ),
                    frame: None,
                    self_val: Value::Nil,
                    destructure: None,
                    is_lambda: true,
                    tag,
                    method_block: None,
                    method_tag: tag,
                    file: act.file,
                }));
            }
            Inst::MakeArray { dst, items } => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    let v = &regs[item.reg as usize];
                    if item.splat {
                        match v {
                            Value::Array(a) => out.extend(a.iter()),
                            other => out.push(other.clone()),
                        }
                    } else {
                        out.push(v.clone());
                    }
                }
                regs[*dst as usize] = Value::array(out);
            }
            Inst::MakeHash { dst, items } => {
                let mut map = ValueMap::with_capacity_and_hasher(items.len(), Default::default());
                for item in items {
                    match item {
                        HashItem::Pair(k, v) => {
                            map.insert(regs[*k as usize].clone(), regs[*v as usize].clone());
                        }
                        HashItem::Splat(h) => {
                            if let Value::Hash(h) = &regs[*h as usize] {
                                for (k, v) in h.iter() {
                                    map.insert(k.clone(), v.clone());
                                }
                            }
                        }
                    }
                }
                regs[*dst as usize] = Value::Hash(Rc::new(map));
            }
            Inst::MakeRange {
                dst,
                lo,
                hi,
                exclusive,
            } => {
                let lo = lo.map(|r| regs[r as usize].clone()).unwrap_or(Value::Nil);
                let hi = hi.map(|r| regs[r as usize].clone()).unwrap_or(Value::Nil);
                regs[*dst as usize] = Value::Range(Rc::new(RangeVal {
                    lo,
                    hi,
                    exclusive: *exclusive,
                }));
            }
            Inst::MakeRegexp { dst, source, flags } => {
                let source = self.to_s(&regs[*source as usize])?;
                regs[*dst as usize] = self.make_regexp(&source, flags)?;
            }
            Inst::Interpolate { dst, parts } => {
                // Every piece is written into one reused buffer (a number
                // is formatted there, not through a temporary string).
                let mut failed = None;
                let v = Value::build_string(|s| {
                    for p in parts {
                        match p {
                            StrPiece::Lit(idx) => s.push_str(self.str_const(f, *idx)),
                            StrPiece::Val(r) => {
                                if let Err(e) = self.append_to_s(s, &regs[*r as usize]) {
                                    failed = Some(e);
                                    return;
                                }
                            }
                        }
                    }
                });
                if let Some(e) = failed {
                    return Err(e);
                }
                regs[*dst as usize] = v;
            }
            Inst::ToSym { dst, src } => {
                let s = self.to_s(&regs[*src as usize])?;
                regs[*dst as usize] = Value::Symbol(self.intern(&s));
            }
            Inst::IsArray { dst, src } => {
                regs[*dst as usize] = Value::Bool(matches!(regs[*src as usize], Value::Array(_)));
            }
            Inst::IsHash { dst, src } => {
                regs[*dst as usize] = Value::Bool(matches!(regs[*src as usize], Value::Hash(_)));
            }
            Inst::IsObject { dst, src } => {
                regs[*dst as usize] = Value::Bool(matches!(regs[*src as usize], Value::Object(_)));
            }
            Inst::ToArray { dst, src } => {
                let v = match &regs[*src as usize] {
                    Value::Array(a) => Value::Array(a.clone()),
                    other => Value::array(vec![other.clone()]),
                };
                regs[*dst as usize] = v;
            }
            Inst::Len { dst, src } => {
                let n = match &regs[*src as usize] {
                    Value::Array(a) => a.len(),
                    Value::Hash(h) => h.len(),
                    Value::Str(s) => s.chars().count(),
                    Value::Short(s) => s.chars().count(),
                    _ => 0,
                };
                regs[*dst as usize] = Value::Int(n as i64);
            }
            Inst::ArrayGet { dst, arr, index } => {
                let v = match &regs[*arr as usize] {
                    Value::Array(a) => {
                        let i = if *index < 0 {
                            a.len().checked_sub((-*index) as usize)
                        } else {
                            Some(*index as usize)
                        };
                        i.and_then(|i| a.get(i)).unwrap_or(Value::Nil)
                    }
                    _ => Value::Nil,
                };
                regs[*dst as usize] = v;
            }
            Inst::ArrayGetReg { dst, arr, index } => {
                let v = match (&regs[*arr as usize], &regs[*index as usize]) {
                    (Value::Array(a), Value::Int(i)) => {
                        let i = if *i < 0 {
                            a.len().checked_sub((-*i) as usize)
                        } else {
                            Some(*i as usize)
                        };
                        i.and_then(|i| a.get(i)).unwrap_or(Value::Nil)
                    }
                    _ => Value::Nil,
                };
                regs[*dst as usize] = v;
            }
            Inst::ArraySlice {
                dst,
                arr,
                from,
                drop_last,
            } => {
                let v = match &regs[*arr as usize] {
                    Value::Array(a) => {
                        let from = *from as usize;
                        let end = a.len().saturating_sub(*drop_last as usize).max(from);
                        if from >= a.len() {
                            Value::array(Vec::new())
                        } else {
                            Value::array(a.values()[from..end.min(a.len())].to_vec())
                        }
                    }
                    _ => Value::array(Vec::new()),
                };
                regs[*dst as usize] = v;
            }
            Inst::ArraySliceReg { dst, arr, from, to } => {
                let v = match (
                    &regs[*arr as usize],
                    &regs[*from as usize],
                    &regs[*to as usize],
                ) {
                    (Value::Array(a), Value::Int(from), Value::Int(to)) => {
                        let from = (*from).clamp(0, a.len() as i64) as usize;
                        let to = (*to).clamp(from as i64, a.len() as i64) as usize;
                        Value::array(a.values()[from..to].to_vec())
                    }
                    _ => Value::array(Vec::new()),
                };
                regs[*dst as usize] = v;
            }
            Inst::ObjectFields { dst, src } => {
                let v = match &regs[*src as usize] {
                    Value::Object(o) => Value::array(o.fields.borrow().to_vec()),
                    _ => Value::array(Vec::new()),
                };
                regs[*dst as usize] = v;
            }
            Inst::HashGetSym {
                dst,
                found,
                hash,
                key,
            } => {
                let key = Value::Symbol(self.symbol_const(f, pool, *key));
                let (v, ok) = match &regs[*hash as usize] {
                    Value::Hash(h) => match h.get(&key) {
                        Some(v) => (v.clone(), true),
                        None => (Value::Nil, false),
                    },
                    _ => (Value::Nil, false),
                };
                regs[*dst as usize] = v;
                regs[*found as usize] = Value::Bool(ok);
            }
            Inst::ArrayPush { arr, src } => {
                let v = regs[*src as usize].clone();
                match &mut regs[*arr as usize] {
                    Value::Array(a) => Rc::make_mut(a).push(v),
                    other => {
                        return Err(self.err_type(&format!(
                            "expected an array, got {}",
                            self.class_name(other)
                        )))
                    }
                }
            }
            Inst::HashRest { dst, hash, keys } => {
                let keys: Vec<Symbol> = keys
                    .iter()
                    .map(|k| self.symbol_const(f, pool, *k))
                    .collect();
                let v = match &regs[*hash as usize] {
                    Value::Hash(h) => {
                        let mut rest = ValueMap::default();
                        for (k, val) in h.iter() {
                            let matched = matches!(k, Value::Symbol(s) if keys.contains(s));
                            if !matched {
                                rest.insert(k.clone(), val.clone());
                            }
                        }
                        Value::Hash(Rc::new(rest))
                    }
                    _ => Value::Hash(Rc::new(ValueMap::default())),
                };
                regs[*dst as usize] = v;
            }
            Inst::CatchException { dst } => {
                regs[*dst as usize] = match pending.take() {
                    Some(Flow::Raise(e)) => e,
                    Some(other) => {
                        return Err(other);
                    }
                    None => Value::Nil,
                };
            }
            Inst::CatchAny { dst } => {
                regs[*dst as usize] = Value::Flow(Rc::new(RefCell::new(pending.take())));
            }
            Inst::ClearRegs { from, to } => {
                for r in &mut regs[*from as usize..*to as usize] {
                    *r = Value::Nil;
                }
            }
            Inst::NoMatch { src, is_assert } => {
                let v = &regs[*src as usize];
                let msg = if *is_assert {
                    format!("{} does not match the pattern", self.inspect(v)?)
                } else {
                    format!("no pattern matched {}", self.inspect(v)?)
                };
                return Err(self.raise(self.exc.no_matching_pattern, &msg));
            }
        }
        let _ = fid;
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
        let Value::Proc(closure) = proc else {
            return Err(self.err_type("not a procedure"));
        };
        match &closure.body {
            ClosureBody::MethodName(name, cache) => {
                if args.is_empty() {
                    return Err(self.err_arg("block needs an argument"));
                }
                let recv = args.remove(0);
                // The method found for the last receiver class is reused.
                let cid = self.class_of(&recv);
                let argc = args.len();
                let mid = match cache.get() {
                    Some((c, n, mid)) if c == cid && n == argc => mid,
                    _ => match self.find_method(cid, name, argc, false) {
                        Some(mid) => {
                            cache.set(Some((cid, argc, mid)));
                            mid
                        }
                        None => return self.send(&recv, name, args, None),
                    },
                };
                if argc <= 3 {
                    if let Some(fast) = self.fast_natives[mid as usize] {
                        let refs: SmallVec<[&Value; 3]> = args.iter().collect();
                        if let Some(r) = fast(self, &recv, &refs) {
                            return r;
                        }
                    }
                }
                self.invoke(mid, recv, args, Vec::new(), None)
            }
            ClosureBody::BoundMethod { recv, name } => self.send(recv, name, args, None),
            ClosureBody::Native(f) => f(self, args),
            ClosureBody::Func(fid) => {
                if sched::stack_exhausted() {
                    return Err(self.raise(self.exc.system_stack, "stack level too deep"));
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
                let (bound, provided) = if simple {
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
                };
                act.bind(&bound);
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
        };
        self.run_func(fid, &act)
    }

    /// Run a method body (parameters already bound).
    pub fn run_method(
        &self,
        _mid: MethodId,
        fid: FuncId,
        recv: Value,
        args: ArgVec,
        provided: u64,
        block: Option<Value>,
    ) -> EvalResult {
        if sched::stack_exhausted() {
            return Err(self.raise(self.exc.system_stack, "stack level too deep"));
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
        };
        act.bind(&args);
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
        };
        self.run_func(fid, &act)
    }
}

/// Positional arguments stored inline (re-exported for natives).
pub type Args4 = SmallVec<[Value; 4]>;
