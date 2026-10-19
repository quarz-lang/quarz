//! The C ABI used by compiled programs. A function compiled by
//! `quarz build` keeps its registers in its own stack frame and calls back
//! here for everything but moves, immediates, branches and integer
//! arithmetic; `qz_main` is the entry point of a compiled executable.
//!
//! Non-local flow crosses the boundary as a status code with the flow
//! itself parked in `Interp::pending_flow`.

use std::ffi::{c_char, CStr};
use std::rc::Rc;

use quarz_ir::{FuncId, Term};

use crate::interp::{CompiledFn, Flow, Interp, SharedState};
use crate::value::Value;
use crate::vm::Activation;

pub const STATUS_OK: u32 = 0;
pub const STATUS_RAISE: u32 = 1;
pub const STATUS_BREAK: u32 = 2;
pub const STATUS_NEXT: u32 = 3;
pub const STATUS_RETURN: u32 = 4;
pub const STATUS_RETRY: u32 = 5;
pub const STATUS_EXIT: u32 = 6;

pub fn flow_status(flow: &Flow) -> u32 {
    match flow {
        Flow::Raise(_) => STATUS_RAISE,
        Flow::Break(_, _) => STATUS_BREAK,
        Flow::Next(_) => STATUS_NEXT,
        Flow::Return(_, _) => STATUS_RETURN,
        Flow::Retry => STATUS_RETRY,
        Flow::Exit(_) => STATUS_EXIT,
    }
}

impl Interp {
    /// Park a flow for compiled code and return its status.
    pub fn park_flow(&self, flow: Flow) -> u32 {
        let status = flow_status(&flow);
        *self.pending_flow.borrow_mut() = Some(flow);
        status
    }

    /// The flow parked by compiled code that returned `status`.
    pub fn take_flow(&self, status: u32) -> Flow {
        match self.pending_flow.borrow_mut().take() {
            Some(flow) => flow,
            None => Flow::Raise(self.make_exception(
                self.exc.runtime_error,
                &format!("internal error: lost flow (status {status})"),
            )),
        }
    }

    /// Run a function's machine code, if it has any.
    pub fn run_compiled(&self, fid: FuncId, act: &Activation) -> Option<Result<Value, Flow>> {
        let f = (*self.compiled.borrow().get(fid as usize)?)?;
        let mut out = Value::Nil;
        // SAFETY: `f` was produced by quarz-aot for this function and
        // follows the ABI described above.
        let status = unsafe { f(self, act, &mut out) };
        Some(if status == STATUS_OK {
            Ok(out)
        } else {
            Err(self.take_flow(status))
        })
    }
}

/// Execute one instruction of function `fid` on the registers `regs`.
///
/// # Safety
/// `rt` and `act` must be live, `regs` must point to `nregs` initialized
/// values.
#[no_mangle]
pub unsafe extern "C" fn qz_exec(
    rt: *const Interp,
    act: *const Activation,
    fid: u32,
    block: u32,
    inst: u32,
    regs: *mut Value,
) -> u32 {
    let rt = &*rt;
    let act = &*act;
    let funcs = rt.funcs.borrow();
    let f = &funcs[fid as usize];
    let pools = rt.pools.borrow();
    let pool = &pools[fid as usize];
    let regs = std::slice::from_raw_parts_mut(regs, f.nregs as usize);
    let b = &f.blocks[block as usize];
    act.line.set(b.lines[inst as usize]);
    let inst = &b.insts[inst as usize];
    let mut pending = rt.pending_flow.borrow_mut().take();
    match rt.exec_inst(f, fid, pool, act, regs, &mut pending, inst) {
        Ok(()) => {
            *rt.pending_flow.borrow_mut() = pending;
            STATUS_OK
        }
        Err(flow) => rt.park_flow(flow),
    }
}

/// Execute the terminator of a block that leaves the function abruptly
/// (`Raise`, `BreakOut`, `ReturnOut`, `Resume`, `Unreachable`).
///
/// # Safety
/// As for `qz_exec`.
#[no_mangle]
pub unsafe extern "C" fn qz_term(
    rt: *const Interp,
    act: *const Activation,
    fid: u32,
    block: u32,
    regs: *mut Value,
) -> u32 {
    let rt = &*rt;
    let act = &*act;
    let f = rt.func(fid);
    let regs = std::slice::from_raw_parts_mut(regs, f.nregs as usize);
    let flow = match &f.blocks[block as usize].term {
        Term::Raise(r) => Flow::Raise(regs[*r as usize].clone()),
        Term::BreakOut(r) => Flow::Break(regs[*r as usize].clone(), act.closure_tag),
        Term::ReturnOut(r) => Flow::Return(regs[*r as usize].clone(), act.method_tag),
        Term::Resume(r) => match &regs[*r as usize] {
            Value::Flow(fb) => match fb.borrow_mut().take() {
                Some(flow) => flow,
                None => return STATUS_OK,
            },
            _ => return STATUS_OK,
        },
        _ => Flow::Raise(rt.make_exception(
            rt.exc.runtime_error,
            "internal error: unreachable code executed",
        )),
    };
    rt.park_flow(flow)
}

/// Size of the buffer compiled code reserves for an `Activation` it
/// builds itself (`qz_enter`); checked against the real size below.
pub const ACT_BUF_SIZE: usize = 320;
const _: () = assert!(std::mem::size_of::<Activation>() <= ACT_BUF_SIZE);
const _: () = assert!(std::mem::align_of::<Activation>() <= 16);

/// Where the arguments and `self` of an activation live, for inline
/// reads: `out[0]` = the arguments, `out[1]` = `self`, `out[2]` = the
/// number of arguments (as a pointer-sized integer).
///
/// # Safety
/// As for `qz_exec`; `out` must have room for three words.
#[no_mangle]
pub unsafe extern "C" fn qz_act_ptrs(act: *const Activation, out: *mut *const Value) {
    let act = &*act;
    *out = act.args_ptr.get();
    *out.add(1) = &act.self_val;
    *out.add(2) = act.nargs.get() as usize as *const Value;
}

/// `regs[dst] = *src` for a reference-counted value (the inline path
/// copies the others).
///
/// # Safety
/// `src` must point to a live value.
#[no_mangle]
pub unsafe extern "C" fn qz_clone_to(regs: *mut Value, dst: u32, src: *const Value) {
    *regs.add(dst as usize) = (*src).clone();
}

/// `*dst = *src` where `dst` holds no value yet (the inline path copies
/// values without reference counts itself).
///
/// # Safety
/// `src` must point to a live value, `dst` to writable space.
#[no_mangle]
pub unsafe extern "C" fn qz_clone_ptr(dst: *mut Value, src: *const Value) {
    std::ptr::write(dst, (*src).clone());
}

/// Release the value at `p` and leave nil there.
///
/// # Safety
/// `p` must point to a live value.
#[no_mangle]
pub unsafe extern "C" fn qz_drop_value(p: *mut Value) {
    *p = Value::Nil;
}

/// Build the activation of a direct call to the compiled body of method
/// `mid` (function `fid`) in `buf`, binding the receiver (`regs[recv]`, or
/// the caller's `self` when `recv` is `u32::MAX`) and the block, and push
/// it on the call stack. The parameters (`nargs` values, nil-padded and
/// with the block last when the method takes one) stay in the caller's
/// argument area `args`, which the activation refers to. The caller then
/// calls the body and finishes with `qz_leave`. Returns a status
/// (non-zero: the stack is exhausted and nothing was built).
///
/// # Safety
/// As for `qz_call_static`; `buf` must have `ACT_BUF_SIZE` bytes of
/// 16-byte aligned space, and `args` must stay untouched, until
/// `qz_leave`.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn qz_enter(
    rt: *const Interp,
    act: *const Activation,
    buf: *mut Activation,
    mid: u32,
    fid: u32,
    regs: *mut Value,
    recv: u32,
    args: *const Value,
    nargs: u32,
    block: u32,
    frame_size: u32,
    file: u32,
    provided: u64,
) -> u32 {
    let rt = &*rt;
    let caller = &*act;
    if crate::sched::stack_exhausted() {
        return rt.park_flow(rt.raise(rt.exc.system_stack, "stack level too deep"));
    }
    let recv = if recv == u32::MAX {
        caller.self_val.clone()
    } else {
        (*regs.add(recv as usize)).clone()
    };
    let block = if block == u32::MAX {
        None
    } else {
        Some((*regs.add(block as usize)).clone())
    };
    let frame = if frame_size > 0 {
        Some(crate::value::Frame::new(frame_size as usize, None))
    } else {
        None
    };
    std::ptr::write(
        buf,
        Activation {
            fid,
            task: rt.current_task_id.get(),
            line: std::cell::Cell::new(0),
            self_val: recv,
            frame,
            block,
            method_tag: rt.new_tag(),
            closure_tag: 0,
            method: Some(mid),
            file,
            args: crate::interp::ArgVec::new(),
            provided,
            args_ptr: std::cell::Cell::new(args),
            nargs: std::cell::Cell::new(nargs),
        },
    );
    rt.call_stack.borrow_mut().push(buf as *const Activation);
    STATUS_OK
}

/// Finish a direct call begun with `qz_enter`: pop the call stack,
/// turn a `return` from the body or a `break` from its block into the
/// result, store it in `regs[dst]`, drop the activation and return the
/// status.
///
/// # Safety
/// As for `qz_enter`; `status` is what the body returned and `out` the
/// value it produced when the status is OK.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn qz_leave(
    rt: *const Interp,
    buf: *mut Activation,
    status: u32,
    out: *mut Value,
    regs: *mut Value,
    dst: u32,
    block: u32,
) -> u32 {
    let rt = &*rt;
    rt.pop_call_stack(&*buf);
    let r = if status == STATUS_OK {
        Ok(std::mem::replace(&mut *out, Value::Nil))
    } else {
        match rt.take_flow(status) {
            Flow::Return(v, t) if t == (*buf).method_tag => Ok(v),
            flow => Err(flow),
        }
    };
    let blk = if block == u32::MAX {
        None
    } else {
        Some((*regs.add(block as usize)).clone())
    };
    let r = rt.catch_break(&blk, r);
    std::ptr::drop_in_place(buf);
    match r {
        Ok(v) => {
            *regs.add(dst as usize) = v;
            STATUS_OK
        }
        Err(flow) => rt.park_flow(flow),
    }
}

/// `regs[dst] = self`.
///
/// # Safety
/// As for `qz_exec`.
#[no_mangle]
pub unsafe extern "C" fn qz_self(act: *const Activation, regs: *mut Value, dst: u32) {
    let act = &*act;
    *regs.add(dst as usize) = act.self_val.clone();
}

/// `regs[dst] = args[index]` (nil when absent).
///
/// # Safety
/// As for `qz_exec`.
#[no_mangle]
pub unsafe extern "C" fn qz_arg(act: *const Activation, index: u32, regs: *mut Value, dst: u32) {
    let act = &*act;
    let v = act.arg(index).cloned().unwrap_or(Value::Nil);
    *regs.add(dst as usize) = v;
}

/// `regs[dst] = the enclosing method's block` (nil when none).
///
/// # Safety
/// As for `qz_exec`.
#[no_mangle]
pub unsafe extern "C" fn qz_block_param(act: *const Activation, regs: *mut Value, dst: u32) {
    let act = &*act;
    *regs.add(dst as usize) = act.block.clone().unwrap_or(Value::Nil);
}

/// `regs[dst] = frame[depth][slot]`.
///
/// # Safety
/// As for `qz_exec`; the function must have a frame.
#[no_mangle]
pub unsafe extern "C" fn qz_frame_get(
    act: *const Activation,
    depth: u32,
    slot: u32,
    regs: *mut Value,
    dst: u32,
) {
    let act = &*act;
    let frame = act
        .frame
        .as_ref()
        .expect("function without a frame uses one");
    *regs.add(dst as usize) = frame.get(depth, slot);
}

/// `frame[depth][slot] = regs[src]`.
///
/// # Safety
/// As for `qz_frame_get`.
#[no_mangle]
pub unsafe extern "C" fn qz_frame_set(
    act: *const Activation,
    depth: u32,
    slot: u32,
    regs: *mut Value,
    src: u32,
) {
    let act = &*act;
    let frame = act
        .frame
        .as_ref()
        .expect("function without a frame uses one");
    frame.set(depth, slot, (*regs.add(src as usize)).clone());
}

/// `regs[dst] = regs[obj].fields[index]`.
///
/// # Safety
/// As for `qz_exec`.
#[no_mangle]
pub unsafe extern "C" fn qz_field_get(
    rt: *const Interp,
    regs: *mut Value,
    obj: u32,
    index: u32,
    dst: u32,
) -> u32 {
    let rt = &*rt;
    let v = match &*regs.add(obj as usize) {
        Value::Object(o) => o
            .fields
            .borrow()
            .get(index as usize)
            .cloned()
            .unwrap_or(Value::Nil),
        _ => {
            return rt.park_flow(rt.raise(
                rt.exc.runtime_error,
                "instance variable access outside of an object",
            ))
        }
    };
    *regs.add(dst as usize) = v;
    STATUS_OK
}

/// `regs[obj].fields[index] = regs[src]`.
///
/// # Safety
/// As for `qz_exec`.
#[no_mangle]
pub unsafe extern "C" fn qz_field_set(
    rt: *const Interp,
    regs: *mut Value,
    obj: u32,
    index: u32,
    src: u32,
) -> u32 {
    let rt = &*rt;
    let v = (*regs.add(src as usize)).clone();
    match &*regs.add(obj as usize) {
        Value::Object(o) => {
            let mut fields = o.fields.borrow_mut();
            let idx = index as usize;
            if idx >= fields.len() {
                fields.resize(idx + 1, Value::Nil);
            }
            fields[idx] = v;
            STATUS_OK
        }
        _ => rt.park_flow(rt.raise(
            rt.exc.runtime_error,
            "instance variable access outside of an object",
        )),
    }
}

/// A statically resolved call of a method that nothing overrides, with
/// positional arguments only (and possibly a block): natives are called
/// directly, bodies get their parameters bound without the generic path
/// (`nil` for missing defaults, which the body evaluates).
///
/// # Safety
/// As for `qz_exec`; `arg_regs` must point to `nargs` register indices;
/// `recv` and `block` are register indices or `u32::MAX` for `self` /
/// no block.
#[no_mangle]
pub unsafe extern "C" fn qz_call_static(
    rt: *const Interp,
    act: *const Activation,
    mid: u32,
    regs: *mut Value,
    recv: u32,
    arg_regs: *const u32,
    nargs: u32,
    block: u32,
    dst: u32,
) -> u32 {
    let rt = &*rt;
    let act = &*act;
    let recv = if recv == u32::MAX {
        act.self_val.clone()
    } else {
        (*regs.add(recv as usize)).clone()
    };
    let block = if block == u32::MAX {
        None
    } else {
        Some((*regs.add(block as usize)).clone())
    };
    let m = &rt.world.methods[mid as usize];
    let nparams = m.params.len();
    let mut args: crate::interp::ArgVec =
        crate::interp::ArgVec::with_capacity(nparams.max(nargs as usize) + 1);
    for i in 0..nargs as usize {
        let r = *arg_regs.add(i);
        args.push((*regs.add(r as usize)).clone());
    }
    let r = if let Some(native) = rt.natives[mid as usize] {
        native(
            rt,
            &recv,
            crate::interp::Args {
                pos: args,
                kw: Vec::new(),
                block: block.clone(),
            },
        )
    } else if let Some(fid) = m.func {
        let bit = |i: usize| if i < 64 { 1u64 << i } else { 0 };
        let mut provided = 0u64;
        for i in 0..(nargs as usize).min(nparams) {
            provided |= bit(i);
        }
        while args.len() < nparams {
            args.push(Value::Nil);
        }
        if m.has_block {
            match &block {
                Some(b) => {
                    args.push(b.clone());
                    provided |= bit(nparams);
                }
                None => args.push(Value::Nil),
            }
        }
        rt.run_method(mid, fid, recv, args, provided, block.clone())
    } else {
        rt.invoke(mid, recv, args, Vec::new(), block.clone())
    };
    match rt.catch_break(&block, r) {
        Ok(v) => {
            *regs.add(dst as usize) = v;
            STATUS_OK
        }
        Err(flow) => rt.park_flow(flow),
    }
}

/// `x = x.meth(args)`: move the receiver out of its variable (a register
/// when `loc_kind` is 0, else frame slot `b` at depth `a`), call the
/// method with the sole reference, and store the result back.
///
/// # Safety
/// As for `qz_call_static`.
#[no_mangle]
pub unsafe extern "C" fn qz_owned_call(
    rt: *const Interp,
    act: *const Activation,
    mid: u32,
    regs: *mut Value,
    loc_kind: u32,
    a: u32,
    b: u32,
    arg_regs: *const u32,
    nargs: u32,
    dst: u32,
) -> u32 {
    let rt = &*rt;
    let act = &*act;
    let mut args: crate::interp::ArgVec = crate::interp::ArgVec::with_capacity(nargs as usize);
    for i in 0..nargs as usize {
        let r = *arg_regs.add(i);
        args.push((*regs.add(r as usize)).clone());
    }
    let old = if loc_kind == 0 {
        std::mem::replace(&mut *regs.add(a as usize), Value::Nil)
    } else {
        let frame = act
            .frame
            .as_ref()
            .expect("function without a frame uses one");
        let old = frame.get(a, b);
        frame.set(a, b, Value::Nil);
        old
    };
    match rt.invoke_owned(mid, old, args, Vec::new()) {
        Ok(v) => {
            if loc_kind == 0 {
                *regs.add(a as usize) = v.clone();
            } else {
                let frame = act
                    .frame
                    .as_ref()
                    .expect("function without a frame uses one");
                frame.set(a, b, v.clone());
            }
            *regs.add(dst as usize) = v;
            STATUS_OK
        }
        Err((flow, old)) => {
            if loc_kind == 0 {
                *regs.add(a as usize) = old;
            } else {
                let frame = act
                    .frame
                    .as_ref()
                    .expect("function without a frame uses one");
                frame.set(a, b, old);
            }
            rt.park_flow(flow)
        }
    }
}

/// `yield(args)`: call the enclosing method's block.
///
/// # Safety
/// As for `qz_call_static`.
#[no_mangle]
pub unsafe extern "C" fn qz_yield(
    rt: *const Interp,
    act: *const Activation,
    regs: *mut Value,
    arg_regs: *const u32,
    nargs: u32,
    dst: u32,
) -> u32 {
    let rt = &*rt;
    let act = &*act;
    let Some(block) = &act.block else {
        return rt.park_flow(rt.raise(rt.exc.runtime_error, "no block given (yield)"));
    };
    let mut args: crate::interp::ArgVec = crate::interp::ArgVec::with_capacity(nargs as usize);
    for i in 0..nargs as usize {
        let r = *arg_regs.add(i);
        args.push((*regs.add(r as usize)).clone());
    }
    match rt.call_block(block, args) {
        Ok(v) => {
            *regs.add(dst as usize) = v;
            STATUS_OK
        }
        Err(flow) => rt.park_flow(flow),
    }
}

/// `Class.new(args)` with positional arguments only.
///
/// # Safety
/// As for `qz_call_static`; `init` is a method id or `u32::MAX`.
#[no_mangle]
pub unsafe extern "C" fn qz_construct(
    rt: *const Interp,
    regs: *mut Value,
    class: u32,
    init: u32,
    arg_regs: *const u32,
    nargs: u32,
    dst: u32,
) -> u32 {
    let rt = &*rt;
    let init = if init == u32::MAX { None } else { Some(init) };
    // A data type given all its fields: no initializer to run, and the
    // fields are copied straight from the registers.
    if let Some(i) = init {
        let info = &rt.world.classes[class as usize];
        if rt.world.methods[i as usize].synth == quarz_ir::RtSynth::DataInit
            && nargs as usize == info.fields.len()
            && matches!(
                info.kind,
                quarz_ir::RtClassKind::Data | quarz_ir::RtClassKind::Variant
            )
        {
            let mut fields = crate::value::Fields::new();
            if nargs > 4 {
                fields.reserve(nargs as usize);
            }
            for k in 0..nargs as usize {
                let r = *arg_regs.add(k);
                fields.push((*regs.add(r as usize)).clone());
            }
            let obj = Value::Object(Rc::new(crate::value::Object {
                class,
                fields: std::cell::RefCell::new(fields),
                backtrace: std::cell::RefCell::new(None),
                cause: std::cell::RefCell::new(None),
            }));
            *regs.add(dst as usize) = obj;
            return STATUS_OK;
        }
    }
    let mut args: crate::interp::ArgVec = crate::interp::ArgVec::with_capacity(nargs as usize);
    for i in 0..nargs as usize {
        let r = *arg_regs.add(i);
        args.push((*regs.add(r as usize)).clone());
    }
    match rt.construct(class, init, args, Vec::new(), None) {
        Ok(v) => {
            *regs.add(dst as usize) = v;
            STATUS_OK
        }
        Err(flow) => rt.park_flow(flow),
    }
}

/// Initialize `n` registers to nil.
///
/// # Safety
/// `regs` must point to room for `n` values.
#[no_mangle]
pub unsafe extern "C" fn qz_init_regs(regs: *mut Value, n: u32) {
    for i in 0..n as usize {
        std::ptr::write(regs.add(i), Value::Nil);
    }
}

/// Drop `n` initialized registers.
///
/// # Safety
/// `regs` must point to `n` initialized values that are not used again.
#[no_mangle]
pub unsafe extern "C" fn qz_drop_regs(regs: *mut Value, n: u32) {
    for i in 0..n as usize {
        std::ptr::drop_in_place(regs.add(i));
    }
}

/// `regs[dst] = regs[src].clone()`.
///
/// # Safety
/// Both indices must be in range of initialized registers.
#[no_mangle]
pub unsafe extern "C" fn qz_move(regs: *mut Value, dst: u32, src: u32) {
    let v = (*regs.add(src as usize)).clone();
    *regs.add(dst as usize) = v;
}

/// `regs[r] = nil` (dropping the old value).
///
/// # Safety
/// `r` must be in range of initialized registers.
#[no_mangle]
pub unsafe extern "C" fn qz_drop_reg(regs: *mut Value, r: u32) {
    *regs.add(r as usize) = Value::Nil;
}

/// Move `regs[r]` into `*out`.
///
/// # Safety
/// `out` must point to an initialized value; `r` must be in range.
#[no_mangle]
pub unsafe extern "C" fn qz_take_reg(regs: *mut Value, r: u32, out: *mut Value) {
    let v = std::mem::replace(&mut *regs.add(r as usize), Value::Nil);
    *out = v;
}

/// Run a compiled program: `blob` is the serialized module, `table` the
/// machine-code bodies by function id (null for functions the VM
/// interprets). Returns the exit code.
///
/// # Safety
/// The pointers must describe valid data produced by `quarz build`.
#[no_mangle]
pub unsafe extern "C" fn qz_main(
    blob: *const u8,
    len: usize,
    table: *const Option<CompiledFn>,
    n: usize,
    argc: i32,
    argv: *const *const c_char,
) -> i32 {
    let bytes = std::slice::from_raw_parts(blob, len);
    let module = match quarz_ir::decode(bytes) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("quarz: corrupt program: {e}");
            return 70;
        }
    };
    let table = std::slice::from_raw_parts(table, n);
    let mut args: Vec<String> = Vec::new();
    for i in 1..argc.max(0) as usize {
        let p = *argv.add(i);
        if !p.is_null() {
            args.push(CStr::from_ptr(p).to_string_lossy().into_owned());
        }
    }
    let state = SharedState::new(Box::new(std::io::BufWriter::new(std::io::stdout())));
    let quarz_ir::Module {
        world,
        functions,
        units,
    } = module;
    let interp: Rc<Interp> = Interp::with_state(world, 0, functions, units, args, state);
    {
        let mut compiled = interp.compiled.borrow_mut();
        for (i, f) in table.iter().enumerate() {
            if i < compiled.len() {
                compiled[i] = *f;
            }
        }
    }
    interp.run()
}
