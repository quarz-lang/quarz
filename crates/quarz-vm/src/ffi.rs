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
    let f = rt.func(fid);
    let pool = rt.pools.borrow()[fid as usize].clone();
    let regs = std::slice::from_raw_parts_mut(regs, f.nregs as usize);
    let b = &f.blocks[block as usize];
    act.line.set(b.lines[inst as usize]);
    let inst = &b.insts[inst as usize];
    let mut pending = rt.pending_flow.borrow_mut().take();
    match rt.exec_inst(&f, fid, &pool, act, regs, &mut pending, inst) {
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
