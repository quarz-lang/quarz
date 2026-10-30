//! Code generation for one function body, written against `Builder`
//! (the backend in `llvm` supplies the instructions).

use std::collections::HashMap;

use quarz_ir::*;
use quarz_vm::layout as L;

use crate::builder::{Builder, FloatCC, IntCC, Ty};
use crate::unbox::{self, Num, State};

/// Size of a `Value` in bytes (`repr(u8)`: a tag byte, then a payload
/// at the next word; only the tag's byte of the first word is defined).
const VALUE_SIZE: i32 = 16;
/// Where a `Bool`'s byte and a `Class`'s id are in a value: right after
/// the tag, as `repr(u8)` lays out a variant whose payload is smaller than
/// a word (the runtime checks both at start-up). Every other payload is
/// at the next word. A tag is stored before the payload, since storing it
/// may write the whole first word.
const BOOL_OFF: i32 = 1;
const CLASS_OFF: i32 = 4;
/// Space for an `Activation` built by compiled code (`qz_enter`); the
/// runtime checks its real size against this.
const ACT_BUF_SIZE: u32 = 320;
/// Tags below this hold no reference-counted payload (`NEEDS_DROP_FROM`).
const NEEDS_DROP_FROM: i64 = 8;
/// `qz_enter_virtual` ran the call itself (see `ffi::STATUS_DONE`).
const STATUS_DONE: i64 = 7;
/// A typed entry's result did not fit its declared type: it is boxed
/// in the caller's `out` instead.
const STATUS_BOXED: i64 = 8;
const TAG_NIL: i64 = 0;
const TAG_BOOL: i64 = 1;
const TAG_INT: i64 = 2;
const TAG_FLOAT: i64 = 3;
const TAG_CLASS: i64 = 5;
const TAG_ARRAY: i64 = 10;
const TAG_OBJECT: i64 = 16;
/// Offset of the field view in an `Object` from its `Rc` allocation
/// (after the allocation's two words); see `Object::bind_fields`.
const OBJECT_FIELDS_PTR_OFF: i32 = 16;

const STATUS_RAISE: i64 = 1;

/// The runtime's entries for the instructions compiled code does not do
/// inline (`quarz_vm::ffi_ops`), one per kind: each takes the
/// interpreter, the activation, the function, the line and the
/// registers, then these operands.
pub(crate) const OPS: &[(&str, &[Ty])] = {
    const I: Ty = Ty::I32;
    const P: Ty = Ty::Ptr;
    &[
        ("qz_op_load_const", &[I, I]),
        ("qz_op_has_arg", &[I, I]),
        ("qz_op_field_get_by_name", &[I, I, I, I]),
        ("qz_op_const_get", &[I, I]),
        ("qz_op_unit_self", &[I, I, I]),
        ("qz_op_variant_singleton", &[I, I]),
        ("qz_op_call", &[P, P, I]),
        ("qz_op_owned_call", &[P]),
        ("qz_op_binop", &[I, I, I, I, I]),
        ("qz_op_case_eq", &[I, I, I]),
        ("qz_op_equal", &[I, I, I]),
        ("qz_op_class_is_a", &[I, I, I]),
        ("qz_op_is_a", &[I, I, P, I, P]),
        ("qz_op_as", &[I, I, P, I, P, I, P, I]),
        ("qz_op_make_block", &[I, I, I, I]),
        ("qz_op_method_ref", &[I, I, I]),
        ("qz_op_symbol_proc", &[I, I, I, I]),
        ("qz_op_make_array", &[I, P, I]),
        ("qz_op_make_hash", &[I, P, I]),
        ("qz_op_make_range", &[I, I, I, I]),
        ("qz_op_make_regexp", &[I, I, P, I]),
        ("qz_op_interpolate", &[I, P, I, I, I]),
        ("qz_op_to_sym", &[I, I]),
        ("qz_op_is_array", &[I, I]),
        ("qz_op_is_hash", &[I, I]),
        ("qz_op_is_object", &[I, I]),
        ("qz_op_to_array", &[I, I]),
        ("qz_op_len", &[I, I]),
        ("qz_op_object_fields", &[I, I]),
        ("qz_op_array_get", &[I, I, I]),
        ("qz_op_array_get_reg", &[I, I, I]),
        ("qz_op_array_words", &[I, I, I]),
        ("qz_op_array_index", &[I, I, I]),
        ("qz_op_array_new_words", &[I, I, I]),
        ("qz_op_array_slice", &[I, I, I, I]),
        ("qz_op_array_slice_reg", &[I, I, I, I]),
        ("qz_op_hash_get_sym", &[I, I, I, I]),
        ("qz_op_array_push", &[I, I]),
        ("qz_op_hash_rest", &[I, I, P, I]),
        ("qz_op_catch_exception", &[I]),
        ("qz_op_catch_any", &[I]),
        ("qz_op_rescuing", &[I, I]),
        ("qz_op_mark_usable", &[I]),
        ("qz_op_no_match", &[I, I]),
        ("qz_op_term", &[I, I]),
    ]
};

/// The position of entry `name` in `OPS`.
fn op_index(name: &str) -> usize {
    OPS.iter()
        .position(|(n, _)| *n == name)
        .unwrap_or_else(|| panic!("no runtime entry {name}"))
}

/// The runtime functions compiled code calls, as a backend's callables.
pub(crate) struct Helpers<F> {
    /// The entries of `OPS`, in its order.
    pub ops: Vec<F>,
    /// `qz_raise`: an error the compiled code detects (see `raise_here`).
    pub raise: F,
    pub enter: F,
    pub enter_virtual: F,
    pub leave: F,
    pub push_call: F,
    pub pop_call: F,
    pub stack_overflow: F,
    pub drop_value: F,
    /// `qz_finalize`: run the `deinitialize` of what was released (none
    /// when the program defines no `deinitialize`).
    pub finalize: Option<F>,
    /// `qz_own`, `qz_disown`: a borrowed register's reference counted,
    /// a counted one given up.
    pub own: F,
    pub disown: F,
    pub clone_ptr: F,
    pub block_param: F,
    pub frame_get: F,
    pub frame_set: F,
    pub field_get: F,
    pub load_const: F,
    pub field_set: F,
    pub call_static: F,
    pub yield_: F,
    pub construct: F,
    pub alloc_data: F,
    pub owned_call: F,
    pub hash_put_int: F,
}

/// A typed entry's exits: the block a status leaves through, the
/// address of its `self`, the caller's result slot, and the block a
/// result of the declared type leaves through (with the bits).
type TypedExit<B> = (
    <B as Builder>::Block,
    <B as Builder>::Value,
    <B as Builder>::Value,
    <B as Builder>::Block,
);

/// What a backend hands the generator for one function: the builder,
/// the runtime callables, the compiled bodies and typed entries the
/// function calls directly, and the signature of a body for indirect
/// calls.
pub(crate) struct Target<'a, B: Builder> {
    pub b: &'a mut B,
    pub h: Helpers<B::Func>,
    pub callees: HashMap<FuncId, B::Func>,
    pub callees_typed: HashMap<FuncId, B::Func>,
    pub body_sig: B::Sig,
    /// A typed entry pushes no activation until something needs one
    /// (the backend walks the native stack for backtraces).
    pub lazy_act: bool,
    /// What of the function compiled code hands the runtime by position.
    /// Generate the *entry* of a typed function rather than its body:
    /// only the part that needs no frame (`unbox::pure_region`), every
    /// way out of it calling this body with the same arguments (the
    /// part has no effects, so the body may run it again).
    pub entry_of: Option<B::Func>,
}

/// The blocks a typed entry runs before it needs a frame, when it has
/// any (see `unbox::pure_region`): a backend gives such a function a
/// separate entry (`Target::entry_of`).
pub(crate) fn typed_entry_region(
    f: &Function,
    methods: &[RtMethod],
    classes: &[RtClass],
    builtin: &RtBuiltin,
    typed_all: &[Option<unbox::TypedSig>],
    sig: &unbox::TypedSig,
) -> Option<Vec<bool>> {
    let heap = quarz_ir::live::heap_possible(f, methods);
    let entry_states = unbox::analyze(f, methods, classes, builtin, typed_all);
    let region = unbox::pure_region(
        f,
        &entry_states,
        methods,
        classes,
        builtin,
        typed_all,
        sig,
        &heap,
    );
    // Worth it when some path returns from the region.
    let returns = f
        .blocks
        .iter()
        .zip(&region)
        .any(|(blk, &r)| r && matches!(blk.term, Term::Return(_)));
    (region.first().copied().unwrap_or(false) && returns).then_some(region)
}

/// The compiled bodies `f` calls directly, and which of them have typed
/// entries: what a backend imports before `gen_function`.
pub(crate) fn direct_callees(f: &Function, methods: &[RtMethod]) -> Vec<FuncId> {
    let mut out: Vec<FuncId> = Vec::new();
    for blk in &f.blocks {
        for inst in &blk.insts {
            if let Some(target) = direct_target(inst, methods) {
                if !out.contains(&target) {
                    out.push(target);
                }
            }
        }
    }
    out
}

/// Emit the body of `f` (its boxed entry, or its typed entry when
/// `typed` says so) into the builder.
#[allow(clippy::too_many_arguments)]
pub(crate) fn gen_function<B: Builder>(
    t: Target<'_, B>,
    fid: FuncId,
    f: &Function,
    methods: &[RtMethod],
    functions: &[Function],
    classes: &[RtClass],
    builtin: &RtBuiltin,
    typed: Option<unbox::TypedSig>,
    typed_all: &[Option<unbox::TypedSig>],
) {
    let Target {
        b,
        h,
        callees,
        callees_typed,
        body_sig,
        lazy_act,
        entry_of,
    } = t;
    let drop_value_fn = h.drop_value;
    let finalize_fn = h.finalize;
    let pop_call = h.pop_call;
    let mut borrowed = vec![false; f.nregs.max(1) as usize];
    for blk in &f.blocks {
        for inst in &blk.insts {
            if let Inst::ArrayGetReg {
                dst, borrow: true, ..
            } = inst
            {
                borrowed[*dst as usize] = true;
            }
        }
    }
    let heap = quarz_ir::live::heap_possible(f, methods);
    // Unboxed numbers: the state of each register at each block's
    // entry, and an SSA variable per register for each kind.
    let entry_states = unbox::analyze(f, methods, classes, builtin, typed_all);
    let live = unbox::liveness(f);
    let last_reads = quarz_ir::live::last_reads_from(f, &live);
    let nregs_usize = f.nregs.max(1) as usize;
    let ivars: Vec<B::Var> = (0..nregs_usize).map(|_| b.declare_var(Ty::I64)).collect();
    let fvars: Vec<B::Var> = (0..nregs_usize).map(|_| b.declare_var(Ty::F64)).collect();
    let bvars: Vec<B::Var> = (0..nregs_usize).map(|_| b.declare_var(Ty::I8)).collect();
    let pvars: Vec<B::Var> = (0..nregs_usize).map(|_| b.declare_var(Ty::Ptr)).collect();
    // Whether a lazily pushed activation has been built (see
    // `materialize`).
    let pushed_var = b.declare_var(Ty::I8);
    // Bit `k` (of word `k / 64`): register `k`'s home holds a value to
    // release at exit.
    let nwords = nregs_usize.div_ceil(64);
    let valid_vars: Vec<B::Var> = (0..nwords).map(|_| b.declare_var(Ty::I64)).collect();
    // The argument area for direct calls: the widest callee's
    // parameters plus its block.
    // The argument area: the parameters of direct calls, or the
    // fields of a data construction, are laid out there.
    let max_direct_args = f
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter())
        .filter_map(|inst| match inst {
            // Direct and virtual calls lay their parameters out there.
            Inst::Call {
                kind: CallKind::Method(mid),
                ..
            } => {
                let m = &methods[*mid as usize];
                if m.native_key.is_some() {
                    return None;
                }
                Some(m.params.len() + usize::from(m.has_block))
            }
            Inst::Call {
                kind: CallKind::Construct { .. },
                args,
                ..
            } => Some(args.len()),
            _ => None,
        })
        .max()
        .unwrap_or(0)
        .max(1);
    let uses_act = typed.is_none()
        && f.blocks.iter().any(|blk| {
            blk.insts.iter().any(|i| {
                matches!(
                    i,
                    Inst::Arg { .. }
                        | Inst::SelfRef { .. }
                        | Inst::FrameGet { .. }
                        | Inst::FrameSet { .. }
                )
            })
        });

    let (entry, params) = b.entry_block();
    let entry_params = params.clone();
    let blocks: Vec<B::Block> = f.blocks.iter().map(|_| b.create_block()).collect();
    let unwinds: Vec<B::Block> = f
        .blocks
        .iter()
        .map(|_| {
            let blk = b.create_block();
            b.append_block_param(blk, Ty::I32);
            blk
        })
        .collect();
    let exit = b.create_block();
    b.append_block_param(exit, Ty::I32);
    // `return` releases its registers inline (only those whose state
    // allows a heap value) and leaves through here.
    let exit_quick = b.create_block();
    b.append_block_param(exit_quick, Ty::I32);

    b.switch_to_block(entry);
    let rt = params[0];
    // A typed entry builds its own activation (the boxed one gets
    // the caller's) and its own result slot.
    let (mut act, mut out) = (params[1], params[2]);
    let nregs = f.nregs.max(1);
    let regs = b.stack_slot((VALUE_SIZE as u32) * nregs, 3);
    // Scratch space for the argument register indices of static calls.
    let max_args = f
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter())
        .map(|inst| match inst {
            Inst::Call { args, .. } | Inst::OwnedCall { args, .. } => args.len(),
            _ => 0,
        })
        .max()
        .unwrap_or(0)
        .max(1);
    let scratch = b.stack_slot(4 * max_args as u32, 2);
    // An activation for direct calls, the callee's result, and the
    // addresses of this activation's arguments and `self`.
    let act_buf = b.stack_slot(ACT_BUF_SIZE, 4);
    // The callee's result slot: nil between calls (each consumer leaves
    // it so), written once here.
    let out_buf = b.stack_slot(VALUE_SIZE as u32, 3);
    let vbody = b.stack_slot(8, 3);
    let ptrs = b.stack_slot(32, 3);
    let args_buf = b.stack_slot((VALUE_SIZE as u32) * max_direct_args as u32, 3);
    // Registers start as nil: the tag word is written for those
    // that may ever be released (they may hold a heap value) or be
    // read before they are written; the others are written first.
    // Written by the runtime somewhere (which drops what it finds),
    // or live at entry, or unknown at some block's entry (a handler
    // knows nothing about any register): the home must hold nil
    // from the start. Only registers written solely by inline code
    // (numbers, copies, typed parameters and calls) are left alone.
    // (A register that may hold a heap value is released at exit only
    // when the mask in `valid_vars` says its home holds one: see
    // `set_valid`.)
    let mut zeroed: Vec<bool> = (0..nregs as usize)
        .map(|i| {
            live.first()
                .and_then(|blk| blk.first())
                .is_some_and(|l| l[i])
                || entry_states.iter().any(|st| st[i].boxed())
        })
        .collect();
    for blk in &f.blocks {
        for inst in &blk.insts {
            let inline_only = match inst {
                Inst::LoadConst { idx, .. } => matches!(
                    f.consts[*idx as usize],
                    Constant::Nil | Constant::Bool(_) | Constant::Int(_) | Constant::Float(_)
                ),
                Inst::Move { .. }
                | Inst::Take { .. }
                | Inst::SelfRef { .. }
                | Inst::Not { .. }
                | Inst::IsNil { .. }
                | Inst::ClassIs { .. }
                | Inst::ClearRegs { .. }
                | Inst::Release { .. } => true,
                Inst::Arg { .. } => typed.is_some(),
                Inst::BinOp { .. } => {
                    unbox::bin_types(inst, methods, builtin).is_some() && !unbox::float_mod(inst)
                }
                Inst::Call { .. } => unbox::call_num(inst, methods, typed_all).is_some(),
                _ => false,
            };
            if !inline_only {
                for r in inst.defs() {
                    zeroed[r as usize] = true;
                }
            }
        }
    }
    // The part of the function that runs before its frame is set up
    // (see `unbox::pure_region`): only with a lazily built activation.
    let region = match (&typed, entry_of) {
        (Some(sig), Some(_)) => unbox::pure_region(
            f,
            &entry_states,
            methods,
            classes,
            builtin,
            typed_all,
            sig,
            &heap,
        ),
        _ => vec![false; f.blocks.len()],
    };
    let mut own_out_slot: Option<B::Value> = None;
    let mut typed_params: Vec<B::Value> = Vec::new();
    let mut typed_self_ptr: Option<B::Value> = None;
    let mut typed_params_buf: Option<B::Value> = None;
    let mut typed_exit: Option<TypedExit<B>> = None;
    if let Some(sig) = &typed {
        let nparams = sig.params.len();
        let self_ptr = params[2];
        typed_params = params[3..3 + nparams].to_vec();
        let out_caller = params[3 + nparams];
        let own_act = b.stack_slot(ACT_BUF_SIZE, 4);
        let own_out = b.stack_slot(VALUE_SIZE as u32, 3);
        let params_buf = b.stack_slot((VALUE_SIZE as u32) * nparams.max(1) as u32, 3);
        // The parameters are boxed into `params_buf`, and `self`
        // cloned into the activation, only when the runtime needs them
        // (see `materialize`).
        typed_self_ptr = Some(self_ptr);
        typed_params_buf = Some(params_buf);
        // Native stack check (and the nil of the slots and homes), then
        // the activation, pushed; deferred when the function may return
        // without needing either.
        own_out_slot = Some(own_out);
        if !region.first().copied().unwrap_or(false) {
            emit_frame_setup(b, &h, rt, regs, out_buf, Some(own_out), &zeroed);
        }
        let self_dst = b.iadd_imm(own_act, L::ACT_SELF as i64);
        let zero8 = b.iconst(Ty::I8, 0);
        b.def_var(pushed_var, zero8);
        if !lazy_act {
            emit_typed_activation(
                b,
                rt,
                own_act,
                fid,
                f.file,
                nparams,
                params_buf,
                h.push_call,
                !sig.params.contains(&unbox::Mach::Boxed),
            );
        }
        act = own_act;
        out = own_out;
        let te = b.create_block();
        b.append_block_param(te, Ty::I32);
        let fast = b.create_block();
        b.append_block_param(fast, Ty::I64);
        typed_exit = Some((te, self_dst, out_caller, fast));
    }
    if typed.is_none() {
        emit_frame_setup(b, &h, rt, regs, out_buf, None, &zeroed);
    }
    if uses_act {
        // `[args, self, nargs, frame]` of this activation: the frame
        // view is the `Frame` inside its `Rc` allocation (after the
        // two counts), null when there is none.
        let args_ptr = b.load(Ty::Ptr, act, L::ACT_ARGS_PTR as i32);
        b.store(args_ptr, ptrs, 0);
        let self_addr = b.iadd_imm(act, L::ACT_SELF as i64);
        b.store(self_addr, ptrs, 8);
        let nargs = b.uload32(act, L::ACT_NARGS as i32);
        b.store(nargs, ptrs, 16);
        let frame_rc = b.load(Ty::Ptr, act, L::ACT_FRAME as i32);
        let frame_view = b.iadd_imm(frame_rc, i64::from(OBJECT_FIELDS_PTR_OFF));
        let none = b.icmp_imm(IntCC::Equal, frame_rc, 0);
        let frame = b.select(none, frame_rc, frame_view);
        b.store(frame, ptrs, 24);
    }
    // No home holds a heap value yet (see `set_valid`).
    let no_valid = b.iconst(Ty::I64, 0);
    for v in &valid_vars {
        b.def_var(*v, no_valid);
    }
    b.jump(blocks[0], &[]);

    let mut g = Gen {
        b,
        h,
        rt,
        act,
        regs,
        exit,
        scratch,
        act_buf,
        out_buf,
        vbody,
        body_sig,
        ptrs,
        args_buf,
        fid,
        f,
        methods,
        functions,
        classes,
        builtin,
        callees,
        states: vec![State::NonHeap; nregs_usize],
        nregs: nregs_usize,
        live: &live,
        last_reads: &last_reads,
        typed_all,
        ivars,
        fvars,
        bvars,
        pvars,
        borrowed,
        pushed_var,
        lazy_act,
        callees_typed,
        typed: typed.clone(),
        typed_params,
        typed_self_ptr,
        typed_params_buf,
        typed_fast_exit: typed_exit.map(|t| t.3),
        zeroed,
        heap: heap.clone(),
        valid_vars: valid_vars.clone(),
        stale: vec![false; nregs_usize],
        region: region.clone(),
        own_out: own_out_slot,
        entry_of,
        entry_params,
    };
    for (i, blk) in f.blocks.iter().enumerate() {
        g.b.switch_to_block(blocks[i]);
        if g.entry_of.is_some() && !region[i] {
            // Not part of an entry (never reached: leaving the region
            // calls the body).
            g.setup_frame();
            let zb = g.b.iconst(Ty::I64, 0);
            g.b.return_(&[zb]);
            continue;
        }
        g.states.clone_from(&entry_states[i]);
        g.stale.fill(false);
        for (j, inst) in blk.insts.iter().enumerate() {
            g.b.set_line(blk.lines[j]);
            g.set_valid();
            g.inst(i as u32, j as u32, inst, unwinds[i]);
            g.after(inst);
        }
        g.b.set_line(blk.term_line);
        g.set_valid();
        // A successor reads homes it knows nothing about.
        let at_term = &live[i][blk.insts.len()];
        for r in (0..g.nregs).filter(|&r| at_term[r]) {
            g.ensure_home(r as Reg);
        }
        // Write back the unboxed registers that a successor expects
        // in memory (a different state there), or that a terminator
        // leaving the function reads.
        let at_term = &live[i][blk.insts.len()];
        if region[i] {
            // In the pure region: the frame is set up on an edge that
            // leaves it, before anything is written back.
            let edge = |g: &mut Gen<'_, B>, t: BlockId| {
                if !region[t as usize] {
                    g.setup_frame();
                }
                g.flush_for_edge(&entry_states[t as usize], at_term);
                g.b.jump(blocks[t as usize], &[]);
            };
            match &blk.term {
                Term::Jump(t) => {
                    edge(&mut g, *t);
                    continue;
                }
                Term::Branch { cond, then, els } => {
                    let truthy = g.truthy(*cond);
                    let to_then = g.b.create_block();
                    let to_els = g.b.create_block();
                    g.b.brif(truthy, to_then, &[], to_els, &[]);
                    let states = g.states.clone();
                    g.b.switch_to_block(to_then);
                    edge(&mut g, *then);
                    g.states.clone_from(&states);
                    g.b.switch_to_block(to_els);
                    edge(&mut g, *els);
                    continue;
                }
                _ => {}
            }
        }
        let fast_return = matches!(&blk.term, Term::Return(r)
        if g.typed_fast_exit.is_some()
            && g.typed.as_ref().is_some_and(|t| t.ret.held(g.states[*r as usize])));
        match &blk.term {
            Term::Jump(t) => g.flush_for_edge(&entry_states[*t as usize], at_term),
            Term::Branch { then, els, .. } => {
                g.flush_for_edge(&entry_states[*then as usize], at_term);
                g.flush_for_edge(&entry_states[*els as usize], at_term);
            }
            // The bits go straight back.
            Term::Return(_) if fast_return => {}
            Term::Return(r) => g.flush(*r),
            _ => g.flush_live(at_term),
        }
        match &blk.term {
            Term::Jump(t) => {
                g.b.jump(blocks[*t as usize], &[]);
            }
            Term::Branch { cond, then, els } => {
                let truthy = g.truthy(*cond);
                g.b.brif(
                    truthy,
                    blocks[*then as usize],
                    &[],
                    blocks[*els as usize],
                    &[],
                );
            }
            Term::Return(r)
                if g.typed_fast_exit.is_some()
                    && g.typed
                        .as_ref()
                        .is_some_and(|t| t.ret.held(g.states[*r as usize])) =>
            {
                // A typed entry returning a value of its declared
                // type: the bits go straight back.
                let ret = g.typed.as_ref().map(|t| t.ret);
                let bits = match (ret, g.states[*r as usize]) {
                    (Some(unbox::Mach::Nil), _) => g.b.iconst(Ty::I64, 0),
                    (_, State::Int) => g.b.use_var(g.ivar(*r)),
                    (_, State::Bool) => {
                        let v = g.b.use_var(g.bvar(*r));
                        g.b.uextend(Ty::I64, v)
                    }
                    _ => {
                        let v = g.b.use_var(g.fvar(*r));
                        g.b.bitcast(Ty::I64, v)
                    }
                };
                if region[i] {
                    // Nothing was set up, pushed or written: return
                    // right here (a return of its own lets the backend
                    // keep the frame off this path).
                    g.b.return_(&[bits]);
                    continue;
                }
                for k in (0..g.nregs).filter(|&k| heap[k]) {
                    g.release(k as Reg);
                }
                g.finalize();
                let fast = g.typed_fast_exit.expect("typed");
                g.b.jump(fast, &[bits]);
            }
            Term::Return(r) => {
                // Move the value into `out` (which holds nil) and
                // leave the register nil, then release the rest.
                g.ensure_home(*r);
                let off = reg_off(*r);
                for k in [0, 8] {
                    let w = g.b.load(Ty::I64, regs, off + k);
                    g.b.store(w, out, k);
                }
                let zero = g.b.iconst(Ty::I64, 0);
                g.b.store(zero, regs, off);
                g.states[*r as usize] = State::NonHeap;
                for k in (0..g.nregs).filter(|&k| heap[k]) {
                    g.release(k as Reg);
                }
                g.finalize();
                let ok = g.b.iconst(Ty::I32, 0);
                g.b.jump(exit_quick, &[ok]);
            }
            Term::Raise(_)
            | Term::BreakOut(_)
            | Term::ReturnOut(_)
            | Term::Resume(_)
            | Term::Unreachable => {
                let (kind, reg) = match &blk.term {
                    Term::Raise(r) => (0, *r),
                    Term::BreakOut(r) => (1, *r),
                    Term::ReturnOut(r) => (2, *r),
                    Term::Resume(r) => (3, *r),
                    _ => (4, 0),
                };
                let kind = g.b.iconst(Ty::I32, kind);
                let reg = g.b.iconst(Ty::I32, i64::from(reg));
                let n = blk.insts.len() as u32;
                let status = g.op_status("qz_op_term", i as u32, n, &[kind, reg]);
                g.b.jump(unwinds[i], &[status]);
            }
        }
    }
    let b = g.b;
    // Unwinding: route a status to the block's handler or out.
    for (i, blk) in f.blocks.iter().enumerate() {
        b.switch_to_block(unwinds[i]);
        let status = b.block_params(unwinds[i])[0];
        match blk.handler {
            Some(h) if h.kind == HandlerKind::Ensure => {
                b.jump(blocks[h.block as usize], &[]);
            }
            Some(h) => {
                // Another flow goes past the rescues to the ensure that
                // covers them.
                let is_raise = b.icmp_imm(IntCC::Equal, status, STATUS_RAISE);
                match quarz_ir::flow_handler(&f.blocks, blk) {
                    Some(e) => b.brif(
                        is_raise,
                        blocks[h.block as usize],
                        &[],
                        blocks[e as usize],
                        &[],
                    ),
                    None => b.brif(is_raise, blocks[h.block as usize], &[], exit, &[status]),
                }
            }
            None => {
                b.jump(exit, &[status]);
            }
        }
    }
    // Exit: release the registers that may hold heap values (those the
    // mask says do: the others may not even have been written).
    b.switch_to_block(exit);
    let status = b.block_params(exit)[0];
    let valid: Vec<B::Value> = valid_vars.iter().map(|v| b.use_var(*v)).collect();
    for i in 0..nregs as usize {
        if !heap[i] {
            continue;
        }
        let p = b.iadd_imm(regs, i as i64 * i64::from(VALUE_SIZE));
        let bit = b.iconst(Ty::I64, 1i64 << (i % 64));
        let set = b.band(valid[i / 64], bit);
        let holds = b.icmp_imm(IntCC::NotEqual, set, 0);
        let release = b.create_block();
        let next = b.create_block();
        b.brif(holds, release, &[], next, &[]);
        b.switch_to_block(release);
        emit_release_ptr(b, drop_value_fn, p);
        b.jump(next, &[]);
        b.switch_to_block(next);
    }
    // What the registers held is finalized as the function ends (as the
    // interpreter does when a function returns), unless a flow is on
    // its way out.
    if let Some(finalize) = finalize_fn {
        let ok_b = b.create_block();
        let done_b = b.create_block();
        let ok = b.icmp_imm(IntCC::Equal, status, 0);
        b.brif(ok, ok_b, &[], done_b, &[]);
        b.switch_to_block(ok_b);
        b.call(finalize, &[rt]);
        b.jump(done_b, &[]);
        b.switch_to_block(done_b);
    }
    match typed_exit {
        Some((te, ..)) => b.jump(te, &[status]),
        None => b.return_(&[status]),
    };
    b.switch_to_block(exit_quick);
    let status = b.block_params(exit_quick)[0];
    match typed_exit {
        Some((te, ..)) => b.jump(te, &[status]),
        None => b.return_(&[status]),
    };
    if let (Some((te, self_dst, out_caller, fast)), Some(sig)) = (typed_exit, &typed) {
        // A `return` of a value already of the declared type: pop,
        // release what `self` may hold, hand the bits back.
        b.switch_to_block(fast);
        let bits = b.block_params(fast)[0];
        emit_typed_teardown(
            b,
            rt,
            act,
            self_dst,
            pop_call,
            drop_value_fn,
            pushed_var,
            lazy_act,
        );
        b.return_(&[bits]);
        // The typed exit: pop the activation, release `self`, and
        // hand the result back as a machine value when it is of the
        // declared type, boxed in the caller's slot otherwise.
        b.switch_to_block(te);
        let status = b.block_params(te)[0];
        emit_typed_teardown(
            b,
            rt,
            act,
            self_dst,
            pop_call,
            drop_value_fn,
            pushed_var,
            lazy_act,
        );
        let ok = b.icmp_imm(IntCC::Equal, status, 0);
        let fits_b = b.create_block();
        let failed_b = b.create_block();
        b.brif(ok, fits_b, &[], failed_b, &[]);
        b.switch_to_block(failed_b);
        emit_typed_fail(b, rt, status);
        b.switch_to_block(fits_b);
        let tag = load_tag(b, out, 0);
        let is = b.icmp_imm(IntCC::Equal, tag, mach_tag(sig.ret));
        let unboxed_b = b.create_block();
        let boxed_b = b.create_block();
        b.brif(is, unboxed_b, &[], boxed_b, &[]);
        b.switch_to_block(unboxed_b);
        let bits = match sig.ret {
            unbox::Mach::Nil => b.iconst(Ty::I64, 0),
            unbox::Mach::Bool => b.uload8(out, BOOL_OFF),
            _ => b.load(Ty::I64, out, 8),
        };
        b.return_(&[bits]);
        b.switch_to_block(boxed_b);
        for k in [0, 8] {
            let w = b.load(Ty::I64, out, k);
            b.store(w, out_caller, k);
        }
        let boxed_v = b.iconst(Ty::I32, STATUS_BOXED);
        emit_typed_fail(b, rt, boxed_v);
    }
}

/// The tag of a boxed value of a typed entry's parameter or result type.
fn mach_tag(m: unbox::Mach) -> i64 {
    match m {
        unbox::Mach::Int => TAG_INT,
        unbox::Mach::Float => TAG_FLOAT,
        unbox::Mach::Bool => TAG_BOOL,
        unbox::Mach::Nil => TAG_NIL,
        unbox::Mach::Boxed => unreachable!("a boxed parameter has no one tag"),
    }
}

/// Leave a typed entry other than with its value: the status goes to the
/// runtime (`Hot::typed_status`), where the caller finds it.
fn emit_typed_fail<B: Builder>(b: &mut B, rt: B::Value, status: B::Value) {
    b.store(status, rt, L::HOT_TYPED_STATUS as i32);
    let zero_bits = b.iconst(Ty::I64, 0);
    b.return_(&[zero_bits]);
}

/// Set a function's frame up: the result slots and the homes that must
/// start nil (see `zeroed`), and, for a typed entry, the native stack
/// check (whose failure returns at once: nothing is pushed yet).
fn emit_frame_setup<B: Builder>(
    b: &mut B,
    h: &Helpers<B::Func>,
    rt: B::Value,
    regs: B::Value,
    out_buf: B::Value,
    own_out: Option<B::Value>,
    zeroed: &[bool],
) {
    let zero = b.iconst(Ty::I64, 0);
    b.store(zero, out_buf, 0);
    if let Some(own_out) = own_out {
        b.store(zero, own_out, 0);
        let sp = b.get_stack_pointer();
        let limit_cell = b.load(Ty::Ptr, rt, L::HOT_LIMIT_PTR as i32);
        let limit = b.load(Ty::Ptr, limit_cell, 0);
        let exhausted = b.icmp(IntCC::UnsignedLessThan, sp, limit);
        let overflow = b.create_block();
        let build = b.create_block();
        b.set_cold(overflow);
        b.brif(exhausted, overflow, &[], build, &[]);
        b.switch_to_block(overflow);
        let status = b.call(h.stack_overflow, &[rt])[0];
        emit_typed_fail(b, rt, status);
        b.switch_to_block(build);
    }
    for (i, z) in zeroed.iter().enumerate() {
        if *z {
            b.store(zero, regs, i as i32 * VALUE_SIZE);
        }
    }
}

/// Leave a typed entry: pop its activation and release its `self`, when
/// it was built at all (always, unless lazily).
#[allow(clippy::too_many_arguments)]
fn emit_typed_teardown<B: Builder>(
    b: &mut B,
    rt: B::Value,
    act: B::Value,
    self_dst: B::Value,
    pop_call: B::Func,
    drop_value: B::Func,
    pushed_var: B::Var,
    lazy_act: bool,
) {
    if lazy_act {
        let pushed = b.use_var(pushed_var);
        let teardown = b.create_block();
        let done = b.create_block();
        b.brif(pushed, teardown, &[], done, &[]);
        b.switch_to_block(teardown);
        emit_typed_pop(b, rt, act, pop_call);
        emit_release_ptr(b, drop_value, self_dst);
        b.jump(done, &[]);
        b.switch_to_block(done);
    } else {
        emit_typed_pop(b, rt, act, pop_call);
        emit_release_ptr(b, drop_value, self_dst);
    }
}

/// The compiled body a static call goes to directly (a method with a
/// QIR body, not a native).
fn direct_target(inst: &Inst, methods: &[RtMethod]) -> Option<FuncId> {
    let Inst::Call {
        kind: CallKind::Method(mid),
        ..
    } = inst
    else {
        return None;
    };
    let m = methods.get(*mid as usize)?;
    // An overridden method (a class method too: the class it is called
    // on decides) is resolved at run time.
    if m.native_key.is_some() || (m.overridden && !m.is_extension) {
        return None;
    }
    m.func
}

/// The first word of an allocation that other threads may hold
/// (`quarz_vm::rc`): its count is elsewhere, updated atomically by the
/// runtime. Any other value is the count of a local allocation.
const RC_SHARED: i64 = 0;

/// Build a typed entry's activation in `own_act` (`self` nil, the
/// parameters at `params_buf`, which the caller fills) and push it on
/// the call stack.
#[allow(clippy::too_many_arguments)]
fn emit_typed_activation<B: Builder>(
    b: &mut B,
    rt: B::Value,
    own_act: B::Value,
    fid: FuncId,
    file: u32,
    nparams: usize,
    params_buf: B::Value,
    push_call: B::Func,
    owned: bool,
) {
    let zero = b.iconst(Ty::I64, 0);
    let fid_v = b.iconst(Ty::I32, i64::from(fid));
    b.store(fid_v, own_act, L::ACT_FID as i32);
    let task = b.load(Ty::I32, rt, L::CURRENT_TASK as i32);
    b.store(task, own_act, L::ACT_TASK as i32);
    let zero32 = b.iconst(Ty::I32, 0);
    b.store(zero32, own_act, L::ACT_LINE as i32);
    let file_v = b.iconst(Ty::I32, i64::from(file));
    b.store(file_v, own_act, L::ACT_FILE as i32);
    let self_dst = b.iadd_imm(own_act, L::ACT_SELF as i64);
    b.store(zero, self_dst, 0);
    for off in [
        L::ACT_FRAME,
        L::ACT_BLOCK,
        L::ACT_METHOD_TAG,
        L::ACT_CLOSURE_TAG,
        L::ACT_YIELD_CALLER,
    ] {
        b.store(zero, own_act, off as i32);
    }
    // Its own address orders it among native frames; a frame the
    // native unwinder also sees is marked so (see `Target::lazy_act`).
    b.store(own_act, own_act, L::ACT_SP as i32);
    let native = b.iconst(Ty::I8, 0);
    b.store(native, own_act, L::ACT_NATIVE as i32);
    // Its parameter area is its own, unless it holds values lent by the
    // caller (copied by whoever reads them).
    let owned = b.iconst(Ty::I8, i64::from(owned));
    b.store(owned, own_act, L::ACT_ARGS_OWNED as i32);
    let provided: u64 = if nparams >= 64 {
        u64::MAX
    } else {
        (1u64 << nparams) - 1
    };
    let provided_v = b.iconst(Ty::I64, provided as i64);
    b.store(provided_v, own_act, L::ACT_PROVIDED as i32);
    b.store(params_buf, own_act, L::ACT_ARGS_PTR as i32);
    let nargs_v = b.iconst(Ty::I32, nparams as i64);
    b.store(nargs_v, own_act, L::ACT_NARGS as i32);
    let len = b.load(Ty::I64, rt, L::HOT_STACK_LEN as i32);
    let cap = b.load(Ty::I64, rt, L::HOT_STACK_CAP as i32);
    let full = b.icmp(IntCC::Equal, len, cap);
    let push_slow = b.create_block();
    let push_fast = b.create_block();
    let pushed = b.create_block();
    b.brif(full, push_slow, &[], push_fast, &[]);
    b.switch_to_block(push_slow);
    b.call(push_call, &[rt, own_act]);
    b.jump(pushed, &[]);
    b.switch_to_block(push_fast);
    let stack = b.load(Ty::Ptr, rt, L::HOT_STACK_PTR as i32);
    let slot_off = b.ishl_imm(len, 3);
    let slot = b.iadd(stack, slot_off);
    b.store(own_act, slot, 0);
    let len1 = b.iadd_imm(len, 1);
    b.store(len1, rt, L::HOT_STACK_LEN as i32);
    b.jump(pushed, &[]);
    b.switch_to_block(pushed);
}

/// Release the value at `p` and leave nil there: nothing for values
/// without a reference count, a decrement when other references remain,
/// the runtime's destructor for the last one.
/// Pop activation `act` off the call stack (the top entry unless tasks
/// interleaved, in which case the runtime finds it).
fn emit_typed_pop<B: Builder>(b: &mut B, rt: B::Value, act: B::Value, pop_call: B::Func) {
    let len = b.load(Ty::I64, rt, L::HOT_STACK_LEN as i32);
    let stack = b.load(Ty::Ptr, rt, L::HOT_STACK_PTR as i32);
    let len0 = b.iadd_imm(len, -1);
    let top_off = b.ishl_imm(len0, 3);
    let top_slot = b.iadd(stack, top_off);
    let top = b.load(Ty::Ptr, top_slot, 0);
    let is_top = b.icmp(IntCC::Equal, top, act);
    let pop_fast = b.create_block();
    let pop_slow = b.create_block();
    let popped = b.create_block();
    b.brif(is_top, pop_fast, &[], pop_slow, &[]);
    b.switch_to_block(pop_fast);
    b.store(len0, rt, L::HOT_STACK_LEN as i32);
    b.jump(popped, &[]);
    b.switch_to_block(pop_slow);
    b.call(pop_call, &[rt, act]);
    b.jump(popped, &[]);
    b.switch_to_block(popped);
}

/// A value's tag: the first byte at `p + off` (the rest of the word is
/// undefined but in a short string), as an `I64`.
fn load_tag<B: Builder>(b: &mut B, p: B::Value, off: i32) -> B::Value {
    b.uload8(p, off)
}

/// Release the value at `p` and leave nil there: a heap value's count is
/// lowered inline when it is local and above 1, else through `drop_value`
/// (the last reference, or a shared count). The payload's first word
/// points at the allocation, whose first word is the count (checked at
/// start-up).
fn emit_release_ptr<B: Builder>(b: &mut B, drop_value: B::Func, p: B::Value) {
    let tag = load_tag(b, p, 0);
    let needs = b.icmp_imm(IntCC::UnsignedGreaterThanOrEqual, tag, NEEDS_DROP_FROM);
    let heap = b.create_block();
    let shared = b.create_block();
    let last = b.create_block();
    let cont = b.create_block();
    b.brif(needs, heap, &[], cont, &[]);
    b.switch_to_block(heap);
    let rc = b.load(Ty::Ptr, p, 8);
    let strong = b.load(Ty::I64, rc, 0);
    // 1 (the last reference) or `RC_SHARED` (0).
    let is_last = b.icmp_imm(IntCC::UnsignedLessThan, strong, 2);
    b.brif(is_last, last, &[], shared, &[]);
    b.switch_to_block(shared);
    let lowered = b.iadd_imm(strong, -1);
    b.store(lowered, rc, 0);
    let zero = b.iconst(Ty::I64, 0);
    b.store(zero, p, 0);
    b.jump(cont, &[]);
    b.switch_to_block(last);
    b.call(drop_value, &[p]);
    b.jump(cont, &[]);
    b.switch_to_block(cont);
}

/// `*dst = *src` where `dst` holds nil: a two-word copy, plus a
/// reference count bump for heap values (inline for a local allocation,
/// through `clone_ptr` for a shared one).
fn emit_clone_ptr<B: Builder>(b: &mut B, clone_ptr: B::Func, dst: B::Value, src: B::Value) {
    let w0 = b.load(Ty::I64, src, 0);
    let w1 = b.load(Ty::I64, src, 8);
    b.store(w0, dst, 0);
    b.store(w1, dst, 8);
    // The tag is the first byte (see `load_tag`).
    let mask = b.iconst(Ty::I64, 0xff);
    let tag = b.band(w0, mask);
    let needs = b.icmp_imm(IntCC::UnsignedGreaterThanOrEqual, tag, NEEDS_DROP_FROM);
    let heap = b.create_block();
    let local = b.create_block();
    let shared = b.create_block();
    let cont = b.create_block();
    b.brif(needs, heap, &[], cont, &[]);
    b.switch_to_block(heap);
    let rc = b.load(Ty::Ptr, src, 8);
    let strong = b.load(Ty::I64, rc, 0);
    let is_local = b.icmp_imm(IntCC::NotEqual, strong, RC_SHARED);
    b.brif(is_local, local, &[], shared, &[]);
    b.switch_to_block(local);
    let bumped = b.iadd_imm(strong, 1);
    b.store(bumped, rc, 0);
    b.jump(cont, &[]);
    b.switch_to_block(shared);
    b.set_cold(shared);
    b.call(clone_ptr, &[dst, src]);
    b.jump(cont, &[]);
    b.switch_to_block(cont);
}

/// One more reference to the heap value whose allocation is `rc`, held
/// in the value at `home`: its local count bumped inline, a shared one
/// through `qz_own`.
fn emit_retain<B: Builder>(b: &mut B, own: B::Func, home: B::Value, rc: B::Value) {
    let local = b.create_block();
    let shared = b.create_block();
    let cont = b.create_block();
    let strong = b.load(Ty::I64, rc, 0);
    let is_local = b.icmp_imm(IntCC::NotEqual, strong, RC_SHARED);
    b.brif(is_local, local, &[], shared, &[]);
    b.switch_to_block(local);
    let bumped = b.iadd_imm(strong, 1);
    b.store(bumped, rc, 0);
    b.jump(cont, &[]);
    b.switch_to_block(shared);
    b.set_cold(shared);
    b.call(own, &[home]);
    b.jump(cont, &[]);
    b.switch_to_block(cont);
}

/// A call compiled to `qz_call_static`.
struct StaticCall {
    mid: MethodId,
    recv: Option<Reg>,
    args: Vec<Reg>,
    block: Option<Reg>,
    dst: Reg,
}

/// The offset of register `r`'s home in the register file.
fn reg_off(r: Reg) -> i32 {
    r as i32 * VALUE_SIZE
}

/// Code generation for one function body.
struct Gen<'a, B: Builder> {
    b: &'a mut B,
    h: Helpers<B::Func>,
    rt: B::Value,
    act: B::Value,
    regs: B::Value,
    exit: B::Block,
    scratch: B::Value,
    /// Space for the activation of a direct call.
    act_buf: B::Value,
    /// Where a directly called body leaves its result.
    out_buf: B::Value,
    /// A word for the body address `qz_enter_virtual` returns.
    vbody: B::Value,
    /// The signature of compiled bodies, for indirect calls.
    body_sig: B::Sig,
    /// `[args, self, nargs]` of this activation (see `qz_act_ptrs`).
    ptrs: B::Value,
    /// The argument area of direct calls.
    args_buf: B::Value,
    fid: FuncId,
    f: &'a Function,
    methods: &'a [RtMethod],
    functions: &'a [Function],
    classes: &'a [RtClass],
    builtin: &'a RtBuiltin,
    callees: HashMap<FuncId, B::Func>,
    /// Liveness per block and instruction (see `quarz_ir::live`).
    live: &'a [Vec<Vec<bool>>],
    /// The registers each instruction reads for the last time
    /// (`quarz_ir::live::last_reads`, what the interpreter moves too).
    last_reads: &'a [Vec<Vec<Reg>>],
    /// What is known about each register here (see `unbox`).
    states: Vec<State>,
    nregs: usize,
    /// The typed entries of every function (see `unbox::typed_sigs`).
    typed_all: &'a [Option<unbox::TypedSig>],
    /// The variables holding each register's unboxed Int, Float and Bool.
    ivars: Vec<B::Var>,
    fvars: Vec<B::Var>,
    bvars: Vec<B::Var>,
    /// The allocation of each register's object, when its state is `Obj`.
    pvars: Vec<B::Var>,
    /// The registers that hold array elements borrowed from their arrays
    /// (`ArrayGetReg`'s `borrow`): read without a count and never
    /// released.
    borrowed: Vec<bool>,
    /// Whether a lazily pushed activation has been built.
    pushed_var: B::Var,
    lazy_act: bool,
    /// The typed entries this function calls directly.
    callees_typed: HashMap<FuncId, B::Func>,
    /// This body's own typed entry, when compiling it as such, and its
    /// parameters as the entry received them.
    typed: Option<unbox::TypedSig>,
    typed_params: Vec<B::Value>,
    /// A typed entry's `self` (the caller's value) and the slots its
    /// parameters are boxed into when the runtime needs them.
    typed_self_ptr: Option<B::Value>,
    typed_params_buf: Option<B::Value>,
    /// Where a typed `return` of the declared type leaves (the bits).
    typed_fast_exit: Option<B::Block>,
    /// Which register homes were set to nil at entry (the others hold
    /// nothing until written, and must not be read or dropped).
    zeroed: Vec<bool>,
    /// Which registers may ever hold a heap value (see `heap_possible`).
    heap: Vec<bool>,
    /// Bit `k` of word `k / 64` set: register `k`'s home holds a value
    /// the exit must release (see `set_valid`).
    valid_vars: Vec<B::Var>,
    /// Registers holding nil (after `ClearRegs`) whose home has not been
    /// written: a read of the home writes nil there first (see
    /// `ensure_home`). Tracked within a block.
    stale: Vec<bool>,
    /// The blocks that run before the frame is set up (see
    /// `unbox::pure_region`), and the typed entry's result slot.
    region: Vec<bool>,
    own_out: Option<B::Value>,
    /// Generating a typed function's entry (see `Target::entry_of`).
    entry_of: Option<B::Func>,
    entry_params: Vec<B::Value>,
}

impl<B: Builder> Gen<'_, B> {
    /// Before a read of `r`'s home: a register cleared to nil whose home
    /// was never written gets its nil now.
    fn ensure_home(&mut self, r: Reg) {
        if self.stale[r as usize] {
            self.store_tag(r, TAG_NIL);
        }
    }

    fn tag(&mut self, r: Reg) -> B::Value {
        self.ensure_home(r);
        load_tag(self.b, self.regs, reg_off(r))
    }

    fn payload(&mut self, r: Reg) -> B::Value {
        self.ensure_home(r);
        self.b.load(Ty::I64, self.regs, reg_off(r) + 8)
    }

    /// The payload's first word as an address (the allocation of a heap
    /// value).
    fn payload_ptr(&mut self, r: Reg) -> B::Value {
        self.ensure_home(r);
        self.b.load(Ty::Ptr, self.regs, reg_off(r) + 8)
    }

    /// A `Bool`'s byte (as an `I64`).
    fn bool_payload(&mut self, r: Reg) -> B::Value {
        self.ensure_home(r);
        self.b.uload8(self.regs, reg_off(r) + BOOL_OFF)
    }

    /// Truthiness of a register: not nil and not false.
    fn truthy(&mut self, r: Reg) -> B::Value {
        match self.states[r as usize] {
            State::Bool => return self.b.use_var(self.bvar(r)),
            State::Int | State::Float => return self.b.iconst(Ty::I8, 1),
            _ => {}
        }
        let tag = self.tag(r);
        let p = self.bool_payload(r);
        let is_nil = self.b.icmp_imm(IntCC::Equal, tag, TAG_NIL);
        let is_bool = self.b.icmp_imm(IntCC::Equal, tag, TAG_BOOL);
        let is_zero = self.b.icmp_imm(IntCC::Equal, p, 0);
        let is_false = self.b.band(is_bool, is_zero);
        let falsy = self.b.bor(is_nil, is_false);
        let one = self.b.iconst(Ty::I8, 1);
        self.b.bxor(falsy, one)
    }

    /// Make sure `dst` holds no reference-counted value before an inline
    /// store overwrites it.
    fn release(&mut self, dst: Reg) {
        // A borrowed element holds no count of its own.
        if self.borrowed[dst as usize] {
            return;
        }
        if !self.states[dst as usize].needs_release() {
            return;
        }
        let p = self.b.iadd_imm(self.regs, i64::from(reg_off(dst)));
        emit_release_ptr(self.b, self.h.drop_value, p);
    }

    /// `regs[dst] = *src`: inline for values without reference counts,
    /// through the runtime for the others.
    fn clone_from(&mut self, dst: Reg, src: B::Value) {
        self.release(dst);
        let d = self.b.iadd_imm(self.regs, i64::from(reg_off(dst)));
        emit_clone_ptr(self.b, self.h.clone_ptr, d, src);
        self.stale[dst as usize] = false;
    }

    /// `*dst = regs[src]` where `dst` holds nil: inline for values without
    /// reference counts, through the runtime for the others.
    /// Whether `src`, read by instruction `index` of `block`, can be
    /// moved out instead of copied: it may hold a heap value (a boxed
    /// register; the rest is this backend's business), and this is its
    /// last read (QIR's answer, shared with the interpreter).
    fn movable(&self, _inst: &Inst, src: Reg, block: u32, index: u32) -> bool {
        !self.borrowed[src as usize]
            && self.states[src as usize].boxed()
            && self.last_reads[block as usize][index as usize].contains(&src)
    }

    /// `*dst = regs[src]`, the value moved out of the register (whose
    /// home becomes nil): no count increment now, no release later.
    fn move_reg_to_ptr(&mut self, dst: B::Value, src: Reg) {
        self.ensure_home(src);
        let src_ptr = self.b.iadd_imm(self.regs, i64::from(reg_off(src)));
        for k in [0, 8] {
            let w = self.b.load(Ty::I64, src_ptr, k);
            self.b.store(w, dst, k);
        }
        self.store_tag(src, TAG_NIL);
    }

    /// After a slow path that copied `src` instead of moving it: release
    /// the register so that both paths leave its home nil.
    fn drop_moved(&mut self, src: Reg) {
        self.release(src);
        self.store_tag(src, TAG_NIL);
    }

    fn clone_reg_to_ptr(&mut self, dst: B::Value, src: Reg) {
        // An unboxed register is written from its variable (its home
        // may be stale); a register that cannot hold a heap value is
        // copied without the count check.
        match self.states[src as usize] {
            State::Int => {
                let v = self.b.use_var(self.ivar(src));
                let t = self.b.iconst(Ty::I64, TAG_INT);
                self.b.store(t, dst, 0);
                self.b.store(v, dst, 8);
            }
            State::Float => {
                let v = self.b.use_var(self.fvar(src));
                let bits = self.b.bitcast(Ty::I64, v);
                let t = self.b.iconst(Ty::I64, TAG_FLOAT);
                self.b.store(t, dst, 0);
                self.b.store(bits, dst, 8);
            }
            State::Bool => {
                let v = self.b.use_var(self.bvar(src));
                let t = self.b.iconst(Ty::I64, TAG_BOOL);
                self.b.store(t, dst, 0);
                self.b.store(v, dst, BOOL_OFF);
            }
            State::NonHeap => {
                self.ensure_home(src);
                let src_ptr = self.b.iadd_imm(self.regs, i64::from(reg_off(src)));
                for k in [0, 8] {
                    let w = self.b.load(Ty::I64, src_ptr, k);
                    self.b.store(w, dst, k);
                }
            }
            State::Unknown | State::Obj | State::Arr => {
                let src_ptr = self.b.iadd_imm(self.regs, i64::from(reg_off(src)));
                emit_clone_ptr(self.b, self.h.clone_ptr, dst, src_ptr);
            }
        }
    }

    /// A direct call to a compiled method that needs neither a frame nor
    /// a method tag (it creates no blocks) and gets no block: the
    /// activation is built, pushed, torn down and popped inline, and
    /// the runtime is only called for a full call stack, a nearly
    /// exhausted native stack, or a non-OK status.
    #[allow(clippy::too_many_arguments)]
    fn lean_call(
        &mut self,
        body: B::Func,
        callee: FuncId,
        file: u32,
        recv: Option<Reg>,
        provided: u64,
        slots: usize,
        dst: Reg,
        unwind: B::Block,
    ) {
        let act = self.act_buf;
        let release_args = |g: &mut Self| {
            for k in 0..slots {
                let p = g.b.iadd_imm(g.args_buf, (k as i64) * i64::from(VALUE_SIZE));
                g.release_ptr(p);
            }
        };
        // Native stack check against the running task's limit.
        let sp = self.b.get_stack_pointer();
        let limit_cell = self.b.load(Ty::I64, self.rt, L::HOT_LIMIT_PTR as i32);
        let limit = self.b.load(Ty::Ptr, limit_cell, 0);
        let exhausted = self.b.icmp(IntCC::UnsignedLessThan, sp, limit);
        let overflow = self.b.create_block();
        let build = self.b.create_block();
        self.b.set_cold(overflow);
        self.b.brif(exhausted, overflow, &[], build, &[]);
        self.b.switch_to_block(overflow);
        let status = self.b.call(self.h.stack_overflow, &[self.rt])[0];
        release_args(self);
        self.b.jump(unwind, &[status]);
        self.b.switch_to_block(build);
        // The activation.
        let fid_v = self.b.iconst(Ty::I32, i64::from(callee));
        self.b.store(fid_v, act, L::ACT_FID as i32);
        let task = self.b.load(Ty::I32, self.rt, L::CURRENT_TASK as i32);
        self.b.store(task, act, L::ACT_TASK as i32);
        let zero32 = self.b.iconst(Ty::I32, 0);
        self.b.store(zero32, act, L::ACT_LINE as i32);
        let file_v = self.b.iconst(Ty::I32, i64::from(file));
        self.b.store(file_v, act, L::ACT_FILE as i32);
        let self_dst = self.b.iadd_imm(act, L::ACT_SELF as i64);
        match recv {
            Some(r) => self.clone_reg_to_ptr(self_dst, r),
            None => {
                let caller_self = self.b.iadd_imm(self.act, L::ACT_SELF as i64);
                emit_clone_ptr(self.b, self.h.clone_ptr, self_dst, caller_self);
            }
        }
        let zero = self.b.iconst(Ty::I64, 0);
        for off in [
            L::ACT_FRAME,
            L::ACT_BLOCK,
            L::ACT_METHOD_TAG,
            L::ACT_CLOSURE_TAG,
            L::ACT_YIELD_CALLER,
        ] {
            self.b.store(zero, act, off as i32);
        }
        self.b.store(act, act, L::ACT_SP as i32);
        let native = self.b.iconst(Ty::I8, 0);
        self.b.store(native, act, L::ACT_NATIVE as i32);
        // The argument area is this caller's, released after the call:
        // the callee may move the parameters out of it.
        let owned = self.b.iconst(Ty::I8, 1);
        self.b.store(owned, act, L::ACT_ARGS_OWNED as i32);
        let provided_v = self.b.iconst(Ty::I64, provided as i64);
        self.b.store(provided_v, act, L::ACT_PROVIDED as i32);
        self.b.store(self.args_buf, act, L::ACT_ARGS_PTR as i32);
        let nargs_v = self.b.iconst(Ty::I32, slots as i64);
        self.b.store(nargs_v, act, L::ACT_NARGS as i32);
        // Push it on the call stack.
        let len = self.b.load(Ty::I64, self.rt, L::HOT_STACK_LEN as i32);
        let cap = self.b.load(Ty::I64, self.rt, L::HOT_STACK_CAP as i32);
        let full = self.b.icmp(IntCC::Equal, len, cap);
        let push_slow = self.b.create_block();
        let push_fast = self.b.create_block();
        let pushed = self.b.create_block();
        self.b.brif(full, push_slow, &[], push_fast, &[]);
        self.b.switch_to_block(push_slow);
        self.b.call(self.h.push_call, &[self.rt, act]);
        self.b.jump(pushed, &[]);
        self.b.switch_to_block(push_fast);
        let stack = self.b.load(Ty::I64, self.rt, L::HOT_STACK_PTR as i32);
        let slot_off = self.b.ishl_imm(len, 3);
        let slot = self.b.iadd(stack, slot_off);
        self.b.store(act, slot, 0);
        let len1 = self.b.iadd_imm(len, 1);
        self.b.store(len1, self.rt, L::HOT_STACK_LEN as i32);
        self.b.jump(pushed, &[]);
        self.b.switch_to_block(pushed);
        // The body (`out_buf` holds nil).
        let status = self.b.call(body, &[self.rt, act, self.out_buf])[0];
        // Leave: inline when the status is OK and the callee cached no
        // block caller, through the runtime otherwise.
        let cache = self.b.load(Ty::I64, act, L::ACT_YIELD_CALLER as i32);
        let not_ok = self.b.icmp_imm(IntCC::NotEqual, status, 0);
        let cached = self.b.icmp_imm(IntCC::NotEqual, cache, 0);
        let slow = self.b.bor(not_ok, cached);
        let leave_slow = self.b.create_block();
        let leave_fast = self.b.create_block();
        let done = self.b.create_block();
        self.b.append_block_param(done, Ty::I32);
        self.b.brif(slow, leave_slow, &[], leave_fast, &[]);
        self.b.switch_to_block(leave_slow);
        let d = self.i32(dst);
        let none = self.i32(u32::MAX);
        let st = self.b.call(
            self.h.leave,
            &[self.rt, act, status, self.out_buf, self.regs, d, none],
        )[0];
        self.b.jump(done, &[st]);
        self.b.switch_to_block(leave_fast);
        // Pop (the entry is the top one unless tasks interleaved).
        let len = self.b.load(Ty::I64, self.rt, L::HOT_STACK_LEN as i32);
        let stack = self.b.load(Ty::I64, self.rt, L::HOT_STACK_PTR as i32);
        let len0 = self.b.iadd_imm(len, -1);
        let top_off = self.b.ishl_imm(len0, 3);
        let top_slot = self.b.iadd(stack, top_off);
        let top = self.b.load(Ty::Ptr, top_slot, 0);
        let is_top = self.b.icmp(IntCC::Equal, top, act);
        let pop_fast = self.b.create_block();
        let pop_slow = self.b.create_block();
        let popped = self.b.create_block();
        self.b.brif(is_top, pop_fast, &[], pop_slow, &[]);
        self.b.switch_to_block(pop_fast);
        self.b.store(len0, self.rt, L::HOT_STACK_LEN as i32);
        self.b.jump(popped, &[]);
        self.b.switch_to_block(pop_slow);
        self.b.call(self.h.pop_call, &[self.rt, act]);
        self.b.jump(popped, &[]);
        self.b.switch_to_block(popped);
        // Tear down: only `self` can hold a reference.
        self.release_ptr(self_dst);
        // The result moves into `dst`; `out` is nil again.
        self.release(dst);
        for k in [0, 8] {
            let w = self.b.load(Ty::I64, self.out_buf, k);
            self.b.store(w, self.regs, reg_off(dst) + k);
        }
        self.b.store(zero, self.out_buf, 0);
        let ok = self.b.iconst(Ty::I32, 0);
        self.b.jump(done, &[ok]);
        self.b.switch_to_block(done);
        let status = self.b.block_params(done)[0];
        release_args(self);
        self.check(status, unwind);
    }

    /// Run the `deinitialize` of what was released (in a program that
    /// defines one).
    fn finalize(&mut self) {
        if let Some(finalize) = self.h.finalize {
            self.b.call(finalize, &[self.rt]);
        }
    }

    /// Release the value at `p` (leaving nil) when it is reference counted.
    fn release_ptr(&mut self, p: B::Value) {
        emit_release_ptr(self.b, self.h.drop_value, p);
    }

    /// `(elements, len, cap)` of the array in `arr` (whose tag is known
    /// to be an array's): the vector sits after the allocation's two
    /// counts, its words where `layout::vec_layout` found them.
    /// Append register `src` to the array in the value at `arr_ptr` when
    /// that is an unshared array with room whose storage takes the value
    /// (boxed takes anything; unboxed Ints/Floats an Int/Float, known
    /// from the state or the tag), branching to `slow` otherwise. Falls
    /// through on success with the array's length updated.
    /// Returns the array's allocation (unchanged by the append).
    fn inline_push(
        &mut self,
        arr_ptr: B::Value,
        known: Option<B::Value>,
        src: Reg,
        slow: B::Block,
        move_src: bool,
    ) -> B::Value {
        let fast = self.b.create_block();
        let rc = match known {
            // An array (`State::Arr`): its allocation is at hand.
            Some(rc) => rc,
            None => {
                let check_b = self.b.create_block();
                let tag = load_tag(self.b, arr_ptr, 0);
                let is_arr = self.b.icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
                self.b.brif(is_arr, check_b, &[], slow, &[]);
                self.b.switch_to_block(check_b);
                self.b.load(Ty::Ptr, arr_ptr, 8)
            }
        };
        // Unique: a local count of 1 (a shared allocation has 0 there).
        let strong = self.b.load(Ty::I64, rc, 0);
        let (kind, ptr, len, cap) = self.array_view_at(rc);
        let unique = self.b.icmp_imm(IntCC::Equal, strong, 1);
        let room = self.b.icmp(IntCC::UnsignedLessThan, len, cap);
        let ok = self.b.band(unique, room);
        let src_state = self.states[src as usize];
        let src_tag = match src_state {
            State::Int => self.b.iconst(Ty::I64, TAG_INT),
            State::Float => self.b.iconst(Ty::I64, TAG_FLOAT),
            State::Bool => self.b.iconst(Ty::I64, TAG_BOOL),
            _ => self.tag(src),
        };
        let kind_values = self.b.icmp_imm(IntCC::Equal, kind, 0);
        let kind_ints = self.b.icmp_imm(IntCC::Equal, kind, 1);
        let kind_floats = self.b.icmp_imm(IntCC::Equal, kind, 2);
        let kind_objects = self.b.icmp_imm(IntCC::Equal, kind, 3);
        let src_int = self.b.icmp_imm(IntCC::Equal, src_tag, TAG_INT);
        let src_float = self.b.icmp_imm(IntCC::Equal, src_tag, TAG_FLOAT);
        let src_obj = self.b.icmp_imm(IntCC::Equal, src_tag, TAG_OBJECT);
        let ints_ok = self.b.band(kind_ints, src_int);
        let floats_ok = self.b.band(kind_floats, src_float);
        let objects_ok = self.b.band(kind_objects, src_obj);
        // An object first in an empty boxed array goes to the runtime,
        // which makes the storage references.
        let empty = self.b.icmp_imm(IntCC::Equal, len, 0);
        let first_obj = self.b.band(empty, src_obj);
        let one = self.b.iconst(Ty::I8, 1);
        let not_first_obj = self.b.bxor(first_obj, one);
        let values_ok = self.b.band(kind_values, not_first_obj);
        let fits = self.b.bor(values_ok, ints_ok);
        let fits = self.b.bor(fits, floats_ok);
        let fits = self.b.bor(fits, objects_ok);
        let ok = self.b.band(ok, fits);
        self.b.brif(ok, fast, &[], slow, &[]);
        self.b.switch_to_block(fast);
        let boxed_b = self.b.create_block();
        let unboxed_b = self.b.create_block();
        let objects_b = self.b.create_block();
        let raw_b = self.b.create_block();
        let done_b = self.b.create_block();
        self.b.brif(kind_values, boxed_b, &[], unboxed_b, &[]);
        self.b.switch_to_block(unboxed_b);
        self.b.brif(kind_objects, objects_b, &[], raw_b, &[]);
        // An object's reference: moved out of the register, or counted.
        // (Never taken for a number in a variable: `objects_ok` is false.)
        self.b.switch_to_block(objects_b);
        if matches!(src_state, State::Int | State::Float | State::Bool) {
            self.b.jump(slow, &[]);
        } else {
            let off = self.b.imul_imm(len, 8);
            let slot = self.b.iadd(ptr, off);
            let p = if src_state == State::Obj {
                self.b.use_var(self.pvar(src))
            } else {
                self.payload_ptr(src)
            };
            self.b.store(p, slot, 0);
            if move_src {
                self.store_tag(src, TAG_NIL);
            } else {
                let home = self.b.iadd_imm(self.regs, i64::from(reg_off(src)));
                emit_retain(self.b, self.h.own, home, p);
            }
            self.b.jump(done_b, &[]);
        }
        self.b.switch_to_block(boxed_b);
        let off = self.b.imul_imm(len, i64::from(VALUE_SIZE));
        let slot = self.b.iadd(ptr, off);
        if move_src {
            self.move_reg_to_ptr(slot, src);
        } else {
            self.clone_reg_to_ptr(slot, src);
        }
        self.b.jump(done_b, &[]);
        self.b.switch_to_block(raw_b);
        let off = self.b.imul_imm(len, 8);
        let slot = self.b.iadd(ptr, off);
        let word = match src_state {
            State::Int => self.b.use_var(self.ivar(src)),
            State::Float => {
                let f = self.b.use_var(self.fvar(src));
                self.b.bitcast(Ty::I64, f)
            }
            _ => self.payload(src),
        };
        self.b.store(word, slot, 0);
        self.b.jump(done_b, &[]);
        self.b.switch_to_block(done_b);
        let len1 = self.b.iadd_imm(len, 1);
        let data = self.b.iadd_imm(rc, i64::from(OBJECT_FIELDS_PTR_OFF));
        let vec = self.b.iadd_imm(data, L::ARRAY_VEC_OFF as i64);
        self.b.store(len1, vec, L::vec_layout().len as i32);
        rc
    }

    fn array_view(&mut self, arr: Reg) -> (B::Value, B::Value, B::Value, B::Value) {
        let rc = if self.states[arr as usize] == State::Arr {
            self.b.use_var(self.pvar(arr))
        } else {
            self.payload_ptr(arr)
        };
        self.array_view_at(rc)
    }

    /// `arr`, whose tag has just been tested, holds an array: keep its
    /// allocation in its variable (`State::Arr`, set by `after`).
    fn note_arr(&mut self, arr: Reg) {
        if self.states[arr as usize] != State::Arr {
            let p = self.payload_ptr(arr);
            self.b.def_var(self.pvar(arr), p);
        }
    }

    /// After the runtime ran an instruction on `arr`: keep its allocation
    /// (`after` makes it `State::Arr`); lowering emits the instruction on
    /// arrays only.
    fn arr_after_slow(&mut self, arr: Reg, block: u32, index: u32) {
        let tag = self.tag(arr);
        let is_arr = self.b.icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
        let ok = self.b.create_block();
        let bad = self.b.create_block();
        self.b.brif(is_arr, ok, &[], bad, &[]);
        self.b.switch_to_block(bad);
        self.unsound(block, index);
        self.b.switch_to_block(ok);
        let p = self.payload_ptr(arr);
        self.b.def_var(self.pvar(arr), p);
    }

    /// The storage kind, element pointer, length and capacity of the
    /// array whose allocation `rc` points at.
    fn array_view_at(&mut self, rc: B::Value) -> (B::Value, B::Value, B::Value, B::Value) {
        let data = self.b.iadd_imm(rc, i64::from(OBJECT_FIELDS_PTR_OFF));
        let kind = self.b.uload8(data, L::ARRAY_KIND_OFF as i32);
        let vec = self.b.iadd_imm(data, L::ARRAY_VEC_OFF as i64);
        let l = L::vec_layout();
        let ptr = self.b.load(Ty::Ptr, vec, l.ptr as i32);
        let len = self.b.load(Ty::I64, vec, l.len as i32);
        let cap = self.b.load(Ty::I64, vec, l.cap as i32);
        (kind, ptr, len, cap)
    }

    /// The address of field `index` of the `class` object in `obj` (whose
    /// tag is known to be an object's): the fields follow the object's
    /// header in its allocation, as the class lays them out.
    fn field_addr(&mut self, obj: Reg, class: ClassId, index: u32) -> B::Value {
        let (_, off) = unbox::field_slot(self.classes, class, index);
        let rc = self.obj_ptr(obj);
        self.b
            .iadd_imm(rc, L::OBJECT_FIELDS_OFF as i64 + i64::from(off))
    }

    /// Store `src` into the word field (of kind `kind`) at `field`, or go
    /// to `slow` when the word cannot hold it (a big integer, `i64::MIN`,
    /// a value of another type).
    fn store_word_field(&mut self, field: B::Value, kind: FieldKind, src: Reg, slow: B::Block) {
        let state = self.states[src as usize];
        let word = match (kind, state) {
            (FieldKind::Float, State::Float) => {
                let v = self.b.use_var(self.fvar(src));
                self.b.bitcast(Ty::I64, v)
            }
            (FieldKind::Bool, State::Bool) => {
                let v = self.b.use_var(self.bvar(src));
                self.b.uextend(Ty::I64, v)
            }
            (FieldKind::Int, State::Int) => {
                let v = self.b.use_var(self.ivar(src));
                let aside = self.b.icmp_imm(IntCC::Equal, v, L::FIELD_INT_MARK);
                let ok = self.b.create_block();
                self.b.brif(aside, slow, &[], ok, &[]);
                self.b.switch_to_block(ok);
                v
            }
            _ if state.boxed() => {
                // A boxed value of the field's type: its payload word (an
                // Int's but the mark).
                let (want, mark) = match kind {
                    FieldKind::Int => (TAG_INT, Some(L::FIELD_INT_MARK)),
                    FieldKind::Float => (TAG_FLOAT, Some(L::FIELD_FLOAT_MARK as i64)),
                    _ => (TAG_BOOL, None),
                };
                let tag = self.tag(src);
                let is = self.b.icmp_imm(IntCC::Equal, tag, want);
                let check = self.b.create_block();
                self.b.brif(is, check, &[], slow, &[]);
                self.b.switch_to_block(check);
                let w = if kind == FieldKind::Bool {
                    let b = self.bool_payload(src);
                    self.b.uextend(Ty::I64, b)
                } else {
                    self.payload(src)
                };
                if let Some(m) = mark {
                    let aside = self.b.icmp_imm(IntCC::Equal, w, m);
                    let ok = self.b.create_block();
                    self.b.brif(aside, slow, &[], ok, &[]);
                    self.b.switch_to_block(ok);
                }
                w
            }
            // An unboxed value of another type: the runtime decides.
            _ => {
                self.b.jump(slow, &[]);
                let dead = self.b.create_block();
                self.b.switch_to_block(dead);
                self.b.iconst(Ty::I64, 0)
            }
        };
        self.b.store(word, field, 0);
    }

    /// The address of field `index` of the object in `obj`, whatever its
    /// class, from the offsets its layout keeps (the object's first word
    /// points at the layout).
    fn field_addr_of(&mut self, obj: Reg, index: u32) -> B::Value {
        let rc = self.obj_ptr(obj);
        let layout = self.b.load(Ty::Ptr, rc, OBJECT_FIELDS_PTR_OFF);
        let offsets = self.b.load(Ty::Ptr, layout, L::FIELD_LAYOUT_OFFSETS as i32);
        let off = self.b.uload32(offsets, index as i32 * 4);
        let fields = self.b.iadd_imm(rc, L::OBJECT_FIELDS_OFF as i64);
        self.b.iadd(fields, off)
    }

    /// The address of `slot` in the frame `depth` levels up from this
    /// activation's frame, branching to `slow` when there is no such
    /// frame or the slot is beyond its size (layout: `Frame`).
    fn frame_slot_addr(&mut self, depth: u32, slot: u32, slow: B::Block) -> B::Value {
        let mut frame = self.b.load(Ty::Ptr, self.ptrs, 24);
        for level in 0..=depth {
            let none = self.b.icmp_imm(IntCC::Equal, frame, 0);
            let next = self.b.create_block();
            self.b.brif(none, slow, &[], next, &[]);
            self.b.switch_to_block(next);
            if level < depth {
                frame = self.b.load(Ty::Ptr, frame, 16);
            }
        }
        let nslots = self.b.uload32(frame, 8);
        let in_range = self
            .b
            .icmp_imm(IntCC::UnsignedGreaterThan, nslots, i64::from(slot));
        let ok = self.b.create_block();
        self.b.brif(in_range, ok, &[], slow, &[]);
        self.b.switch_to_block(ok);
        let slots = self.b.load(Ty::Ptr, frame, 0);
        self.b
            .iadd_imm(slots, i64::from(slot) * i64::from(VALUE_SIZE))
    }

    fn ivar(&self, r: Reg) -> B::Var {
        self.ivars[r as usize]
    }

    fn fvar(&self, r: Reg) -> B::Var {
        self.fvars[r as usize]
    }

    fn bvar(&self, r: Reg) -> B::Var {
        self.bvars[r as usize]
    }

    fn pvar(&self, r: Reg) -> B::Var {
        self.pvars[r as usize]
    }

    /// The allocation of the object in `r` (whose tag is an object's).
    fn obj_ptr(&mut self, r: Reg) -> B::Value {
        if self.states[r as usize] == State::Obj {
            self.b.use_var(self.pvar(r))
        } else {
            self.payload_ptr(r)
        }
    }

    /// Go to `yes` when `r` holds an object, to `no` otherwise (no test
    /// when it is known to).
    fn branch_obj(&mut self, r: Reg, yes: B::Block, no: B::Block) {
        if self.states[r as usize] == State::Obj {
            self.b.jump(yes, &[]);
        } else {
            let tag = self.tag(r);
            let is_obj = self.b.icmp_imm(IntCC::Equal, tag, TAG_OBJECT);
            self.b.brif(is_obj, yes, &[], no, &[]);
        }
    }

    /// `r` holds an object now: keep its allocation in its variable (when
    /// it is not there already).
    fn note_obj(&mut self, r: Reg) {
        if self.states[r as usize] != State::Obj {
            let p = self.payload_ptr(r);
            self.b.def_var(self.pvar(r), p);
        }
    }

    /// Update the states after an instruction, and pick up a Bool the
    /// runtime produced into its variable.
    fn after(&mut self, inst: &Inst) {
        unbox::transfer(
            inst,
            &mut self.states,
            self.f,
            self.methods,
            self.classes,
            self.builtin,
            self.typed_all,
        );
        if matches!(
            inst,
            Inst::HasArg { .. }
                | Inst::Equal { .. }
                | Inst::CaseEq { .. }
                | Inst::IsArray { .. }
                | Inst::IsHash { .. }
                | Inst::IsObject { .. }
                | Inst::ClassIsA { .. }
                | Inst::IsA { .. }
        ) {
            for r in unbox::defs(inst) {
                let v = self.bool_payload(r);
                let v = self.b.ireduce(Ty::I8, v);
                self.b.def_var(self.bvar(r), v);
            }
        }
        if let Inst::Len { dst, .. } = inst {
            let v = self.payload(*dst);
            self.b.def_var(self.ivar(*dst), v);
        }
        if let Inst::ArrayWords { dst, .. }
        | Inst::MakeArray { dst, .. }
        | Inst::ArrayNewWords { dst, .. } = inst
        {
            let p = self.payload_ptr(*dst);
            self.b.def_var(self.pvar(*dst), p);
        }
    }

    /// Raise `kind` (`layout::RAISE_*`) at instruction `index` of `block`,
    /// as the instruction would: through the block's handler, if any
    /// (which reads the homes of what is live), or out of the function.
    fn raise_here(&mut self, kind: u32, block: u32, index: u32, unwind: B::Block) {
        let here = self.b.current_block();
        self.b.set_cold(here);
        if self.region[block as usize] {
            self.setup_frame();
        }
        let live = self.live[block as usize][index as usize].clone();
        self.flush_live(&live);
        self.materialize();
        let k = self.b.iconst(Ty::I32, i64::from(kind));
        let fid = self.b.iconst(Ty::I32, i64::from(self.fid));
        let line = self
            .b
            .iconst(Ty::I32, i64::from(self.line_at(block, index)));
        let status = self
            .b
            .call(self.h.raise, &[self.rt, self.act, k, fid, line])[0];
        // The status is never OK: what follows is unreachable, and joins
        // nothing (emission goes on in a fresh block).
        self.b.set_cold(unwind);
        self.b.jump(unwind, &[status]);
        let dead = self.b.create_block();
        self.b.switch_to_block(dead);
    }

    /// The line of instruction `index` of `block` (its terminator's past
    /// the end).
    fn line_at(&self, block: u32, index: u32) -> u32 {
        let blk = &self.f.blocks[block as usize];
        blk.lines
            .get(index as usize)
            .copied()
            .unwrap_or(blk.term_line)
    }

    /// A value not of its static type, which the checker rules out: a
    /// compiler bug, raised as a `TypeError` out of the function (its
    /// handlers are not run: nothing is known to be sound any more).
    fn unsound(&mut self, block: u32, index: u32) {
        let here = self.b.current_block();
        self.b.set_cold(here);
        if self.region[block as usize] {
            self.setup_frame();
        }
        self.materialize();
        let k = self.b.iconst(Ty::I32, i64::from(L::RAISE_UNSOUND));
        let fid = self.b.iconst(Ty::I32, i64::from(self.fid));
        let line = self
            .b
            .iconst(Ty::I32, i64::from(self.line_at(block, index)));
        let status = self
            .b
            .call(self.h.raise, &[self.rt, self.act, k, fid, line])[0];
        self.b.jump(self.exit, &[status]);
        let dead = self.b.create_block();
        self.b.switch_to_block(dead);
    }

    /// Set the frame up on leaving the pure region (see `emit_frame_setup`).
    fn setup_frame(&mut self) {
        if let Some(body) = self.entry_of {
            // An entry: the body does the rest, from the start.
            let args = self.entry_params.clone();
            let r = self.b.call(body, &args);
            self.b.return_(&r);
            let dead = self.b.create_block();
            self.b.switch_to_block(dead);
            return;
        }
        let zeroed = self.zeroed.clone();
        emit_frame_setup(
            self.b,
            &self.h,
            self.rt,
            self.regs,
            self.out_buf,
            self.own_out,
            &zeroed,
        );
    }

    /// The unboxed value of `r`, statically an Int or a Float: from its
    /// variable when the state says so, else from memory after a tag
    /// check (one that fails is a compiler bug: `unsound`).
    fn get_num(&mut self, r: Reg, n: Num, block: u32, index: u32) -> B::Value {
        let st = self.states[r as usize];
        match (n, st) {
            (Num::Int, State::Int) => return self.b.use_var(self.ivar(r)),
            (Num::Float, State::Float) => return self.b.use_var(self.fvar(r)),
            _ => {}
        }
        let tag = self.tag(r);
        let want = if n == Num::Int { TAG_INT } else { TAG_FLOAT };
        let is = self.b.icmp_imm(IntCC::Equal, tag, want);
        let ok = self.b.create_block();
        let bad = self.b.create_block();
        self.b.brif(is, ok, &[], bad, &[]);
        self.b.switch_to_block(bad);
        self.unsound(block, index);
        self.b.switch_to_block(ok);
        let p = self.payload(r);
        match n {
            Num::Int => {
                self.b.def_var(self.ivar(r), p);
                self.states[r as usize] = State::Int;
                p
            }
            Num::Float => {
                let v = self.b.bitcast(Ty::F64, p);
                self.b.def_var(self.fvar(r), v);
                self.states[r as usize] = State::Float;
                v
            }
        }
    }

    /// After a call through `call_static`, which copies its operands: in
    /// a program with a `deinitialize`, the ones it read for the last
    /// time (`moved`) are released now, as the call would have when they
    /// moved into it, and what that frees finalized (an object whose last
    /// method call this was goes at the end of it, not at a later clear).
    fn drop_copied_moves(&mut self, inst: &Inst, dst: Reg) {
        let Inst::Call {
            recv, args, moved, ..
        } = inst
        else {
            return;
        };
        if self.h.finalize.is_none() || *moved == 0 {
            return;
        }
        let mut regs: Vec<Reg> = args
            .iter()
            .take(15)
            .enumerate()
            .filter(|(i, _)| moved & (1 << i) != 0)
            .map(|(_, r)| *r)
            .collect();
        if let Some(r) = recv.filter(|_| moved & (1 << 15) != 0) {
            regs.push(r);
        }
        let mut dropped = false;
        for r in regs {
            if r != dst && self.states[r as usize].needs_release() && !self.borrowed[r as usize] {
                self.drop_moved(r);
                self.states[r as usize] = State::NonHeap;
                dropped = true;
            }
        }
        if dropped {
            self.finalize();
        }
    }

    /// After a typed call: a boxed argument the call reads for the last
    /// time, lent rather than moved, is released now (and what that frees
    /// finalized, as when the callee releases what it took).
    fn drop_lent(&mut self, inst: &Inst, args: &[Reg], sig: &unbox::TypedSig) {
        let Inst::Call { moved, .. } = inst else {
            return;
        };
        let mut dropped = false;
        for (i, (r, n)) in args.iter().zip(&sig.params).enumerate() {
            if *n == unbox::Mach::Boxed && i < 15 && moved & (1 << i) != 0 {
                self.drop_moved(*r);
                self.states[*r as usize] = State::NonHeap;
                dropped = true;
            }
        }
        if dropped {
            self.finalize();
        }
    }

    /// The result of a typed call in `r`'s home, put in its variable as
    /// `get_num` does (a Bool after a tag check, nil as it is).
    fn get_mach(&mut self, r: Reg, m: unbox::Mach, block: u32, index: u32) {
        match m {
            unbox::Mach::Int => {
                self.get_num(r, Num::Int, block, index);
            }
            unbox::Mach::Float => {
                self.get_num(r, Num::Float, block, index);
            }
            unbox::Mach::Bool => {
                let tag = self.tag(r);
                let is = self.b.icmp_imm(IntCC::Equal, tag, TAG_BOOL);
                let ok = self.b.create_block();
                let bad = self.b.create_block();
                self.b.brif(is, ok, &[], bad, &[]);
                self.b.switch_to_block(bad);
                self.unsound(block, index);
                self.b.switch_to_block(ok);
                let v = self.b.load(Ty::I8, self.regs, reg_off(r) + BOOL_OFF);
                self.b.def_var(self.bvar(r), v);
                self.states[r as usize] = State::Bool;
            }
            // (A method declared to return Nil returns nil.)
            unbox::Mach::Nil => self.states[r as usize] = State::NonHeap,
            unbox::Mach::Boxed => {}
        }
    }

    /// `regs[dst] = Int(v)`: the variable, and the boxed home.
    /// `regs[dst] = Int(v)`, in the variable only: the home is written
    /// when something reads it (`flush`). A home that may hold a heap
    /// value is released and set to nil, so it never dangles.
    fn store_int(&mut self, dst: Reg, v: B::Value) {
        self.b.def_var(self.ivar(dst), v);
        self.unbox(dst, State::Int);
    }

    fn store_float(&mut self, dst: Reg, v: B::Value) {
        self.b.def_var(self.fvar(dst), v);
        self.unbox(dst, State::Float);
    }

    fn unbox(&mut self, dst: Reg, state: State) {
        if self.states[dst as usize].needs_release() {
            self.release(dst);
            self.store_tag(dst, TAG_NIL);
        }
        self.states[dst as usize] = state;
    }

    /// Write an unboxed register's value to its home in memory.
    fn flush(&mut self, r: Reg) {
        match self.states[r as usize] {
            State::Int => {
                let v = self.b.use_var(self.ivar(r));
                self.store_tag(r, TAG_INT);
                self.store_payload(r, v);
            }
            State::Float => {
                let v = self.b.use_var(self.fvar(r));
                let bits = self.b.bitcast(Ty::I64, v);
                self.store_tag(r, TAG_FLOAT);
                self.store_payload(r, bits);
            }
            State::Bool => {
                let v = self.b.use_var(self.bvar(r));
                self.store_tag(r, TAG_BOOL);
                // An I8, stored after the tag.
                self.b.store(v, self.regs, reg_off(r) + BOOL_OFF);
            }
            State::Unknown | State::NonHeap | State::Obj | State::Arr => {}
        }
    }

    /// Write back every unboxed register that is live (and the nil of a
    /// cleared one whose home was never written).
    fn flush_live(&mut self, live: &[bool]) {
        for r in (0..self.nregs).filter(|&r| live[r]) {
            self.flush(r as Reg);
            self.ensure_home(r as Reg);
        }
    }

    /// Before an edge: write back the live unboxed registers whose state
    /// at the target differs (the target reads the home).
    fn flush_for_edge(&mut self, target: &[State], live: &[bool]) {
        for r in 0..self.nregs {
            if live[r] && target[r] != self.states[r] {
                self.flush(r as Reg);
            }
        }
    }

    fn i32(&mut self, v: u32) -> B::Value {
        self.b.iconst(Ty::I32, i64::from(v))
    }

    /// Branch to `unwind` when a status is not OK.
    fn check(&mut self, status: B::Value, unwind: B::Block) {
        let cont = self.b.create_block();
        // A status is an exception or a flow leaving the function: rare.
        self.b.set_cold(unwind);
        self.b.brif(status, unwind, &[status], cont, &[]);
        self.b.switch_to_block(cont);
    }

    /// Whether a call can go straight to the method (a native, or a body
    /// with positional parameters) without dynamic dispatch.
    /// The registers satisfying `pick`, as words of 64 bits.
    fn masks(&self, pick: impl Fn(&Self, usize) -> bool) -> Vec<i64> {
        let mut words = vec![0u64; self.nregs.div_ceil(64)];
        for k in (0..self.nregs).filter(|&k| pick(self, k)) {
            words[k / 64] |= 1 << (k % 64);
        }
        words.into_iter().map(|w| w as i64).collect()
    }

    /// Before an instruction (or a terminator) that may leave the
    /// function through `exit`: which homes the exit must release, from
    /// the states here (a register in an unknown state holds a value in
    /// its home; the others hold nothing to release, or were never
    /// written).
    fn set_valid(&mut self) {
        let words = self.masks(|g, k| g.heap[k] && g.states[k].boxed() && !g.borrowed[k]);
        for (k, word) in words.into_iter().enumerate() {
            let v = self.b.iconst(Ty::I64, word);
            self.b.def_var(self.valid_vars[k], v);
        }
    }

    /// The callee may raise: a backtrace shows this activation at the
    /// call's line. (A typed entry whose frame the native unwinder
    /// reports gets its line from there.)
    fn set_call_line(&mut self, block: u32, index: u32) {
        if self.lazy_act && self.typed.is_some() {
            return;
        }
        let line = self.f.blocks[block as usize].lines[index as usize];
        let line_v = self.b.iconst(Ty::I32, i64::from(line));
        self.b.store(line_v, self.act, L::ACT_LINE as i32);
    }

    /// The typed entry a call goes through, when it does (the conditions
    /// of the `Inst::Call` arm of `inst`).
    fn typed_callee(&self, inst: &Inst) -> Option<FuncId> {
        let call = self.static_target(inst)?;
        let m = &self.methods[call.mid as usize];
        if m.overridden && !m.is_extension && m.native_key.is_none() {
            return None;
        }
        let callee = direct_target(inst, self.methods)?;
        let sig = self.typed_all.get(callee as usize)?.as_ref()?;
        (call.block.is_none()
            && call.args.len() == sig.params.len()
            && self.callees_typed.contains_key(&callee))
        .then_some(callee)
    }

    fn static_target(&self, inst: &Inst) -> Option<StaticCall> {
        let Inst::Call {
            dst,
            kind: CallKind::Method(mid),
            recv,
            args,
            splat: false,
            kw,
            kw_splat: None,
            block,
            ..
        } = inst
        else {
            return None;
        };
        if !kw.is_empty() {
            return None;
        }
        let m = self.methods.get(*mid as usize)?;
        // A method some class overrides (an abstract one always is) is
        // resolved on the receiver by `qz_call_static` itself; the
        // declared signature says what the call passes.
        let virtual_ = m.overridden && !m.singleton && !m.is_extension;
        let fixed = m.synth == RtSynth::None
            && (!m.is_abstract || virtual_)
            && (m.native_key.is_some()
                || ((m.func.is_some() || virtual_)
                    && m.params.iter().all(|p| p.kind == RtParamKind::Positional)
                    && args.len() <= m.params.len()
                    && (block.is_none() || m.has_block)));
        if !fixed {
            return None;
        }
        Some(StaticCall {
            mid: *mid,
            recv: *recv,
            args: args.clone(),
            block: *block,
            dst: *dst,
        })
    }

    /// A call to a method some class overrides: the parameters are laid
    /// out as for a direct call, `qz_enter_virtual` resolves the method
    /// on the receiver and builds the activation (or runs the call
    /// itself when the target's shape differs), and the body is called
    /// through the address it returns.
    #[allow(clippy::too_many_arguments)]
    fn virtual_call(
        &mut self,
        inst: &Inst,
        mid: MethodId,
        recv: Option<Reg>,
        args: &[Reg],
        blk: Option<Reg>,
        dst: Reg,
        block: u32,
        index: u32,
        unwind: B::Block,
    ) {
        if recv.is_none() {
            self.materialize();
        }
        let (nparams, has_block) = {
            let m = &self.methods[mid as usize];
            (m.params.len(), m.has_block)
        };
        let mut provided: u64 = 0;
        let mut slots = 0usize;
        for (k, r) in args.iter().enumerate() {
            let p = self
                .b
                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
            if self.movable(inst, *r, block, index) {
                self.move_reg_to_ptr(p, *r);
                self.states[*r as usize] = State::NonHeap;
            } else {
                self.clone_reg_to_ptr(p, *r);
            }
            if k < 64 {
                provided |= 1 << k;
            }
            slots += 1;
        }
        while slots < nparams {
            let p = self
                .b
                .iadd_imm(self.args_buf, (slots as i64) * i64::from(VALUE_SIZE));
            let zero = self.b.iconst(Ty::I64, 0);
            self.b.store(zero, p, 0);
            slots += 1;
        }
        if has_block {
            let p = self
                .b
                .iadd_imm(self.args_buf, (slots as i64) * i64::from(VALUE_SIZE));
            match blk {
                Some(r) => {
                    self.clone_reg_to_ptr(p, r);
                    if nparams < 64 {
                        provided |= 1 << nparams;
                    }
                }
                None => {
                    let zero = self.b.iconst(Ty::I64, 0);
                    self.b.store(zero, p, 0);
                }
            }
            slots += 1;
        }
        let mid_v = self.i32(mid);
        let recv_v = self.i32(recv.unwrap_or(u32::MAX));
        let nparams_v = self.i32(nparams as u32);
        let blk_v = self.i32(blk.unwrap_or(u32::MAX));
        let provided_v = self.b.iconst(Ty::I64, provided as i64);
        let d = self.i32(dst);
        let status = self.b.call(
            self.h.enter_virtual,
            &[
                self.rt,
                self.act,
                self.act_buf,
                mid_v,
                self.regs,
                recv_v,
                self.args_buf,
                nparams_v,
                blk_v,
                provided_v,
                self.vbody,
                d,
            ],
        )[0];
        let entered = self.b.create_block();
        let not_entered = self.b.create_block();
        let done = self.b.create_block();
        let failed = self.b.create_block();
        let cont = self.b.create_block();
        let is_ok = self.b.icmp_imm(IntCC::Equal, status, 0);
        self.b.brif(is_ok, entered, &[], not_entered, &[]);
        self.b.switch_to_block(not_entered);
        let is_done = self.b.icmp_imm(IntCC::Equal, status, STATUS_DONE);
        self.b.brif(is_done, done, &[], failed, &[]);
        // On failure nothing was built: release the area.
        self.b.switch_to_block(failed);
        for k in 0..slots {
            let p = self
                .b
                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
            self.release_ptr(p);
        }
        self.b.jump(unwind, &[status]);
        // The runtime ran the call and emptied the area.
        self.b.switch_to_block(done);
        self.b.jump(cont, &[]);
        // Call the body, finish, release the parameters.
        self.b.switch_to_block(entered);
        let body = self.b.load(Ty::Ptr, self.vbody, 0);
        let call =
            self.b
                .call_indirect(self.body_sig, body, &[self.rt, self.act_buf, self.out_buf]);
        let status = call[0];
        let status = self.b.call(
            self.h.leave,
            &[
                self.rt,
                self.act_buf,
                status,
                self.out_buf,
                self.regs,
                d,
                blk_v,
            ],
        )[0];
        for k in 0..slots {
            let p = self
                .b
                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
            self.release_ptr(p);
        }
        self.check(status, unwind);
        self.b.jump(cont, &[]);
        self.b.switch_to_block(cont);
    }

    /// A direct call to the compiled body `callee`: the parameters laid
    /// out in the argument area, the activation built inline (a lean
    /// callee) or by the runtime, the body called, the result in `dst`.
    #[allow(clippy::too_many_arguments)]
    fn direct_call(
        &mut self,
        inst: &Inst,
        mid: MethodId,
        callee: FuncId,
        recv: Option<Reg>,
        args: &[Reg],
        blk: Option<Reg>,
        dst: Reg,
        block: u32,
        index: u32,
        unwind: B::Block,
        allow_move: bool,
    ) {
        if recv.is_none() {
            self.materialize();
        }
        let mid_v = self.i32(mid);
        let recv_v = self.i32(recv.unwrap_or(u32::MAX));
        let blk_v = self.i32(blk.unwrap_or(u32::MAX));
        let d = self.i32(dst);
        // Build the activation, call the body, finish.
        let (frame_size, file) = {
            let target = &self.functions[callee as usize];
            (target.frame_size, target.file)
        };
        let body = self.callees[&callee];
        let callee_v = self.i32(callee);
        let frame_v = self.i32(frame_size);
        let file_v = self.i32(file);
        let (nparams, has_block) = {
            let m = &self.methods[mid as usize];
            (m.params.len(), m.has_block)
        };
        // Lay the parameters out in the argument area:
        // the arguments, nil for missing ones, the block.
        let mut provided: u64 = 0;
        let mut slots = 0usize;
        for (k, r) in args.iter().enumerate() {
            let p = self
                .b
                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
            // The area is released after the call: a
            // dead argument is moved there.
            if allow_move && self.movable(inst, *r, block, index) {
                self.move_reg_to_ptr(p, *r);
                self.states[*r as usize] = State::NonHeap;
            } else {
                self.clone_reg_to_ptr(p, *r);
            }
            if k < 64 {
                provided |= 1 << k;
            }
            slots += 1;
        }
        while slots < nparams {
            let p = self
                .b
                .iadd_imm(self.args_buf, (slots as i64) * i64::from(VALUE_SIZE));
            let zero = self.b.iconst(Ty::I64, 0);
            self.b.store(zero, p, 0);
            slots += 1;
        }
        if has_block {
            let p = self
                .b
                .iadd_imm(self.args_buf, (slots as i64) * i64::from(VALUE_SIZE));
            match blk {
                Some(r) => {
                    self.clone_reg_to_ptr(p, r);
                    if nparams < 64 {
                        provided |= 1 << nparams;
                    }
                }
                None => {
                    let zero = self.b.iconst(Ty::I64, 0);
                    self.b.store(zero, p, 0);
                }
            }
            slots += 1;
        }
        let lean = frame_size == 0
            && blk.is_none()
            && !self.functions[callee as usize]
                .blocks
                .iter()
                .any(|b| b.insts.iter().any(|i| matches!(i, Inst::MakeBlock { .. })));
        if lean {
            self.lean_call(body, callee, file, recv, provided, slots, dst, unwind);
            return;
        }
        let total_v = self.i32(slots as u32);
        let provided_v = self.b.iconst(Ty::I64, provided as i64);
        let status = self.b.call(
            self.h.enter,
            &[
                self.rt,
                self.act,
                self.act_buf,
                mid_v,
                callee_v,
                self.regs,
                recv_v,
                self.args_buf,
                total_v,
                blk_v,
                frame_v,
                file_v,
                provided_v,
            ],
        )[0];
        // On failure nothing was built: release the area.
        let failed = self.b.create_block();
        let ok_blk = self.b.create_block();
        self.b.brif(status, failed, &[], ok_blk, &[]);
        self.b.switch_to_block(failed);
        for k in 0..slots {
            let p = self
                .b
                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
            self.release_ptr(p);
        }
        self.b.jump(unwind, &[status]);
        self.b.switch_to_block(ok_blk);
        let call = self.b.call(body, &[self.rt, self.act_buf, self.out_buf]);
        let status = call[0];
        let status = self.b.call(
            self.h.leave,
            &[
                self.rt,
                self.act_buf,
                status,
                self.out_buf,
                self.regs,
                d,
                blk_v,
            ],
        )[0];
        // The callee is gone: release its parameters.
        for k in 0..slots {
            let p = self
                .b
                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
            self.release_ptr(p);
        }
        self.check(status, unwind);
    }

    /// A direct call through the callee's typed entry: the arguments as
    /// machine values (checked when their state does not say), the
    /// result straight into `dst`'s variable; the boxed protocol when an
    /// argument is not of its declared type, and a check of a result
    /// that comes back boxed (`STATUS_BOXED`).
    #[allow(clippy::too_many_arguments)]
    fn typed_call(
        &mut self,
        inst: &Inst,
        mid: MethodId,
        callee: FuncId,
        sig: &unbox::TypedSig,
        recv: Option<Reg>,
        args: &[Reg],
        dst: Reg,
        block: u32,
        index: u32,
        unwind: B::Block,
    ) {
        let entry = self.callees_typed[&callee];
        let typed_b = self.b.create_block();
        let fallback_b = self.b.create_block();
        // Rare (an argument of another type than declared): out of the
        // hot path's way.
        self.b.set_cold(fallback_b);
        let cont = self.b.create_block();
        // Every argument of the declared type?
        let mut ok: Option<B::Value> = None;
        for (r, n) in args.iter().zip(&sig.params) {
            let st = self.states[*r as usize];
            let fine = match st {
                // Any value: the callee gets its address.
                _ if *n == unbox::Mach::Boxed => continue,
                _ if n.held(st) => continue,
                State::Int | State::Float | State::Bool => self.b.iconst(Ty::I8, 0),
                _ => {
                    let tag = self.tag(*r);
                    self.b.icmp_imm(IntCC::Equal, tag, mach_tag(*n))
                }
            };
            ok = Some(match ok {
                Some(acc) => self.b.band(acc, fine),
                None => fine,
            });
        }
        match ok {
            Some(c) => self.b.brif(c, typed_b, &[], fallback_b, &[]),
            None => self.b.jump(typed_b, &[]),
        };
        let saved = self.states.clone();
        // The typed path (the receiver is passed by its home's address).
        self.b.switch_to_block(typed_b);
        if let Some(r) = recv {
            self.flush(r);
            self.ensure_home(r);
        }
        let self_ptr = match (recv, self.typed_self_ptr) {
            (Some(r), _) => self.b.iadd_imm(self.regs, i64::from(reg_off(r))),
            // A typed entry passes its own `self` on, without cloning it.
            (None, Some(p)) => p,
            (None, None) => self.b.iadd_imm(self.act, L::ACT_SELF as i64),
        };
        let mut call_args = vec![self.rt, self.act, self_ptr];
        for (r, n) in args.iter().zip(&sig.params) {
            let v = match (self.states[*r as usize], n) {
                (State::Int, unbox::Mach::Int) => self.b.use_var(self.ivar(*r)),
                (State::Float, unbox::Mach::Float) => self.b.use_var(self.fvar(*r)),
                (State::Bool, unbox::Mach::Bool) => self.b.use_var(self.bvar(*r)),
                (_, unbox::Mach::Float) => {
                    let p = self.payload(*r);
                    self.b.bitcast(Ty::F64, p)
                }
                (_, unbox::Mach::Bool) => {
                    self.ensure_home(*r);
                    self.b.load(Ty::I8, self.regs, reg_off(*r) + BOOL_OFF)
                }
                // The value stays the caller's: its address is lent.
                (_, unbox::Mach::Boxed) => {
                    self.flush(*r);
                    self.ensure_home(*r);
                    self.b.iadd_imm(self.regs, i64::from(reg_off(*r)))
                }
                _ => self.payload(*r),
            };
            call_args.push(v);
        }
        let zero = self.b.iconst(Ty::I64, 0);
        call_args.push(self.out_buf);
        self.set_call_line(block, index);
        let bits = self.b.call(entry, &call_args)[0];
        // A status other than 0 (the value came back) is left in the
        // runtime, and taken from there.
        let status = self.b.uload32(self.rt, L::HOT_TYPED_STATUS as i32);
        let status = self.b.ireduce(Ty::I32, status);
        let ok_b = self.b.create_block();
        let not_ok_b = self.b.create_block();
        // An exception or a boxed result: rare, and laid out of the way
        // (between the hot blocks, it moved their alignment with every
        // change to its size).
        self.b.set_cold(not_ok_b);
        let boxed_b = self.b.create_block();
        let is_ok = self.b.icmp_imm(IntCC::Equal, status, 0);
        self.b.brif(is_ok, ok_b, &[], not_ok_b, &[]);
        self.b.switch_to_block(ok_b);
        match sig.ret {
            unbox::Mach::Int => self.store_int(dst, bits),
            unbox::Mach::Float => {
                let v = self.b.bitcast(Ty::F64, bits);
                self.store_float(dst, v);
            }
            unbox::Mach::Bool => {
                let v = self.b.ireduce(Ty::I8, bits);
                self.store_bool(dst, v);
            }
            unbox::Mach::Nil => {
                self.release(dst);
                self.store_tag(dst, TAG_NIL);
                self.states[dst as usize] = State::NonHeap;
            }
            unbox::Mach::Boxed => unreachable!("a typed entry's result is a machine value"),
        }
        self.drop_lent(inst, args, sig);
        self.b.jump(cont, &[]);
        // A boxed result: the value goes to the register's home and is
        // checked there.
        self.b.switch_to_block(not_ok_b);
        let zero32 = self.b.iconst(Ty::I32, 0);
        self.b.store(zero32, self.rt, L::HOT_TYPED_STATUS as i32);
        let is_boxed = self.b.icmp_imm(IntCC::Equal, status, STATUS_BOXED);
        self.b.brif(is_boxed, boxed_b, &[], unwind, &[status]);
        self.b.switch_to_block(boxed_b);
        self.states.clone_from(&saved);
        self.clear_home(dst);
        let home = self.b.iadd_imm(self.regs, i64::from(reg_off(dst)));
        for k in [0, 8] {
            let w = self.b.load(Ty::I64, self.out_buf, k);
            self.b.store(w, home, k);
        }
        self.b.store(zero, self.out_buf, 0);
        self.states[dst as usize] = State::Unknown;
        self.get_mach(dst, sig.ret, block, index + 1);
        self.drop_lent(inst, args, sig);
        self.b.jump(cont, &[]);
        // The boxed protocol (through the runtime: this path is rare and
        // the inline one is long), then the result checked into the
        // variable.
        self.b.switch_to_block(fallback_b);
        self.states.clone_from(&saved);
        // The runtime reads the homes: written back here, not before
        // the call.
        let live = self.live[block as usize][index as usize].clone();
        self.flush_live(&live);
        self.clear_home(dst);
        let _ = (inst, callee);
        self.runtime_call(mid, recv, args, None, dst, unwind);
        self.states[dst as usize] = State::Unknown;
        self.get_mach(dst, sig.ret, block, index + 1);
        self.b.jump(cont, &[]);
        self.b.switch_to_block(cont);
        self.states.clone_from(&saved);
        self.states[dst as usize] = sig.ret.state();
    }

    /// A call through `qz_call_static`: the argument registers' indices
    /// in the scratch area, the runtime does the rest.
    fn runtime_call(
        &mut self,
        mid: MethodId,
        recv: Option<Reg>,
        args: &[Reg],
        blk: Option<Reg>,
        dst: Reg,
        unwind: B::Block,
    ) {
        if recv.is_none() {
            self.materialize();
        }
        for (k, r) in args.iter().enumerate() {
            let v = self.i32(*r);
            self.b.store(v, self.scratch, 4 * k as i32);
        }
        let mid_v = self.i32(mid);
        let recv_v = self.i32(recv.unwrap_or(u32::MAX));
        let nargs = self.i32(args.len() as u32);
        let blk_v = self.i32(blk.unwrap_or(u32::MAX));
        let d = self.i32(dst);
        let status = self.b.call(
            self.h.call_static,
            &[
                self.rt,
                self.act,
                mid_v,
                self.regs,
                recv_v,
                self.scratch,
                nargs,
                blk_v,
                d,
            ],
        )[0];
        self.check(status, unwind);
    }

    /// Leave nil in `r`'s home before the runtime writes it (which drops
    /// what is there): released first when it may hold a value.
    fn clear_home(&mut self, r: Reg) {
        if self.states[r as usize].needs_release() {
            self.release(r);
        }
        self.store_tag(r, TAG_NIL);
    }

    /// In a typed entry, give the activation what the runtime may read
    /// from it: `self` (cloned once; its slot is
    /// nil until then) and the parameters, boxed.
    fn materialize(&mut self) {
        let (Some(self_ptr), Some(params_buf)) = (self.typed_self_ptr, self.typed_params_buf)
        else {
            return;
        };
        let self_dst = self.b.iadd_imm(self.act, L::ACT_SELF as i64);
        let fill = self.b.create_block();
        let done = self.b.create_block();
        if self.lazy_act {
            // Not built yet: build and push it, marked as a frame the
            // native unwinder sees (so backtraces take it from there).
            let pushed = self.b.use_var(self.pushed_var);
            self.b.brif(pushed, done, &[], fill, &[]);
            self.b.switch_to_block(fill);
            let nparams = self.typed_params.len();
            let (rt, act, fid, file, push_call) =
                (self.rt, self.act, self.fid, self.f.file, self.h.push_call);
            let owned = self
                .typed
                .as_ref()
                .is_none_or(|t| !t.params.contains(&unbox::Mach::Boxed));
            emit_typed_activation(
                self.b, rt, act, fid, file, nparams, params_buf, push_call, owned,
            );
            let one = self.b.iconst(Ty::I8, 1);
            self.b.store(one, act, L::ACT_NATIVE as i32);
            self.b.def_var(self.pushed_var, one);
        } else {
            let tag = load_tag(self.b, self_dst, 0);
            let unset = self.b.icmp_imm(IntCC::Equal, tag, TAG_NIL);
            self.b.brif(unset, fill, &[], done, &[]);
            self.b.switch_to_block(fill);
        }
        emit_clone_ptr(self.b, self.h.clone_ptr, self_dst, self_ptr);
        let params: Vec<(B::Value, unbox::Mach)> = self
            .typed_params
            .iter()
            .copied()
            .zip(
                self.typed
                    .as_ref()
                    .map(|t| t.params.clone())
                    .unwrap_or_default(),
            )
            .collect();
        for (k, (v, n)) in params.into_iter().enumerate() {
            let p = self
                .b
                .iadd_imm(params_buf, (k as i64) * i64::from(VALUE_SIZE));
            if n == unbox::Mach::Boxed {
                // The caller's value, not counted: the activation does
                // not own its parameters then (see
                // `emit_typed_activation`).
                for k in [0, 8] {
                    let w = self.b.load(Ty::I64, v, k);
                    self.b.store(w, p, k);
                }
                continue;
            }
            let tag = self.b.iconst(Ty::I64, mach_tag(n));
            self.b.store(tag, p, 0);
            match n {
                unbox::Mach::Float => {
                    let word = self.b.bitcast(Ty::I64, v);
                    self.b.store(word, p, 8);
                }
                unbox::Mach::Bool => self.b.store(v, p, BOOL_OFF),
                _ => self.b.store(v, p, 8),
            }
        }
        self.b.jump(done, &[]);
        self.b.switch_to_block(done);
    }

    /// Register `dst` gets the object element at `elem` of an array of
    /// objects (a reference): counted, or `borrow`ed (the array keeps
    /// it; the register holds no count, see `ArrayGetReg`). Returns the
    /// object's allocation.
    fn load_object_elem(&mut self, dst: Reg, elem: B::Value, borrow: bool) -> B::Value {
        let p = self.b.load(Ty::Ptr, elem, 0);
        if !borrow {
            self.release(dst);
        }
        self.store_tag(dst, TAG_OBJECT);
        self.b.store(p, self.regs, reg_off(dst) + 8);
        if !borrow {
            let home = self.b.iadd_imm(self.regs, i64::from(reg_off(dst)));
            emit_retain(self.b, self.h.own, home, p);
        }
        p
    }

    fn store_tag(&mut self, dst: Reg, tag: i64) {
        let t = self.b.iconst(Ty::I64, tag);
        self.b.store(t, self.regs, reg_off(dst));
        self.stale[dst as usize] = false;
    }

    fn store_payload(&mut self, dst: Reg, v: B::Value) {
        self.b.store(v, self.regs, reg_off(dst) + 8);
    }

    /// Store a boolean (an I8 value) as a `Bool`.
    fn store_bool(&mut self, dst: Reg, v: B::Value) {
        self.b.def_var(self.bvar(dst), v);
        self.unbox(dst, State::Bool);
    }

    /// Store a boolean to the register's home (for a path of a generic
    /// operation, whose result stays boxed).
    fn store_bool_home(&mut self, dst: Reg, v: B::Value) {
        self.release(dst);
        self.store_tag(dst, TAG_BOOL);
        self.b.store(v, self.regs, reg_off(dst) + BOOL_OFF);
    }

    /// Delegate the instruction to the runtime and check its status.
    /// Have the runtime do instruction `index` of `block` (`inst`), through
    /// its entry for the kind (`OPS`), its operands passed as arguments
    /// and data. `dead`: an append to a builder whose result is not read.
    fn exec(&mut self, block: u32, index: u32, unwind: B::Block) {
        let inst = self.f.blocks[block as usize].insts[index as usize].clone();
        self.emit_op(&inst, block, index, false, unwind);
    }

    fn emit_op(&mut self, inst: &Inst, block: u32, index: u32, dead: bool, unwind: B::Block) {
        let w = |g: &mut Self, v: u32| g.b.iconst(Ty::I32, i64::from(v));
        let opt = |r: Option<u32>| r.unwrap_or(u32::MAX);
        let (name, extra): (&str, Vec<B::Value>) = match inst {
            Inst::LoadConst { dst, idx } => {
                ("qz_op_load_const", vec![w(self, *dst), w(self, *idx)])
            }
            Inst::HasArg { dst, index } => ("qz_op_has_arg", vec![w(self, *dst), w(self, *index)]),
            Inst::FieldGetByName {
                dst,
                found,
                obj,
                name,
            } => (
                "qz_op_field_get_by_name",
                vec![
                    w(self, *dst),
                    w(self, *found),
                    w(self, *obj),
                    w(self, *name),
                ],
            ),
            Inst::ConstGet { dst, id } => ("qz_op_const_get", vec![w(self, *dst), w(self, *id)]),
            Inst::UnitSelf { dst, file, class } => (
                "qz_op_unit_self",
                vec![w(self, *dst), w(self, *file), w(self, *class)],
            ),
            Inst::VariantSingleton { dst, class } => (
                "qz_op_variant_singleton",
                vec![w(self, *dst), w(self, *class)],
            ),
            Inst::Call {
                dst,
                kind,
                recv,
                args,
                splat,
                kw,
                kw_splat,
                block: blk,
                moved,
            } => {
                let (tag, a, b2, name): (u32, u32, u32, &str) = match kind {
                    CallKind::Method(m) => (0, *m, 0, ""),
                    CallKind::Send(n) => (1, 0, 0, n),
                    CallKind::Construct { class, init } => (2, *class, opt(*init), ""),
                    CallKind::ConstructRecv { class, init } => (3, *class, opt(*init), ""),
                    CallKind::ProcCall => (4, 0, 0, ""),
                    CallKind::Yield => (5, 0, 0, ""),
                    CallKind::Super(m) => (6, *m, 0, ""),
                    CallKind::Raise => (7, 0, 0, ""),
                };
                let mut desc = vec![
                    *dst,
                    tag,
                    a,
                    b2,
                    opt(*recv),
                    u32::from(*splat),
                    opt(*kw_splat),
                    opt(*blk),
                    u32::from(*moved),
                    args.len() as u32,
                    kw.len() as u32,
                ];
                desc.extend(args.iter().copied());
                for (k, r) in kw {
                    desc.extend([*k, *r]);
                }
                let d = self.b.data_words(&desc);
                let n = self.b.data_bytes(name.as_bytes());
                let len = w(self, name.len() as u32);
                ("qz_op_call", vec![d, n, len])
            }
            Inst::OwnedCall {
                dst,
                method,
                recv,
                args,
                kw,
                unused,
            } => {
                let (kind, a, b2) = match recv {
                    VarLoc::Reg(r) => (0, *r, 0),
                    VarLoc::Frame { depth, slot } => (1, *depth, *slot),
                    VarLoc::Field { obj, index } => (2, *obj, *index),
                };
                let mut desc = vec![
                    *dst,
                    *method,
                    kind,
                    a,
                    b2,
                    u32::from(*unused),
                    args.len() as u32,
                    kw.len() as u32,
                ];
                desc.extend(args.iter().copied());
                for (k, r) in kw {
                    desc.extend([*k, *r]);
                }
                let d = self.b.data_words(&desc);
                ("qz_op_owned_call", vec![d])
            }
            Inst::BinOp {
                dst,
                op,
                lhs,
                rhs,
                method,
            } => (
                "qz_op_binop",
                vec![
                    w(self, *dst),
                    w(self, op.index()),
                    w(self, *lhs),
                    w(self, *rhs),
                    w(self, opt(*method)),
                ],
            ),
            Inst::CaseEq {
                dst,
                pattern,
                value,
            } => (
                "qz_op_case_eq",
                vec![w(self, *dst), w(self, *pattern), w(self, *value)],
            ),
            Inst::Equal { dst, a, b: b2 } => (
                "qz_op_equal",
                vec![w(self, *dst), w(self, *a), w(self, *b2)],
            ),
            Inst::ClassIsA { dst, src, class } => (
                "qz_op_class_is_a",
                vec![w(self, *dst), w(self, *src), w(self, *class)],
            ),
            Inst::IsA { dst, src, ty } => {
                let mut words = Vec::new();
                quarz_vm::ffi_ops::encode_type(ty, &mut words);
                let t = self.b.data_words(&words);
                let n = w(self, words.len() as u32);
                let cell = self.b.data_cell();
                ("qz_op_is_a", vec![w(self, *dst), w(self, *src), t, n, cell])
            }
            Inst::As {
                dst,
                src,
                ty,
                optional,
                name,
            } => {
                let mut words = Vec::new();
                quarz_vm::ffi_ops::encode_type(ty, &mut words);
                let t = self.b.data_words(&words);
                let n = w(self, words.len() as u32);
                let cell = self.b.data_cell();
                let nm = self.b.data_bytes(name.as_bytes());
                let len = w(self, name.len() as u32);
                let o = w(self, u32::from(*optional));
                (
                    "qz_op_as",
                    vec![w(self, *dst), w(self, *src), t, n, cell, o, nm, len],
                )
            }
            Inst::MakeBlock {
                dst,
                func,
                destructure,
                is_lambda,
            } => (
                "qz_op_make_block",
                vec![
                    w(self, *dst),
                    w(self, *func),
                    w(self, opt(*destructure)),
                    w(self, u32::from(*is_lambda)),
                ],
            ),
            Inst::MethodRef { dst, recv, name } => (
                "qz_op_method_ref",
                vec![w(self, *dst), w(self, *recv), w(self, *name)],
            ),
            Inst::SymbolProc {
                dst,
                name,
                method,
                discard,
            } => (
                "qz_op_symbol_proc",
                vec![
                    w(self, *dst),
                    w(self, *name),
                    w(self, opt(*method)),
                    w(self, u32::from(*discard)),
                ],
            ),
            Inst::MakeArray { dst, items } => {
                let words: Vec<u32> = items
                    .iter()
                    .flat_map(|i| [i.reg, u32::from(i.splat)])
                    .collect();
                let d = self.b.data_words(&words);
                (
                    "qz_op_make_array",
                    vec![w(self, *dst), d, w(self, items.len() as u32)],
                )
            }
            Inst::MakeHash { dst, items } => {
                let words: Vec<u32> = items
                    .iter()
                    .flat_map(|i| match i {
                        HashItem::Pair(k, v) => [0, *k, *v],
                        HashItem::Splat(h) => [1, *h, 0],
                    })
                    .collect();
                let d = self.b.data_words(&words);
                (
                    "qz_op_make_hash",
                    vec![w(self, *dst), d, w(self, items.len() as u32)],
                )
            }
            Inst::MakeRange {
                dst,
                lo,
                hi,
                exclusive,
            } => (
                "qz_op_make_range",
                vec![
                    w(self, *dst),
                    w(self, opt(*lo)),
                    w(self, opt(*hi)),
                    w(self, u32::from(*exclusive)),
                ],
            ),
            Inst::MakeRegexp { dst, source, flags } => {
                let fl = self.b.data_bytes(flags.as_bytes());
                (
                    "qz_op_make_regexp",
                    vec![
                        w(self, *dst),
                        w(self, *source),
                        fl,
                        w(self, flags.len() as u32),
                    ],
                )
            }
            Inst::Interpolate { dst, parts, into } => {
                let words: Vec<u32> = parts
                    .iter()
                    .flat_map(|p| match p {
                        StrPiece::Lit(c) => [0, *c],
                        StrPiece::Val(r) => [1, *r],
                    })
                    .collect();
                let d = self.b.data_words(&words);
                (
                    "qz_op_interpolate",
                    vec![
                        w(self, *dst),
                        d,
                        w(self, parts.len() as u32),
                        w(self, opt(*into)),
                        w(self, u32::from(dead)),
                    ],
                )
            }
            Inst::ToSym { dst, src } => ("qz_op_to_sym", vec![w(self, *dst), w(self, *src)]),
            Inst::IsArray { dst, src } => ("qz_op_is_array", vec![w(self, *dst), w(self, *src)]),
            Inst::IsHash { dst, src } => ("qz_op_is_hash", vec![w(self, *dst), w(self, *src)]),
            Inst::IsObject { dst, src } => ("qz_op_is_object", vec![w(self, *dst), w(self, *src)]),
            Inst::ToArray { dst, src } => ("qz_op_to_array", vec![w(self, *dst), w(self, *src)]),
            Inst::Len { dst, src } => ("qz_op_len", vec![w(self, *dst), w(self, *src)]),
            Inst::ObjectFields { dst, src } => {
                ("qz_op_object_fields", vec![w(self, *dst), w(self, *src)])
            }
            Inst::ArrayGet { dst, arr, index } => (
                "qz_op_array_get",
                vec![w(self, *dst), w(self, *arr), w(self, *index as u32)],
            ),
            Inst::ArrayGetReg {
                dst, arr, index, ..
            } => (
                "qz_op_array_get_reg",
                vec![w(self, *dst), w(self, *arr), w(self, *index)],
            ),
            Inst::ArrayIndex {
                dst, arr, index, ..
            } => (
                "qz_op_array_index",
                vec![w(self, *dst), w(self, *arr), w(self, *index)],
            ),
            Inst::ArrayNewWords {
                dst,
                capacity,
                float,
            } => (
                "qz_op_array_new_words",
                vec![
                    w(self, *dst),
                    w(self, *capacity),
                    w(self, u32::from(*float)),
                ],
            ),
            Inst::ArrayPushWord { arr, src, .. } => {
                ("qz_op_array_push", vec![w(self, *arr), w(self, *src)])
            }
            Inst::ArrayWords { dst, arr, float } => (
                "qz_op_array_words",
                vec![w(self, *dst), w(self, *arr), w(self, u32::from(*float))],
            ),
            Inst::ArraySlice {
                dst,
                arr,
                from,
                drop_last,
            } => (
                "qz_op_array_slice",
                vec![
                    w(self, *dst),
                    w(self, *arr),
                    w(self, *from),
                    w(self, *drop_last),
                ],
            ),
            Inst::ArraySliceReg { dst, arr, from, to } => (
                "qz_op_array_slice_reg",
                vec![w(self, *dst), w(self, *arr), w(self, *from), w(self, *to)],
            ),
            Inst::HashGetSym {
                dst,
                found,
                hash,
                key,
            } => (
                "qz_op_hash_get_sym",
                vec![
                    w(self, *dst),
                    w(self, *found),
                    w(self, *hash),
                    w(self, *key),
                ],
            ),
            Inst::ArrayPush { arr, src } => {
                ("qz_op_array_push", vec![w(self, *arr), w(self, *src)])
            }
            Inst::HashRest { dst, hash, keys } => {
                let d = self.b.data_words(keys);
                (
                    "qz_op_hash_rest",
                    vec![w(self, *dst), w(self, *hash), d, w(self, keys.len() as u32)],
                )
            }
            Inst::CatchException { dst } => ("qz_op_catch_exception", vec![w(self, *dst)]),
            Inst::CatchAny { dst } => ("qz_op_catch_any", vec![w(self, *dst)]),
            Inst::Rescuing { src, enter } => (
                "qz_op_rescuing",
                vec![w(self, *src), w(self, u32::from(*enter))],
            ),
            Inst::MarkUsable { obj } => ("qz_op_mark_usable", vec![w(self, *obj)]),
            Inst::NoMatch { src, is_assert } => (
                "qz_op_no_match",
                vec![w(self, *src), w(self, u32::from(*is_assert))],
            ),
            other => unreachable!("compiled code does {other:?} inline"),
        };
        self.call_op(name, block, index, &extra, unwind);
    }

    /// Call the runtime's entry `name` for instruction `index` of `block`
    /// with the operands `extra`, then go on or unwind.
    fn call_op(
        &mut self,
        name: &str,
        block: u32,
        index: u32,
        extra: &[B::Value],
        unwind: B::Block,
    ) {
        let status = self.op_status(name, block, index, extra);
        self.check(status, unwind);
    }

    /// Call the runtime's entry `name` as `call_op` does, returning the
    /// status.
    fn op_status(&mut self, name: &str, block: u32, index: u32, extra: &[B::Value]) -> B::Value {
        self.materialize();
        let entry = self.h.ops[op_index(name)];
        let fid = self.b.iconst(Ty::I32, i64::from(self.fid));
        let line = self
            .b
            .iconst(Ty::I32, i64::from(self.line_at(block, index)));
        let mut args = vec![self.rt, self.act, fid, line, self.regs];
        args.extend_from_slice(extra);
        self.b.call(entry, &args)[0]
    }

    fn inst(&mut self, block: u32, index: u32, inst: &Inst, unwind: B::Block) {
        // What the instruction defines is written by it (inline, or by
        // the runtime), whatever the home held.
        for d in inst.defs() {
            self.stale[d as usize] = false;
        }
        // Anything that reads register homes (the runtime, mostly) sees
        // the live unboxed registers written back first; the typed
        // arithmetic below works on the variables.
        let typed = (matches!(inst, Inst::BinOp { .. })
            && unbox::bin_types(inst, self.methods, self.builtin).is_some()
            && !unbox::float_mod(inst))
            || unbox::num_eq(inst, &self.states, self.methods, self.builtin).is_some();
        let has_handler = self.f.blocks[block as usize].handler.is_some();
        // A call through a typed entry reads homes only on its fallback
        // paths, which write back there (see `typed_call`).
        let to_f = unbox::int_to_f(inst, self.methods, &self.states);
        // A store into a word field: its slow path writes back the source
        // itself.
        let word_store = matches!(inst, Inst::FieldSet { index, class, .. }
            if unbox::field_slot(self.classes, *class, *index).0 != FieldKind::Value);
        // Array length, element reads and appends read only their own
        // operands' homes, on the runtime path, which writes them back; so
        // does an owned call (its in-place paths read no home).
        let array_op = matches!(
            inst,
            Inst::Len { .. }
                | Inst::ArrayGetReg { .. }
                | Inst::ArrayGetWord { .. }
                | Inst::ArrayIndex { .. }
                | Inst::ArrayPush { .. }
                | Inst::ArrayPushWord { .. }
        ) || matches!(inst, Inst::OwnedCall { kw, .. } if kw.is_empty());
        let lazy =
            typed || to_f.is_some() || word_store || array_op || self.typed_callee(inst).is_some();
        // A handler reads the homes of whatever is live: anything that may
        // reach the runtime writes them back first.
        let unwinds_to_handler =
            has_handler && (unbox::may_unwind(inst) || !unbox::reads_no_home(inst));
        if (!lazy && !unbox::reads_no_home(inst)) || (!typed && unwinds_to_handler) {
            let live = self.live[block as usize][index as usize].clone();
            self.flush_live(&live);
        }
        if let Some((recv, dst)) = to_f {
            let i = self.b.use_var(self.ivar(recv));
            let f = self.b.fcvt_from_sint(i);
            self.store_float(dst, f);
            return;
        }
        match inst {
            Inst::Move { dst, src } | Inst::Take { dst, src } => {
                if dst == src {
                    return;
                }
                match self.states[*src as usize] {
                    State::Int => {
                        let v = self.b.use_var(self.ivar(*src));
                        self.store_int(*dst, v);
                    }
                    State::Float => {
                        let v = self.b.use_var(self.fvar(*src));
                        self.store_float(*dst, v);
                    }
                    State::Bool => {
                        let v = self.b.use_var(self.bvar(*src));
                        self.store_bool(*dst, v);
                    }
                    State::NonHeap => {
                        // A plain copy of both words (a short string's
                        // bytes, a `Bool`'s or a `Class`'s payload are in
                        // the first): nothing to count on either side.
                        self.release(*dst);
                        self.ensure_home(*src);
                        for k in [0, 8] {
                            let w = self.b.load(Ty::I64, self.regs, reg_off(*src) + k);
                            self.b.store(w, self.regs, reg_off(*dst) + k);
                        }
                        self.stale[*dst as usize] = false;
                    }
                    // The last read of a boxed register: its value moves,
                    // nil left behind.
                    st @ (State::Unknown | State::Obj | State::Arr) => {
                        // An object's or array's allocation goes with it.
                        let obj = (st != State::Unknown).then(|| self.b.use_var(self.pvar(*src)));
                        if matches!(inst, Inst::Take { .. }) {
                            // The last read of a boxed register: its value
                            // moves, nil left behind.
                            self.release(*dst);
                            for k in [0, 8] {
                                let w = self.b.load(Ty::I64, self.regs, reg_off(*src) + k);
                                self.b.store(w, self.regs, reg_off(*dst) + k);
                            }
                            // (`unbox` then knows it for nil.)
                            self.store_tag(*src, TAG_NIL);
                            self.stale[*dst as usize] = false;
                        } else {
                            let s = self.b.iadd_imm(self.regs, i64::from(reg_off(*src)));
                            self.clone_from(*dst, s);
                        }
                        if let Some(p) = obj {
                            self.b.def_var(self.pvar(*dst), p);
                        }
                    }
                }
            }
            Inst::LoadConst { dst, idx } => match &self.f.consts[*idx as usize] {
                Constant::Nil => {
                    self.release(*dst);
                    self.store_tag(*dst, TAG_NIL);
                }
                Constant::Bool(v) => {
                    let v = self.b.iconst(Ty::I8, i64::from(*v));
                    self.store_bool(*dst, v);
                }
                Constant::Int(i) => {
                    let v = self.b.iconst(Ty::I64, *i);
                    self.store_int(*dst, v);
                }
                Constant::Float(f) => {
                    let v = self.b.f64const(*f);
                    self.store_float(*dst, v);
                }
                // A short string is the two words of its value.
                Constant::Str(text) if quarz_vm::value::ShortStr::new(text).is_some() => {
                    let v = quarz_vm::value::Value::str(text);
                    // SAFETY: a short string has no heap payload: its
                    // two words are the whole value (and need no drop).
                    let words: [u64; 2] = unsafe {
                        std::ptr::read(&v as *const quarz_vm::value::Value as *const [u64; 2])
                    };
                    std::mem::forget(v);
                    self.release(*dst);
                    for (k, w) in words.iter().enumerate() {
                        let c = self.b.iconst(Ty::I64, *w as i64);
                        self.b.store(c, self.regs, reg_off(*dst) + 8 * k as i32);
                    }
                }
                // A longer string or a symbol: cloned from the function's pool.
                Constant::Str(_) | Constant::Symbol(_) => {
                    let fid = self.i32(self.fid);
                    let i = self.i32(*idx);
                    let d = self.i32(*dst);
                    self.b
                        .call(self.h.load_const, &[self.rt, fid, i, self.regs, d]);
                }
                _ => self.exec(block, index, unwind),
            },
            Inst::BinOp {
                dst, op, lhs, rhs, ..
            } if unbox::num_eq(inst, &self.states, self.methods, self.builtin).is_some() => {
                let eq = *op == FastOp::Eq;
                let r = match unbox::num_eq(inst, &self.states, self.methods, self.builtin) {
                    Some(Num::Int) => {
                        let x = self.b.use_var(self.ivar(*lhs));
                        let y = self.b.use_var(self.ivar(*rhs));
                        self.b
                            .icmp(if eq { IntCC::Equal } else { IntCC::NotEqual }, x, y)
                    }
                    _ => {
                        let x = self.b.use_var(self.fvar(*lhs));
                        let y = self.b.use_var(self.fvar(*rhs));
                        self.b.fcmp(
                            if eq {
                                FloatCC::Equal
                            } else {
                                FloatCC::NotEqual
                            },
                            x,
                            y,
                        )
                    }
                };
                self.store_bool(*dst, r);
            }
            Inst::BinOp {
                dst, op, lhs, rhs, ..
            } if unbox::bin_types(inst, self.methods, self.builtin).is_some()
                && !(unbox::float_mod(inst)
                    && unbox::bin_types(inst, self.methods, self.builtin)
                        .unwrap()
                        .result
                        == Some(Num::Float)) =>
            {
                let t = unbox::bin_types(inst, self.methods, self.builtin).unwrap();
                let x = self.get_num(*lhs, t.lhs, block, index);
                let y = self.get_num(*rhs, t.rhs, block, index);
                match t.result {
                    Some(Num::Int) => {
                        let r = match op {
                            FastOp::Add | FastOp::Sub => {
                                let (r, overflow) = if *op == FastOp::Add {
                                    self.b.sadd_overflow(x, y)
                                } else {
                                    self.b.ssub_overflow(x, y)
                                };
                                let ok = self.b.create_block();
                                let bad = self.b.create_block();
                                self.b.brif(overflow, bad, &[], ok, &[]);
                                self.b.switch_to_block(bad);
                                self.raise_here(L::RAISE_OVERFLOW, block, index, unwind);
                                self.b.switch_to_block(ok);
                                r
                            }
                            FastOp::Mul => {
                                let (r, overflow) = self.b.smul_overflow(x, y);
                                let ok = self.b.create_block();
                                let bad = self.b.create_block();
                                self.b.brif(overflow, bad, &[], ok, &[]);
                                self.b.switch_to_block(bad);
                                self.raise_here(L::RAISE_OVERFLOW, block, index, unwind);
                                self.b.switch_to_block(ok);
                                r
                            }
                            _ => {
                                // Division by zero raises, and so does
                                // MIN / -1 (an overflow); MIN % -1 is 0,
                                // which `x % 1` gives (the machine's
                                // remainder traps there).
                                let y_zero = self.b.icmp_imm(IntCC::Equal, y, 0);
                                let ok = self.b.create_block();
                                let bad = self.b.create_block();
                                self.b.brif(y_zero, bad, &[], ok, &[]);
                                self.b.switch_to_block(bad);
                                self.raise_here(L::RAISE_ZERO_DIVISION, block, index, unwind);
                                self.b.switch_to_block(ok);
                                let y_m1 = self.b.icmp_imm(IntCC::Equal, y, -1);
                                let y = if *op == FastOp::Div {
                                    let x_min = self.b.icmp_imm(IntCC::Equal, x, i64::MIN);
                                    let min_case = self.b.band(x_min, y_m1);
                                    let fine = self.b.create_block();
                                    let over = self.b.create_block();
                                    self.b.brif(min_case, over, &[], fine, &[]);
                                    self.b.switch_to_block(over);
                                    self.raise_here(L::RAISE_OVERFLOW, block, index, unwind);
                                    self.b.switch_to_block(fine);
                                    y
                                } else {
                                    let one = self.b.iconst(Ty::I64, 1);
                                    self.b.select(y_m1, one, y)
                                };
                                // Floor semantics, as in Ruby.
                                let rem = self.b.srem(x, y);
                                let nonzero = self.b.icmp_imm(IntCC::NotEqual, rem, 0);
                                let y_neg = self.b.icmp_imm(IntCC::SignedLessThan, y, 0);
                                if *op == FastOp::Div {
                                    let q = self.b.sdiv(x, y);
                                    let x_neg = self.b.icmp_imm(IntCC::SignedLessThan, x, 0);
                                    let differ = self.b.bxor(x_neg, y_neg);
                                    let adjust = self.b.band(nonzero, differ);
                                    let adjust = self.b.uextend(Ty::I64, adjust);
                                    self.b.isub(q, adjust)
                                } else {
                                    let r_neg = self.b.icmp_imm(IntCC::SignedLessThan, rem, 0);
                                    let differ = self.b.bxor(r_neg, y_neg);
                                    let adjust = self.b.band(nonzero, differ);
                                    let zero = self.b.iconst(Ty::I64, 0);
                                    let add = self.b.select(adjust, y, zero);
                                    self.b.iadd(rem, add)
                                }
                            }
                        };
                        self.store_int(*dst, r);
                    }
                    Some(Num::Float) => {
                        let xf = if t.lhs == Num::Int {
                            self.b.fcvt_from_sint(x)
                        } else {
                            x
                        };
                        let yf = if t.rhs == Num::Int {
                            self.b.fcvt_from_sint(y)
                        } else {
                            y
                        };
                        let r = match op {
                            FastOp::Add => self.b.fadd(xf, yf),
                            FastOp::Sub => self.b.fsub(xf, yf),
                            FastOp::Mul => self.b.fmul(xf, yf),
                            _ => self.b.fdiv(xf, yf),
                        };
                        self.store_float(*dst, r);
                    }
                    None => {
                        let r = if t.lhs == Num::Int && t.rhs == Num::Int {
                            let cc = match op {
                                FastOp::Lt => IntCC::SignedLessThan,
                                FastOp::Le => IntCC::SignedLessThanOrEqual,
                                FastOp::Gt => IntCC::SignedGreaterThan,
                                FastOp::Ge => IntCC::SignedGreaterThanOrEqual,
                                FastOp::Eq => IntCC::Equal,
                                _ => IntCC::NotEqual,
                            };
                            self.b.icmp(cc, x, y)
                        } else {
                            let xf = if t.lhs == Num::Int {
                                self.b.fcvt_from_sint(x)
                            } else {
                                x
                            };
                            let yf = if t.rhs == Num::Int {
                                self.b.fcvt_from_sint(y)
                            } else {
                                y
                            };
                            let cc = match op {
                                FastOp::Lt => FloatCC::LessThan,
                                FastOp::Le => FloatCC::LessThanOrEqual,
                                FastOp::Gt => FloatCC::GreaterThan,
                                FastOp::Ge => FloatCC::GreaterThanOrEqual,
                                FastOp::Eq => FloatCC::Equal,
                                _ => FloatCC::NotEqual,
                            };
                            self.b.fcmp(cc, xf, yf)
                        };
                        self.store_bool(*dst, r);
                    }
                }
            }
            Inst::BinOp {
                dst, op, lhs, rhs, ..
            } if matches!(
                op,
                FastOp::Add
                    | FastOp::Sub
                    | FastOp::Mul
                    | FastOp::Div
                    | FastOp::Mod
                    | FastOp::Lt
                    | FastOp::Le
                    | FastOp::Gt
                    | FastOp::Ge
                    | FastOp::Eq
                    | FastOp::Ne
            ) =>
            {
                let tl = self.tag(*lhs);
                let tr = self.tag(*rhs);
                let a = self.b.icmp_imm(IntCC::Equal, tl, TAG_INT);
                let c = self.b.icmp_imm(IntCC::Equal, tr, TAG_INT);
                let both = self.b.band(a, c);
                let fast_blk = self.b.create_block();
                let not_int = self.b.create_block();
                let slow_blk = self.b.create_block();
                let cont = self.b.create_block();
                self.b.brif(both, fast_blk, &[], not_int, &[]);
                // Both floats: inline floating-point arithmetic.
                self.b.switch_to_block(not_int);
                let fa = self.b.icmp_imm(IntCC::Equal, tl, TAG_FLOAT);
                let fc = self.b.icmp_imm(IntCC::Equal, tr, TAG_FLOAT);
                let both_f = self.b.band(fa, fc);
                let float_blk = self.b.create_block();
                self.b.brif(both_f, float_blk, &[], slow_blk, &[]);
                self.b.switch_to_block(float_blk);
                let xb = self.payload(*lhs);
                let yb = self.payload(*rhs);
                let x = self.b.bitcast(Ty::F64, xb);
                let y = self.b.bitcast(Ty::F64, yb);
                match op {
                    FastOp::Mod => {
                        self.b.jump(slow_blk, &[]);
                        let dead = self.b.create_block();
                        self.b.switch_to_block(dead);
                    }
                    FastOp::Add | FastOp::Sub | FastOp::Mul | FastOp::Div => {
                        let r = match op {
                            FastOp::Add => self.b.fadd(x, y),
                            FastOp::Sub => self.b.fsub(x, y),
                            FastOp::Mul => self.b.fmul(x, y),
                            _ => self.b.fdiv(x, y),
                        };
                        let bits = self.b.bitcast(Ty::I64, r);
                        self.release(*dst);
                        self.store_tag(*dst, TAG_FLOAT);
                        self.store_payload(*dst, bits);
                    }
                    _ => {
                        let cc = match op {
                            FastOp::Lt => FloatCC::LessThan,
                            FastOp::Le => FloatCC::LessThanOrEqual,
                            FastOp::Gt => FloatCC::GreaterThan,
                            FastOp::Ge => FloatCC::GreaterThanOrEqual,
                            FastOp::Eq => FloatCC::Equal,
                            _ => FloatCC::NotEqual,
                        };
                        let r = self.b.fcmp(cc, x, y);
                        self.store_bool_home(*dst, r);
                    }
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(fast_blk);
                let x = self.payload(*lhs);
                let y = self.payload(*rhs);
                match op {
                    FastOp::Mul => {
                        // Overflow when the high word is not the sign
                        // extension of the low one.
                        let r = self.b.imul(x, y);
                        let hi = self.b.smulhi(x, y);
                        let sign = self.b.sshr_imm(r, 63);
                        let overflow = self.b.icmp(IntCC::NotEqual, hi, sign);
                        let ok_blk = self.b.create_block();
                        self.b.brif(overflow, slow_blk, &[], ok_blk, &[]);
                        self.b.switch_to_block(ok_blk);
                        self.release(*dst);
                        self.store_tag(*dst, TAG_INT);
                        self.store_payload(*dst, r);
                    }
                    FastOp::Div | FastOp::Mod => {
                        // Division by zero and MIN / -1 go to the runtime.
                        let y_zero = self.b.icmp_imm(IntCC::Equal, y, 0);
                        let x_min = self.b.icmp_imm(IntCC::Equal, x, i64::MIN);
                        let y_m1 = self.b.icmp_imm(IntCC::Equal, y, -1);
                        let min_case = self.b.band(x_min, y_m1);
                        let bad = self.b.bor(y_zero, min_case);
                        let ok_blk = self.b.create_block();
                        self.b.brif(bad, slow_blk, &[], ok_blk, &[]);
                        self.b.switch_to_block(ok_blk);
                        // Floor semantics, as in Ruby.
                        let rem = self.b.srem(x, y);
                        let nonzero = self.b.icmp_imm(IntCC::NotEqual, rem, 0);
                        let y_neg = self.b.icmp_imm(IntCC::SignedLessThan, y, 0);
                        let r = if *op == FastOp::Div {
                            let q = self.b.sdiv(x, y);
                            let x_neg = self.b.icmp_imm(IntCC::SignedLessThan, x, 0);
                            let differ = self.b.bxor(x_neg, y_neg);
                            let adjust = self.b.band(nonzero, differ);
                            let adjust = self.b.uextend(Ty::I64, adjust);
                            self.b.isub(q, adjust)
                        } else {
                            let r_neg = self.b.icmp_imm(IntCC::SignedLessThan, rem, 0);
                            let differ = self.b.bxor(r_neg, y_neg);
                            let adjust = self.b.band(nonzero, differ);
                            let zero = self.b.iconst(Ty::I64, 0);
                            let add = self.b.select(adjust, y, zero);
                            self.b.iadd(rem, add)
                        };
                        self.release(*dst);
                        self.store_tag(*dst, TAG_INT);
                        self.store_payload(*dst, r);
                    }
                    FastOp::Add | FastOp::Sub => {
                        let r = if *op == FastOp::Add {
                            self.b.iadd(x, y)
                        } else {
                            self.b.isub(x, y)
                        };
                        // Signed overflow: the result's sign differs from
                        // both operands' (add) or from x and not-y (sub).
                        let y2 = if *op == FastOp::Add {
                            y
                        } else {
                            self.b.bnot(y)
                        };
                        let a = self.b.bxor(x, r);
                        let c = self.b.bxor(y2, r);
                        let both_neg = self.b.band(a, c);
                        let overflow = self.b.icmp_imm(IntCC::SignedLessThan, both_neg, 0);
                        let ok_blk = self.b.create_block();
                        self.b.brif(overflow, slow_blk, &[], ok_blk, &[]);
                        self.b.switch_to_block(ok_blk);
                        self.release(*dst);
                        self.store_tag(*dst, TAG_INT);
                        self.store_payload(*dst, r);
                    }
                    _ => {
                        let cc = match op {
                            FastOp::Lt => IntCC::SignedLessThan,
                            FastOp::Le => IntCC::SignedLessThanOrEqual,
                            FastOp::Gt => IntCC::SignedGreaterThan,
                            FastOp::Ge => IntCC::SignedGreaterThanOrEqual,
                            FastOp::Eq => IntCC::Equal,
                            _ => IntCC::NotEqual,
                        };
                        let r = self.b.icmp(cc, x, y);
                        self.store_bool_home(*dst, r);
                    }
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(slow_blk);
                self.exec(block, index, unwind);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::Not { dst, src } => {
                let t = self.truthy(*src);
                let one = self.b.iconst(Ty::I8, 1);
                let v = self.b.bxor(t, one);
                self.store_bool(*dst, v);
            }
            Inst::Len { dst, src } => {
                // An array: its length from the vector; anything else
                // through the runtime.
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                if self.states[*src as usize] == State::Arr {
                    self.b.jump(fast, &[]);
                } else {
                    let tag = self.tag(*src);
                    let is_arr = self.b.icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
                    self.b.brif(is_arr, fast, &[], slow, &[]);
                }
                self.b.switch_to_block(fast);
                let (_, _, len, _) = self.array_view(*src);
                if src != dst {
                    self.note_arr(*src);
                }
                // The home too: `after` reads it back into the variable.
                self.release(*dst);
                self.store_tag(*dst, TAG_INT);
                self.store_payload(*dst, len);
                self.b.def_var(self.ivar(*dst), len);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(slow);
                self.flush(*src);
                self.exec(block, index, unwind);
                if src != dst {
                    self.arr_after_slow(*src, block, index);
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::ArrayIndex {
                dst,
                arr,
                index: idx,
                word,
            } => {
                // An Int index within range: the element from the vector
                // (as the number it is for an `Array[Int]`/`Array[Float]`
                // stored as words); a negative or out-of-range index, or
                // other storage, through the runtime, which counts from
                // the end or raises `IndexError`.
                let check_b = self.b.create_block();
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let known = self.states[*arr as usize] == State::Arr;
                let int_state = self.states[*idx as usize] == State::Int;
                if !known {
                    let tag = self.tag(*arr);
                    let is_arr = self.b.icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
                    let ok = if int_state {
                        is_arr
                    } else {
                        let itag = self.tag(*idx);
                        let is_int = self.b.icmp_imm(IntCC::Equal, itag, TAG_INT);
                        self.b.band(is_arr, is_int)
                    };
                    self.b.brif(ok, check_b, &[], slow, &[]);
                } else if !int_state {
                    let itag = self.tag(*idx);
                    let is_int = self.b.icmp_imm(IntCC::Equal, itag, TAG_INT);
                    self.b.brif(is_int, check_b, &[], slow, &[]);
                } else {
                    self.b.jump(check_b, &[]);
                }
                // The result's state, on every path.
                let num = match word {
                    Some(true) => Some(State::Float),
                    Some(false) => Some(State::Int),
                    None => None,
                };
                self.b.switch_to_block(check_b);
                if arr != dst {
                    self.note_arr(*arr);
                }
                let i = if int_state {
                    self.b.use_var(self.ivar(*idx))
                } else {
                    self.payload(*idx)
                };
                let (kind, ptr, len, _) = self.array_view(*arr);
                let in_range = self.b.icmp(IntCC::UnsignedLessThan, i, len);
                self.b.brif(in_range, fast, &[], slow, &[]);
                self.b.switch_to_block(fast);
                let off8 = self.b.imul_imm(i, 8);
                match num {
                    Some(st) => {
                        let words = self.b.create_block();
                        let want = if st == State::Float { 2 } else { 1 };
                        let is_words = self.b.icmp_imm(IntCC::Equal, kind, want);
                        self.b.brif(is_words, words, &[], slow, &[]);
                        self.b.switch_to_block(words);
                        let elem = self.b.iadd(ptr, off8);
                        let w = self.b.load(Ty::I64, elem, 0);
                        self.unbox(*dst, st);
                        if st == State::Float {
                            let v = self.b.bitcast(Ty::F64, w);
                            self.b.def_var(self.fvar(*dst), v);
                        } else {
                            self.b.def_var(self.ivar(*dst), w);
                        }
                        self.b.jump(cont, &[]);
                    }
                    None => {
                        let values_b = self.b.create_block();
                        let ints_b = self.b.create_block();
                        let floats_b = self.b.create_block();
                        let objects_b = self.b.create_block();
                        let not_values = self.b.create_block();
                        let words_b = self.b.create_block();
                        let is_values = self.b.icmp_imm(IntCC::Equal, kind, 0);
                        self.b.brif(is_values, values_b, &[], not_values, &[]);
                        self.b.switch_to_block(not_values);
                        let is_objects = self.b.icmp_imm(IntCC::Equal, kind, 3);
                        self.b.brif(is_objects, objects_b, &[], words_b, &[]);
                        self.b.switch_to_block(objects_b);
                        let elem = self.b.iadd(ptr, off8);
                        self.load_object_elem(*dst, elem, false);
                        self.b.jump(cont, &[]);
                        self.b.switch_to_block(words_b);
                        let is_ints = self.b.icmp_imm(IntCC::Equal, kind, 1);
                        self.b.brif(is_ints, ints_b, &[], floats_b, &[]);
                        self.b.switch_to_block(values_b);
                        let off = self.b.imul_imm(i, i64::from(VALUE_SIZE));
                        let elem = self.b.iadd(ptr, off);
                        self.clone_from(*dst, elem);
                        self.b.jump(cont, &[]);
                        for (blk, tag) in [(ints_b, TAG_INT), (floats_b, TAG_FLOAT)] {
                            self.b.switch_to_block(blk);
                            let elem = self.b.iadd(ptr, off8);
                            let w = self.b.load(Ty::I64, elem, 0);
                            self.release(*dst);
                            self.store_tag(*dst, tag);
                            self.store_payload(*dst, w);
                            self.b.jump(cont, &[]);
                        }
                    }
                }
                self.b.switch_to_block(slow);
                self.flush(*arr);
                self.flush(*idx);
                if let Some(st) = num {
                    // The runtime writes the number into the home: read
                    // it back into the variable.
                    self.unbox(*dst, State::Unknown);
                    self.exec(block, index, unwind);
                    let want = if st == State::Float {
                        TAG_FLOAT
                    } else {
                        TAG_INT
                    };
                    let tag = self.tag(*dst);
                    let ok = self.b.icmp_imm(IntCC::Equal, tag, want);
                    let good = self.b.create_block();
                    let bad = self.b.create_block();
                    self.b.brif(ok, good, &[], bad, &[]);
                    self.b.switch_to_block(bad);
                    self.unsound(block, index);
                    self.b.switch_to_block(good);
                    let w = self.payload(*dst);
                    self.states[*dst as usize] = st;
                    if st == State::Float {
                        let v = self.b.bitcast(Ty::F64, w);
                        self.b.def_var(self.fvar(*dst), v);
                    } else {
                        self.b.def_var(self.ivar(*dst), w);
                    }
                } else {
                    self.exec(block, index, unwind);
                }
                if arr != dst {
                    self.arr_after_slow(*arr, block, index);
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::ArrayGetWord {
                dst,
                arr,
                index: idx,
                float,
            } => {
                // In range, and the elements are words (`ArrayWords`):
                // a load, into the variable.
                let i = if self.states[*idx as usize] == State::Int {
                    self.b.use_var(self.ivar(*idx))
                } else {
                    self.payload(*idx)
                };
                if arr != dst {
                    self.note_arr(*arr);
                }
                let (_, ptr, _, _) = self.array_view(*arr);
                let off = self.b.imul_imm(i, 8);
                let elem = self.b.iadd(ptr, off);
                let word = self.b.load(Ty::I64, elem, 0);
                if *float {
                    self.unbox(*dst, State::Float);
                    let v = self.b.bitcast(Ty::F64, word);
                    self.b.def_var(self.fvar(*dst), v);
                } else {
                    self.unbox(*dst, State::Int);
                    self.b.def_var(self.ivar(*dst), word);
                }
            }
            Inst::ArrayGetReg {
                dst,
                arr,
                index: idx,
                borrow,
                objects,
            } => {
                // An array indexed by an Int within range: the element
                // copied from the vector; everything else (negative
                // indices, other receivers) through the runtime.
                let check_b = self.b.create_block();
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let known = self.states[*arr as usize] == State::Arr;
                let int_state = self.states[*idx as usize] == State::Int;
                match (known, int_state) {
                    (true, true) => self.b.jump(check_b, &[]),
                    (true, false) => {
                        let itag = self.tag(*idx);
                        let is_int = self.b.icmp_imm(IntCC::Equal, itag, TAG_INT);
                        self.b.brif(is_int, check_b, &[], slow, &[]);
                    }
                    (false, true) => {
                        let tag = self.tag(*arr);
                        let is_arr = self.b.icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
                        self.b.brif(is_arr, check_b, &[], slow, &[]);
                    }
                    (false, false) => {
                        let tag = self.tag(*arr);
                        let is_arr = self.b.icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
                        let itag = self.tag(*idx);
                        let is_int = self.b.icmp_imm(IntCC::Equal, itag, TAG_INT);
                        let both = self.b.band(is_arr, is_int);
                        self.b.brif(both, check_b, &[], slow, &[]);
                    }
                }
                self.b.switch_to_block(check_b);
                if arr != dst {
                    self.note_arr(*arr);
                }
                let i = if int_state {
                    self.b.use_var(self.ivar(*idx))
                } else {
                    self.payload(*idx)
                };
                let (kind, ptr, len, _) = self.array_view(*arr);
                let in_range = self.b.icmp(IntCC::UnsignedLessThan, i, len);
                self.b.brif(in_range, fast, &[], slow, &[]);
                self.b.switch_to_block(fast);
                // Boxed elements are copied; unboxed ones are read as the
                // machine word they are and boxed into the register. An
                // array of objects only (`objects`) holds values: any other
                // storage is a bug.
                let values_b = self.b.create_block();
                let objects_b = self.b.create_block();
                let not_values = self.b.create_block();
                let is_values = self.b.icmp_imm(IntCC::Equal, kind, 0);
                self.b.brif(is_values, values_b, &[], not_values, &[]);
                self.b.switch_to_block(not_values);
                let unboxed = if *objects {
                    let bad = self.b.create_block();
                    let is_objects = self.b.icmp_imm(IntCC::Equal, kind, 3);
                    self.b.brif(is_objects, objects_b, &[], bad, &[]);
                    self.b.switch_to_block(bad);
                    self.unsound(block, index);
                    None
                } else {
                    let ints_b = self.b.create_block();
                    let floats_b = self.b.create_block();
                    let words_b = self.b.create_block();
                    let is_objects = self.b.icmp_imm(IntCC::Equal, kind, 3);
                    self.b.brif(is_objects, objects_b, &[], words_b, &[]);
                    self.b.switch_to_block(words_b);
                    let is_ints = self.b.icmp_imm(IntCC::Equal, kind, 1);
                    self.b.brif(is_ints, ints_b, &[], floats_b, &[]);
                    Some((ints_b, floats_b))
                };
                self.b.switch_to_block(objects_b);
                let off8 = self.b.imul_imm(i, 8);
                let elem8 = self.b.iadd(ptr, off8);
                let p = self.load_object_elem(*dst, elem8, *borrow);
                if *objects {
                    self.b.def_var(self.pvar(*dst), p);
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(values_b);
                let off = self.b.imul_imm(i, i64::from(VALUE_SIZE));
                let elem = self.b.iadd(ptr, off);
                if *borrow {
                    // The two words, no count: the array keeps it.
                    for k in [0, 8] {
                        let w = self.b.load(Ty::I64, elem, k);
                        self.b.store(w, self.regs, reg_off(*dst) + k);
                    }
                    self.stale[*dst as usize] = false;
                } else {
                    self.clone_from(*dst, elem);
                }
                if *objects {
                    // The element's allocation, for `State::Obj`.
                    let p = self.b.load(Ty::Ptr, elem, 8);
                    self.b.def_var(self.pvar(*dst), p);
                }
                self.b.jump(cont, &[]);
                if let Some((ints_b, floats_b)) = unboxed {
                    for (blk, tag) in [(ints_b, TAG_INT), (floats_b, TAG_FLOAT)] {
                        self.b.switch_to_block(blk);
                        let off = self.b.imul_imm(i, 8);
                        let elem = self.b.iadd(ptr, off);
                        let w = self.b.load(Ty::I64, elem, 0);
                        self.release(*dst);
                        self.store_tag(*dst, tag);
                        self.store_payload(*dst, w);
                        self.b.jump(cont, &[]);
                    }
                }
                self.b.switch_to_block(slow);
                self.flush(*arr);
                self.flush(*idx);
                if *borrow {
                    // The runtime drops what it overwrites (a borrowed
                    // element: not to be released) and counts what it
                    // stores (given up again: the array keeps it).
                    self.store_tag(*dst, TAG_NIL);
                    self.exec(block, index, unwind);
                    let p = self.b.iadd_imm(self.regs, i64::from(reg_off(*dst)));
                    self.b.call(self.h.disown, &[p]);
                } else {
                    self.exec(block, index, unwind);
                }
                if *objects {
                    // In range in the loops that use it: an object.
                    let tag = self.tag(*dst);
                    let is_obj = self.b.icmp_imm(IntCC::Equal, tag, TAG_OBJECT);
                    let good = self.b.create_block();
                    let bad = self.b.create_block();
                    self.b.brif(is_obj, good, &[], bad, &[]);
                    self.b.switch_to_block(bad);
                    self.unsound(block, index);
                    self.b.switch_to_block(good);
                    let p = self.payload_ptr(*dst);
                    self.b.def_var(self.pvar(*dst), p);
                }
                if arr != dst {
                    self.arr_after_slow(*arr, block, index);
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::ArrayPushWord { arr, src, float } => {
                // The array `ArrayNewWords` made, unshared, storing words:
                // with room, the word is stored and the length bumped;
                // otherwise the runtime grows it.
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let rc = if self.states[*arr as usize] == State::Arr {
                    self.b.use_var(self.pvar(*arr))
                } else {
                    self.payload_ptr(*arr)
                };
                let (_, ptr, len, cap) = self.array_view_at(rc);
                let room = self.b.icmp(IntCC::UnsignedLessThan, len, cap);
                self.b.brif(room, fast, &[], slow, &[]);
                self.b.switch_to_block(fast);
                let word = match self.states[*src as usize] {
                    State::Int => self.b.use_var(self.ivar(*src)),
                    State::Float => {
                        let f = self.b.use_var(self.fvar(*src));
                        self.b.bitcast(Ty::I64, f)
                    }
                    _ => {
                        // The checker's type: anything else is a bug (the
                        // runtime would store it boxed, under the words).
                        let want = if *float { TAG_FLOAT } else { TAG_INT };
                        let tag = self.tag(*src);
                        let ok = self.b.icmp_imm(IntCC::Equal, tag, want);
                        let good = self.b.create_block();
                        let bad = self.b.create_block();
                        self.b.brif(ok, good, &[], bad, &[]);
                        self.b.switch_to_block(bad);
                        self.unsound(block, index);
                        self.b.switch_to_block(good);
                        self.payload(*src)
                    }
                };
                let off = self.b.imul_imm(len, 8);
                let slot = self.b.iadd(ptr, off);
                self.b.store(word, slot, 0);
                let len1 = self.b.iadd_imm(len, 1);
                let data = self.b.iadd_imm(rc, i64::from(OBJECT_FIELDS_PTR_OFF));
                let vec = self.b.iadd_imm(data, L::ARRAY_VEC_OFF as i64);
                self.b.store(len1, vec, L::vec_layout().len as i32);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(slow);
                self.flush(*src);
                self.exec(block, index, unwind);
                self.arr_after_slow(*arr, block, index);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::ArrayPush { arr, src } => {
                // An unshared array with room: append in place; otherwise
                // the runtime copies or grows it.
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let arr_ptr = self.b.iadd_imm(self.regs, i64::from(reg_off(*arr)));
                let moving = self.movable(inst, *src, block, index);
                self.inline_push(arr_ptr, None, *src, slow, moving);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(slow);
                self.flush(*arr);
                self.flush(*src);
                self.exec(block, index, unwind);
                if moving {
                    self.drop_moved(*src);
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
                if moving {
                    self.states[*src as usize] = State::NonHeap;
                }
            }
            Inst::Interpolate { dst, into, .. } => {
                // Appending to a builder whose result is not read: the
                // runtime is told not to store it.
                let dead =
                    into.is_some() && !self.live[block as usize][index as usize + 1][*dst as usize];
                self.emit_op(inst, block, index, dead, unwind);
            }
            Inst::ClearRegs { from, to } => {
                // A register that may hold a heap value is released and
                // set to nil; the others become nil lazily (the home is
                // written when something reads it: `ensure_home`).
                for r in *from..*to {
                    if self.states[r as usize].needs_release() {
                        self.release(r);
                        self.store_tag(r, TAG_NIL);
                    } else {
                        self.stale[r as usize] = true;
                    }
                    self.states[r as usize] = State::NonHeap;
                }
                // The end of a statement or a pass: what it released, or
                // a call in it did (a value moved into a native), is
                // finalized here (in a program with a `deinitialize`).
                if from < to {
                    self.finalize();
                }
            }
            // The end of a variable's scope: released, then what it held
            // finalized.
            Inst::Release { src } => {
                if self.states[*src as usize].needs_release() {
                    self.release(*src);
                    self.store_tag(*src, TAG_NIL);
                } else {
                    self.stale[*src as usize] = true;
                }
                self.states[*src as usize] = State::NonHeap;
                self.finalize();
            }
            Inst::ClassIs { dst, src, class } => {
                // An object of exactly the class: its id is read from the
                // allocation; anything else (an unboxed number, another
                // tag) is not.
                let v = match self.states[*src as usize] {
                    State::Int | State::Float | State::Bool | State::NonHeap | State::Arr => {
                        self.b.iconst(Ty::I8, 0)
                    }
                    // An object: only its class to compare.
                    State::Obj => {
                        let rc = self.b.use_var(self.pvar(*src));
                        let cid = self
                            .b
                            .uload32(rc, OBJECT_FIELDS_PTR_OFF + L::OBJECT_CLASS_OFF as i32);
                        self.b.icmp_imm(IntCC::Equal, cid, i64::from(*class))
                    }
                    State::Unknown => {
                        let check = self.b.create_block();
                        let join = self.b.create_block();
                        self.b.append_block_param(join, Ty::I8);
                        let tag = self.tag(*src);
                        let is_obj = self.b.icmp_imm(IntCC::Equal, tag, TAG_OBJECT);
                        let no = self.b.iconst(Ty::I8, 0);
                        self.b.brif(is_obj, check, &[], join, &[no]);
                        self.b.switch_to_block(check);
                        let rc = self.payload_ptr(*src);
                        // Where the test holds, an object (see
                        // `unbox::class_tested`).
                        if dst != src {
                            self.b.def_var(self.pvar(*src), rc);
                        }
                        let cid = self
                            .b
                            .uload32(rc, OBJECT_FIELDS_PTR_OFF + L::OBJECT_CLASS_OFF as i32);
                        let same = self.b.icmp_imm(IntCC::Equal, cid, i64::from(*class));
                        self.b.jump(join, &[same]);
                        self.b.switch_to_block(join);
                        self.b.block_params(join)[0]
                    }
                };
                self.store_bool(*dst, v);
            }
            Inst::IsNil { dst, src } => {
                let v = match self.states[*src as usize] {
                    State::Int | State::Float | State::Bool => self.b.iconst(Ty::I8, 0),
                    _ => {
                        let tag = self.tag(*src);
                        self.b.icmp_imm(IntCC::Equal, tag, TAG_NIL)
                    }
                };
                self.store_bool(*dst, v);
            }
            Inst::SelfRef { dst } => {
                let self_ptr = match self.typed_self_ptr {
                    Some(p) => p,
                    None => self.b.load(Ty::Ptr, self.ptrs, 8),
                };
                self.clone_from(*dst, self_ptr);
                if unbox::self_is_object(self.f, self.methods, self.classes) {
                    let p = self.b.load(Ty::Ptr, self_ptr, 8);
                    self.b.def_var(self.pvar(*dst), p);
                }
            }
            Inst::Arg { dst, index: arg } if self.typed.is_some() => {
                // A typed entry's parameter is already the machine value.
                let v = self.typed_params[*arg as usize];
                match self.typed.as_ref().map(|t| t.params[*arg as usize]) {
                    Some(unbox::Mach::Float) => self.store_float(*dst, v),
                    Some(unbox::Mach::Bool) => self.store_bool(*dst, v),
                    // The caller's value, counted again here.
                    Some(unbox::Mach::Boxed) => self.clone_from(*dst, v),
                    _ => self.store_int(*dst, v),
                }
            }
            Inst::Arg { dst, index: arg } => {
                // Present arguments are copied inline; a missing one is nil.
                let nargs = self.b.load(Ty::I64, self.ptrs, 16);
                let present = self
                    .b
                    .icmp_imm(IntCC::UnsignedGreaterThan, nargs, i64::from(*arg));
                let yes = self.b.create_block();
                let no = self.b.create_block();
                let cont = self.b.create_block();
                self.b.brif(present, yes, &[], no, &[]);
                self.b.switch_to_block(yes);
                let args = self.b.load(Ty::Ptr, self.ptrs, 0);
                let src = self
                    .b
                    .iadd_imm(args, i64::from(*arg) * i64::from(VALUE_SIZE));
                // An area the call owns gives the value up (the callee
                // then holds its only reference); a borrowed one is
                // copied from. So is it by an entry, whose body reads the
                // parameters again from the start when it takes over.
                let owned = if self.entry_of.is_some() {
                    self.b.iconst(Ty::I8, 0)
                } else {
                    self.b.load(Ty::I8, self.act, L::ACT_ARGS_OWNED as i32)
                };
                let take = self.b.create_block();
                let copy = self.b.create_block();
                self.b.brif(owned, take, &[], copy, &[]);
                self.b.switch_to_block(take);
                self.release(*dst);
                for k in [0, 8] {
                    let w = self.b.load(Ty::I64, src, k);
                    self.b.store(w, self.regs, reg_off(*dst) + k);
                }
                let nil = self.b.iconst(Ty::I64, TAG_NIL);
                self.b.store(nil, src, 0);
                self.stale[*dst as usize] = false;
                self.b.jump(cont, &[]);
                self.b.switch_to_block(copy);
                self.clone_from(*dst, src);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(no);
                self.release(*dst);
                self.store_tag(*dst, TAG_NIL);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
                // The home holds the argument now, whatever the register
                // held before (an earlier parameter sharing it may have
                // left it unboxed).
                self.states[*dst as usize] = State::Unknown;
                // A parameter declared Int/Float: check once, then unboxed.
                // A failed check hands over after this instruction: the
                // value is in the home, and may have left the area.
                if unbox::param_bool(self.f, self.methods, *arg) {
                    self.get_mach(*dst, unbox::Mach::Bool, block, index + 1);
                }
                if let Some(n) = unbox::param_num(self.f, self.methods, *arg) {
                    self.get_num(*dst, n, block, index + 1);
                }
            }
            Inst::BlockParam { dst } => {
                let d = self.i32(*dst);
                self.b.call(self.h.block_param, &[self.act, self.regs, d]);
            }
            Inst::FrameGet { dst, depth, slot } => {
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let addr = self.frame_slot_addr(*depth, *slot, slow);
                self.clone_from(*dst, addr);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(slow);
                let dp = self.i32(*depth);
                let sl = self.i32(*slot);
                let d = self.i32(*dst);
                self.b
                    .call(self.h.frame_get, &[self.act, dp, sl, self.regs, d]);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::FrameSet { depth, slot, src } => {
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let addr = self.frame_slot_addr(*depth, *slot, slow);
                self.release_ptr(addr);
                self.clone_reg_to_ptr(addr, *src);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(slow);
                let dp = self.i32(*depth);
                let sl = self.i32(*slot);
                let s = self.i32(*src);
                self.b
                    .call(self.h.frame_set, &[self.act, dp, sl, self.regs, s]);
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            // A class nothing reads (an inlined constructor's receiver,
            // once the construction was replaced by its fields), over a
            // value with nothing to release: not written at all.
            Inst::ClassRef { dst, .. }
                if !self.live[block as usize][index as usize + 1][*dst as usize]
                    && !self.states[*dst as usize].needs_release() => {}
            Inst::ClassRef { dst, class } => {
                self.release(*dst);
                self.store_tag(*dst, TAG_CLASS);
                let v = self.b.iconst(Ty::I32, i64::from(*class));
                self.b.store(v, self.regs, reg_off(*dst) + CLASS_OFF);
            }
            Inst::FieldGet {
                dst,
                obj,
                index: field,
                class,
            } => {
                // An object: read the field where it is (no test when the
                // register is known to hold one).
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                self.branch_obj(*obj, fast, slow);
                let num = unbox::field_num(self.classes, *class, *field);
                let (kind, _) = unbox::field_slot(self.classes, *class, *field);
                // The slow path first: a field declared Int/Float/Bool is
                // checked once there (the compile-time state must still
                // be the one before this instruction).
                self.b.switch_to_block(slow);
                let o = self.i32(*obj);
                let i = self.i32(*field);
                let d = self.i32(*dst);
                let call = self
                    .b
                    .call(self.h.field_get, &[self.rt, self.regs, o, i, d]);
                let status = call[0];
                self.check(status, unwind);
                let before = self.states[*dst as usize];
                if dst != obj {
                    // It was an object after all.
                    self.note_obj(*obj);
                    // The home holds the field now, not what the
                    // register held unboxed before.
                    self.states[*dst as usize] = State::Unknown;
                }
                if let Some(n) = num {
                    self.get_num(*dst, n, block, index);
                } else if kind == FieldKind::Bool {
                    self.get_mach(*dst, unbox::Mach::Bool, block, index);
                }
                self.b.jump(cont, &[]);
                self.states[*dst as usize] = before;
                self.b.switch_to_block(fast);
                if dst != obj {
                    self.note_obj(*obj);
                }
                let addr = self.field_addr(*obj, *class, *field);
                match kind {
                    // A Float or Bool field always holds one (the checker
                    // sees to it that fields are assigned before the
                    // object is used): its word is the value.
                    FieldKind::Float => {
                        let p = self.b.load(Ty::I64, addr, 0);
                        self.unbox(*dst, State::Float);
                        let v = self.b.bitcast(Ty::F64, p);
                        self.b.def_var(self.fvar(*dst), v);
                    }
                    FieldKind::Bool => {
                        let p = self.b.load(Ty::I8, addr, 0);
                        self.unbox(*dst, State::Bool);
                        self.b.def_var(self.bvar(*dst), p);
                    }
                    // An Int field's mark (the smallest Int, kept aside):
                    // the runtime reads it.
                    FieldKind::Int => {
                        let p = self.b.load(Ty::I64, addr, 0);
                        let aside = self.b.icmp_imm(IntCC::Equal, p, L::FIELD_INT_MARK);
                        let ok = self.b.create_block();
                        self.b.brif(aside, slow, &[], ok, &[]);
                        self.b.switch_to_block(ok);
                        self.unbox(*dst, State::Int);
                        self.b.def_var(self.ivar(*dst), p);
                    }
                    FieldKind::Value => self.clone_from(*dst, addr),
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::FieldSet {
                obj,
                index: field_index,
                src,
                class,
            } => {
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                self.branch_obj(*obj, fast, slow);
                self.b.switch_to_block(fast);
                let field = self.field_addr(*obj, *class, *field_index);
                let (kind, _) = unbox::field_slot(self.classes, *class, *field_index);
                // A word field: the number or boolean as its word, when
                // the source is one the word holds (nothing to release);
                // anything else through the runtime, which keeps it
                // aside.
                if kind != FieldKind::Value {
                    self.store_word_field(field, kind, *src, slow);
                    self.b.jump(cont, &[]);
                    self.b.switch_to_block(slow);
                    self.flush(*src);
                    let o = self.i32(*obj);
                    let i = self.i32(*field_index);
                    let s = self.i32(*src);
                    let call = self
                        .b
                        .call(self.h.field_set, &[self.rt, self.regs, o, i, s]);
                    self.check(call[0], unwind);
                    self.b.jump(cont, &[]);
                    self.b.switch_to_block(cont);
                    self.note_obj(*obj);
                    return;
                }
                self.release_ptr(field);
                // The last read of the source moves it into the field.
                let moving = self.movable(inst, *src, block, index);
                if moving {
                    self.move_reg_to_ptr(field, *src);
                } else {
                    self.clone_reg_to_ptr(field, *src);
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(slow);
                let o = self.i32(*obj);
                let i = self.i32(*field_index);
                let s = self.i32(*src);
                let call = self
                    .b
                    .call(self.h.field_set, &[self.rt, self.regs, o, i, s]);
                let status = call[0];
                self.check(status, unwind);
                if moving {
                    self.drop_moved(*src);
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
                if obj != src || !moving {
                    self.note_obj(*obj);
                }
                if moving {
                    self.states[*src as usize] = State::NonHeap;
                }
            }
            Inst::Call {
                dst,
                kind: CallKind::Construct { class, init },
                args,
                splat: false,
                kw,
                kw_splat: None,
                block: None,
                ..
            } if kw.is_empty() => {
                // A data type given all its fields: allocate it with nil
                // fields and write the arguments straight into them.
                let data = init.is_some_and(|i| {
                    self.methods[i as usize].synth == RtSynth::DataInit
                        && matches!(
                            self.classes[*class as usize].kind,
                            RtClassKind::Data | RtClassKind::Variant
                        )
                        && self.classes[*class as usize].fields.len() == args.len()
                });
                if data {
                    // The fields are laid out in the argument area and
                    // moved into the object.
                    for (k, r) in args.iter().enumerate() {
                        let p = self
                            .b
                            .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
                        if self.movable(inst, *r, block, index) {
                            self.move_reg_to_ptr(p, *r);
                            self.states[*r as usize] = State::NonHeap;
                        } else {
                            self.clone_reg_to_ptr(p, *r);
                        }
                    }
                    let class_v = self.i32(*class);
                    let n = self.i32(args.len() as u32);
                    let d = self.i32(*dst);
                    self.b.call(
                        self.h.alloc_data,
                        &[self.regs, class_v, self.args_buf, n, d],
                    );
                    return;
                }
                for (k, r) in args.iter().enumerate() {
                    let v = self.i32(*r);
                    self.b.store(v, self.scratch, 4 * k as i32);
                }
                let class_v = self.i32(*class);
                let init_v = self.i32(init.unwrap_or(u32::MAX));
                let nargs = self.i32(args.len() as u32);
                let d = self.i32(*dst);
                let status = self.b.call(
                    self.h.construct,
                    &[self.rt, self.regs, class_v, init_v, self.scratch, nargs, d],
                )[0];
                self.check(status, unwind);
                // The runtime copied the arguments: those read for the
                // last time are released now, as the interpreter moves
                // them (what `initialize` kept stays).
                for r in args {
                    if *r != *dst && self.movable(inst, *r, block, index) {
                        self.drop_moved(*r);
                        self.states[*r as usize] = State::NonHeap;
                    }
                }
            }
            Inst::OwnedCall {
                dst,
                method,
                recv,
                args,
                kw,
                unused,
            } if kw.is_empty() => {
                // A result nobody reads (`xs = xs.push(v)` as a statement)
                // is not stored: one clone and one release fewer (and the
                // register keeps its state, see `unbox::transfer`).
                let wanted = !*unused;
                // `xs = xs.push(v)`: the append in place is inline when the
                // array (in its register, frame slot or field) is unshared
                // and has room; the runtime handles the rest.
                let is_push = args.len() == 1
                    && self.methods[*method as usize]
                        .native_key
                        .as_deref()
                        .is_some_and(|k| k == "Array#push")
                    && !matches!(recv, VarLoc::Reg(r) if *r == args[0]);
                // `h = h.put(k, v)` with numbers known to be Ints: in place
                // through a small runtime entry when the hash is unshared
                // and all Ints.
                let is_put = args.len() == 2
                    && self.methods[*method as usize]
                        .native_key
                        .as_deref()
                        .is_some_and(|k| k == "Hash#put")
                    && args.iter().all(|a| self.states[*a as usize] == State::Int);
                let moving = is_push && self.movable(inst, args[0], block, index);
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                if is_put {
                    let slot = match recv {
                        VarLoc::Reg(r) => self.b.iadd_imm(self.regs, i64::from(reg_off(*r))),
                        VarLoc::Frame { depth, slot } => self.frame_slot_addr(*depth, *slot, slow),
                        VarLoc::Field { obj, index } => {
                            let check = self.b.create_block();
                            self.branch_obj(*obj, check, slow);
                            self.b.switch_to_block(check);
                            self.field_addr_of(*obj, *index)
                        }
                    };
                    let k = self.b.use_var(self.ivar(args[0]));
                    let v = self.b.use_var(self.ivar(args[1]));
                    let done = self.b.call(self.h.hash_put_int, &[slot, k, v])[0];
                    let ok = self.b.create_block();
                    self.b.brif(done, ok, &[], slow, &[]);
                    self.b.switch_to_block(ok);
                    if wanted {
                        self.clone_from(*dst, slot);
                    }
                    self.b.jump(cont, &[]);
                    self.b.switch_to_block(slow);
                }
                if is_push {
                    let arr_ptr = match recv {
                        VarLoc::Reg(r) => self.b.iadd_imm(self.regs, i64::from(reg_off(*r))),
                        VarLoc::Frame { depth, slot } => self.frame_slot_addr(*depth, *slot, slow),
                        VarLoc::Field { obj, index } => {
                            let check = self.b.create_block();
                            self.branch_obj(*obj, check, slow);
                            self.b.switch_to_block(check);
                            self.field_addr_of(*obj, *index)
                        }
                    };
                    // An array register stays one (`unbox::transfer`): its
                    // allocation, the same after an append in place, is
                    // kept in its variable on both paths.
                    let arr_reg = match recv {
                        VarLoc::Reg(r) => Some(*r),
                        _ => None,
                    };
                    let known = arr_reg
                        .filter(|r| self.states[*r as usize] == State::Arr)
                        .map(|r| self.b.use_var(self.pvar(r)));
                    let rc = self.inline_push(arr_ptr, known, args[0], slow, moving);
                    if let Some(r) = arr_reg {
                        self.b.def_var(self.pvar(r), rc);
                    }
                    if wanted {
                        self.clone_from(*dst, arr_ptr);
                    }
                    self.b.jump(cont, &[]);
                    self.b.switch_to_block(slow);
                }
                // The runtime reads the homes: written back here, on its
                // path only.
                let live = self.live[block as usize][index as usize].clone();
                self.flush_live(&live);
                for (k, r) in args.iter().enumerate() {
                    let v = self.i32(*r);
                    self.b.store(v, self.scratch, 4 * k as i32);
                }
                let (kind, a, bb) = match recv {
                    VarLoc::Reg(r) => (0, *r, 0),
                    VarLoc::Frame { depth, slot } => (1, *depth, *slot),
                    VarLoc::Field { obj, index } => (2, *obj, *index),
                };
                self.materialize();
                let mid_v = self.i32(*method);
                let kind_v = self.i32(kind);
                let a_v = self.i32(a);
                let b_v = self.i32(bb);
                let nargs = self.i32(args.len() as u32);
                let d = self.i32(if wanted { *dst } else { u32::MAX });
                let status = self.b.call(
                    self.h.owned_call,
                    &[
                        self.rt,
                        self.act,
                        mid_v,
                        self.regs,
                        kind_v,
                        a_v,
                        b_v,
                        self.scratch,
                        nargs,
                        d,
                    ],
                )[0];
                self.check(status, unwind);
                if moving {
                    self.drop_moved(args[0]);
                }
                if let (true, VarLoc::Reg(r)) = (is_push, recv) {
                    self.arr_after_slow(*r, block, index);
                }
                self.b.jump(cont, &[]);
                self.b.switch_to_block(cont);
                if moving {
                    self.states[args[0] as usize] = State::NonHeap;
                }
            }
            Inst::Call {
                dst,
                kind: CallKind::Yield,
                args,
                splat: false,
                kw,
                kw_splat: None,
                block: None,
                ..
            } if kw.is_empty() => {
                for (k, r) in args.iter().enumerate() {
                    let v = self.i32(*r);
                    self.b.store(v, self.scratch, 4 * k as i32);
                }
                let nargs = self.i32(args.len() as u32);
                let d = self.i32(*dst);
                let status = self.b.call(
                    self.h.yield_,
                    &[self.rt, self.act, self.regs, self.scratch, nargs, d],
                )[0];
                self.check(status, unwind);
            }
            Inst::Call { .. } => match self.static_target(inst) {
                Some(StaticCall {
                    mid,
                    recv,
                    args,
                    block: blk,
                    dst,
                }) => {
                    self.set_call_line(block, index);
                    for (k, r) in args.iter().enumerate() {
                        let v = self.i32(*r);
                        self.b.store(v, self.scratch, 4 * k as i32);
                    }
                    let mid_v = self.i32(mid);
                    let recv_v = self.i32(recv.unwrap_or(u32::MAX));
                    let nargs = self.i32(args.len() as u32);
                    let blk_v = self.i32(blk.unwrap_or(u32::MAX));
                    let d = self.i32(dst);
                    {
                        let m = &self.methods[mid as usize];
                        if m.overridden && !m.singleton && !m.is_extension && m.native_key.is_none()
                        {
                            self.virtual_call(
                                inst, mid, recv, &args, blk, dst, block, index, unwind,
                            );
                            self.drop_copied_moves(inst, dst);
                            return;
                        }
                    }
                    if let Some(callee) = direct_target(inst, self.methods) {
                        let typed = self.typed_all.get(callee as usize).cloned().flatten();
                        match typed {
                            Some(sig)
                                if blk.is_none()
                                    && args.len() == sig.params.len()
                                    && self.callees_typed.contains_key(&callee) =>
                            {
                                self.typed_call(
                                    inst, mid, callee, &sig, recv, &args, dst, block, index, unwind,
                                );
                            }
                            _ => self.direct_call(
                                inst, mid, callee, recv, &args, blk, dst, block, index, unwind,
                                true,
                            ),
                        }
                        self.drop_copied_moves(inst, dst);
                        return;
                    }
                    if recv.is_none() {
                        self.materialize();
                    }
                    let status = self.b.call(
                        self.h.call_static,
                        &[
                            self.rt,
                            self.act,
                            mid_v,
                            self.regs,
                            recv_v,
                            self.scratch,
                            nargs,
                            blk_v,
                            d,
                        ],
                    )[0];
                    self.check(status, unwind);
                    self.drop_copied_moves(inst, dst);
                }
                None => self.exec(block, index, unwind),
            },
            _ => self.exec(block, index, unwind),
        }
    }
}
