//! Ahead-of-time compilation of QIR with Cranelift.
//!
//! Every QIR function becomes a native function with the signature
//! `(rt, act, out) -> status` (see `quarz_vm::ffi`). The generated code
//! keeps the function's registers in its own stack frame and inlines
//! moves, immediates, branches on truthiness and `Int` arithmetic and
//! comparisons; every other instruction is delegated to the runtime's
//! `qz_exec`, which executes it on the same registers. Control flow,
//! including the routing of exceptions and `ensure` to handler blocks,
//! is compiled.
//!
//! The executable also embeds the serialized module (the runtime needs
//! its metadata, and interprets any function without machine code) and
//! a table of the compiled bodies, and defines `main`.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::{
    types, AbiParam, Block as CBlock, FuncRef, InstBuilder, MemFlags, Signature, StackSlotData,
    StackSlotKind, Value as CValue,
};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, FuncId as CFuncId, Linkage, Module as _};
use cranelift_object::{ObjectBuilder, ObjectModule};
use quarz_ir::*;
use quarz_vm::layout as L;

mod unbox;
use unbox::{Num, State};

/// Size of a `Value` in bytes (`repr(C, u64)`: a tag word and a two-word
/// payload, since some variants hold fat pointers).
const VALUE_SIZE: i32 = 24;
/// Space for an `Activation` built by compiled code (`qz_enter`); the
/// runtime checks its real size against this.
const ACT_BUF_SIZE: u32 = 320;
/// Tags below this hold no reference-counted payload (`NEEDS_DROP_FROM`).
const NEEDS_DROP_FROM: i64 = 8;
const TAG_NIL: i64 = 0;
const TAG_BOOL: i64 = 1;
const TAG_INT: i64 = 2;
const TAG_FLOAT: i64 = 3;
const TAG_CLASS: i64 = 5;
const TAG_ARRAY: i64 = 10;
const TAG_OBJECT: i64 = 16;
/// Offset of the field view in an `Object` from its `Rc` allocation
/// (after the strong and weak counts); see `Object::bind_fields`.
const OBJECT_FIELDS_PTR_OFF: i32 = 16;

const STATUS_RAISE: i64 = 1;

/// The runtime functions compiled code calls.
struct Runtime {
    resume: CFuncId,
    enter: CFuncId,
    enter_virtual: CFuncId,
    leave: CFuncId,
    push_call: CFuncId,
    pop_call: CFuncId,
    stack_overflow: CFuncId,
    drop_value: CFuncId,
    exec: CFuncId,
    term: CFuncId,
    block_param: CFuncId,
    frame_get: CFuncId,
    frame_set: CFuncId,
    field_get: CFuncId,
    load_const: CFuncId,
    interpolate: CFuncId,
    field_set: CFuncId,
    call_static: CFuncId,
    yield_: CFuncId,
    construct: CFuncId,
    alloc_data: CFuncId,
    owned_call: CFuncId,
    main: CFuncId,
}

/// Imported runtime functions, as function references inside one
/// function being built.
struct Helpers {
    resume: FuncRef,
    enter: FuncRef,
    enter_virtual: FuncRef,
    leave: FuncRef,
    push_call: FuncRef,
    pop_call: FuncRef,
    stack_overflow: FuncRef,
    drop_value: FuncRef,
    exec: FuncRef,
    term: FuncRef,
    block_param: FuncRef,
    frame_get: FuncRef,
    frame_set: FuncRef,
    field_get: FuncRef,
    load_const: FuncRef,
    interpolate: FuncRef,
    field_set: FuncRef,
    call_static: FuncRef,
    yield_: FuncRef,
    construct: FuncRef,
    alloc_data: FuncRef,
    owned_call: FuncRef,
}

struct Compiler {
    module: ObjectModule,
    rt: Runtime,
    fn_sig: Signature,
    funcs: Vec<CFuncId>,
}

/// Compile a module to an object file.
pub fn compile(module: &Module) -> Result<Vec<u8>, String> {
    let mut flags = settings::builder();
    flags.set("opt_level", "speed").map_err(|e| e.to_string())?;
    flags.set("is_pic", "true").map_err(|e| e.to_string())?;
    let isa = cranelift_native::builder()
        .map_err(|e| e.to_string())?
        .finish(settings::Flags::new(flags))
        .map_err(|e| e.to_string())?;
    let call_conv = isa.default_call_conv();
    let builder = ObjectBuilder::new(isa, "quarz", cranelift_module::default_libcall_names())
        .map_err(|e| e.to_string())?;
    let mut obj = ObjectModule::new(builder);

    let sig = |params: &[types::Type], ret: Option<types::Type>| {
        let mut s = Signature::new(call_conv);
        for p in params {
            s.params.push(AbiParam::new(*p));
        }
        if let Some(r) = ret {
            s.returns.push(AbiParam::new(r));
        }
        s
    };
    let i64_ = types::I64;
    let i32_ = types::I32;
    let import = |obj: &mut ObjectModule, name: &str, s: &Signature| {
        obj.declare_function(name, Linkage::Import, s)
            .map_err(|e| e.to_string())
    };
    let rt = Runtime {
        exec: import(
            &mut obj,
            "qz_exec",
            &sig(&[i64_, i64_, i32_, i32_, i32_, i64_], Some(i32_)),
        )?,
        term: import(
            &mut obj,
            "qz_term",
            &sig(&[i64_, i64_, i32_, i32_, i64_], Some(i32_)),
        )?,
        block_param: import(&mut obj, "qz_block_param", &sig(&[i64_, i64_, i32_], None))?,
        frame_get: import(
            &mut obj,
            "qz_frame_get",
            &sig(&[i64_, i32_, i32_, i64_, i32_], None),
        )?,
        frame_set: import(
            &mut obj,
            "qz_frame_set",
            &sig(&[i64_, i32_, i32_, i64_, i32_], None),
        )?,
        load_const: import(
            &mut obj,
            "qz_load_const",
            &sig(&[i64_, i32_, i32_, i64_, i32_], None),
        )?,
        interpolate: import(
            &mut obj,
            "qz_interpolate",
            &sig(&[i64_, i64_, i32_, i32_, i32_, i64_], Some(i32_)),
        )?,
        field_get: import(
            &mut obj,
            "qz_field_get",
            &sig(&[i64_, i64_, i32_, i32_, i32_], Some(i32_)),
        )?,
        field_set: import(
            &mut obj,
            "qz_field_set",
            &sig(&[i64_, i64_, i32_, i32_, i32_], Some(i32_)),
        )?,
        resume: import(
            &mut obj,
            "qz_resume",
            &sig(&[i64_, i64_, i32_, i32_, i32_, i64_, i64_], Some(i32_)),
        )?,
        enter_virtual: import(
            &mut obj,
            "qz_enter_virtual",
            &sig(
                &[
                    i64_, i64_, i64_, i32_, i64_, i32_, i64_, i32_, i32_, i64_, i64_, i32_,
                ],
                Some(i32_),
            ),
        )?,
        enter: import(
            &mut obj,
            "qz_enter",
            &sig(
                &[
                    i64_, i64_, i64_, i32_, i32_, i64_, i32_, i64_, i32_, i32_, i32_, i32_, i64_,
                ],
                Some(i32_),
            ),
        )?,
        leave: import(
            &mut obj,
            "qz_leave",
            &sig(&[i64_, i64_, i32_, i64_, i64_, i32_, i32_], Some(i32_)),
        )?,
        push_call: import(&mut obj, "qz_push_call", &sig(&[i64_, i64_], None))?,
        pop_call: import(&mut obj, "qz_pop_call", &sig(&[i64_, i64_], None))?,
        stack_overflow: import(&mut obj, "qz_stack_overflow", &sig(&[i64_], Some(i32_)))?,
        drop_value: import(&mut obj, "qz_drop_value", &sig(&[i64_], None))?,
        call_static: import(
            &mut obj,
            "qz_call_static",
            &sig(
                &[i64_, i64_, i32_, i64_, i32_, i64_, i32_, i32_, i32_],
                Some(i32_),
            ),
        )?,
        yield_: import(
            &mut obj,
            "qz_yield",
            &sig(&[i64_, i64_, i64_, i64_, i32_, i32_], Some(i32_)),
        )?,
        owned_call: import(
            &mut obj,
            "qz_owned_call",
            &sig(
                &[i64_, i64_, i32_, i64_, i32_, i32_, i32_, i64_, i32_, i32_],
                Some(i32_),
            ),
        )?,
        alloc_data: import(
            &mut obj,
            "qz_alloc_data",
            &sig(&[i64_, i32_, i64_, i32_, i32_], None),
        )?,
        construct: import(
            &mut obj,
            "qz_construct",
            &sig(&[i64_, i64_, i32_, i32_, i64_, i32_, i32_], Some(i32_)),
        )?,
        main: import(
            &mut obj,
            "qz_main",
            &sig(
                &[i64_, i64_, i64_, i64_, i32_, i64_, i64_, i64_],
                Some(i32_),
            ),
        )?,
    };
    let fn_sig = sig(&[i64_, i64_, i64_], Some(i32_));
    let funcs: Vec<CFuncId> = (0..module.functions.len())
        .map(|i| {
            obj.declare_function(&format!("qz_fn_{i}"), Linkage::Local, &fn_sig)
                .map_err(|e| e.to_string())
        })
        .collect::<Result<_, _>>()?;
    let mut c = Compiler {
        module: obj,
        rt,
        fn_sig,
        funcs,
    };
    for (i, f) in module.functions.iter().enumerate() {
        c.compile_function(
            i as FuncId,
            f,
            &module.world.methods,
            &module.functions,
            &module.world.classes,
            &module.world.builtin,
        )?;
    }
    c.emit_data_and_main(module, call_conv)?;
    let product = c.module.finish();
    product.emit().map_err(|e| e.to_string())
}

impl Compiler {
    fn compile_function(
        &mut self,
        fid: FuncId,
        f: &Function,
        methods: &[RtMethod],
        functions: &[Function],
        classes: &[RtClass],
        builtin: &RtBuiltin,
    ) -> Result<(), String> {
        let mut ctx: Context = self.module.make_context();
        ctx.func.signature = self.fn_sig.clone();
        let mut fbc = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let drop_value_fn = self.module.declare_func_in_func(self.rt.drop_value, b.func);
        let h = Helpers {
            resume: self.module.declare_func_in_func(self.rt.resume, b.func),
            enter: self.module.declare_func_in_func(self.rt.enter, b.func),
            enter_virtual: self
                .module
                .declare_func_in_func(self.rt.enter_virtual, b.func),
            leave: self.module.declare_func_in_func(self.rt.leave, b.func),
            push_call: self.module.declare_func_in_func(self.rt.push_call, b.func),
            pop_call: self.module.declare_func_in_func(self.rt.pop_call, b.func),
            stack_overflow: self
                .module
                .declare_func_in_func(self.rt.stack_overflow, b.func),
            drop_value: self.module.declare_func_in_func(self.rt.drop_value, b.func),
            exec: self.module.declare_func_in_func(self.rt.exec, b.func),
            term: self.module.declare_func_in_func(self.rt.term, b.func),
            block_param: self
                .module
                .declare_func_in_func(self.rt.block_param, b.func),
            frame_get: self.module.declare_func_in_func(self.rt.frame_get, b.func),
            frame_set: self.module.declare_func_in_func(self.rt.frame_set, b.func),
            field_get: self.module.declare_func_in_func(self.rt.field_get, b.func),
            load_const: self.module.declare_func_in_func(self.rt.load_const, b.func),
            interpolate: self
                .module
                .declare_func_in_func(self.rt.interpolate, b.func),
            field_set: self.module.declare_func_in_func(self.rt.field_set, b.func),
            call_static: self
                .module
                .declare_func_in_func(self.rt.call_static, b.func),
            yield_: self.module.declare_func_in_func(self.rt.yield_, b.func),
            construct: self.module.declare_func_in_func(self.rt.construct, b.func),
            alloc_data: self.module.declare_func_in_func(self.rt.alloc_data, b.func),
            owned_call: self.module.declare_func_in_func(self.rt.owned_call, b.func),
        };
        let heap = heap_possible(f);
        // Unboxed numbers: the state of each register at each block's
        // entry, and an SSA variable per register for each kind.
        let entry_states = unbox::analyze(f, methods, classes, builtin);
        let live = unbox::liveness(f);
        let nregs_usize = f.nregs.max(1) as usize;
        for r in 0..nregs_usize {
            b.declare_var(Variable::from_u32((r) as u32), types::I64);
            b.declare_var(Variable::from_u32((nregs_usize + r) as u32), types::F64);
            b.declare_var(Variable::from_u32((2 * nregs_usize + r) as u32), types::I8);
        }
        // The compiled bodies this function calls directly.
        let mut callees: HashMap<FuncId, FuncRef> = HashMap::new();
        for blk in &f.blocks {
            for inst in &blk.insts {
                if let Some(target) = direct_target(inst, methods) {
                    callees.entry(target).or_insert_with(|| {
                        self.module
                            .declare_func_in_func(self.funcs[target as usize], b.func)
                    });
                }
            }
        }
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
        let uses_act = f.blocks.iter().any(|blk| {
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

        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        let blocks: Vec<CBlock> = f.blocks.iter().map(|_| b.create_block()).collect();
        let unwinds: Vec<CBlock> = f
            .blocks
            .iter()
            .map(|_| {
                let blk = b.create_block();
                b.append_block_param(blk, types::I32);
                blk
            })
            .collect();
        let exit = b.create_block();
        b.append_block_param(exit, types::I32);
        // `return` releases its registers inline (only those whose state
        // allows a heap value) and leaves through here.
        let exit_quick = b.create_block();
        b.append_block_param(exit_quick, types::I32);

        b.switch_to_block(entry);
        let params = b.block_params(entry).to_vec();
        let (rt, act, out) = (params[0], params[1], params[2]);
        let nregs = f.nregs.max(1);
        let slot = b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (VALUE_SIZE as u32) * nregs,
            3,
        ));
        let regs = b.ins().stack_addr(types::I64, slot, 0);
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
        let scratch_slot = b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            4 * max_args as u32,
            2,
        ));
        let scratch = b.ins().stack_addr(types::I64, scratch_slot, 0);
        // An activation for direct calls, the callee's result, and the
        // addresses of this activation's arguments and `self`.
        let act_slot = b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            ACT_BUF_SIZE,
            4,
        ));
        let act_buf = b.ins().stack_addr(types::I64, act_slot, 0);
        let out_slot = b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            VALUE_SIZE as u32,
            3,
        ));
        let out_buf = b.ins().stack_addr(types::I64, out_slot, 0);
        let vbody_slot =
            b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 3));
        let vbody = b.ins().stack_addr(types::I64, vbody_slot, 0);
        let body_sig = b.import_signature(self.fn_sig.clone());
        let ptrs_slot =
            b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 32, 3));
        let ptrs = b.ins().stack_addr(types::I64, ptrs_slot, 0);
        let args_slot = b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (VALUE_SIZE as u32) * max_direct_args as u32,
            3,
        ));
        let args_buf = b.ins().stack_addr(types::I64, args_slot, 0);
        // Registers start as nil: only the tag word needs writing.
        let zero = b.ins().iconst(types::I64, 0);
        for i in 0..nregs as i32 {
            b.ins()
                .store(MemFlags::trusted(), zero, regs, i * VALUE_SIZE);
        }
        if uses_act {
            // `[args, self, nargs, frame]` of this activation: the frame
            // view is the `Frame` inside its `Rc` allocation (after the
            // two counts), null when there is none.
            let args_ptr =
                b.ins()
                    .load(types::I64, MemFlags::trusted(), act, L::ACT_ARGS_PTR as i32);
            b.ins().store(MemFlags::trusted(), args_ptr, ptrs, 0);
            let self_addr = b.ins().iadd_imm(act, L::ACT_SELF as i64);
            b.ins().store(MemFlags::trusted(), self_addr, ptrs, 8);
            let nargs = b
                .ins()
                .uload32(MemFlags::trusted(), act, L::ACT_NARGS as i32);
            b.ins().store(MemFlags::trusted(), nargs, ptrs, 16);
            let frame_rc = b
                .ins()
                .load(types::I64, MemFlags::trusted(), act, L::ACT_FRAME as i32);
            let frame_view = b.ins().iadd_imm(frame_rc, i64::from(OBJECT_FIELDS_PTR_OFF));
            let none = b.ins().icmp_imm(IntCC::Equal, frame_rc, 0);
            let frame = b.ins().select(none, frame_rc, frame_view);
            b.ins().store(MemFlags::trusted(), frame, ptrs, 24);
        }
        b.ins().jump(blocks[0], &[]);

        let mut g = Gen {
            b: &mut b,
            h,
            rt,
            act,
            regs,
            out,
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
        };
        for (i, blk) in f.blocks.iter().enumerate() {
            g.b.switch_to_block(blocks[i]);
            g.states.clone_from(&entry_states[i]);
            for (j, inst) in blk.insts.iter().enumerate() {
                g.inst(i as u32, j as u32, inst, unwinds[i]);
                g.after(inst);
            }
            // Write back the unboxed registers that a successor expects
            // in memory (a different state there), or that a terminator
            // leaving the function reads.
            let at_term = &live[i][blk.insts.len()];
            match &blk.term {
                Term::Jump(t) => g.flush_for_edge(&entry_states[*t as usize], at_term),
                Term::Branch { then, els, .. } => {
                    g.flush_for_edge(&entry_states[*then as usize], at_term);
                    g.flush_for_edge(&entry_states[*els as usize], at_term);
                }
                Term::Return(r) => g.flush(*r),
                _ => g.flush_live(at_term),
            }
            match &blk.term {
                Term::Jump(t) => {
                    g.b.ins().jump(blocks[*t as usize], &[]);
                }
                Term::Branch { cond, then, els } => {
                    let truthy = g.truthy(*cond);
                    g.b.ins().brif(
                        truthy,
                        blocks[*then as usize],
                        &[],
                        blocks[*els as usize],
                        &[],
                    );
                }
                Term::Return(r) => {
                    // Move the value into `out` (which holds nil) and
                    // leave the register nil, then release the rest.
                    let off = Gen::reg_off(*r);
                    for k in [0, 8, 16] {
                        let w =
                            g.b.ins()
                                .load(types::I64, MemFlags::trusted(), regs, off + k);
                        g.b.ins().store(MemFlags::trusted(), w, out, k);
                    }
                    let zero = g.b.ins().iconst(types::I64, 0);
                    g.b.ins().store(MemFlags::trusted(), zero, regs, off);
                    g.states[*r as usize] = State::NonHeap;
                    for k in (0..g.nregs).filter(|&k| heap[k]) {
                        g.release(k as Reg);
                    }
                    let ok = g.b.ins().iconst(types::I32, 0);
                    g.b.ins().jump(exit_quick, &[ok]);
                }
                Term::Raise(_)
                | Term::BreakOut(_)
                | Term::ReturnOut(_)
                | Term::Resume(_)
                | Term::Unreachable => {
                    let fid_v = g.b.ins().iconst(types::I32, i64::from(fid));
                    let blk_v = g.b.ins().iconst(types::I32, i as i64);
                    let call = g.b.ins().call(g.h.term, &[rt, act, fid_v, blk_v, regs]);
                    let status = g.b.inst_results(call)[0];
                    g.b.ins().jump(unwinds[i], &[status]);
                }
            }
        }
        // Unwinding: route a status to the block's handler or out.
        for (i, blk) in f.blocks.iter().enumerate() {
            b.switch_to_block(unwinds[i]);
            let status = b.block_params(unwinds[i])[0];
            match blk.handler {
                Some(h) if h.kind == HandlerKind::Ensure => {
                    b.ins().jump(blocks[h.block as usize], &[]);
                }
                Some(h) => {
                    let is_raise = b.ins().icmp_imm(IntCC::Equal, status, STATUS_RAISE);
                    b.ins()
                        .brif(is_raise, blocks[h.block as usize], &[], exit, &[status]);
                }
                None => {
                    b.ins().jump(exit, &[status]);
                }
            }
        }
        // Exit: release the registers that may hold heap values.
        b.switch_to_block(exit);
        let status = b.block_params(exit)[0];
        for i in 0..nregs {
            if !heap[i as usize] {
                continue;
            }
            let p = b.ins().iadd_imm(regs, i64::from(i) * i64::from(VALUE_SIZE));
            emit_release_ptr(&mut b, drop_value_fn, p);
        }
        b.ins().return_(&[status]);
        b.switch_to_block(exit_quick);
        let status = b.block_params(exit_quick)[0];
        b.ins().return_(&[status]);
        b.seal_all_blocks();
        b.finalize();
        self.module
            .define_function(self.funcs[fid as usize], &mut ctx)
            .map_err(|e| format!("{}: {e:?}\n{}", f.name, ctx.func.display()))?;
        self.module.clear_context(&mut ctx);
        Ok(())
    }

    fn emit_data_and_main(
        &mut self,
        module: &Module,
        call_conv: cranelift_codegen::isa::CallConv,
    ) -> Result<(), String> {
        // The serialized module.
        let bytes = quarz_ir::encode(module);
        let blob_len = bytes.len();
        let blob = self
            .module
            .declare_data("qz_module_blob", Linkage::Local, false, false)
            .map_err(|e| e.to_string())?;
        let mut desc = DataDescription::new();
        desc.define(bytes.into_boxed_slice());
        self.module
            .define_data(blob, &desc)
            .map_err(|e| e.to_string())?;
        // The table of compiled bodies.
        let n = module.functions.len();
        let table = self
            .module
            .declare_data("qz_fn_table", Linkage::Local, false, false)
            .map_err(|e| e.to_string())?;
        let mut desc = DataDescription::new();
        desc.set_align(8);
        // Explicit bytes, not zero-init: relocations cannot apply to .bss.
        desc.define(vec![0u8; 8 * n.max(1)].into_boxed_slice());
        for (i, func) in self.funcs.iter().enumerate() {
            let fref = self.module.declare_func_in_data(*func, &mut desc);
            desc.write_function_addr((8 * i) as u32, fref);
        }
        self.module
            .define_data(table, &desc)
            .map_err(|e| e.to_string())?;
        // main(argc, argv) -> qz_main(blob, len, table, n, argc, argv, layout)
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I32));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I32));
        let main = self
            .module
            .declare_function("main", Linkage::Export, &sig)
            .map_err(|e| e.to_string())?;
        let mut ctx = self.module.make_context();
        ctx.func.signature = sig;
        let mut fbc = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let params = b.block_params(entry).to_vec();
        let blob_gv = self.module.declare_data_in_func(blob, b.func);
        let table_gv = self.module.declare_data_in_func(table, b.func);
        let qz_main = self.module.declare_func_in_func(self.rt.main, b.func);
        let blob_ptr = b.ins().symbol_value(types::I64, blob_gv);
        let table_ptr = b.ins().symbol_value(types::I64, table_gv);
        let len = b.ins().iconst(types::I64, blob_len as i64);
        let count = b.ins().iconst(types::I64, n as i64);
        let layout = b.ins().iconst(types::I64, L::SIGNATURE as i64);
        let vec_layout = b.ins().iconst(types::I64, L::vec_layout_packed() as i64);
        let call = b.ins().call(
            qz_main,
            &[
                blob_ptr, len, table_ptr, count, params[0], params[1], layout, vec_layout,
            ],
        );
        let code = b.inst_results(call)[0];
        b.ins().return_(&[code]);
        b.seal_all_blocks();
        b.finalize();
        self.module
            .define_function(main, &mut ctx)
            .map_err(|e| e.to_string())?;
        self.module.clear_context(&mut ctx);
        Ok(())
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
    if m.native_key.is_some() || (m.overridden && !m.singleton && !m.is_extension) {
        return None;
    }
    m.func
}

/// Bump the reference count of the heap value at `p` (whose tag is known
/// to be a heap tag): the payload's first word points at the allocation,
/// whose first word is the strong count (checked at start-up).
fn rc_increment(b: &mut FunctionBuilder, p: CValue) {
    let rc = b.ins().load(types::I64, MemFlags::trusted(), p, 8);
    let strong = b.ins().load(types::I64, MemFlags::trusted(), rc, 0);
    let bumped = b.ins().iadd_imm(strong, 1);
    b.ins().store(MemFlags::trusted(), bumped, rc, 0);
}

/// Release the value at `p` and leave nil there: nothing for values
/// without a reference count, a decrement when other references remain,
/// the runtime's destructor for the last one.
fn emit_release_ptr(b: &mut FunctionBuilder, drop_value: FuncRef, p: CValue) {
    let tag = b.ins().load(types::I64, MemFlags::trusted(), p, 0);
    let needs = b
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, tag, NEEDS_DROP_FROM);
    let heap = b.create_block();
    let shared = b.create_block();
    let last = b.create_block();
    let cont = b.create_block();
    b.ins().brif(needs, heap, &[], cont, &[]);
    b.switch_to_block(heap);
    let rc = b.ins().load(types::I64, MemFlags::trusted(), p, 8);
    let strong = b.ins().load(types::I64, MemFlags::trusted(), rc, 0);
    let is_last = b.ins().icmp_imm(IntCC::Equal, strong, 1);
    b.ins().brif(is_last, last, &[], shared, &[]);
    b.switch_to_block(shared);
    let lowered = b.ins().iadd_imm(strong, -1);
    b.ins().store(MemFlags::trusted(), lowered, rc, 0);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().store(MemFlags::trusted(), zero, p, 0);
    b.ins().jump(cont, &[]);
    b.switch_to_block(last);
    b.ins().call(drop_value, &[p]);
    b.ins().jump(cont, &[]);
    b.switch_to_block(cont);
}

/// `*dst = *src` where `dst` holds nil: a three-word copy, plus a
/// reference count bump for heap values.
fn emit_clone_ptr(b: &mut FunctionBuilder, dst: CValue, src: CValue) {
    let tag = b.ins().load(types::I64, MemFlags::trusted(), src, 0);
    let w1 = b.ins().load(types::I64, MemFlags::trusted(), src, 8);
    let w2 = b.ins().load(types::I64, MemFlags::trusted(), src, 16);
    b.ins().store(MemFlags::trusted(), tag, dst, 0);
    b.ins().store(MemFlags::trusted(), w1, dst, 8);
    b.ins().store(MemFlags::trusted(), w2, dst, 16);
    let needs = b
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, tag, NEEDS_DROP_FROM);
    let heap = b.create_block();
    let cont = b.create_block();
    b.ins().brif(needs, heap, &[], cont, &[]);
    b.switch_to_block(heap);
    rc_increment(b, src);
    b.ins().jump(cont, &[]);
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

/// Which registers may ever hold a reference-counted value (the others
/// need no release at exit).
fn heap_possible(f: &Function) -> Vec<bool> {
    let mut heap = vec![false; f.nregs as usize];
    let mut mark = |r: Reg| heap[r as usize] = true;
    for blk in &f.blocks {
        for inst in &blk.insts {
            match inst {
                Inst::LoadConst { dst, idx } => {
                    if !matches!(
                        f.consts[*idx as usize],
                        Constant::Nil | Constant::Bool(_) | Constant::Int(_) | Constant::Float(_)
                    ) {
                        mark(*dst);
                    }
                }
                Inst::BinOp { dst, op, .. } => {
                    // Arithmetic may overflow into a BigInt.
                    if !matches!(
                        op,
                        FastOp::Lt
                            | FastOp::Le
                            | FastOp::Gt
                            | FastOp::Ge
                            | FastOp::Eq
                            | FastOp::Ne
                            | FastOp::Cmp
                    ) {
                        mark(*dst);
                    }
                }
                Inst::HasArg { .. }
                | Inst::Not { .. }
                | Inst::IsNil { .. }
                | Inst::IsArray { .. }
                | Inst::IsHash { .. }
                | Inst::IsObject { .. }
                | Inst::Len { .. }
                | Inst::ClassIsA { .. }
                | Inst::ClassIs { .. }
                | Inst::IsA { .. }
                | Inst::Equal { .. }
                | Inst::CaseEq { .. } => {}
                Inst::FieldGetByName { dst, .. } | Inst::HashGetSym { dst, .. } => mark(*dst),
                Inst::Move { dst, .. }
                | Inst::SelfRef { dst }
                | Inst::Arg { dst, .. }
                | Inst::BlockParam { dst }
                | Inst::FrameGet { dst, .. }
                | Inst::FieldGet { dst, .. }
                | Inst::ConstGet { dst, .. }
                | Inst::ClassRef { dst, .. }
                | Inst::VariantSingleton { dst, .. }
                | Inst::Call { dst, .. }
                | Inst::OwnedCall { dst, .. }
                | Inst::As { dst, .. }
                | Inst::MakeBlock { dst, .. }
                | Inst::MethodRef { dst, .. }
                | Inst::SymbolProc { dst, .. }
                | Inst::MakeArray { dst, .. }
                | Inst::MakeHash { dst, .. }
                | Inst::MakeRange { dst, .. }
                | Inst::MakeRegexp { dst, .. }
                | Inst::Interpolate { dst, .. }
                | Inst::ToSym { dst, .. }
                | Inst::ToArray { dst, .. }
                | Inst::ArrayGet { dst, .. }
                | Inst::ArrayGetReg { dst, .. }
                | Inst::ArraySlice { dst, .. }
                | Inst::ArraySliceReg { dst, .. }
                | Inst::ObjectFields { dst, .. }
                | Inst::HashRest { dst, .. }
                | Inst::CatchException { dst }
                | Inst::CatchAny { dst } => mark(*dst),
                Inst::FrameSet { .. }
                | Inst::FieldSet { .. }
                | Inst::ArrayPush { .. }
                | Inst::ClearRegs { .. }
                | Inst::NoMatch { .. } => {}
            }
        }
    }
    heap
}

/// Code generation for one function body.
struct Gen<'a, 'b> {
    b: &'a mut FunctionBuilder<'b>,
    h: Helpers,
    rt: CValue,
    act: CValue,
    regs: CValue,
    out: CValue,
    exit: CBlock,
    scratch: CValue,
    /// Space for the activation of a direct call.
    act_buf: CValue,
    /// Where a directly called body leaves its result.
    out_buf: CValue,
    /// A word for the body address `qz_enter_virtual` returns.
    vbody: CValue,
    /// The signature of compiled bodies, for indirect calls.
    body_sig: cranelift_codegen::ir::SigRef,
    /// `[args, self, nargs]` of this activation (see `qz_act_ptrs`).
    ptrs: CValue,
    /// The argument area of direct calls.
    args_buf: CValue,
    fid: FuncId,
    f: &'a Function,
    methods: &'a [RtMethod],
    functions: &'a [Function],
    classes: &'a [RtClass],
    builtin: &'a RtBuiltin,
    callees: HashMap<FuncId, FuncRef>,
    /// Liveness per block and instruction (see `unbox::liveness`).
    live: &'a [Vec<Vec<bool>>],
    /// What is known about each register here (see `unbox`).
    states: Vec<State>,
    nregs: usize,
}

impl Gen<'_, '_> {
    fn reg_off(r: Reg) -> i32 {
        r as i32 * VALUE_SIZE
    }

    fn tag(&mut self, r: Reg) -> CValue {
        self.b
            .ins()
            .load(types::I64, MemFlags::trusted(), self.regs, Self::reg_off(r))
    }

    fn payload(&mut self, r: Reg) -> CValue {
        self.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            self.regs,
            Self::reg_off(r) + 8,
        )
    }

    fn payload8(&mut self, r: Reg) -> CValue {
        self.b.ins().uload8(
            types::I64,
            MemFlags::trusted(),
            self.regs,
            Self::reg_off(r) + 8,
        )
    }

    /// Truthiness of a register: not nil and not false.
    fn truthy(&mut self, r: Reg) -> CValue {
        match self.states[r as usize] {
            State::Bool => return self.b.use_var(self.bvar(r)),
            State::Int | State::Float => return self.b.ins().iconst(types::I8, 1),
            _ => {}
        }
        let tag = self.tag(r);
        let p = self.payload8(r);
        let is_nil = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_NIL);
        let is_bool = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_BOOL);
        let is_zero = self.b.ins().icmp_imm(IntCC::Equal, p, 0);
        let is_false = self.b.ins().band(is_bool, is_zero);
        let falsy = self.b.ins().bor(is_nil, is_false);
        let one = self.b.ins().iconst(types::I8, 1);
        self.b.ins().bxor(falsy, one)
    }

    /// Make sure `dst` holds no reference-counted value before an inline
    /// store overwrites it.
    fn release(&mut self, dst: Reg) {
        if !self.states[dst as usize].needs_release() {
            return;
        }
        let p = self
            .b
            .ins()
            .iadd_imm(self.regs, i64::from(Self::reg_off(dst)));
        emit_release_ptr(self.b, self.h.drop_value, p);
    }

    /// `regs[dst] = *src`: inline for values without reference counts,
    /// through the runtime for the others.
    fn clone_from(&mut self, dst: Reg, src: CValue) {
        self.release(dst);
        let d = self
            .b
            .ins()
            .iadd_imm(self.regs, i64::from(Self::reg_off(dst)));
        emit_clone_ptr(self.b, d, src);
    }

    /// `*dst = regs[src]` where `dst` holds nil: inline for values without
    /// reference counts, through the runtime for the others.
    /// Whether `src`, read by instruction `index` of `block` (`inst`),
    /// can be moved out instead of copied: it may hold a heap value, this
    /// is its only read in the instruction, and nothing reads it after.
    fn movable(&self, inst: &Inst, src: Reg, block: u32, index: u32) -> bool {
        self.states[src as usize] == State::Unknown
            && inst.uses().iter().filter(|&&u| u == src).count() == 1
            && !self.live[block as usize]
                .get(index as usize + 1)
                .is_some_and(|l| l[src as usize])
    }

    /// `*dst = regs[src]`, the value moved out of the register (whose
    /// home becomes nil): no count increment now, no release later.
    fn move_reg_to_ptr(&mut self, dst: CValue, src: Reg) {
        let src_ptr = self
            .b
            .ins()
            .iadd_imm(self.regs, i64::from(Self::reg_off(src)));
        for k in [0, 8, 16] {
            let w = self
                .b
                .ins()
                .load(types::I64, MemFlags::trusted(), src_ptr, k);
            self.b.ins().store(MemFlags::trusted(), w, dst, k);
        }
        self.store_tag(src, TAG_NIL);
    }

    /// After a slow path that copied `src` instead of moving it: release
    /// the register so that both paths leave its home nil.
    fn drop_moved(&mut self, src: Reg) {
        self.release(src);
        self.store_tag(src, TAG_NIL);
    }

    fn clone_reg_to_ptr(&mut self, dst: CValue, src: Reg) {
        // An unboxed register is written from its variable (its home
        // may be stale); a register that cannot hold a heap value is
        // copied without the count check.
        match self.states[src as usize] {
            State::Int => {
                let v = self.b.use_var(self.ivar(src));
                let t = self.b.ins().iconst(types::I64, TAG_INT);
                self.b.ins().store(MemFlags::trusted(), t, dst, 0);
                self.b.ins().store(MemFlags::trusted(), v, dst, 8);
            }
            State::Float => {
                let v = self.b.use_var(self.fvar(src));
                let bits = self.b.ins().bitcast(types::I64, MemFlags::new(), v);
                let t = self.b.ins().iconst(types::I64, TAG_FLOAT);
                self.b.ins().store(MemFlags::trusted(), t, dst, 0);
                self.b.ins().store(MemFlags::trusted(), bits, dst, 8);
            }
            State::Bool => {
                let v = self.b.use_var(self.bvar(src));
                let t = self.b.ins().iconst(types::I64, TAG_BOOL);
                self.b.ins().store(MemFlags::trusted(), t, dst, 0);
                let zero = self.b.ins().iconst(types::I64, 0);
                self.b.ins().store(MemFlags::trusted(), zero, dst, 8);
                self.b.ins().store(MemFlags::trusted(), v, dst, 8);
            }
            State::NonHeap => {
                let src_ptr = self
                    .b
                    .ins()
                    .iadd_imm(self.regs, i64::from(Self::reg_off(src)));
                for k in [0, 8, 16] {
                    let w = self
                        .b
                        .ins()
                        .load(types::I64, MemFlags::trusted(), src_ptr, k);
                    self.b.ins().store(MemFlags::trusted(), w, dst, k);
                }
            }
            State::Unknown => {
                let src_ptr = self
                    .b
                    .ins()
                    .iadd_imm(self.regs, i64::from(Self::reg_off(src)));
                emit_clone_ptr(self.b, dst, src_ptr);
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
        body: FuncRef,
        callee: FuncId,
        file: u32,
        recv: Option<Reg>,
        provided: u64,
        slots: usize,
        dst: Reg,
        unwind: CBlock,
    ) {
        let act = self.act_buf;
        let release_args = |g: &mut Self| {
            for k in 0..slots {
                let p =
                    g.b.ins()
                        .iadd_imm(g.args_buf, (k as i64) * i64::from(VALUE_SIZE));
                g.release_ptr(p);
            }
        };
        // Native stack check against the running task's limit.
        let sp = self.b.ins().get_stack_pointer(types::I64);
        let limit_cell = self.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            self.rt,
            L::HOT_LIMIT_PTR as i32,
        );
        let limit = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), limit_cell, 0);
        let exhausted = self.b.ins().icmp(IntCC::UnsignedLessThan, sp, limit);
        let overflow = self.b.create_block();
        let build = self.b.create_block();
        self.b.ins().brif(exhausted, overflow, &[], build, &[]);
        self.b.switch_to_block(overflow);
        let call = self.b.ins().call(self.h.stack_overflow, &[self.rt]);
        let status = self.b.inst_results(call)[0];
        release_args(self);
        self.b.ins().jump(unwind, &[status]);
        self.b.switch_to_block(build);
        // The activation.
        let fid_v = self.b.ins().iconst(types::I32, i64::from(callee));
        self.b
            .ins()
            .store(MemFlags::trusted(), fid_v, act, L::ACT_FID as i32);
        let task = self.b.ins().load(
            types::I32,
            MemFlags::trusted(),
            self.act,
            L::ACT_TASK as i32,
        );
        self.b
            .ins()
            .store(MemFlags::trusted(), task, act, L::ACT_TASK as i32);
        let zero32 = self.b.ins().iconst(types::I32, 0);
        self.b
            .ins()
            .store(MemFlags::trusted(), zero32, act, L::ACT_LINE as i32);
        let file_v = self.b.ins().iconst(types::I32, i64::from(file));
        self.b
            .ins()
            .store(MemFlags::trusted(), file_v, act, L::ACT_FILE as i32);
        let self_dst = self.b.ins().iadd_imm(act, L::ACT_SELF as i64);
        match recv {
            Some(r) => self.clone_reg_to_ptr(self_dst, r),
            None => {
                let caller_self = self.b.ins().iadd_imm(self.act, L::ACT_SELF as i64);
                emit_clone_ptr(self.b, self_dst, caller_self);
            }
        }
        let zero = self.b.ins().iconst(types::I64, 0);
        for off in [
            L::ACT_FRAME,
            L::ACT_BLOCK,
            L::ACT_METHOD_TAG,
            L::ACT_CLOSURE_TAG,
            L::ACT_YIELD_CALLER,
        ] {
            self.b
                .ins()
                .store(MemFlags::trusted(), zero, act, off as i32);
        }
        let provided_v = self.b.ins().iconst(types::I64, provided as i64);
        self.b
            .ins()
            .store(MemFlags::trusted(), provided_v, act, L::ACT_PROVIDED as i32);
        self.b.ins().store(
            MemFlags::trusted(),
            self.args_buf,
            act,
            L::ACT_ARGS_PTR as i32,
        );
        let nargs_v = self.b.ins().iconst(types::I32, slots as i64);
        self.b
            .ins()
            .store(MemFlags::trusted(), nargs_v, act, L::ACT_NARGS as i32);
        // Push it on the call stack.
        let len = self.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            self.rt,
            L::HOT_STACK_LEN as i32,
        );
        let cap = self.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            self.rt,
            L::HOT_STACK_CAP as i32,
        );
        let full = self.b.ins().icmp(IntCC::Equal, len, cap);
        let push_slow = self.b.create_block();
        let push_fast = self.b.create_block();
        let pushed = self.b.create_block();
        self.b.ins().brif(full, push_slow, &[], push_fast, &[]);
        self.b.switch_to_block(push_slow);
        self.b.ins().call(self.h.push_call, &[self.rt, act]);
        self.b.ins().jump(pushed, &[]);
        self.b.switch_to_block(push_fast);
        let stack = self.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            self.rt,
            L::HOT_STACK_PTR as i32,
        );
        let slot_off = self.b.ins().ishl_imm(len, 3);
        let slot = self.b.ins().iadd(stack, slot_off);
        self.b.ins().store(MemFlags::trusted(), act, slot, 0);
        let len1 = self.b.ins().iadd_imm(len, 1);
        self.b
            .ins()
            .store(MemFlags::trusted(), len1, self.rt, L::HOT_STACK_LEN as i32);
        self.b.ins().jump(pushed, &[]);
        self.b.switch_to_block(pushed);
        // The body.
        self.b
            .ins()
            .store(MemFlags::trusted(), zero, self.out_buf, 0);
        let call = self.b.ins().call(body, &[self.rt, act, self.out_buf]);
        let status = self.b.inst_results(call)[0];
        // Leave: inline when the status is OK and the callee cached no
        // block caller, through the runtime otherwise.
        let cache = self.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            act,
            L::ACT_YIELD_CALLER as i32,
        );
        let not_ok = self.b.ins().icmp_imm(IntCC::NotEqual, status, 0);
        let cached = self.b.ins().icmp_imm(IntCC::NotEqual, cache, 0);
        let slow = self.b.ins().bor(not_ok, cached);
        let leave_slow = self.b.create_block();
        let leave_fast = self.b.create_block();
        let done = self.b.create_block();
        self.b.append_block_param(done, types::I32);
        self.b.ins().brif(slow, leave_slow, &[], leave_fast, &[]);
        self.b.switch_to_block(leave_slow);
        let d = self.i32(dst);
        let none = self.i32(u32::MAX);
        let call = self.b.ins().call(
            self.h.leave,
            &[self.rt, act, status, self.out_buf, self.regs, d, none],
        );
        let st = self.b.inst_results(call)[0];
        self.b.ins().jump(done, &[st]);
        self.b.switch_to_block(leave_fast);
        // Pop (the entry is the top one unless tasks interleaved).
        let len = self.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            self.rt,
            L::HOT_STACK_LEN as i32,
        );
        let stack = self.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            self.rt,
            L::HOT_STACK_PTR as i32,
        );
        let len0 = self.b.ins().iadd_imm(len, -1);
        let top_off = self.b.ins().ishl_imm(len0, 3);
        let top_slot = self.b.ins().iadd(stack, top_off);
        let top = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), top_slot, 0);
        let is_top = self.b.ins().icmp(IntCC::Equal, top, act);
        let pop_fast = self.b.create_block();
        let pop_slow = self.b.create_block();
        let popped = self.b.create_block();
        self.b.ins().brif(is_top, pop_fast, &[], pop_slow, &[]);
        self.b.switch_to_block(pop_fast);
        self.b
            .ins()
            .store(MemFlags::trusted(), len0, self.rt, L::HOT_STACK_LEN as i32);
        self.b.ins().jump(popped, &[]);
        self.b.switch_to_block(pop_slow);
        self.b.ins().call(self.h.pop_call, &[self.rt, act]);
        self.b.ins().jump(popped, &[]);
        self.b.switch_to_block(popped);
        // Tear down: only `self` can hold a reference.
        self.release_ptr(self_dst);
        // The result moves into `dst`; `out` is nil again.
        self.release(dst);
        for k in [0, 8, 16] {
            let w = self
                .b
                .ins()
                .load(types::I64, MemFlags::trusted(), self.out_buf, k);
            self.b
                .ins()
                .store(MemFlags::trusted(), w, self.regs, Self::reg_off(dst) + k);
        }
        self.b
            .ins()
            .store(MemFlags::trusted(), zero, self.out_buf, 0);
        let ok = self.b.ins().iconst(types::I32, 0);
        self.b.ins().jump(done, &[ok]);
        self.b.switch_to_block(done);
        let status = self.b.block_params(done)[0];
        release_args(self);
        self.check(status, unwind);
    }

    /// Release the value at `p` (leaving nil) when it is reference counted.
    fn release_ptr(&mut self, p: CValue) {
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
    fn inline_push(&mut self, arr_ptr: CValue, src: Reg, slow: CBlock, move_src: bool) {
        let check_b = self.b.create_block();
        let fast = self.b.create_block();
        let tag = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), arr_ptr, 0);
        let is_arr = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
        self.b.ins().brif(is_arr, check_b, &[], slow, &[]);
        self.b.switch_to_block(check_b);
        let rc = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), arr_ptr, 8);
        let strong = self.b.ins().load(types::I64, MemFlags::trusted(), rc, 0);
        let weak = self.b.ins().load(types::I64, MemFlags::trusted(), rc, 8);
        let (kind, ptr, len, cap) = self.array_view_at(rc);
        let unique_s = self.b.ins().icmp_imm(IntCC::Equal, strong, 1);
        let unique_w = self.b.ins().icmp_imm(IntCC::Equal, weak, 1);
        let room = self.b.ins().icmp(IntCC::UnsignedLessThan, len, cap);
        let ok = self.b.ins().band(unique_s, unique_w);
        let ok = self.b.ins().band(ok, room);
        let src_state = self.states[src as usize];
        let src_tag = match src_state {
            State::Int => self.b.ins().iconst(types::I64, TAG_INT),
            State::Float => self.b.ins().iconst(types::I64, TAG_FLOAT),
            State::Bool => self.b.ins().iconst(types::I64, TAG_BOOL),
            _ => self.tag(src),
        };
        let kind_values = self.b.ins().icmp_imm(IntCC::Equal, kind, 0);
        let kind_ints = self.b.ins().icmp_imm(IntCC::Equal, kind, 1);
        let kind_floats = self.b.ins().icmp_imm(IntCC::Equal, kind, 2);
        let src_int = self.b.ins().icmp_imm(IntCC::Equal, src_tag, TAG_INT);
        let src_float = self.b.ins().icmp_imm(IntCC::Equal, src_tag, TAG_FLOAT);
        let ints_ok = self.b.ins().band(kind_ints, src_int);
        let floats_ok = self.b.ins().band(kind_floats, src_float);
        let fits = self.b.ins().bor(kind_values, ints_ok);
        let fits = self.b.ins().bor(fits, floats_ok);
        let ok = self.b.ins().band(ok, fits);
        self.b.ins().brif(ok, fast, &[], slow, &[]);
        self.b.switch_to_block(fast);
        let boxed_b = self.b.create_block();
        let raw_b = self.b.create_block();
        let done_b = self.b.create_block();
        self.b.ins().brif(kind_values, boxed_b, &[], raw_b, &[]);
        self.b.switch_to_block(boxed_b);
        let off = self.b.ins().imul_imm(len, i64::from(VALUE_SIZE));
        let slot = self.b.ins().iadd(ptr, off);
        if move_src {
            self.move_reg_to_ptr(slot, src);
        } else {
            self.clone_reg_to_ptr(slot, src);
        }
        self.b.ins().jump(done_b, &[]);
        self.b.switch_to_block(raw_b);
        let off = self.b.ins().imul_imm(len, 8);
        let slot = self.b.ins().iadd(ptr, off);
        let word = match src_state {
            State::Int => self.b.use_var(self.ivar(src)),
            State::Float => {
                let f = self.b.use_var(self.fvar(src));
                self.b.ins().bitcast(types::I64, MemFlags::new(), f)
            }
            _ => self.payload(src),
        };
        self.b.ins().store(MemFlags::trusted(), word, slot, 0);
        self.b.ins().jump(done_b, &[]);
        self.b.switch_to_block(done_b);
        let len1 = self.b.ins().iadd_imm(len, 1);
        let data = self.b.ins().iadd_imm(rc, i64::from(OBJECT_FIELDS_PTR_OFF));
        let vec = self.b.ins().iadd_imm(data, L::ARRAY_VEC_OFF as i64);
        self.b
            .ins()
            .store(MemFlags::trusted(), len1, vec, L::vec_layout().len as i32);
    }

    fn array_view(&mut self, arr: Reg) -> (CValue, CValue, CValue, CValue) {
        let rc = self.payload(arr);
        self.array_view_at(rc)
    }

    /// The storage kind, element pointer, length and capacity of the
    /// array whose allocation `rc` points at.
    fn array_view_at(&mut self, rc: CValue) -> (CValue, CValue, CValue, CValue) {
        let data = self.b.ins().iadd_imm(rc, i64::from(OBJECT_FIELDS_PTR_OFF));
        let kind = self.b.ins().uload8(
            types::I64,
            MemFlags::trusted(),
            data,
            L::ARRAY_KIND_OFF as i32,
        );
        let vec = self.b.ins().iadd_imm(data, L::ARRAY_VEC_OFF as i64);
        let l = L::vec_layout();
        let ptr = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), vec, l.ptr as i32);
        let len = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), vec, l.len as i32);
        let cap = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), vec, l.cap as i32);
        (kind, ptr, len, cap)
    }

    /// The address of field `index` of the object in `obj` (whose tag is
    /// known to be an object's): the payload points at the allocation,
    /// the object's first word at the fields.
    fn field_addr(&mut self, obj: Reg, index: u32) -> CValue {
        let rc = self.payload(obj);
        let fields = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), rc, OBJECT_FIELDS_PTR_OFF);
        self.b
            .ins()
            .iadd_imm(fields, i64::from(index) * i64::from(VALUE_SIZE))
    }

    /// The address of `slot` in the frame `depth` levels up from this
    /// activation's frame, branching to `slow` when there is no such
    /// frame or the slot is beyond its size (layout: `Frame`).
    fn frame_slot_addr(&mut self, depth: u32, slot: u32, slow: CBlock) -> CValue {
        let mut frame = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), self.ptrs, 24);
        for level in 0..=depth {
            let none = self.b.ins().icmp_imm(IntCC::Equal, frame, 0);
            let next = self.b.create_block();
            self.b.ins().brif(none, slow, &[], next, &[]);
            self.b.switch_to_block(next);
            if level < depth {
                frame = self
                    .b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), frame, 16);
            }
        }
        let nslots = self.b.ins().uload32(MemFlags::trusted(), frame, 8);
        let in_range = self
            .b
            .ins()
            .icmp_imm(IntCC::UnsignedGreaterThan, nslots, i64::from(slot));
        let ok = self.b.create_block();
        self.b.ins().brif(in_range, ok, &[], slow, &[]);
        self.b.switch_to_block(ok);
        let slots = self.b.ins().load(types::I64, MemFlags::trusted(), frame, 0);
        self.b
            .ins()
            .iadd_imm(slots, i64::from(slot) * i64::from(VALUE_SIZE))
    }

    fn ivar(&self, r: Reg) -> Variable {
        Variable::from_u32((r as usize) as u32)
    }

    fn fvar(&self, r: Reg) -> Variable {
        Variable::from_u32((self.nregs + r as usize) as u32)
    }

    fn bvar(&self, r: Reg) -> Variable {
        Variable::from_u32((2 * self.nregs + r as usize) as u32)
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
                let v = self.payload8(r);
                let v = self.b.ins().ireduce(types::I8, v);
                self.b.def_var(self.bvar(r), v);
            }
        }
        if let Inst::Len { dst, .. } = inst {
            let v = self.payload(*dst);
            self.b.def_var(self.ivar(*dst), v);
        }
    }

    /// Give up on this function's speculation: the interpreter runs the
    /// rest from instruction `index` of `block`, and the function exits
    /// with its status. Emission continues in a fresh (unreachable) block.
    fn deopt(&mut self, block: u32, index: u32) {
        let live = self.live[block as usize][index as usize].clone();
        self.flush_live(&live);
        let fid = self.b.ins().iconst(types::I32, i64::from(self.fid));
        let blk = self.b.ins().iconst(types::I32, i64::from(block));
        let i = self.b.ins().iconst(types::I32, i64::from(index));
        let call = self.b.ins().call(
            self.h.resume,
            &[self.rt, self.act, fid, blk, i, self.regs, self.out],
        );
        let status = self.b.inst_results(call)[0];
        self.b.ins().jump(self.exit, &[status]);
        let dead = self.b.create_block();
        self.b.switch_to_block(dead);
    }

    /// The unboxed value of `r`, statically an Int or a Float: from its
    /// variable when the state says so, else from memory after a tag
    /// check that fails into the interpreter.
    fn get_num(&mut self, r: Reg, n: Num, block: u32, index: u32) -> CValue {
        let st = self.states[r as usize];
        match (n, st) {
            (Num::Int, State::Int) => return self.b.use_var(self.ivar(r)),
            (Num::Float, State::Float) => return self.b.use_var(self.fvar(r)),
            _ => {}
        }
        let tag = self.tag(r);
        let want = if n == Num::Int { TAG_INT } else { TAG_FLOAT };
        let is = self.b.ins().icmp_imm(IntCC::Equal, tag, want);
        let ok = self.b.create_block();
        let bad = self.b.create_block();
        self.b.ins().brif(is, ok, &[], bad, &[]);
        self.b.switch_to_block(bad);
        self.deopt(block, index);
        self.b.switch_to_block(ok);
        let p = self.payload(r);
        match n {
            Num::Int => {
                self.b.def_var(self.ivar(r), p);
                self.states[r as usize] = State::Int;
                p
            }
            Num::Float => {
                let v = self.b.ins().bitcast(types::F64, MemFlags::new(), p);
                self.b.def_var(self.fvar(r), v);
                self.states[r as usize] = State::Float;
                v
            }
        }
    }

    /// `regs[dst] = Int(v)`: the variable, and the boxed home.
    /// `regs[dst] = Int(v)`, in the variable only: the home is written
    /// when something reads it (`flush`). A home that may hold a heap
    /// value is released and set to nil, so it never dangles.
    fn store_int(&mut self, dst: Reg, v: CValue) {
        self.b.def_var(self.ivar(dst), v);
        self.unbox(dst, State::Int);
    }

    fn store_float(&mut self, dst: Reg, v: CValue) {
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
                let bits = self.b.ins().bitcast(types::I64, MemFlags::new(), v);
                self.store_tag(r, TAG_FLOAT);
                self.store_payload(r, bits);
            }
            State::Bool => {
                let v = self.b.use_var(self.bvar(r));
                self.store_tag(r, TAG_BOOL);
                // An I8, stored as the payload's first byte.
                self.b
                    .ins()
                    .store(MemFlags::trusted(), v, self.regs, Self::reg_off(r) + 8);
            }
            State::Unknown | State::NonHeap => {}
        }
    }

    /// Write back every unboxed register that is live.
    fn flush_live(&mut self, live: &[bool]) {
        for r in (0..self.nregs).filter(|&r| live[r]) {
            self.flush(r as Reg);
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

    fn i32(&mut self, v: u32) -> CValue {
        self.b.ins().iconst(types::I32, i64::from(v))
    }

    /// Branch to `unwind` when a status is not OK.
    fn check(&mut self, status: CValue, unwind: CBlock) {
        let cont = self.b.create_block();
        self.b.ins().brif(status, unwind, &[status], cont, &[]);
        self.b.switch_to_block(cont);
    }

    /// Whether a call can go straight to the method (a native, or a body
    /// with positional parameters) without dynamic dispatch.
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
        unwind: CBlock,
    ) {
        let (nparams, has_block) = {
            let m = &self.methods[mid as usize];
            (m.params.len(), m.has_block)
        };
        let mut provided: u64 = 0;
        let mut slots = 0usize;
        for (k, r) in args.iter().enumerate() {
            let p = self
                .b
                .ins()
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
                .ins()
                .iadd_imm(self.args_buf, (slots as i64) * i64::from(VALUE_SIZE));
            let zero = self.b.ins().iconst(types::I64, 0);
            self.b.ins().store(MemFlags::trusted(), zero, p, 0);
            slots += 1;
        }
        if has_block {
            let p = self
                .b
                .ins()
                .iadd_imm(self.args_buf, (slots as i64) * i64::from(VALUE_SIZE));
            match blk {
                Some(r) => {
                    self.clone_reg_to_ptr(p, r);
                    if nparams < 64 {
                        provided |= 1 << nparams;
                    }
                }
                None => {
                    let zero = self.b.ins().iconst(types::I64, 0);
                    self.b.ins().store(MemFlags::trusted(), zero, p, 0);
                }
            }
            slots += 1;
        }
        let mid_v = self.i32(mid);
        let recv_v = self.i32(recv.unwrap_or(u32::MAX));
        let nparams_v = self.i32(nparams as u32);
        let blk_v = self.i32(blk.unwrap_or(u32::MAX));
        let provided_v = self.b.ins().iconst(types::I64, provided as i64);
        let d = self.i32(dst);
        let call = self.b.ins().call(
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
        );
        let status = self.b.inst_results(call)[0];
        let entered = self.b.create_block();
        let not_entered = self.b.create_block();
        let done = self.b.create_block();
        let failed = self.b.create_block();
        let cont = self.b.create_block();
        let is_ok = self.b.ins().icmp_imm(IntCC::Equal, status, 0);
        self.b.ins().brif(is_ok, entered, &[], not_entered, &[]);
        self.b.switch_to_block(not_entered);
        let is_done = self.b.ins().icmp_imm(IntCC::Equal, status, 2);
        self.b.ins().brif(is_done, done, &[], failed, &[]);
        // On failure nothing was built: release the area.
        self.b.switch_to_block(failed);
        for k in 0..slots {
            let p = self
                .b
                .ins()
                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
            self.release_ptr(p);
        }
        self.b.ins().jump(unwind, &[status]);
        // The runtime ran the call and emptied the area.
        self.b.switch_to_block(done);
        self.b.ins().jump(cont, &[]);
        // Call the body, finish, release the parameters.
        self.b.switch_to_block(entered);
        let zero = self.b.ins().iconst(types::I64, 0);
        self.b
            .ins()
            .store(MemFlags::trusted(), zero, self.out_buf, 0);
        let body = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), self.vbody, 0);
        let call =
            self.b
                .ins()
                .call_indirect(self.body_sig, body, &[self.rt, self.act_buf, self.out_buf]);
        let status = self.b.inst_results(call)[0];
        let call = self.b.ins().call(
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
        );
        let status = self.b.inst_results(call)[0];
        for k in 0..slots {
            let p = self
                .b
                .ins()
                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
            self.release_ptr(p);
        }
        self.check(status, unwind);
        self.b.ins().jump(cont, &[]);
        self.b.switch_to_block(cont);
    }

    fn store_tag(&mut self, dst: Reg, tag: i64) {
        let t = self.b.ins().iconst(types::I64, tag);
        self.b
            .ins()
            .store(MemFlags::trusted(), t, self.regs, Self::reg_off(dst));
    }

    fn store_payload(&mut self, dst: Reg, v: CValue) {
        self.b
            .ins()
            .store(MemFlags::trusted(), v, self.regs, Self::reg_off(dst) + 8);
    }

    /// Store a boolean (an I8 value) as a `Bool`.
    fn store_bool(&mut self, dst: Reg, v: CValue) {
        self.b.def_var(self.bvar(dst), v);
        self.unbox(dst, State::Bool);
    }

    /// Store a boolean to the register's home (for a path of a generic
    /// operation, whose result stays boxed).
    fn store_bool_home(&mut self, dst: Reg, v: CValue) {
        self.release(dst);
        self.store_tag(dst, TAG_BOOL);
        self.b
            .ins()
            .store(MemFlags::trusted(), v, self.regs, Self::reg_off(dst) + 8);
    }

    /// Delegate the instruction to the runtime and check its status.
    fn exec(&mut self, block: u32, inst: u32, unwind: CBlock) {
        let entry = self.h.exec;
        self.exec_via(entry, block, inst, unwind);
    }

    /// Delegate the instruction to a runtime entry with `qz_exec`'s
    /// signature (a dedicated one for some instructions).
    fn exec_via(&mut self, entry: FuncRef, block: u32, inst: u32, unwind: CBlock) {
        let fid = self.b.ins().iconst(types::I32, i64::from(self.fid));
        let blk = self.b.ins().iconst(types::I32, i64::from(block));
        let i = self.b.ins().iconst(types::I32, i64::from(inst));
        let call = self
            .b
            .ins()
            .call(entry, &[self.rt, self.act, fid, blk, i, self.regs]);
        let status = self.b.inst_results(call)[0];
        self.check(status, unwind);
    }

    fn inst(&mut self, block: u32, index: u32, inst: &Inst, unwind: CBlock) {
        // Anything that reads register homes (the runtime, mostly) sees
        // the live unboxed registers written back first; the typed
        // arithmetic below works on the variables.
        let typed = matches!(inst, Inst::BinOp { .. })
            && unbox::bin_types(inst, self.methods, self.builtin).is_some()
            && !unbox::float_mod(inst);
        let has_handler = self.f.blocks[block as usize].handler.is_some();
        if !typed && (!unbox::reads_no_home(inst) || (has_handler && unbox::may_unwind(inst))) {
            let live = self.live[block as usize][index as usize].clone();
            self.flush_live(&live);
        }
        match inst {
            Inst::Move { dst, src } => {
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
                        // A plain copy: nothing to count on either side.
                        self.release(*dst);
                        let t = self.tag(*src);
                        let p = self.payload(*src);
                        self.b
                            .ins()
                            .store(MemFlags::trusted(), t, self.regs, Self::reg_off(*dst));
                        self.store_payload(*dst, p);
                    }
                    State::Unknown => {
                        let s = self
                            .b
                            .ins()
                            .iadd_imm(self.regs, i64::from(Self::reg_off(*src)));
                        self.clone_from(*dst, s);
                    }
                }
            }
            Inst::LoadConst { dst, idx } => match &self.f.consts[*idx as usize] {
                Constant::Nil => {
                    self.release(*dst);
                    self.store_tag(*dst, TAG_NIL);
                }
                Constant::Bool(v) => {
                    let v = self.b.ins().iconst(types::I8, i64::from(*v));
                    self.store_bool(*dst, v);
                }
                Constant::Int(i) => {
                    let v = self.b.ins().iconst(types::I64, *i);
                    self.store_int(*dst, v);
                }
                Constant::Float(f) => {
                    let v = self.b.ins().f64const(*f);
                    self.store_float(*dst, v);
                }
                // A short string is the three words of its value.
                Constant::Str(text) if quarz_vm::value::ShortStr::new(text).is_some() => {
                    let v = quarz_vm::value::Value::str(text);
                    // SAFETY: a short string has no heap payload: its
                    // three words are the whole value (and need no drop).
                    let words: [u64; 3] = unsafe {
                        std::ptr::read(&v as *const quarz_vm::value::Value as *const [u64; 3])
                    };
                    std::mem::forget(v);
                    self.release(*dst);
                    for (k, w) in words.iter().enumerate() {
                        let c = self.b.ins().iconst(types::I64, *w as i64);
                        self.b.ins().store(
                            MemFlags::trusted(),
                            c,
                            self.regs,
                            Self::reg_off(*dst) + 8 * k as i32,
                        );
                    }
                }
                // A longer string or a symbol: cloned from the function's pool.
                Constant::Str(_) | Constant::Symbol(_) => {
                    let fid = self.i32(self.fid);
                    let i = self.i32(*idx);
                    let d = self.i32(*dst);
                    self.b
                        .ins()
                        .call(self.h.load_const, &[self.rt, fid, i, self.regs, d]);
                }
                _ => self.exec(block, index, unwind),
            },
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
                                    self.b.ins().sadd_overflow(x, y)
                                } else {
                                    self.b.ins().ssub_overflow(x, y)
                                };
                                let ok = self.b.create_block();
                                let bad = self.b.create_block();
                                self.b.ins().brif(overflow, bad, &[], ok, &[]);
                                self.b.switch_to_block(bad);
                                self.deopt(block, index);
                                self.b.switch_to_block(ok);
                                r
                            }
                            FastOp::Mul => {
                                let (r, overflow) = self.b.ins().smul_overflow(x, y);
                                let ok = self.b.create_block();
                                let bad = self.b.create_block();
                                self.b.ins().brif(overflow, bad, &[], ok, &[]);
                                self.b.switch_to_block(bad);
                                self.deopt(block, index);
                                self.b.switch_to_block(ok);
                                r
                            }
                            _ => {
                                // Division by zero and MIN / -1 go to the
                                // interpreter (an error, or a BigInt).
                                let y_zero = self.b.ins().icmp_imm(IntCC::Equal, y, 0);
                                let x_min = self.b.ins().icmp_imm(IntCC::Equal, x, i64::MIN);
                                let y_m1 = self.b.ins().icmp_imm(IntCC::Equal, y, -1);
                                let min_case = self.b.ins().band(x_min, y_m1);
                                let bad_cond = self.b.ins().bor(y_zero, min_case);
                                let ok = self.b.create_block();
                                let bad = self.b.create_block();
                                self.b.ins().brif(bad_cond, bad, &[], ok, &[]);
                                self.b.switch_to_block(bad);
                                self.deopt(block, index);
                                self.b.switch_to_block(ok);
                                // Floor semantics, as in Ruby.
                                let rem = self.b.ins().srem(x, y);
                                let nonzero = self.b.ins().icmp_imm(IntCC::NotEqual, rem, 0);
                                let y_neg = self.b.ins().icmp_imm(IntCC::SignedLessThan, y, 0);
                                if *op == FastOp::Div {
                                    let q = self.b.ins().sdiv(x, y);
                                    let x_neg = self.b.ins().icmp_imm(IntCC::SignedLessThan, x, 0);
                                    let differ = self.b.ins().bxor(x_neg, y_neg);
                                    let adjust = self.b.ins().band(nonzero, differ);
                                    let adjust = self.b.ins().uextend(types::I64, adjust);
                                    self.b.ins().isub(q, adjust)
                                } else {
                                    let r_neg =
                                        self.b.ins().icmp_imm(IntCC::SignedLessThan, rem, 0);
                                    let differ = self.b.ins().bxor(r_neg, y_neg);
                                    let adjust = self.b.ins().band(nonzero, differ);
                                    let zero = self.b.ins().iconst(types::I64, 0);
                                    let add = self.b.ins().select(adjust, y, zero);
                                    self.b.ins().iadd(rem, add)
                                }
                            }
                        };
                        self.store_int(*dst, r);
                    }
                    Some(Num::Float) => {
                        let xf = if t.lhs == Num::Int {
                            self.b.ins().fcvt_from_sint(types::F64, x)
                        } else {
                            x
                        };
                        let yf = if t.rhs == Num::Int {
                            self.b.ins().fcvt_from_sint(types::F64, y)
                        } else {
                            y
                        };
                        let r = match op {
                            FastOp::Add => self.b.ins().fadd(xf, yf),
                            FastOp::Sub => self.b.ins().fsub(xf, yf),
                            FastOp::Mul => self.b.ins().fmul(xf, yf),
                            _ => self.b.ins().fdiv(xf, yf),
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
                            self.b.ins().icmp(cc, x, y)
                        } else {
                            let xf = if t.lhs == Num::Int {
                                self.b.ins().fcvt_from_sint(types::F64, x)
                            } else {
                                x
                            };
                            let yf = if t.rhs == Num::Int {
                                self.b.ins().fcvt_from_sint(types::F64, y)
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
                            self.b.ins().fcmp(cc, xf, yf)
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
                let a = self.b.ins().icmp_imm(IntCC::Equal, tl, TAG_INT);
                let c = self.b.ins().icmp_imm(IntCC::Equal, tr, TAG_INT);
                let both = self.b.ins().band(a, c);
                let fast_blk = self.b.create_block();
                let not_int = self.b.create_block();
                let slow_blk = self.b.create_block();
                let cont = self.b.create_block();
                self.b.ins().brif(both, fast_blk, &[], not_int, &[]);
                // Both floats: inline floating-point arithmetic.
                self.b.switch_to_block(not_int);
                let fa = self.b.ins().icmp_imm(IntCC::Equal, tl, TAG_FLOAT);
                let fc = self.b.ins().icmp_imm(IntCC::Equal, tr, TAG_FLOAT);
                let both_f = self.b.ins().band(fa, fc);
                let float_blk = self.b.create_block();
                self.b.ins().brif(both_f, float_blk, &[], slow_blk, &[]);
                self.b.switch_to_block(float_blk);
                let xb = self.payload(*lhs);
                let yb = self.payload(*rhs);
                let x = self.b.ins().bitcast(types::F64, MemFlags::new(), xb);
                let y = self.b.ins().bitcast(types::F64, MemFlags::new(), yb);
                match op {
                    FastOp::Mod => {
                        self.b.ins().jump(slow_blk, &[]);
                        let dead = self.b.create_block();
                        self.b.switch_to_block(dead);
                    }
                    FastOp::Add | FastOp::Sub | FastOp::Mul | FastOp::Div => {
                        let r = match op {
                            FastOp::Add => self.b.ins().fadd(x, y),
                            FastOp::Sub => self.b.ins().fsub(x, y),
                            FastOp::Mul => self.b.ins().fmul(x, y),
                            _ => self.b.ins().fdiv(x, y),
                        };
                        let bits = self.b.ins().bitcast(types::I64, MemFlags::new(), r);
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
                        let r = self.b.ins().fcmp(cc, x, y);
                        self.store_bool_home(*dst, r);
                    }
                }
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(fast_blk);
                let x = self.payload(*lhs);
                let y = self.payload(*rhs);
                match op {
                    FastOp::Mul => {
                        // Overflow when the high word is not the sign
                        // extension of the low one.
                        let r = self.b.ins().imul(x, y);
                        let hi = self.b.ins().smulhi(x, y);
                        let sign = self.b.ins().sshr_imm(r, 63);
                        let overflow = self.b.ins().icmp(IntCC::NotEqual, hi, sign);
                        let ok_blk = self.b.create_block();
                        self.b.ins().brif(overflow, slow_blk, &[], ok_blk, &[]);
                        self.b.switch_to_block(ok_blk);
                        self.release(*dst);
                        self.store_tag(*dst, TAG_INT);
                        self.store_payload(*dst, r);
                    }
                    FastOp::Div | FastOp::Mod => {
                        // Division by zero and MIN / -1 go to the runtime.
                        let y_zero = self.b.ins().icmp_imm(IntCC::Equal, y, 0);
                        let x_min = self.b.ins().icmp_imm(IntCC::Equal, x, i64::MIN);
                        let y_m1 = self.b.ins().icmp_imm(IntCC::Equal, y, -1);
                        let min_case = self.b.ins().band(x_min, y_m1);
                        let bad = self.b.ins().bor(y_zero, min_case);
                        let ok_blk = self.b.create_block();
                        self.b.ins().brif(bad, slow_blk, &[], ok_blk, &[]);
                        self.b.switch_to_block(ok_blk);
                        // Floor semantics, as in Ruby.
                        let rem = self.b.ins().srem(x, y);
                        let nonzero = self.b.ins().icmp_imm(IntCC::NotEqual, rem, 0);
                        let y_neg = self.b.ins().icmp_imm(IntCC::SignedLessThan, y, 0);
                        let r = if *op == FastOp::Div {
                            let q = self.b.ins().sdiv(x, y);
                            let x_neg = self.b.ins().icmp_imm(IntCC::SignedLessThan, x, 0);
                            let differ = self.b.ins().bxor(x_neg, y_neg);
                            let adjust = self.b.ins().band(nonzero, differ);
                            let adjust = self.b.ins().uextend(types::I64, adjust);
                            self.b.ins().isub(q, adjust)
                        } else {
                            let r_neg = self.b.ins().icmp_imm(IntCC::SignedLessThan, rem, 0);
                            let differ = self.b.ins().bxor(r_neg, y_neg);
                            let adjust = self.b.ins().band(nonzero, differ);
                            let zero = self.b.ins().iconst(types::I64, 0);
                            let add = self.b.ins().select(adjust, y, zero);
                            self.b.ins().iadd(rem, add)
                        };
                        self.release(*dst);
                        self.store_tag(*dst, TAG_INT);
                        self.store_payload(*dst, r);
                    }
                    FastOp::Add | FastOp::Sub => {
                        let r = if *op == FastOp::Add {
                            self.b.ins().iadd(x, y)
                        } else {
                            self.b.ins().isub(x, y)
                        };
                        // Signed overflow: the result's sign differs from
                        // both operands' (add) or from x and not-y (sub).
                        let y2 = if *op == FastOp::Add {
                            y
                        } else {
                            self.b.ins().bnot(y)
                        };
                        let a = self.b.ins().bxor(x, r);
                        let c = self.b.ins().bxor(y2, r);
                        let both_neg = self.b.ins().band(a, c);
                        let overflow = self.b.ins().icmp_imm(IntCC::SignedLessThan, both_neg, 0);
                        let ok_blk = self.b.create_block();
                        self.b.ins().brif(overflow, slow_blk, &[], ok_blk, &[]);
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
                        let r = self.b.ins().icmp(cc, x, y);
                        self.store_bool_home(*dst, r);
                    }
                }
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(slow_blk);
                self.exec(block, index, unwind);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::Not { dst, src } => {
                let t = self.truthy(*src);
                let one = self.b.ins().iconst(types::I8, 1);
                let v = self.b.ins().bxor(t, one);
                self.store_bool(*dst, v);
            }
            Inst::Len { dst, src } => {
                // An array: its length from the vector; anything else
                // through the runtime.
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let tag = self.tag(*src);
                let is_arr = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
                self.b.ins().brif(is_arr, fast, &[], slow, &[]);
                self.b.switch_to_block(fast);
                let (_, _, len, _) = self.array_view(*src);
                // The home too: `after` reads it back into the variable.
                self.release(*dst);
                self.store_tag(*dst, TAG_INT);
                self.store_payload(*dst, len);
                self.b.def_var(self.ivar(*dst), len);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(slow);
                self.exec(block, index, unwind);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::ArrayGetReg {
                dst,
                arr,
                index: idx,
            } => {
                // An array indexed by an Int within range: the element
                // copied from the vector; everything else (negative
                // indices, other receivers) through the runtime.
                let check_b = self.b.create_block();
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let tag = self.tag(*arr);
                let is_arr = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_ARRAY);
                let int_state = self.states[*idx as usize] == State::Int;
                if int_state {
                    self.b.ins().brif(is_arr, check_b, &[], slow, &[]);
                } else {
                    let itag = self.tag(*idx);
                    let is_int = self.b.ins().icmp_imm(IntCC::Equal, itag, TAG_INT);
                    let both = self.b.ins().band(is_arr, is_int);
                    self.b.ins().brif(both, check_b, &[], slow, &[]);
                }
                self.b.switch_to_block(check_b);
                let i = if int_state {
                    self.b.use_var(self.ivar(*idx))
                } else {
                    self.payload(*idx)
                };
                let (kind, ptr, len, _) = self.array_view(*arr);
                let in_range = self.b.ins().icmp(IntCC::UnsignedLessThan, i, len);
                self.b.ins().brif(in_range, fast, &[], slow, &[]);
                self.b.switch_to_block(fast);
                // Boxed elements are copied; unboxed ones are read as the
                // machine word they are and boxed into the register.
                let values_b = self.b.create_block();
                let ints_b = self.b.create_block();
                let floats_b = self.b.create_block();
                let not_values = self.b.create_block();
                let is_values = self.b.ins().icmp_imm(IntCC::Equal, kind, 0);
                self.b.ins().brif(is_values, values_b, &[], not_values, &[]);
                self.b.switch_to_block(not_values);
                let is_ints = self.b.ins().icmp_imm(IntCC::Equal, kind, 1);
                self.b.ins().brif(is_ints, ints_b, &[], floats_b, &[]);
                self.b.switch_to_block(values_b);
                let off = self.b.ins().imul_imm(i, i64::from(VALUE_SIZE));
                let elem = self.b.ins().iadd(ptr, off);
                self.clone_from(*dst, elem);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(ints_b);
                let off = self.b.ins().imul_imm(i, 8);
                let elem = self.b.ins().iadd(ptr, off);
                let v = self.b.ins().load(types::I64, MemFlags::trusted(), elem, 0);
                self.release(*dst);
                self.store_tag(*dst, TAG_INT);
                self.store_payload(*dst, v);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(floats_b);
                let off = self.b.ins().imul_imm(i, 8);
                let elem = self.b.ins().iadd(ptr, off);
                let bits = self.b.ins().load(types::I64, MemFlags::trusted(), elem, 0);
                self.release(*dst);
                self.store_tag(*dst, TAG_FLOAT);
                self.store_payload(*dst, bits);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(slow);
                self.exec(block, index, unwind);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::ArrayPush { arr, src } => {
                // An unshared array with room: append in place; otherwise
                // the runtime copies or grows it.
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let arr_ptr = self
                    .b
                    .ins()
                    .iadd_imm(self.regs, i64::from(Self::reg_off(*arr)));
                let moving = self.movable(inst, *src, block, index);
                self.inline_push(arr_ptr, *src, slow, moving);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(slow);
                self.exec(block, index, unwind);
                if moving {
                    self.drop_moved(*src);
                }
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
                if moving {
                    self.states[*src as usize] = State::NonHeap;
                }
            }
            Inst::Interpolate { .. } => {
                let entry = self.h.interpolate;
                self.exec_via(entry, block, index, unwind);
            }
            Inst::ClearRegs { from, to } => {
                for r in *from..*to {
                    self.release(r);
                    self.store_tag(r, TAG_NIL);
                    self.states[r as usize] = State::NonHeap;
                }
            }
            Inst::ClassIs { dst, src, class } => {
                // An object of exactly the class: its id is read from the
                // allocation; anything else (an unboxed number, another
                // tag) is not.
                let v = match self.states[*src as usize] {
                    State::Int | State::Float | State::Bool | State::NonHeap => {
                        self.b.ins().iconst(types::I8, 0)
                    }
                    State::Unknown => {
                        let check = self.b.create_block();
                        let join = self.b.create_block();
                        self.b.append_block_param(join, types::I8);
                        let tag = self.tag(*src);
                        let is_obj = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_OBJECT);
                        let no = self.b.ins().iconst(types::I8, 0);
                        self.b.ins().brif(is_obj, check, &[], join, &[no]);
                        self.b.switch_to_block(check);
                        let rc = self.payload(*src);
                        let cid = self.b.ins().uload32(
                            MemFlags::trusted(),
                            rc,
                            OBJECT_FIELDS_PTR_OFF + L::OBJECT_CLASS_OFF as i32,
                        );
                        let same = self.b.ins().icmp_imm(IntCC::Equal, cid, i64::from(*class));
                        self.b.ins().jump(join, &[same]);
                        self.b.switch_to_block(join);
                        self.b.block_params(join)[0]
                    }
                };
                self.store_bool(*dst, v);
            }
            Inst::IsNil { dst, src } => {
                let v = match self.states[*src as usize] {
                    State::Int | State::Float | State::Bool => self.b.ins().iconst(types::I8, 0),
                    _ => {
                        let tag = self.tag(*src);
                        self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_NIL)
                    }
                };
                self.store_bool(*dst, v);
            }
            Inst::SelfRef { dst } => {
                let self_ptr = self
                    .b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), self.ptrs, 8);
                self.clone_from(*dst, self_ptr);
            }
            Inst::Arg { dst, index: arg } => {
                // Present arguments are copied inline; a missing one is nil.
                let nargs = self
                    .b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), self.ptrs, 16);
                let present =
                    self.b
                        .ins()
                        .icmp_imm(IntCC::UnsignedGreaterThan, nargs, i64::from(*arg));
                let yes = self.b.create_block();
                let no = self.b.create_block();
                let cont = self.b.create_block();
                self.b.ins().brif(present, yes, &[], no, &[]);
                self.b.switch_to_block(yes);
                let args = self
                    .b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), self.ptrs, 0);
                let src = self
                    .b
                    .ins()
                    .iadd_imm(args, i64::from(*arg) * i64::from(VALUE_SIZE));
                self.clone_from(*dst, src);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(no);
                self.release(*dst);
                self.store_tag(*dst, TAG_NIL);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
                // A parameter declared Int/Float: check once, then unboxed.
                if let Some(n) = unbox::param_num(self.f, self.methods, *arg) {
                    self.get_num(*dst, n, block, index);
                }
            }
            Inst::BlockParam { dst } => {
                let d = self.i32(*dst);
                self.b
                    .ins()
                    .call(self.h.block_param, &[self.act, self.regs, d]);
            }
            Inst::FrameGet { dst, depth, slot } => {
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let addr = self.frame_slot_addr(*depth, *slot, slow);
                self.clone_from(*dst, addr);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(slow);
                let dp = self.i32(*depth);
                let sl = self.i32(*slot);
                let d = self.i32(*dst);
                self.b
                    .ins()
                    .call(self.h.frame_get, &[self.act, dp, sl, self.regs, d]);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::FrameSet { depth, slot, src } => {
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let addr = self.frame_slot_addr(*depth, *slot, slow);
                self.release_ptr(addr);
                self.clone_reg_to_ptr(addr, *src);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(slow);
                let dp = self.i32(*depth);
                let sl = self.i32(*slot);
                let s = self.i32(*src);
                self.b
                    .ins()
                    .call(self.h.frame_set, &[self.act, dp, sl, self.regs, s]);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::ClassRef { dst, class } => {
                self.release(*dst);
                self.store_tag(*dst, TAG_CLASS);
                let v = self.b.ins().iconst(types::I64, i64::from(*class));
                self.store_payload(*dst, v);
            }
            Inst::FieldGet {
                dst,
                obj,
                index: field,
                class,
            } => {
                // An object: read the field through the object's view.
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let tag = self.tag(*obj);
                let is_obj = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_OBJECT);
                self.b.ins().brif(is_obj, fast, &[], slow, &[]);
                let num = unbox::field_num(self.classes, *class, *field);
                // The slow path first: a field declared Int/Float is
                // checked once there (the compile-time state must still
                // be the one before this instruction).
                self.b.switch_to_block(slow);
                let o = self.i32(*obj);
                let i = self.i32(*field);
                let d = self.i32(*dst);
                let call = self
                    .b
                    .ins()
                    .call(self.h.field_get, &[self.rt, self.regs, o, i, d]);
                let status = self.b.inst_results(call)[0];
                self.check(status, unwind);
                let before = self.states[*dst as usize];
                if let Some(n) = num {
                    self.get_num(*dst, n, block, index);
                }
                self.b.ins().jump(cont, &[]);
                self.states[*dst as usize] = before;
                self.b.switch_to_block(fast);
                let addr = self.field_addr(*obj, *field);
                match num {
                    // A numeric field goes straight into the unboxed
                    // variable: the tag is checked in the field (a
                    // mismatch re-runs the read in the interpreter), and
                    // the home is not written.
                    Some(n) => {
                        let ftag = self.b.ins().load(types::I64, MemFlags::trusted(), addr, 0);
                        let want = if n == Num::Int { TAG_INT } else { TAG_FLOAT };
                        let is = self.b.ins().icmp_imm(IntCC::Equal, ftag, want);
                        let ok = self.b.create_block();
                        let bad = self.b.create_block();
                        self.b.ins().brif(is, ok, &[], bad, &[]);
                        self.b.switch_to_block(bad);
                        self.deopt(block, index);
                        self.b.switch_to_block(ok);
                        let p = self.b.ins().load(types::I64, MemFlags::trusted(), addr, 8);
                        self.unbox(*dst, unbox::num_state(n));
                        match n {
                            Num::Int => self.b.def_var(self.ivar(*dst), p),
                            Num::Float => {
                                let v = self.b.ins().bitcast(types::F64, MemFlags::new(), p);
                                self.b.def_var(self.fvar(*dst), v);
                            }
                        }
                    }
                    None => self.clone_from(*dst, addr),
                }
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
            }
            Inst::FieldSet {
                obj,
                index: field_index,
                src,
                ..
            } => {
                let fast = self.b.create_block();
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                let tag = self.tag(*obj);
                let is_obj = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_OBJECT);
                self.b.ins().brif(is_obj, fast, &[], slow, &[]);
                self.b.switch_to_block(fast);
                let field = self.field_addr(*obj, *field_index);
                self.release_ptr(field);
                // The last read of the source moves it into the field.
                let moving = self.movable(inst, *src, block, index);
                if moving {
                    self.move_reg_to_ptr(field, *src);
                } else {
                    self.clone_reg_to_ptr(field, *src);
                }
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(slow);
                let o = self.i32(*obj);
                let i = self.i32(*field_index);
                let s = self.i32(*src);
                let call = self
                    .b
                    .ins()
                    .call(self.h.field_set, &[self.rt, self.regs, o, i, s]);
                let status = self.b.inst_results(call)[0];
                self.check(status, unwind);
                if moving {
                    self.drop_moved(*src);
                }
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
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
                            .ins()
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
                    self.b.ins().call(
                        self.h.alloc_data,
                        &[self.regs, class_v, self.args_buf, n, d],
                    );
                    return;
                }
                for (k, r) in args.iter().enumerate() {
                    let v = self.i32(*r);
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), v, self.scratch, 4 * k as i32);
                }
                let class_v = self.i32(*class);
                let init_v = self.i32(init.unwrap_or(u32::MAX));
                let nargs = self.i32(args.len() as u32);
                let d = self.i32(*dst);
                let call = self.b.ins().call(
                    self.h.construct,
                    &[self.rt, self.regs, class_v, init_v, self.scratch, nargs, d],
                );
                let status = self.b.inst_results(call)[0];
                self.check(status, unwind);
            }
            Inst::OwnedCall {
                dst,
                method,
                recv,
                args,
                kw,
            } if kw.is_empty() => {
                // A result nobody reads (`xs = xs.push(v)` as a statement)
                // is not stored: one clone and one release fewer.
                let wanted = self.live[block as usize]
                    .get(index as usize + 1)
                    .is_some_and(|l| l[*dst as usize]);
                // `xs = xs.push(v)`: the append in place is inline when the
                // array (in its register, frame slot or field) is unshared
                // and has room; the runtime handles the rest.
                let is_push = args.len() == 1
                    && self.methods[*method as usize]
                        .native_key
                        .as_deref()
                        .is_some_and(|k| k == "Array#push")
                    && !matches!(recv, VarLoc::Reg(r) if *r == args[0]);
                let moving = is_push && self.movable(inst, args[0], block, index);
                let slow = self.b.create_block();
                let cont = self.b.create_block();
                if is_push {
                    let arr_ptr = match recv {
                        VarLoc::Reg(r) => self
                            .b
                            .ins()
                            .iadd_imm(self.regs, i64::from(Self::reg_off(*r))),
                        VarLoc::Frame { depth, slot } => self.frame_slot_addr(*depth, *slot, slow),
                        VarLoc::Field { obj, index } => {
                            let check = self.b.create_block();
                            let tag = self.tag(*obj);
                            let is_obj = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_OBJECT);
                            self.b.ins().brif(is_obj, check, &[], slow, &[]);
                            self.b.switch_to_block(check);
                            self.field_addr(*obj, *index)
                        }
                    };
                    self.inline_push(arr_ptr, args[0], slow, moving);
                    if wanted {
                        self.clone_from(*dst, arr_ptr);
                    }
                    self.b.ins().jump(cont, &[]);
                    self.b.switch_to_block(slow);
                }
                for (k, r) in args.iter().enumerate() {
                    let v = self.i32(*r);
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), v, self.scratch, 4 * k as i32);
                }
                let (kind, a, bb) = match recv {
                    VarLoc::Reg(r) => (0, *r, 0),
                    VarLoc::Frame { depth, slot } => (1, *depth, *slot),
                    VarLoc::Field { obj, index } => (2, *obj, *index),
                };
                let mid_v = self.i32(*method);
                let kind_v = self.i32(kind);
                let a_v = self.i32(a);
                let b_v = self.i32(bb);
                let nargs = self.i32(args.len() as u32);
                let d = self.i32(if wanted { *dst } else { u32::MAX });
                let call = self.b.ins().call(
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
                );
                let status = self.b.inst_results(call)[0];
                self.check(status, unwind);
                if moving {
                    self.drop_moved(args[0]);
                }
                self.b.ins().jump(cont, &[]);
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
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), v, self.scratch, 4 * k as i32);
                }
                let nargs = self.i32(args.len() as u32);
                let d = self.i32(*dst);
                let call = self.b.ins().call(
                    self.h.yield_,
                    &[self.rt, self.act, self.regs, self.scratch, nargs, d],
                );
                let status = self.b.inst_results(call)[0];
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
                    // The callee may raise: a backtrace shows this
                    // activation at the call's line.
                    let line = self.f.blocks[block as usize].lines[index as usize];
                    let line_v = self.b.ins().iconst(types::I32, i64::from(line));
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), line_v, self.act, L::ACT_LINE as i32);
                    for (k, r) in args.iter().enumerate() {
                        let v = self.i32(*r);
                        self.b
                            .ins()
                            .store(MemFlags::trusted(), v, self.scratch, 4 * k as i32);
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
                            return;
                        }
                    }
                    if let Some(callee) = direct_target(inst, self.methods) {
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
                                .ins()
                                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
                            // The area is released after the call: a
                            // dead argument is moved there.
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
                                .ins()
                                .iadd_imm(self.args_buf, (slots as i64) * i64::from(VALUE_SIZE));
                            let zero = self.b.ins().iconst(types::I64, 0);
                            self.b.ins().store(MemFlags::trusted(), zero, p, 0);
                            slots += 1;
                        }
                        if has_block {
                            let p = self
                                .b
                                .ins()
                                .iadd_imm(self.args_buf, (slots as i64) * i64::from(VALUE_SIZE));
                            match blk {
                                Some(r) => {
                                    self.clone_reg_to_ptr(p, r);
                                    if nparams < 64 {
                                        provided |= 1 << nparams;
                                    }
                                }
                                None => {
                                    let zero = self.b.ins().iconst(types::I64, 0);
                                    self.b.ins().store(MemFlags::trusted(), zero, p, 0);
                                }
                            }
                            slots += 1;
                        }
                        let lean = frame_size == 0
                            && blk.is_none()
                            && !self.functions[callee as usize].blocks.iter().any(|b| {
                                b.insts.iter().any(|i| matches!(i, Inst::MakeBlock { .. }))
                            });
                        if lean {
                            self.lean_call(body, callee, file, recv, provided, slots, dst, unwind);
                            return;
                        }
                        let total_v = self.i32(slots as u32);
                        let provided_v = self.b.ins().iconst(types::I64, provided as i64);
                        let call = self.b.ins().call(
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
                        );
                        let status = self.b.inst_results(call)[0];
                        // On failure nothing was built: release the area.
                        let failed = self.b.create_block();
                        let ok_blk = self.b.create_block();
                        self.b.ins().brif(status, failed, &[], ok_blk, &[]);
                        self.b.switch_to_block(failed);
                        for k in 0..slots {
                            let p = self
                                .b
                                .ins()
                                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
                            self.release_ptr(p);
                        }
                        self.b.ins().jump(unwind, &[status]);
                        self.b.switch_to_block(ok_blk);
                        let zero = self.b.ins().iconst(types::I64, 0);
                        self.b
                            .ins()
                            .store(MemFlags::trusted(), zero, self.out_buf, 0);
                        let call = self
                            .b
                            .ins()
                            .call(body, &[self.rt, self.act_buf, self.out_buf]);
                        let status = self.b.inst_results(call)[0];
                        let call = self.b.ins().call(
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
                        );
                        let status = self.b.inst_results(call)[0];
                        // The callee is gone: release its parameters.
                        for k in 0..slots {
                            let p = self
                                .b
                                .ins()
                                .iadd_imm(self.args_buf, (k as i64) * i64::from(VALUE_SIZE));
                            self.release_ptr(p);
                        }
                        self.check(status, unwind);
                        return;
                    }
                    let call = self.b.ins().call(
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
                    );
                    let status = self.b.inst_results(call)[0];
                    self.check(status, unwind);
                }
                None => self.exec(block, index, unwind),
            },
            _ => self.exec(block, index, unwind),
        }
    }
}

// ----- building executables ----------------------------------------------------------

/// The runtime static library compiled programs link against: `$QUARZ_RT_LIB`
/// or `libquarz_vm.a` next to the running executable (or one directory
/// up, for `target/debug/deps`).
pub fn find_runtime_lib() -> Result<PathBuf, String> {
    if let Ok(p) = std::env::var("QUARZ_RT_LIB") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Ok(p);
        }
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let mut dir = exe.parent();
    for _ in 0..3 {
        if let Some(d) = dir {
            let candidate = d.join("libquarz_vm.a");
            if candidate.exists() {
                return Ok(candidate);
            }
            dir = d.parent();
        }
    }
    Err("cannot find libquarz_vm.a (build it with `cargo build` or set QUARZ_RT_LIB)".to_string())
}

/// Compile a module and link it into the executable `output`.
pub fn build(module: &Module, output: &Path) -> Result<(), String> {
    let object = compile(module)?;
    let runtime = find_runtime_lib()?;
    let obj_path = output.with_extension("o");
    std::fs::write(&obj_path, &object).map_err(|e| format!("{}: {e}", obj_path.display()))?;
    let status = Command::new("cc")
        .arg("-o")
        .arg(output)
        .arg(&obj_path)
        .arg(&runtime)
        .args(["-lpthread", "-ldl", "-lm", "-lgcc_s", "-lrt", "-lutil"])
        .status()
        .map_err(|e| format!("cannot run cc: {e}"))?;
    let _ = std::fs::remove_file(&obj_path);
    if !status.success() {
        return Err(format!("linking failed ({status})"));
    }
    Ok(())
}
