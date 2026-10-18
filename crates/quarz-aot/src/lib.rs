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

use std::path::{Path, PathBuf};
use std::process::Command;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    types, AbiParam, Block as CBlock, FuncRef, InstBuilder, MemFlags, Signature, StackSlotData,
    StackSlotKind, Value as CValue,
};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, FuncId as CFuncId, Linkage, Module as _};
use cranelift_object::{ObjectBuilder, ObjectModule};
use quarz_ir::*;

/// Size of a `Value` in bytes (`repr(C, u64)`: a tag word and a two-word
/// payload, since some variants hold fat pointers).
const VALUE_SIZE: i32 = 24;
/// Tags below this hold no reference-counted payload (`NEEDS_DROP_FROM`).
const NEEDS_DROP_FROM: i64 = 7;
const TAG_NIL: i64 = 0;
const TAG_BOOL: i64 = 1;
const TAG_INT: i64 = 2;
const TAG_FLOAT: i64 = 3;

const STATUS_RAISE: i64 = 1;

/// The runtime functions compiled code calls.
struct Runtime {
    exec: CFuncId,
    term: CFuncId,
    init_regs: CFuncId,
    drop_regs: CFuncId,
    mov: CFuncId,
    drop_reg: CFuncId,
    take_reg: CFuncId,
    main: CFuncId,
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
        init_regs: import(&mut obj, "qz_init_regs", &sig(&[i64_, i32_], None))?,
        drop_regs: import(&mut obj, "qz_drop_regs", &sig(&[i64_, i32_], None))?,
        mov: import(&mut obj, "qz_move", &sig(&[i64_, i32_, i32_], None))?,
        drop_reg: import(&mut obj, "qz_drop_reg", &sig(&[i64_, i32_], None))?,
        take_reg: import(&mut obj, "qz_take_reg", &sig(&[i64_, i32_, i64_], None))?,
        main: import(
            &mut obj,
            "qz_main",
            &sig(&[i64_, i64_, i64_, i64_, i32_, i64_], Some(i32_)),
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
        c.compile_function(i as FuncId, f)?;
    }
    c.emit_data_and_main(module, call_conv)?;
    let product = c.module.finish();
    product.emit().map_err(|e| e.to_string())
}

impl Compiler {
    fn compile_function(&mut self, fid: FuncId, f: &Function) -> Result<(), String> {
        let mut ctx: Context = self.module.make_context();
        ctx.func.signature = self.fn_sig.clone();
        let mut fbc = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let exec = self.module.declare_func_in_func(self.rt.exec, b.func);
        let term = self.module.declare_func_in_func(self.rt.term, b.func);
        let init_regs = self.module.declare_func_in_func(self.rt.init_regs, b.func);
        let drop_regs = self.module.declare_func_in_func(self.rt.drop_regs, b.func);
        let mov = self.module.declare_func_in_func(self.rt.mov, b.func);
        let drop_reg = self.module.declare_func_in_func(self.rt.drop_reg, b.func);
        let take_reg = self.module.declare_func_in_func(self.rt.take_reg, b.func);

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
        let n = b.ins().iconst(types::I32, i64::from(nregs));
        b.ins().call(init_regs, &[regs, n]);
        b.ins().jump(blocks[0], &[]);

        let mut g = Gen {
            b: &mut b,
            exec,
            term,
            mov,
            drop_reg,
            rt,
            act,
            regs,
            fid,
            f,
        };
        for (i, blk) in f.blocks.iter().enumerate() {
            g.b.switch_to_block(blocks[i]);
            for (j, inst) in blk.insts.iter().enumerate() {
                g.inst(i as u32, j as u32, inst, unwinds[i]);
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
                    let r = g.b.ins().iconst(types::I32, i64::from(*r));
                    g.b.ins().call(take_reg, &[regs, r, out]);
                    g.b.ins().call(drop_regs, &[regs, n]);
                    let zero = g.b.ins().iconst(types::I32, 0);
                    g.b.ins().return_(&[zero]);
                }
                Term::Raise(_)
                | Term::BreakOut(_)
                | Term::ReturnOut(_)
                | Term::Resume(_)
                | Term::Unreachable => {
                    let fid_v = g.b.ins().iconst(types::I32, i64::from(fid));
                    let blk_v = g.b.ins().iconst(types::I32, i as i64);
                    let call = g.b.ins().call(term, &[rt, act, fid_v, blk_v, regs]);
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
        b.switch_to_block(exit);
        let status = b.block_params(exit)[0];
        b.ins().call(drop_regs, &[regs, n]);
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
        // main(argc, argv) -> qz_main(blob, len, table, n, argc, argv)
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
        let call = b.ins().call(
            qz_main,
            &[blob_ptr, len, table_ptr, count, params[0], params[1]],
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

/// Code generation for one function body.
struct Gen<'a, 'b> {
    b: &'a mut FunctionBuilder<'b>,
    exec: FuncRef,
    term: FuncRef,
    mov: FuncRef,
    drop_reg: FuncRef,
    rt: CValue,
    act: CValue,
    regs: CValue,
    fid: FuncId,
    f: &'a Function,
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
        let tag = self.tag(dst);
        let needs = self
            .b
            .ins()
            .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, tag, NEEDS_DROP_FROM);
        let drop_blk = self.b.create_block();
        let cont = self.b.create_block();
        self.b.ins().brif(needs, drop_blk, &[], cont, &[]);
        self.b.switch_to_block(drop_blk);
        let d = self.b.ins().iconst(types::I32, i64::from(dst));
        self.b.ins().call(self.drop_reg, &[self.regs, d]);
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
        self.release(dst);
        self.store_tag(dst, TAG_BOOL);
        // `v` is an I8, stored as the payload's first byte.
        self.b
            .ins()
            .store(MemFlags::trusted(), v, self.regs, Self::reg_off(dst) + 8);
    }

    /// Delegate the instruction to the runtime and check its status.
    fn exec(&mut self, block: u32, inst: u32, unwind: CBlock) {
        let fid = self.b.ins().iconst(types::I32, i64::from(self.fid));
        let blk = self.b.ins().iconst(types::I32, i64::from(block));
        let i = self.b.ins().iconst(types::I32, i64::from(inst));
        let call = self
            .b
            .ins()
            .call(self.exec, &[self.rt, self.act, fid, blk, i, self.regs]);
        let status = self.b.inst_results(call)[0];
        let cont = self.b.create_block();
        self.b.ins().brif(status, unwind, &[status], cont, &[]);
        self.b.switch_to_block(cont);
    }

    fn inst(&mut self, block: u32, index: u32, inst: &Inst, unwind: CBlock) {
        match inst {
            Inst::Move { dst, src } => {
                if dst == src {
                    return;
                }
                // Values without reference counts are copied inline.
                let ts = self.tag(*src);
                let td = self.tag(*dst);
                let a = self
                    .b
                    .ins()
                    .icmp_imm(IntCC::UnsignedLessThan, ts, NEEDS_DROP_FROM);
                let c = self
                    .b
                    .ins()
                    .icmp_imm(IntCC::UnsignedLessThan, td, NEEDS_DROP_FROM);
                let fast = self.b.ins().band(a, c);
                let fast_blk = self.b.create_block();
                let slow_blk = self.b.create_block();
                let cont = self.b.create_block();
                self.b.ins().brif(fast, fast_blk, &[], slow_blk, &[]);
                self.b.switch_to_block(fast_blk);
                let p = self.payload(*src);
                let p2 = self.b.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    self.regs,
                    Self::reg_off(*src) + 16,
                );
                self.b
                    .ins()
                    .store(MemFlags::trusted(), ts, self.regs, Self::reg_off(*dst));
                self.store_payload(*dst, p);
                self.b
                    .ins()
                    .store(MemFlags::trusted(), p2, self.regs, Self::reg_off(*dst) + 16);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(slow_blk);
                let d = self.b.ins().iconst(types::I32, i64::from(*dst));
                let s = self.b.ins().iconst(types::I32, i64::from(*src));
                self.b.ins().call(self.mov, &[self.regs, d, s]);
                self.b.ins().jump(cont, &[]);
                self.b.switch_to_block(cont);
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
                    self.release(*dst);
                    self.store_tag(*dst, TAG_INT);
                    let v = self.b.ins().iconst(types::I64, *i);
                    self.store_payload(*dst, v);
                }
                Constant::Float(f) => {
                    self.release(*dst);
                    self.store_tag(*dst, TAG_FLOAT);
                    let v = self.b.ins().iconst(types::I64, f.to_bits() as i64);
                    self.store_payload(*dst, v);
                }
                _ => self.exec(block, index, unwind),
            },
            Inst::BinOp {
                dst, op, lhs, rhs, ..
            } if matches!(
                op,
                FastOp::Add
                    | FastOp::Sub
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
                let slow_blk = self.b.create_block();
                let cont = self.b.create_block();
                self.b.ins().brif(both, fast_blk, &[], slow_blk, &[]);
                self.b.switch_to_block(fast_blk);
                let x = self.payload(*lhs);
                let y = self.payload(*rhs);
                match op {
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
                        self.store_bool(*dst, r);
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
            Inst::IsNil { dst, src } => {
                let tag = self.tag(*src);
                let v = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_NIL);
                self.store_bool(*dst, v);
            }
            _ => self.exec(block, index, unwind),
        }
        let _ = self.term;
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
