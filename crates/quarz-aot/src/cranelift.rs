//! The Cranelift backend: an object file, with every compiled frame
//! described by an activation (the development backend; see `llvm` for
//! the production one).

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::{FloatCC as ClFloatCC, IntCC as ClIntCC};
use cranelift_codegen::ir::{
    types, AbiParam, Block, BlockArg, FuncRef, InstBuilder, MemFlagsData, SigRef, Signature,
    StackSlotData, StackSlotKind, Value,
};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, FuncId as CFuncId, Linkage, Module as _};
use cranelift_object::{ObjectBuilder, ObjectModule};
use quarz_ir::*;
use quarz_vm::layout as L;

use crate::builder::{Builder, FloatCC, IntCC, Ty};
use crate::gen::{self, Helpers};
use crate::unbox::{self, Num};

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
    clone_ptr: CFuncId,
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
    hash_put_int: CFuncId,
    main: CFuncId,
}

struct Compiler {
    module: ObjectModule,
    rt: Runtime,
    fn_sig: Signature,
    funcs: Vec<CFuncId>,
    /// The typed entries (`qz_fn_N_t`), for the functions that have one.
    typed: Vec<Option<unbox::TypedSig>>,
    typed_funcs: Vec<Option<CFuncId>>,
}

fn cl_type(ty: Ty) -> types::Type {
    match ty {
        Ty::I8 => types::I8,
        Ty::I32 => types::I32,
        Ty::I64 | Ty::Ptr => types::I64,
        Ty::F64 => types::F64,
    }
}

/// The signature of a typed entry: the interpreter, the caller's
/// activation, the address of `self`, the parameters as machine values,
/// then the address of a `Value` for a result that does not fit;
/// returns the status and the result's bits.
fn typed_signature(
    call_conv: cranelift_codegen::isa::CallConv,
    sig: &unbox::TypedSig,
) -> Signature {
    let mut s = Signature::new(call_conv);
    for _ in 0..3 {
        s.params.push(AbiParam::new(types::I64));
    }
    for p in &sig.params {
        s.params.push(AbiParam::new(match p {
            Num::Int => types::I64,
            Num::Float => types::F64,
        }));
    }
    s.params.push(AbiParam::new(types::I64));
    s.returns.push(AbiParam::new(types::I64));
    s
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
            &sig(
                &[i64_, i64_, i32_, i32_, i32_, i64_, i64_, i64_],
                Some(i32_),
            ),
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
        clone_ptr: import(&mut obj, "qz_clone_ptr", &sig(&[i64_, i64_], None))?,
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
        hash_put_int: import(
            &mut obj,
            "qz_hash_put_int",
            &sig(&[i64_, i64_, i64_], Some(i32_)),
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
                &[i64_, i64_, i64_, i64_, i32_, i64_, i64_, i64_, i64_],
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
    let typed = unbox::typed_sigs(&module.functions, &module.world.methods);
    let typed_funcs: Vec<Option<CFuncId>> = typed
        .iter()
        .enumerate()
        .map(|(i, t)| {
            t.as_ref()
                .map(|sig| {
                    obj.declare_function(
                        &format!("qz_fn_{i}_t"),
                        Linkage::Local,
                        &typed_signature(call_conv, sig),
                    )
                    .map_err(|e| e.to_string())
                })
                .transpose()
        })
        .collect::<Result<_, _>>()?;
    let mut c = Compiler {
        module: obj,
        rt,
        fn_sig,
        funcs,
        typed,
        typed_funcs,
    };
    for (i, f) in module.functions.iter().enumerate() {
        c.compile_function(i as FuncId, f, module, None)?;
        if let Some(sig) = c.typed[i].clone() {
            c.compile_function(i as FuncId, f, module, Some(sig))?;
        }
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
        module: &Module,
        typed: Option<unbox::TypedSig>,
    ) -> Result<(), String> {
        let mut ctx: Context = self.module.make_context();
        ctx.func.signature = match &typed {
            Some(sig) => typed_signature(self.fn_sig.call_conv, sig),
            None => self.fn_sig.clone(),
        };
        let mut fbc = FunctionBuilderContext::new();
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let mut imp =
            |id: CFuncId, fb: &mut FunctionBuilder| self.module.declare_func_in_func(id, fb.func);
        let h = Helpers {
            resume: imp(self.rt.resume, &mut fb),
            enter: imp(self.rt.enter, &mut fb),
            enter_virtual: imp(self.rt.enter_virtual, &mut fb),
            leave: imp(self.rt.leave, &mut fb),
            push_call: imp(self.rt.push_call, &mut fb),
            pop_call: imp(self.rt.pop_call, &mut fb),
            stack_overflow: imp(self.rt.stack_overflow, &mut fb),
            drop_value: imp(self.rt.drop_value, &mut fb),
            clone_ptr: imp(self.rt.clone_ptr, &mut fb),
            exec: imp(self.rt.exec, &mut fb),
            term: imp(self.rt.term, &mut fb),
            block_param: imp(self.rt.block_param, &mut fb),
            frame_get: imp(self.rt.frame_get, &mut fb),
            frame_set: imp(self.rt.frame_set, &mut fb),
            field_get: imp(self.rt.field_get, &mut fb),
            load_const: imp(self.rt.load_const, &mut fb),
            interpolate: imp(self.rt.interpolate, &mut fb),
            field_set: imp(self.rt.field_set, &mut fb),
            call_static: imp(self.rt.call_static, &mut fb),
            yield_: imp(self.rt.yield_, &mut fb),
            construct: imp(self.rt.construct, &mut fb),
            alloc_data: imp(self.rt.alloc_data, &mut fb),
            owned_call: imp(self.rt.owned_call, &mut fb),
            hash_put_int: imp(self.rt.hash_put_int, &mut fb),
        };
        let methods = &module.world.methods;
        let mut callees: HashMap<FuncId, FuncRef> = HashMap::new();
        let mut callees_typed: HashMap<FuncId, FuncRef> = HashMap::new();
        for target in gen::direct_callees(f, methods) {
            callees.insert(target, imp(self.funcs[target as usize], &mut fb));
            if let Some(Some(tf)) = self.typed_funcs.get(target as usize) {
                callees_typed.insert(target, imp(*tf, &mut fb));
            }
        }
        let body_sig = fb.import_signature(self.fn_sig.clone());
        let mut b = Cl { fb };
        gen::gen_function(
            gen::Target {
                b: &mut b,
                h,
                callees,
                callees_typed,
                body_sig,
                lazy_act: false,
                entry_of: None,
            },
            fid,
            f,
            methods,
            &module.functions,
            &module.world.classes,
            &module.world.builtin,
            typed.clone(),
            &self.typed,
        );
        b.fb.seal_all_blocks();
        b.fb.finalize(self.module.target_config());
        let target = match &typed {
            Some(_) => self.typed_funcs[fid as usize].expect("typed entry declared"),
            None => self.funcs[fid as usize],
        };
        self.module
            .define_function(target, &mut ctx)
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
        // main(argc, argv) -> qz_main(blob, len, table, n, argc, argv, layout, vec_layout, flags)
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
        let flags = b.ins().iconst(types::I64, 0);
        let call = b.ins().call(
            qz_main,
            &[
                blob_ptr, len, table_ptr, count, params[0], params[1], layout, vec_layout, flags,
            ],
        );
        let code = b.inst_results(call)[0];
        b.ins().return_(&[code]);
        b.seal_all_blocks();
        b.finalize(self.module.target_config());
        self.module
            .define_function(main, &mut ctx)
            .map_err(|e| e.to_string())?;
        self.module.clear_context(&mut ctx);
        Ok(())
    }
}

/// The builder of one function.
struct Cl<'a> {
    fb: FunctionBuilder<'a>,
}

fn block_args(args: &[Value]) -> Vec<BlockArg> {
    args.iter().map(|v| BlockArg::Value(*v)).collect()
}

fn cl_intcc(cc: IntCC) -> ClIntCC {
    match cc {
        IntCC::Equal => ClIntCC::Equal,
        IntCC::NotEqual => ClIntCC::NotEqual,
        IntCC::SignedLessThan => ClIntCC::SignedLessThan,
        IntCC::SignedLessThanOrEqual => ClIntCC::SignedLessThanOrEqual,
        IntCC::SignedGreaterThan => ClIntCC::SignedGreaterThan,
        IntCC::SignedGreaterThanOrEqual => ClIntCC::SignedGreaterThanOrEqual,
        IntCC::UnsignedLessThan => ClIntCC::UnsignedLessThan,
        IntCC::UnsignedGreaterThan => ClIntCC::UnsignedGreaterThan,
        IntCC::UnsignedGreaterThanOrEqual => ClIntCC::UnsignedGreaterThanOrEqual,
    }
}

fn cl_floatcc(cc: FloatCC) -> ClFloatCC {
    match cc {
        FloatCC::Equal => ClFloatCC::Equal,
        FloatCC::NotEqual => ClFloatCC::NotEqual,
        FloatCC::LessThan => ClFloatCC::LessThan,
        FloatCC::LessThanOrEqual => ClFloatCC::LessThanOrEqual,
        FloatCC::GreaterThan => ClFloatCC::GreaterThan,
        FloatCC::GreaterThanOrEqual => ClFloatCC::GreaterThanOrEqual,
    }
}

impl Builder for Cl<'_> {
    type Value = Value;
    type Block = Block;
    type Var = Variable;
    type Func = FuncRef;
    type Sig = SigRef;

    fn entry_block(&mut self) -> (Block, Vec<Value>) {
        let entry = self.fb.create_block();
        self.fb.append_block_params_for_function_params(entry);
        let params = self.fb.block_params(entry).to_vec();
        (entry, params)
    }

    fn create_block(&mut self) -> Block {
        self.fb.create_block()
    }

    fn switch_to_block(&mut self, block: Block) {
        self.fb.switch_to_block(block);
    }

    fn append_block_param(&mut self, block: Block, ty: Ty) -> Value {
        self.fb.append_block_param(block, cl_type(ty))
    }

    fn block_params(&self, block: Block) -> Vec<Value> {
        self.fb.block_params(block).to_vec()
    }

    fn declare_var(&mut self, ty: Ty) -> Variable {
        self.fb.declare_var(cl_type(ty))
    }

    fn def_var(&mut self, var: Variable, v: Value) {
        self.fb.def_var(var, v);
    }

    fn use_var(&mut self, var: Variable) -> Value {
        self.fb.use_var(var)
    }

    fn stack_slot(&mut self, size: u32, align_log2: u8) -> Value {
        let slot = self.fb.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            size,
            align_log2,
        ));
        self.fb.ins().stack_addr(types::I64, slot, 0)
    }

    fn get_stack_pointer(&mut self) -> Value {
        self.fb.ins().get_stack_pointer(types::I64)
    }

    fn iconst(&mut self, ty: Ty, v: i64) -> Value {
        self.fb.ins().iconst(cl_type(ty), v)
    }

    fn f64const(&mut self, v: f64) -> Value {
        self.fb.ins().f64const(v)
    }

    fn iadd(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().iadd(a, b)
    }

    fn isub(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().isub(a, b)
    }

    fn imul(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().imul(a, b)
    }

    fn smulhi(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().smulhi(a, b)
    }

    fn sdiv(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().sdiv(a, b)
    }

    fn srem(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().srem(a, b)
    }

    fn band(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().band(a, b)
    }

    fn bor(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().bor(a, b)
    }

    fn bxor(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().bxor(a, b)
    }

    fn bnot(&mut self, a: Value) -> Value {
        self.fb.ins().bnot(a)
    }

    fn iadd_imm(&mut self, a: Value, imm: i64) -> Value {
        self.fb.ins().iadd_imm_s(a, imm)
    }

    fn imul_imm(&mut self, a: Value, imm: i64) -> Value {
        self.fb.ins().imul_imm_s(a, imm)
    }

    fn ishl_imm(&mut self, a: Value, imm: i64) -> Value {
        self.fb.ins().ishl_imm_s(a, imm)
    }

    fn sshr_imm(&mut self, a: Value, imm: i64) -> Value {
        self.fb.ins().sshr_imm_s(a, imm)
    }

    fn sadd_overflow(&mut self, a: Value, b: Value) -> (Value, Value) {
        self.fb.ins().sadd_overflow(a, b)
    }

    fn ssub_overflow(&mut self, a: Value, b: Value) -> (Value, Value) {
        self.fb.ins().ssub_overflow(a, b)
    }

    fn smul_overflow(&mut self, a: Value, b: Value) -> (Value, Value) {
        self.fb.ins().smul_overflow(a, b)
    }

    fn icmp(&mut self, cc: IntCC, a: Value, b: Value) -> Value {
        self.fb.ins().icmp(cl_intcc(cc), a, b)
    }

    fn icmp_imm(&mut self, cc: IntCC, a: Value, imm: i64) -> Value {
        self.fb.ins().icmp_imm_s(cl_intcc(cc), a, imm)
    }

    fn fcmp(&mut self, cc: FloatCC, a: Value, b: Value) -> Value {
        self.fb.ins().fcmp(cl_floatcc(cc), a, b)
    }

    fn fadd(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().fadd(a, b)
    }

    fn fsub(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().fsub(a, b)
    }

    fn fmul(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().fmul(a, b)
    }

    fn fdiv(&mut self, a: Value, b: Value) -> Value {
        self.fb.ins().fdiv(a, b)
    }

    fn fcvt_from_sint(&mut self, a: Value) -> Value {
        self.fb.ins().fcvt_from_sint(types::F64, a)
    }

    fn bitcast(&mut self, ty: Ty, a: Value) -> Value {
        self.fb.ins().bitcast(cl_type(ty), MemFlagsData::new(), a)
    }

    fn uextend(&mut self, ty: Ty, a: Value) -> Value {
        self.fb.ins().uextend(cl_type(ty), a)
    }

    fn ireduce(&mut self, ty: Ty, a: Value) -> Value {
        self.fb.ins().ireduce(cl_type(ty), a)
    }

    fn select(&mut self, c: Value, a: Value, b: Value) -> Value {
        self.fb.ins().select(c, a, b)
    }

    fn load(&mut self, ty: Ty, p: Value, off: i32) -> Value {
        self.fb
            .ins()
            .load(cl_type(ty), MemFlagsData::trusted(), p, off)
    }

    fn uload8(&mut self, p: Value, off: i32) -> Value {
        self.fb
            .ins()
            .uload8(types::I64, MemFlagsData::trusted(), p, off)
    }

    fn uload32(&mut self, p: Value, off: i32) -> Value {
        self.fb.ins().uload32(MemFlagsData::trusted(), p, off)
    }

    fn store(&mut self, v: Value, p: Value, off: i32) {
        self.fb.ins().store(MemFlagsData::trusted(), v, p, off);
    }

    fn jump(&mut self, block: Block, args: &[Value]) {
        self.fb.ins().jump(block, &block_args(args));
    }

    fn brif(&mut self, c: Value, then: Block, then_args: &[Value], els: Block, els_args: &[Value]) {
        self.fb
            .ins()
            .brif(c, then, &block_args(then_args), els, &block_args(els_args));
    }

    fn return_(&mut self, vals: &[Value]) {
        self.fb.ins().return_(vals);
    }

    fn set_cold(&mut self, block: Block) {
        self.fb.set_cold_block(block);
    }

    fn current_block(&self) -> Block {
        self.fb.current_block().expect("a block is being filled")
    }

    fn call(&mut self, f: FuncRef, args: &[Value]) -> Vec<Value> {
        let inst = self.fb.ins().call(f, args);
        self.fb.inst_results(inst).to_vec()
    }

    fn call_indirect(&mut self, sig: SigRef, callee: Value, args: &[Value]) -> Vec<Value> {
        let inst = self.fb.ins().call_indirect(sig, callee, args);
        self.fb.inst_results(inst).to_vec()
    }
}
