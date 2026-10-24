//! What code generation needs from a backend: the instructions of one
//! function, in SSA form with block parameters (which the LLVM backend
//! turns into phis). The generator in `gen` is written against this
//! trait, which `llvm` implements.

/// A machine type. `Ptr` is an address (a pointer for LLVM, so that its
/// alias analysis sees through the register file and the activation).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ty {
    I8,
    I32,
    I64,
    F64,
    Ptr,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IntCC {
    Equal,
    NotEqual,
    SignedLessThan,
    SignedLessThanOrEqual,
    SignedGreaterThan,
    SignedGreaterThanOrEqual,
    UnsignedLessThan,
    UnsignedGreaterThan,
    UnsignedGreaterThanOrEqual,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FloatCC {
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
}

/// The instruction builder of one function. Blocks take parameters;
/// variables are mutable locals the backend turns into SSA values.
pub trait Builder {
    type Value: Copy + std::fmt::Debug;
    type Block: Copy + PartialEq + std::fmt::Debug;
    type Var: Copy;
    /// A callable: a runtime function or a compiled body.
    type Func: Copy;
    /// The signature of an indirect call.
    type Sig: Copy;

    /// The entry block, with the function's parameters as its values.
    fn entry_block(&mut self) -> (Self::Block, Vec<Self::Value>);
    fn create_block(&mut self) -> Self::Block;
    fn switch_to_block(&mut self, block: Self::Block);
    fn append_block_param(&mut self, block: Self::Block, ty: Ty) -> Self::Value;
    fn block_params(&self, block: Self::Block) -> Vec<Self::Value>;

    fn declare_var(&mut self, ty: Ty) -> Self::Var;
    fn def_var(&mut self, var: Self::Var, v: Self::Value);
    fn use_var(&mut self, var: Self::Var) -> Self::Value;

    /// The address of `size` bytes of this frame, aligned to
    /// `2^align_log2`.
    fn stack_slot(&mut self, size: u32, align_log2: u8) -> Self::Value;
    /// The native stack pointer.
    fn get_stack_pointer(&mut self) -> Self::Value;

    fn iconst(&mut self, ty: Ty, v: i64) -> Self::Value;
    fn f64const(&mut self, v: f64) -> Self::Value;

    fn iadd(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn isub(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn imul(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn smulhi(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn sdiv(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn srem(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn band(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn bor(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn bxor(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn bnot(&mut self, a: Self::Value) -> Self::Value;
    fn iadd_imm(&mut self, a: Self::Value, imm: i64) -> Self::Value;
    fn imul_imm(&mut self, a: Self::Value, imm: i64) -> Self::Value;
    fn ishl_imm(&mut self, a: Self::Value, imm: i64) -> Self::Value;
    fn sshr_imm(&mut self, a: Self::Value, imm: i64) -> Self::Value;
    /// `(result, overflowed)`.
    fn sadd_overflow(&mut self, a: Self::Value, b: Self::Value) -> (Self::Value, Self::Value);
    fn ssub_overflow(&mut self, a: Self::Value, b: Self::Value) -> (Self::Value, Self::Value);
    fn smul_overflow(&mut self, a: Self::Value, b: Self::Value) -> (Self::Value, Self::Value);

    /// Comparisons produce an `I8` (0 or 1).
    fn icmp(&mut self, cc: IntCC, a: Self::Value, b: Self::Value) -> Self::Value;
    fn icmp_imm(&mut self, cc: IntCC, a: Self::Value, imm: i64) -> Self::Value;
    fn fcmp(&mut self, cc: FloatCC, a: Self::Value, b: Self::Value) -> Self::Value;

    fn fadd(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn fsub(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn fmul(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn fdiv(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    fn fcvt_from_sint(&mut self, a: Self::Value) -> Self::Value;

    /// Reinterpret the bits (`I64` <-> `F64`).
    fn bitcast(&mut self, ty: Ty, a: Self::Value) -> Self::Value;
    fn uextend(&mut self, ty: Ty, a: Self::Value) -> Self::Value;
    fn ireduce(&mut self, ty: Ty, a: Self::Value) -> Self::Value;
    fn select(&mut self, c: Self::Value, a: Self::Value, b: Self::Value) -> Self::Value;

    fn load(&mut self, ty: Ty, p: Self::Value, off: i32) -> Self::Value;
    /// A byte, zero-extended to `I64`.
    fn uload8(&mut self, p: Self::Value, off: i32) -> Self::Value;
    /// A 32-bit word, zero-extended to `I64`.
    fn uload32(&mut self, p: Self::Value, off: i32) -> Self::Value;
    fn store(&mut self, v: Self::Value, p: Self::Value, off: i32);

    fn jump(&mut self, block: Self::Block, args: &[Self::Value]);
    fn brif(
        &mut self,
        c: Self::Value,
        then: Self::Block,
        then_args: &[Self::Value],
        els: Self::Block,
        els_args: &[Self::Value],
    );
    fn return_(&mut self, vals: &[Self::Value]);
    /// Mark `block` as rarely run (a deoptimization, an error or a stack
    /// overflow), so that the code generator lays the hot path out and
    /// allocates its registers first.
    fn set_cold(&mut self, block: Self::Block);
    /// The block being filled.
    fn current_block(&self) -> Self::Block;

    /// Call, returning the results.
    fn call(&mut self, f: Self::Func, args: &[Self::Value]) -> Vec<Self::Value>;
    fn call_indirect(
        &mut self,
        sig: Self::Sig,
        callee: Self::Value,
        args: &[Self::Value],
    ) -> Vec<Self::Value>;

    /// The source line of what is emitted next, for backtraces that walk
    /// the native stack (a backend without them ignores it).
    fn set_line(&mut self, _line: u32) {}

    /// The address of `words`, constant data of the executable (null
    /// when there are none).
    fn data_words(&mut self, words: &[u32]) -> Self::Value;
    /// The address of `bytes`, constant data (null when empty).
    fn data_bytes(&mut self, bytes: &[u8]) -> Self::Value;
    /// The address of a pointer-sized variable of the executable, null
    /// at start (what the runtime keeps for one site).
    fn data_cell(&mut self) -> Self::Value;
}
