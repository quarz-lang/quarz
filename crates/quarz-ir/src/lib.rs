//! QIR: the intermediate representation that the VM interprets and the
//! compiler translates to machine code, plus the run-time metadata
//! (`RtWorld`) that both need about classes, methods and constants.
//!
//! A function is a register machine: numbered registers hold values, basic
//! blocks end in a terminator, and each block may name a handler block
//! that receives control when an instruction raises (or, for `ensure`,
//! when any non-local flow passes through). Local variables captured by
//! blocks live in heap frames (`FrameGet`/`FrameSet`); all other locals
//! are registers.

use serde::{Deserialize, Serialize};
/// The maps of the run-time tables use a fast hasher: a program builds
/// them at every start.
pub type HashMap<K, V> = rustc_hash::FxHashMap<K, V>;

pub type FuncId = u32;
pub type Reg = u32;
pub type BlockId = u32;
pub type ClassId = u32;
pub type MethodId = u32;
pub type ConstId = u32;

/// A lowered program: metadata plus every function.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Module {
    pub world: RtWorld,
    #[serde(with = "dropped")]
    pub functions: Vec<Function>,
    /// Compilation units in execution order (dependencies first).
    pub units: Vec<Unit>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Unit {
    pub file: u32,
    pub name: String,
    pub main_class: ClassId,
    /// The function running the unit's top-level statements.
    pub body: FuncId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FuncKind {
    /// A method body; the runtime binds the parameters.
    Method(MethodId),
    /// A block or lambda body.
    Block,
    /// A file's top-level statements.
    TopLevel,
    /// A REPL input: runs in the persistent REPL frame.
    Repl,
    /// A constant initializer or a field default; `self` is the owner.
    Init,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Function {
    /// Display name for backtraces and dumps (`Class#method`, `block in …`).
    pub name: String,
    pub kind: FuncKind,
    pub file: u32,
    pub nregs: u32,
    /// Slots of the heap frame allocated per call (0 = the call shares its
    /// creator's frame and needs none of its own).
    pub frame_size: u32,
    /// The parameters a block body declares, in binding order (methods
    /// are bound from their `RtMethod` instead).
    pub param_kinds: Vec<RtParamKind>,
    /// `Proc#arity` of a block body.
    pub arity: i32,
    pub consts: Vec<Constant>,
    pub blocks: Vec<Block>,
    /// Where instructions copied in from inlined callees came from: a
    /// line `INLINE_LINE_FLAG | i` refers to `inlined[i]`.
    #[serde(default)]
    pub inlined: Vec<InlineOrigin>,
}

/// The bit that marks a line number as an index into `Function::inlined`.
pub const INLINE_LINE_FLAG: u32 = 1 << 31;

/// An instruction's origin in an inlined callee: the callee, its line
/// there, and the line of the call it replaced (for backtraces, which
/// show both frames).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InlineOrigin {
    pub callee: FuncId,
    pub line: u32,
    pub call_line: u32,
}

impl Function {
    pub fn new(name: String, kind: FuncKind, file: u32) -> Function {
        Function {
            name,
            kind,
            file,
            nregs: 0,
            frame_size: 0,
            param_kinds: Vec::new(),
            arity: 0,
            consts: Vec::new(),
            blocks: Vec::new(),
            inlined: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Constant {
    Nil,
    Bool(bool),
    Int(i64),
    /// An integer that does not fit in 64 bits: its digits and base.
    BigInt {
        digits: String,
        base: u8,
    },
    Float(f64),
    Str(String),
    Symbol(String),
    Regexp {
        source: String,
        flags: String,
    },
    Bytes(Vec<u8>),
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Block {
    pub insts: Vec<Inst>,
    /// Source line of each instruction (parallel to `insts`).
    pub lines: Vec<u32>,
    pub term: Term,
    pub term_line: u32,
    pub handler: Option<Handler>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Handler {
    pub block: BlockId,
    pub kind: HandlerKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HandlerKind {
    /// Receives raised exceptions only.
    Rescue,
    /// Receives every non-local flow (exceptions, `break`, `return`,
    /// `exit`) so that `ensure` can run before it continues.
    Ensure,
}

/// Where a variable lives when a call needs to move its value out
/// (`x = x.push(v)`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VarLoc {
    Reg(Reg),
    Frame {
        depth: u32,
        slot: u32,
    },
    /// A field of the object in `obj` (`@items = @items.push(x)`).
    Field {
        obj: Reg,
        index: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CallKind {
    /// A statically resolved method (dispatched on the receiver's class
    /// for overrides).
    Method(MethodId),
    /// A method looked up by name at run time.
    Send(String),
    /// `Class.new(...)`.
    Construct {
        class: ClassId,
        init: Option<MethodId>,
    },
    /// `new` on the receiver in a class method (`def self.build = new`):
    /// the receiver is a class object, `class` or a subclass of it, and
    /// the instance is of that class, built with its `initialize` (`init`
    /// when it is `class` itself).
    ConstructRecv {
        class: ClassId,
        init: Option<MethodId>,
    },
    /// Calling a procedure value (the receiver).
    ProcCall,
    /// `yield`: calls the enclosing method's block.
    Yield,
    /// `super`: the superclass method, on `self`.
    Super(MethodId),
    /// `raise(...)`.
    Raise,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArrayItem {
    pub reg: Reg,
    pub splat: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HashItem {
    Pair(Reg, Reg),
    Splat(Reg),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StrPiece {
    /// A constant string (index into the pool).
    Lit(u32),
    /// A value converted with `to_s`.
    Val(Reg),
}

/// Operators of `Int` and `Float` with an inline implementation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FastOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    Cmp,
}

impl FastOp {
    pub fn from_name(name: &str) -> Option<FastOp> {
        Some(match name {
            "+" => FastOp::Add,
            "-" => FastOp::Sub,
            "*" => FastOp::Mul,
            "/" => FastOp::Div,
            "%" => FastOp::Mod,
            "<" => FastOp::Lt,
            "<=" => FastOp::Le,
            ">" => FastOp::Gt,
            ">=" => FastOp::Ge,
            "==" => FastOp::Eq,
            "!=" => FastOp::Ne,
            "<=>" => FastOp::Cmp,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            FastOp::Add => "+",
            FastOp::Sub => "-",
            FastOp::Mul => "*",
            FastOp::Div => "/",
            FastOp::Mod => "%",
            FastOp::Lt => "<",
            FastOp::Le => "<=",
            FastOp::Gt => ">",
            FastOp::Ge => ">=",
            FastOp::Eq => "==",
            FastOp::Ne => "!=",
            FastOp::Cmp => "<=>",
        }
    }
}

/// A type as far as the runtime can test it (`is_a?`, `as`, rescue).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RtType {
    Nothing,
    Class(ClassId),
    ClassObject,
    Union(Vec<RtType>),
    Tuple(u32),
    Proc,
    Any,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Inst {
    LoadConst {
        dst: Reg,
        idx: u32,
    },
    Move {
        dst: Reg,
        src: Reg,
    },
    SelfRef {
        dst: Reg,
    },
    /// Bound parameter `index` (`nil` when absent).
    Arg {
        dst: Reg,
        index: u32,
    },
    /// Whether parameter `index` was passed (for defaults).
    HasArg {
        dst: Reg,
        index: u32,
    },
    /// The block of the enclosing method (`nil` when none).
    BlockParam {
        dst: Reg,
    },
    FrameGet {
        dst: Reg,
        depth: u32,
        slot: u32,
    },
    FrameSet {
        depth: u32,
        slot: u32,
        src: Reg,
    },
    FieldGet {
        dst: Reg,
        obj: Reg,
        index: u32,
        /// The object's class when statically known (`u32::MAX` otherwise),
        /// for the field's declared type.
        class: ClassId,
    },
    FieldSet {
        obj: Reg,
        index: u32,
        src: Reg,
        class: ClassId,
    },
    /// A field looked up by name on an object of unknown class (hash
    /// patterns); `found` tells whether the field exists.
    FieldGetByName {
        dst: Reg,
        found: Reg,
        obj: Reg,
        name: u32,
    },
    ConstGet {
        dst: Reg,
        id: ConstId,
    },
    ClassRef {
        dst: Reg,
        class: ClassId,
    },
    VariantSingleton {
        dst: Reg,
        class: ClassId,
    },
    Call {
        dst: Reg,
        kind: CallKind,
        /// `None` means `self`.
        recv: Option<Reg>,
        args: Vec<Reg>,
        /// `args` is one register holding an array of the arguments.
        splat: bool,
        /// Keyword arguments: symbol constant and value.
        kw: Vec<(u32, Reg)>,
        /// A hash whose symbol keys are passed as keyword arguments
        /// (`**opts`).
        kw_splat: Option<Reg>,
        block: Option<Reg>,
    },
    /// `x = x.meth(args)`: the receiver is moved out of its variable so a
    /// uniquely referenced collection is updated in place; the result is
    /// stored back.
    OwnedCall {
        dst: Reg,
        method: MethodId,
        recv: VarLoc,
        args: Vec<Reg>,
        kw: Vec<(u32, Reg)>,
    },
    IsNil {
        dst: Reg,
        src: Reg,
    },
    /// Arithmetic/comparison with an inline path for numbers, falling back
    /// to the method.
    BinOp {
        dst: Reg,
        op: FastOp,
        lhs: Reg,
        rhs: Reg,
        /// The method to call when the operands are not numbers; `None`
        /// means look it up by the operator's name.
        method: Option<MethodId>,
    },
    Not {
        dst: Reg,
        src: Reg,
    },
    /// `pattern === value`.
    CaseEq {
        dst: Reg,
        pattern: Reg,
        value: Reg,
    },
    /// `a == b` honouring user-defined equality.
    Equal {
        dst: Reg,
        a: Reg,
        b: Reg,
    },
    /// Whether the value's class is (a subclass of) `class`.
    ClassIsA {
        dst: Reg,
        src: Reg,
        class: ClassId,
    },
    /// `dst` = whether `src` is an object of exactly `class`.
    ClassIs {
        dst: Reg,
        src: Reg,
        class: ClassId,
    },
    IsA {
        dst: Reg,
        src: Reg,
        ty: RtType,
    },
    /// `as` / `as?`: the value itself, `nil` (optional) or a TypeError.
    As {
        dst: Reg,
        src: Reg,
        ty: RtType,
        optional: bool,
        /// Type name for the error message.
        name: String,
    },
    MakeBlock {
        dst: Reg,
        func: FuncId,
        destructure: Option<u32>,
        is_lambda: bool,
    },
    /// `recv.:name`
    MethodRef {
        dst: Reg,
        recv: Reg,
        name: u32,
    },
    /// `&:name`
    /// `&:name`: a procedure calling `name` on its argument; `method`
    /// is the one the checker resolved for the block's parameter type
    /// (an extension method visible there is only reachable this way).
    SymbolProc {
        dst: Reg,
        name: u32,
        method: Option<MethodId>,
    },
    MakeArray {
        dst: Reg,
        items: Vec<ArrayItem>,
    },
    MakeHash {
        dst: Reg,
        items: Vec<HashItem>,
    },
    MakeRange {
        dst: Reg,
        lo: Option<Reg>,
        hi: Option<Reg>,
        exclusive: bool,
    },
    MakeRegexp {
        dst: Reg,
        source: Reg,
        flags: String,
    },
    /// String interpolation; with `into`, appended to that register's
    /// `String::Builder` (no string is made), `dst` getting the builder
    /// (`b << "..."`).
    Interpolate {
        dst: Reg,
        parts: Vec<StrPiece>,
        #[serde(default)]
        into: Option<Reg>,
    },
    /// Intern a string as a symbol.
    ToSym {
        dst: Reg,
        src: Reg,
    },
    /// Whether the value is an Array.
    IsArray {
        dst: Reg,
        src: Reg,
    },
    IsHash {
        dst: Reg,
        src: Reg,
    },
    IsObject {
        dst: Reg,
        src: Reg,
    },
    /// The value as an array: itself when it is one, else `[value]`.
    ToArray {
        dst: Reg,
        src: Reg,
    },
    /// Length of an array or hash as an Int.
    Len {
        dst: Reg,
        src: Reg,
    },
    /// Element `index` of an array (negative counts from the end; `nil`
    /// when out of range).
    ArrayGet {
        dst: Reg,
        arr: Reg,
        index: i32,
    },
    /// `arr[from .. len - drop_last]` as a new array (empty when the range
    /// is inverted).
    ArraySlice {
        dst: Reg,
        arr: Reg,
        from: u32,
        drop_last: u32,
    },
    /// Element at a run-time index (an Int register; `nil` when out of
    /// range).
    ArrayGetReg {
        dst: Reg,
        arr: Reg,
        index: Reg,
    },
    /// `arr[from..to]` with run-time Int bounds (clamped).
    ArraySliceReg {
        dst: Reg,
        arr: Reg,
        from: Reg,
        to: Reg,
    },
    /// Append `src` to the array in `arr`, in place when nothing else
    /// refers to it (building a result inside an inlined loop).
    ArrayPush {
        arr: Reg,
        src: Reg,
    },
    /// Set the registers `from..to` to nil (the fresh state of a block
    /// body or an inlined callee entered again, releasing what the
    /// previous pass left in them).
    ClearRegs {
        from: Reg,
        to: Reg,
    },
    /// The fields of an object as an array.
    ObjectFields {
        dst: Reg,
        src: Reg,
    },
    /// Hash lookup by symbol constant; `found` tells whether the key
    /// exists.
    HashGetSym {
        dst: Reg,
        found: Reg,
        hash: Reg,
        key: u32,
    },
    /// A hash without the given symbol keys.
    HashRest {
        dst: Reg,
        hash: Reg,
        keys: Vec<u32>,
    },
    /// The exception caught by this handler block.
    CatchException {
        dst: Reg,
    },
    /// The flow (exception or other) caught by this `ensure` handler.
    CatchAny {
        dst: Reg,
    },
    /// Raise NoMatchingPatternError for the value.
    NoMatch {
        src: Reg,
        /// `value => pattern` ("does not match") vs `case/in` ("no pattern
        /// matched").
        is_assert: bool,
    },
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum Term {
    Jump(BlockId),
    /// Branch on truthiness.
    Branch {
        cond: Reg,
        then: BlockId,
        els: BlockId,
    },
    /// Return normally from the function.
    Return(Reg),
    /// Raise the exception value.
    Raise(Reg),
    /// `break` out of the block (returns from the function with the
    /// break status).
    BreakOut(Reg),
    /// `return` inside a block: unwinds to the enclosing method.
    ReturnOut(Reg),
    /// Continue the flow caught by `CatchAny`.
    Resume(Reg),
    #[default]
    Unreachable,
}

impl Inst {
    /// The registers an instruction may write.
    pub fn defs(&self) -> Vec<Reg> {
        match self {
            Inst::LoadConst { dst, .. }
            | Inst::Move { dst, .. }
            | Inst::SelfRef { dst }
            | Inst::Arg { dst, .. }
            | Inst::HasArg { dst, .. }
            | Inst::BlockParam { dst }
            | Inst::FrameGet { dst, .. }
            | Inst::FieldGet { dst, .. }
            | Inst::ConstGet { dst, .. }
            | Inst::ClassRef { dst, .. }
            | Inst::VariantSingleton { dst, .. }
            | Inst::Call { dst, .. }
            | Inst::IsNil { dst, .. }
            | Inst::BinOp { dst, .. }
            | Inst::Not { dst, .. }
            | Inst::CaseEq { dst, .. }
            | Inst::Equal { dst, .. }
            | Inst::ClassIsA { dst, .. }
            | Inst::ClassIs { dst, .. }
            | Inst::IsA { dst, .. }
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
            | Inst::IsArray { dst, .. }
            | Inst::IsHash { dst, .. }
            | Inst::IsObject { dst, .. }
            | Inst::ToArray { dst, .. }
            | Inst::Len { dst, .. }
            | Inst::ArrayGet { dst, .. }
            | Inst::ArrayGetReg { dst, .. }
            | Inst::ArraySlice { dst, .. }
            | Inst::ArraySliceReg { dst, .. }
            | Inst::ObjectFields { dst, .. }
            | Inst::HashRest { dst, .. }
            | Inst::CatchException { dst }
            | Inst::CatchAny { dst } => vec![*dst],
            Inst::ClearRegs { from, to } => (*from..*to).collect(),
            Inst::FieldGetByName { dst, found, .. } | Inst::HashGetSym { dst, found, .. } => {
                vec![*dst, *found]
            }
            Inst::OwnedCall { dst, recv, .. } => match recv {
                VarLoc::Reg(r) => vec![*dst, *r],
                _ => vec![*dst],
            },
            Inst::FrameSet { .. }
            | Inst::FieldSet { .. }
            | Inst::ArrayPush { .. }
            | Inst::NoMatch { .. } => vec![],
        }
    }

    /// Replace the registers the instruction reads (the same positions
    /// `uses` lists, plus the location of an `OwnedCall`).
    pub fn map_uses(&mut self, f: &mut dyn FnMut(Reg) -> Reg) {
        match self {
            Inst::LoadConst { .. }
            | Inst::SelfRef { .. }
            | Inst::Arg { .. }
            | Inst::HasArg { .. }
            | Inst::BlockParam { .. }
            | Inst::FrameGet { .. }
            | Inst::ConstGet { .. }
            | Inst::ClassRef { .. }
            | Inst::VariantSingleton { .. }
            | Inst::MakeBlock { .. }
            | Inst::SymbolProc { .. }
            | Inst::CatchException { .. }
            | Inst::CatchAny { .. }
            | Inst::ClearRegs { .. } => {}
            Inst::Move { src, .. }
            | Inst::Not { src, .. }
            | Inst::IsNil { src, .. }
            | Inst::FrameSet { src, .. }
            | Inst::ToSym { src, .. }
            | Inst::IsArray { src, .. }
            | Inst::IsHash { src, .. }
            | Inst::IsObject { src, .. }
            | Inst::ToArray { src, .. }
            | Inst::Len { src, .. }
            | Inst::ObjectFields { src, .. }
            | Inst::ClassIsA { src, .. }
            | Inst::ClassIs { src, .. }
            | Inst::IsA { src, .. }
            | Inst::As { src, .. }
            | Inst::NoMatch { src, .. } => *src = f(*src),
            Inst::FieldGet { obj, .. } | Inst::FieldGetByName { obj, .. } => *obj = f(*obj),
            Inst::FieldSet { obj, src, .. } => {
                *obj = f(*obj);
                *src = f(*src);
            }
            Inst::Call {
                recv,
                args,
                kw,
                kw_splat,
                block,
                ..
            } => {
                if let Some(r) = recv {
                    *r = f(*r);
                }
                for a in args.iter_mut() {
                    *a = f(*a);
                }
                for (_, r) in kw.iter_mut() {
                    *r = f(*r);
                }
                if let Some(r) = kw_splat {
                    *r = f(*r);
                }
                if let Some(r) = block {
                    *r = f(*r);
                }
            }
            Inst::OwnedCall { recv, args, kw, .. } => {
                match recv {
                    VarLoc::Reg(r) => *r = f(*r),
                    VarLoc::Field { obj, .. } => *obj = f(*obj),
                    VarLoc::Frame { .. } => {}
                }
                for a in args.iter_mut() {
                    *a = f(*a);
                }
                for (_, r) in kw.iter_mut() {
                    *r = f(*r);
                }
            }
            Inst::BinOp { lhs, rhs, .. } => {
                *lhs = f(*lhs);
                *rhs = f(*rhs);
            }
            Inst::CaseEq { pattern, value, .. } => {
                *pattern = f(*pattern);
                *value = f(*value);
            }
            Inst::Equal { a, b, .. } => {
                *a = f(*a);
                *b = f(*b);
            }
            Inst::MethodRef { recv, .. } => *recv = f(*recv),
            Inst::MakeArray { items, .. } => {
                for i in items.iter_mut() {
                    i.reg = f(i.reg);
                }
            }
            Inst::MakeHash { items, .. } => {
                for i in items.iter_mut() {
                    match i {
                        HashItem::Pair(k, v) => {
                            *k = f(*k);
                            *v = f(*v);
                        }
                        HashItem::Splat(r) => *r = f(*r),
                    }
                }
            }
            Inst::MakeRange { lo, hi, .. } => {
                if let Some(r) = lo {
                    *r = f(*r);
                }
                if let Some(r) = hi {
                    *r = f(*r);
                }
            }
            Inst::MakeRegexp { source, .. } => *source = f(*source),
            Inst::Interpolate { parts, into, .. } => {
                for p in parts.iter_mut() {
                    if let StrPiece::Val(r) = p {
                        *r = f(*r);
                    }
                }
                if let Some(b) = into {
                    *b = f(*b);
                }
            }
            Inst::ArrayGet { arr, .. } | Inst::ArraySlice { arr, .. } => *arr = f(*arr),
            Inst::ArrayGetReg { arr, index, .. } => {
                *arr = f(*arr);
                *index = f(*index);
            }
            Inst::ArraySliceReg { arr, from, to, .. } => {
                *arr = f(*arr);
                *from = f(*from);
                *to = f(*to);
            }
            Inst::ArrayPush { arr, src } => {
                *arr = f(*arr);
                *src = f(*src);
            }
            Inst::HashGetSym { hash, .. } | Inst::HashRest { hash, .. } => *hash = f(*hash),
        }
    }

    /// The registers an instruction reads.
    pub fn uses(&self) -> Vec<Reg> {
        match self {
            Inst::LoadConst { .. }
            | Inst::SelfRef { .. }
            | Inst::Arg { .. }
            | Inst::HasArg { .. }
            | Inst::BlockParam { .. }
            | Inst::FrameGet { .. }
            | Inst::ConstGet { .. }
            | Inst::ClassRef { .. }
            | Inst::VariantSingleton { .. }
            | Inst::MakeBlock { .. }
            | Inst::SymbolProc { .. }
            | Inst::CatchException { .. }
            | Inst::CatchAny { .. }
            | Inst::ClearRegs { .. } => vec![],
            Inst::Move { src, .. }
            | Inst::Not { src, .. }
            | Inst::IsNil { src, .. }
            | Inst::FrameSet { src, .. }
            | Inst::ToSym { src, .. }
            | Inst::IsArray { src, .. }
            | Inst::IsHash { src, .. }
            | Inst::IsObject { src, .. }
            | Inst::ToArray { src, .. }
            | Inst::Len { src, .. }
            | Inst::ObjectFields { src, .. }
            | Inst::ClassIsA { src, .. }
            | Inst::ClassIs { src, .. }
            | Inst::IsA { src, .. }
            | Inst::As { src, .. }
            | Inst::NoMatch { src, .. } => vec![*src],
            Inst::FieldGet { obj, .. } | Inst::FieldGetByName { obj, .. } => vec![*obj],
            Inst::FieldSet { obj, src, .. } => vec![*obj, *src],
            Inst::Call {
                recv,
                args,
                kw,
                kw_splat,
                block,
                ..
            } => {
                let mut v: Vec<Reg> = recv.iter().copied().collect();
                v.extend(args.iter().copied());
                v.extend(kw.iter().map(|(_, r)| *r));
                v.extend(kw_splat.iter().copied());
                v.extend(block.iter().copied());
                v
            }
            Inst::OwnedCall { recv, args, kw, .. } => {
                let mut v: Vec<Reg> = match recv {
                    VarLoc::Reg(r) => vec![*r],
                    VarLoc::Field { obj, .. } => vec![*obj],
                    VarLoc::Frame { .. } => vec![],
                };
                v.extend(args.iter().copied());
                v.extend(kw.iter().map(|(_, r)| *r));
                v
            }
            Inst::BinOp { lhs, rhs, .. } => vec![*lhs, *rhs],
            Inst::CaseEq { pattern, value, .. } => vec![*pattern, *value],
            Inst::Equal { a, b, .. } => vec![*a, *b],
            Inst::MethodRef { recv, .. } => vec![*recv],
            Inst::MakeArray { items, .. } => items.iter().map(|i| i.reg).collect(),
            Inst::MakeHash { items, .. } => items
                .iter()
                .flat_map(|i| match i {
                    HashItem::Pair(k, v) => vec![*k, *v],
                    HashItem::Splat(r) => vec![*r],
                })
                .collect(),
            Inst::MakeRange { lo, hi, .. } => lo.iter().chain(hi.iter()).copied().collect(),
            Inst::MakeRegexp { source, .. } => vec![*source],
            Inst::Interpolate { parts, into, .. } => parts
                .iter()
                .filter_map(|p| match p {
                    StrPiece::Val(r) => Some(*r),
                    StrPiece::Lit(_) => None,
                })
                .chain(*into)
                .collect(),
            Inst::ArrayGet { arr, .. } | Inst::ArraySlice { arr, .. } => vec![*arr],
            Inst::ArrayGetReg { arr, index, .. } => vec![*arr, *index],
            Inst::ArraySliceReg { arr, from, to, .. } => vec![*arr, *from, *to],
            Inst::ArrayPush { arr, src } => vec![*arr, *src],
            Inst::HashGetSym { hash, .. } | Inst::HashRest { hash, .. } => vec![*hash],
        }
    }
}

impl Term {
    /// Replace the register the terminator reads.
    pub fn map_uses(&mut self, f: &mut dyn FnMut(Reg) -> Reg) {
        match self {
            Term::Branch { cond, .. } => *cond = f(*cond),
            Term::Return(r)
            | Term::Raise(r)
            | Term::BreakOut(r)
            | Term::ReturnOut(r)
            | Term::Resume(r) => *r = f(*r),
            Term::Jump(_) | Term::Unreachable => {}
        }
    }

    /// The register a terminator reads, if any.
    pub fn uses(&self) -> Option<Reg> {
        match self {
            Term::Branch { cond, .. } => Some(*cond),
            Term::Return(r)
            | Term::Raise(r)
            | Term::BreakOut(r)
            | Term::ReturnOut(r)
            | Term::Resume(r) => Some(*r),
            Term::Jump(_) | Term::Unreachable => None,
        }
    }
}

// ----- run-time metadata ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RtClassKind {
    Class,
    Module,
    Data,
    Enum,
    Variant,
    Main,
}

/// A field as the program declares it. `slot` is where it starts in the
/// object's physical fields; a `flat` field is a data value stored in
/// place (its data class's physical fields follow from `slot`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtIvar {
    pub name: String,
    pub ty: Option<String>,
    pub slot: u32,
    pub flat: Option<ClassId>,
    pub default: Option<FuncId>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtField {
    pub name: String,
    /// The default value's initializer (run with `self` = the new object).
    pub default: Option<FuncId>,
    /// The declared type's name (`None` for a type parameter).
    pub ty: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtClass {
    pub name: String,
    pub kind: RtClassKind,
    pub superclass: Option<ClassId>,
    /// Method resolution order, starting with the class itself.
    pub ancestors: Vec<ClassId>,
    /// The physical fields, in layout order (inherited first): a data
    /// value held by value contributes its own physical fields.
    pub fields: Vec<RtField>,
    /// The declared fields, with where each lives.
    #[serde(default)]
    pub ivars: Vec<RtIvar>,
    /// Methods declared by the class, by name (overloads in declaration
    /// order).
    pub methods: HashMap<String, Vec<MethodId>>,
    /// `def self.` methods, by name.
    pub singleton_methods: HashMap<String, Vec<MethodId>>,
    /// Modules whose instance methods are this class's class methods.
    pub extends: Vec<ClassId>,
    /// Nested classes by short name.
    pub members: HashMap<String, ClassId>,
    pub variants: Vec<ClassId>,
    pub variant_of: Option<ClassId>,
    /// Instances compare and hash structurally (data, variants).
    pub structural: bool,
    pub is_exception: bool,
    /// `abstract class`: never instantiated.
    #[serde(default)]
    pub is_abstract: bool,
    pub file: u32,
}

impl RtClass {
    pub fn short_name(&self) -> &str {
        self.name.rsplit("::").next().unwrap_or(&self.name)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RtParamKind {
    Positional,
    Rest,
    KeywordOnly,
    KeywordRest,
    Block,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtParam {
    pub name: String,
    pub kind: RtParamKind,
    pub has_default: bool,
    /// The declared type, for telling overloads apart (`None` for a type
    /// parameter, which matches anything).
    pub ty: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RtSynth {
    None,
    FieldGet(u32),
    FieldSet(u32),
    DataInit,
    DataWith,
    DataToH,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtMethod {
    pub name: String,
    pub owner: ClassId,
    pub singleton: bool,
    pub params: Vec<RtParam>,
    pub has_block: bool,
    pub func: Option<FuncId>,
    /// `Class#name` / `Class.name` for natives.
    pub native_key: Option<String>,
    pub synth: RtSynth,
    pub is_abstract: bool,
    pub is_extension: bool,
    /// Another method of the owner has the same name.
    pub overloaded: bool,
    /// Some descendant of the owner (or an extension on one) declares a
    /// method of this name, so dynamic dispatch may pick it instead.
    pub overridden: bool,
    pub fast_op: Option<FastOp>,
    pub file: u32,
    /// The declared return type's name, when known.
    #[serde(default)]
    pub ret: Option<String>,
    /// Methods of ancestors this one overrides although their parameter
    /// types are written differently (`put(x: T)` of `Box[T]` for
    /// `put(x: Int)` of `IntBox < Box[Int]`); an exact signature match
    /// needs no entry.
    #[serde(default)]
    pub overrides: Vec<MethodId>,
}

impl RtMethod {
    pub fn positional_arity(&self) -> (usize, usize) {
        let mut min = 0;
        let mut max = 0;
        for p in &self.params {
            match p.kind {
                RtParamKind::Positional => {
                    max += 1;
                    if !p.has_default {
                        min += 1;
                    }
                }
                RtParamKind::Rest => max = usize::MAX,
                _ => {}
            }
        }
        (min, max)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtConst {
    pub name: String,
    pub owner: Option<ClassId>,
    pub init: Option<FuncId>,
    pub file: u32,
}

/// Methods added to a class by an extension (always-active ones first).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtExtension {
    pub target: ClassId,
    pub methods: HashMap<String, Vec<MethodId>>,
    /// Active everywhere (declared outside a module): its methods take
    /// part in dispatch by name. A module's extension applies only where
    /// `using` makes it visible, which the checker resolves statically.
    pub always_active: bool,
    /// The modules the extension makes its target conform to: their
    /// methods dispatch to the extension's wherever the value goes.
    pub includes: Vec<ClassId>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct RtBuiltin {
    pub object: ClassId,
    pub nil: ClassId,
    pub bool_: ClassId,
    pub int: ClassId,
    pub float: ClassId,
    pub string: ClassId,
    pub symbol: ClassId,
    pub array: ClassId,
    pub hash: ClassId,
    pub set: ClassId,
    pub range: ClassId,
    pub regexp: ClassId,
    pub proc_: ClassId,
    pub class_: ClassId,
    pub task: ClassId,
    pub channel: ClassId,
    pub atom: ClassId,
    pub scope: ClassId,
    pub duration: ClassId,
    pub bytes: ClassId,
    pub time: ClassId,
    pub array_builder: ClassId,
    pub hash_builder: ClassId,
    pub string_builder: ClassId,
    pub set_builder: ClassId,
    pub bytes_builder: ClassId,
    pub match_data: ClassId,
    pub standard_error: ClassId,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct RtWorld {
    pub classes: Vec<RtClass>,
    #[serde(with = "dropped")]
    pub methods: Vec<RtMethod>,
    pub consts: Vec<RtConst>,
    pub extensions: Vec<RtExtension>,
    /// Top-level classes and modules by name.
    pub top: HashMap<String, ClassId>,
    pub builtin: RtBuiltin,
    /// Display names by file index (0 = the prelude).
    pub file_names: Vec<String>,
}

impl RtWorld {
    pub fn class(&self, id: ClassId) -> &RtClass {
        &self.classes[id as usize]
    }

    pub fn method(&self, id: MethodId) -> &RtMethod {
        &self.methods[id as usize]
    }

    /// Whether the methods of `ext` take part in the dispatch of a
    /// method declared by `owner`: always for an extension active
    /// everywhere, and for the methods of a module the extension makes
    /// its target conform to (a value typed as that module may have come
    /// from anywhere, so its conformance must hold everywhere).
    pub fn extension_dispatches(&self, ext: &RtExtension, owner: ClassId) -> bool {
        ext.always_active
            || ext
                .includes
                .iter()
                .any(|m| *m == owner || self.classes[*m as usize].ancestors.contains(&owner))
    }

    pub fn class_is_a(&self, sub: ClassId, sup: ClassId) -> bool {
        sub == sup
            || sup == self.builtin.object
            || self.classes[sub as usize].ancestors.contains(&sup)
    }

    pub fn is_exception_class(&self, id: ClassId) -> bool {
        self.classes[id as usize].is_exception
    }

    pub fn field_index(&self, id: ClassId, name: &str) -> Option<usize> {
        self.classes[id as usize]
            .fields
            .iter()
            .position(|f| f.name == name)
    }

    /// A class by qualified name (`Task::Cancelled`).
    pub fn class_by_name(&self, name: &str) -> Option<ClassId> {
        let mut cur: Option<ClassId> = None;
        for part in name.split("::") {
            cur = Some(match cur {
                Some(c) => *self.classes[c as usize].members.get(part)?,
                None => *self.top.get(part)?,
            });
        }
        cur
    }
}

/// Serialize a module for embedding in a compiled executable.
/// What `shake::shake` dropped is an empty record: it is written as a
/// single byte and read back as the empty record.
pub trait Droppable: Sized {
    fn is_dropped(&self) -> bool;
    fn dropped() -> Self;
}

impl Droppable for RtMethod {
    fn is_dropped(&self) -> bool {
        self.name.is_empty()
    }

    fn dropped() -> Self {
        RtMethod {
            name: String::new(),
            owner: 0,
            singleton: false,
            params: Vec::new(),
            has_block: false,
            func: None,
            native_key: None,
            synth: RtSynth::None,
            is_abstract: false,
            is_extension: false,
            overloaded: false,
            overridden: false,
            fast_op: None,
            file: 0,
            ret: None,
            overrides: Vec::new(),
        }
    }
}

impl Droppable for Function {
    fn is_dropped(&self) -> bool {
        self.name.is_empty()
    }

    fn dropped() -> Self {
        shake::empty_function(String::new(), FuncKind::TopLevel, 0, 0)
    }
}

mod dropped {
    use super::Droppable;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<T: Serialize + Droppable, S: Serializer>(
        items: &[T],
        s: S,
    ) -> Result<S::Ok, S::Error> {
        let kept: Vec<Option<&T>> = items
            .iter()
            .map(|x| (!x.is_dropped()).then_some(x))
            .collect();
        kept.serialize(s)
    }

    pub fn deserialize<'de, T: Deserialize<'de> + Droppable, D: Deserializer<'de>>(
        d: D,
    ) -> Result<Vec<T>, D::Error> {
        let kept: Vec<Option<T>> = Vec::deserialize(d)?;
        Ok(kept
            .into_iter()
            .map(|x| x.unwrap_or_else(T::dropped))
            .collect())
    }
}

pub fn encode(module: &Module) -> Vec<u8> {
    bincode::serialize(module).expect("serializing QIR")
}

pub fn decode(bytes: &[u8]) -> Result<Module, String> {
    bincode::deserialize(bytes).map_err(|e| e.to_string())
}

pub mod dump;
pub mod shake;
