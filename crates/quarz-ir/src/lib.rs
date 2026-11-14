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

/// A map written in key order: the order a hash map iterates in depends
/// on how it was filled, and the embedded module should be the same
/// bytes for the same program.
fn sorted<K, V, S>(map: &HashMap<K, V>, s: S) -> Result<S::Ok, S::Error>
where
    K: Ord + Serialize,
    V: Serialize,
    S: serde::Serializer,
{
    s.collect_map(map.iter().collect::<std::collections::BTreeMap<_, _>>())
}

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
    /// The names of a block body's keyword-only parameters, in order (a
    /// call binds keyword arguments by name, docs/02 §9).
    #[serde(default)]
    pub kw_names: Vec<String>,
    /// `Proc#arity` of a block body.
    pub arity: i32,
    pub consts: Vec<Constant>,
    pub blocks: Vec<Block>,
    /// Where instructions copied in from inlined callees came from: a
    /// line `INLINE_LINE_FLAG | i` refers to `inlined[i]`.
    #[serde(default)]
    pub inlined: Vec<InlineOrigin>,
    /// For a block given to `Task.blocking`: the slots of the frame it
    /// is made in (its closure's frame) that the call may move rather
    /// than copy, the caller reading them no more (`live::blocking_takes`,
    /// #478).
    #[serde(default)]
    pub takes: Vec<u32>,
}

/// A function without its body (`Function::split`): what the runtime
/// keeps of every function, and all a compiled program carries of one.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FuncInfo {
    pub name: String,
    pub kind: FuncKind,
    pub file: u32,
    pub nregs: u32,
    pub frame_size: u32,
    pub param_kinds: Vec<RtParamKind>,
    #[serde(default)]
    pub kw_names: Vec<String>,
    pub arity: i32,
    pub consts: Vec<Constant>,
    pub inlined: Vec<InlineOrigin>,
    /// What its body does with frames.
    pub facts: FrameFacts,
}

/// What the body of a function does with frames, which the runtime
/// looks at to know what a spawned block reads.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrameFacts {
    /// The frame slots (depth, slot) it reads or writes, in order.
    pub uses: Vec<(u32, u32)>,
    /// The functions of the blocks it creates.
    pub blocks: Vec<FuncId>,
    /// `Function::takes`.
    #[serde(default)]
    pub takes: Vec<u32>,
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
            kw_names: Vec::new(),
            arity: 0,
            consts: Vec::new(),
            blocks: Vec::new(),
            inlined: Vec::new(),
            takes: Vec::new(),
        }
    }

    /// What its body does with frames.
    pub fn frame_facts(&self) -> FrameFacts {
        let mut facts = FrameFacts::default();
        for inst in self.blocks.iter().flat_map(|b| &b.insts) {
            match inst {
                Inst::FrameGet { depth, slot, .. }
                | Inst::FrameSet { depth, slot, .. }
                | Inst::OwnedCall {
                    recv: VarLoc::Frame { depth, slot },
                    ..
                } => facts.uses.push((*depth, *slot)),
                Inst::MakeBlock { func, .. } => facts.blocks.push(*func),
                _ => {}
            }
        }
        facts.uses.sort_unstable();
        facts.uses.dedup();
        facts.blocks.sort_unstable();
        facts.blocks.dedup();
        facts
    }

    /// Its body apart.
    pub fn split(self) -> (FuncInfo, Vec<Block>) {
        let mut facts = self.frame_facts();
        facts.takes = self.takes;
        let info = FuncInfo {
            name: self.name,
            kind: self.kind,
            file: self.file,
            nregs: self.nregs,
            frame_size: self.frame_size,
            param_kinds: self.param_kinds,
            kw_names: self.kw_names,
            arity: self.arity,
            consts: self.consts,
            inlined: self.inlined,
            facts,
        };
        (info, self.blocks)
    }
}

/// The name a `**hash` argument is passed under among a call's keywords,
/// in its place (`Interp::bind_params`): no parameter has it, so only
/// `**kw` takes its entries (docs/01 §9).
pub const KW_SPLAT: &str = "**";

/// The keyword the lowering passes `Meta::ClassDef#def_field` and
/// `#field_ref`, their call's node (docs/14 §5): no parameter has it.
pub const FIELD_REF_SITE: &str = "__site";

/// The keyword under which a call of `JSON.decode[T]` passes `T`'s
/// descriptor (`quarz_types::json_decode`), a string constant.
pub const JSON_DECODE_TYPE: &str = "__decode_type";

/// What a descriptor of `JSON.decode[T]` starts with
/// (`quarz_types::json_decode::PREFIX`, the same): the tree shake keeps
/// the `data` classes one names (`dC:...` nodes).
pub const JSON_TYPE_PREFIX: &str = "\u{1}json-type:";

/// The keyword the lowering passes `Meta::ClassDef#def_method`,
/// `#def_class_method` and `#def_initialize` called in a generic method:
/// the values of its `Type[T]` parameters, the classes its type
/// parameters stand for in this run (docs/14 §5,
/// `Lowerer::carried_type_params`). No parameter has it.
pub const TYPE_ARG_VALUES: &str = "__type_args";

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

/// The handler a flow other than an exception (`break`, `return`,
/// `exit`) leaving `b` goes to: the first `Ensure` along its chain of
/// handlers, past the `Rescue`s (whose own handlers cover them), or none.
pub fn flow_handler(blocks: &[Block], b: &Block) -> Option<BlockId> {
    let mut h = b.handler;
    // (A chain is never longer than the blocks.)
    for _ in 0..=blocks.len() {
        let hd = h?;
        if hd.kind == HandlerKind::Ensure {
            return Some(hd.block);
        }
        h = blocks[hd.block as usize].handler;
    }
    None
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
    /// `recv.instance_exec(args, k: v, &b)` with keyword arguments: runs
    /// the block (`block`) with `self` = the receiver, passing it the
    /// arguments and keywords (docs/01 §9).
    InstanceExec,
    /// `super`: the superclass method, on `self`.
    Super(MethodId),
    /// A function: this method, never looked up again on the receiver
    /// (a built-in `Kernel` function called on the implicit receiver,
    /// which no method of the receiver's class takes over).
    Function(MethodId),
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
    const ALL: [FastOp; 12] = [
        FastOp::Add,
        FastOp::Sub,
        FastOp::Mul,
        FastOp::Div,
        FastOp::Mod,
        FastOp::Lt,
        FastOp::Le,
        FastOp::Gt,
        FastOp::Ge,
        FastOp::Eq,
        FastOp::Ne,
        FastOp::Cmp,
    ];

    /// Its number, as compiled code passes it to the runtime.
    pub fn index(self) -> u32 {
        Self::ALL.iter().position(|o| *o == self).unwrap_or(0) as u32
    }

    pub fn from_index(i: u32) -> FastOp {
        Self::ALL.get(i as usize).copied().unwrap_or(FastOp::Add)
    }

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
    /// A built-in collection of the class whose elements are of these
    /// types (`Array[String]`: one, `Hash[K, V]`: two), for `as`/`is_a?`
    /// with type arguments.
    Elems(ClassId, Vec<RtType>),
    /// A class value (`Type[Object]`).
    ClassObject,
    /// A class value that is the class or a subclass of it, or includes
    /// it (`Type[Model]`, for `as`/`is_a?`).
    ClassOf(ClassId),
    Union(Vec<RtType>),
    /// An array of this many elements, of these types.
    Tuple(Vec<RtType>),
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
    /// A `Move` that is `src`'s last read (`live::mark_moves`): the value
    /// is moved out, `src` left nil. Only the final pass of lowering
    /// writes it.
    Take {
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
        /// The registers the call reads for the last time, moved into
        /// it rather than copied (`live::mark_moves`): bit `i` for
        /// `args[i]` (`i` < 15), bit 15 for `recv`.
        #[serde(default)]
        moved: u16,
        /// For a `CallKind::Method`, the classes the receiver's static
        /// type says it is an instance of (one, or a union's members),
        /// when each is a class: the receiver is then of one of them or a
        /// subclass, which bounds the overrides a run may reach
        /// (`shake::Ref::Bounded`, docs/14 §7). `None` (a module type, a
        /// type parameter, `self` or a call made by a pass): any.
        #[serde(default)]
        recv_classes: Option<Box<[ClassId]>>,
        /// A `CallKind::Method` (or a `Super`) on the function's `self` as
        /// its method has it (an implicit or `self.` call in the method's
        /// body, or in a block whose `self` is the method's): a run of the method
        /// reached through a call on a bounded receiver
        /// (`shake::Ref::Bounded`) has that receiver here, with its bound
        /// (docs/14 §7). A pass that copies the call into another
        /// function (inlining) clears it.
        #[serde(default)]
        on_self: bool,
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
        /// Nothing reads `dst` after (`live::mark_moves`): the result is
        /// not stored there, where a second reference would keep the
        /// collection shared and make its next update copy it.
        #[serde(default)]
        unused: bool,
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
    /// `recv.:name`: a procedure calling `method` on `recv` as a call of
    /// it dispatches (by signature; the method the checker resolved, or a
    /// method handle's, docs/14 §5), or, without one, `name` found by
    /// name and arity.
    MethodRef {
        dst: Reg,
        recv: Reg,
        name: u32,
        method: Option<MethodId>,
    },
    /// `&:name`
    /// `&:name`: a procedure calling `name` on its argument; `method`
    /// is the one the checker resolved for the block's parameter type
    /// (an extension method visible there is only reachable this way).
    /// With `discard`, the procedure gives nil instead of the call's value
    /// (given to a block whose result is `Void`). With `among` (the checks
    /// of a block, once per type, found different methods), the method of
    /// the first type the argument is (docs/05 §9), a TypeError if none.
    SymbolProc {
        dst: Reg,
        name: u32,
        method: Option<MethodId>,
        discard: bool,
        among: Vec<(RtType, MethodId)>,
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
        /// Compiled code reads the element without counting a reference:
        /// `arr` keeps it alive wherever `dst` is (see
        /// `quarz-lower`'s `borrow`). The interpreter copies it.
        #[serde(default)]
        borrow: bool,
        /// The checker types every element an object (`RtClass::objects`:
        /// a `data` type, an enum, an exception, or a class of the
        /// program): compiled code takes the element's allocation with no
        /// tag test.
        #[serde(default)]
        objects: bool,
    },
    /// A new empty array storing `Int`s (or `Float`s with `float`) as
    /// machine words, with room for `capacity` (an Int register) of them:
    /// the array a loop over an `Array[Int]` builds (`map`, `select`).
    ArrayNewWords {
        dst: Reg,
        capacity: Reg,
        float: bool,
    },
    /// Append the Int (or Float) in `src` to an array `ArrayNewWords`
    /// made, which nothing else refers to.
    ArrayPushWord {
        arr: Reg,
        src: Reg,
        float: bool,
    },
    /// `arr[index]`, `Array#[]` with an Int: from the end when negative,
    /// `IndexError` when out of range. `word`: the checker types `arr`
    /// `Array[Int]` (`Some(false)`) or `Array[Float]` (`Some(true)`), so
    /// the element is that number.
    ArrayIndex {
        dst: Reg,
        arr: Reg,
        index: Reg,
        word: Option<bool>,
    },
    /// An array the checker types `Array[Int]` (or `Array[Float]` with
    /// `float`), with its elements stored as machine words: `arr` itself
    /// when they are, else a copy that stores them so. Before a loop
    /// that reads it with `ArrayGetWord`.
    ArrayWords {
        dst: Reg,
        arr: Reg,
        float: bool,
    },
    /// Element `index` of an array that `ArrayWords` made, which must be
    /// in range: the Int (or Float) itself, with no check.
    ArrayGetWord {
        dst: Reg,
        arr: Reg,
        index: Reg,
        float: bool,
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
    /// The end of the scope of a variable whose release may be observed
    /// (an IO handle, an object with `deinitialize`): it lives to here,
    /// not its last use, and is released here (`src` left nil), then the
    /// `deinitialize` of what was released runs.
    Release {
        src: Reg,
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
    /// Start (`enter`) or end handling the exception `src` holds (one
    /// caught by `CatchException`, or the flow of `CatchAny` when it is
    /// one): while a `rescue` clause or an `ensure` clause an exception
    /// passes through runs, it is Ruby's `$!`, the cause of the exceptions
    /// raised meanwhile. Ending it ends those handled since, left by jumps.
    Rescuing {
        src: Reg,
        enter: bool,
    },
    /// In `initialize`: the object `obj` is usable from here on (every
    /// field it requires is assigned), so an `initialize` failing later
    /// leaves it to be finalized as any object (docs/03 §4).
    MarkUsable {
        obj: Reg,
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

/// The registers an instruction reads or writes: a few, kept inline.
pub type Regs = smallvec::SmallVec<[Reg; 4]>;

impl Inst {
    /// The registers an instruction may write.
    pub fn defs(&self) -> Regs {
        match self {
            Inst::LoadConst { dst, .. }
            | Inst::Move { dst, .. }
            | Inst::Take { dst, .. }
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
            | Inst::ArrayWords { dst, .. }
            | Inst::ArrayGetWord { dst, .. }
            | Inst::ArrayIndex { dst, .. }
            | Inst::ArrayNewWords { dst, .. }
            | Inst::ArraySlice { dst, .. }
            | Inst::ArraySliceReg { dst, .. }
            | Inst::ObjectFields { dst, .. }
            | Inst::HashRest { dst, .. }
            | Inst::CatchException { dst }
            | Inst::CatchAny { dst } => smallvec::smallvec![*dst],
            Inst::ClearRegs { from, to } => (*from..*to).collect(),
            Inst::Release { src } => smallvec::smallvec![*src],
            Inst::FieldGetByName { dst, found, .. } | Inst::HashGetSym { dst, found, .. } => {
                smallvec::smallvec![*dst, *found]
            }
            Inst::OwnedCall { dst, recv, .. } => match recv {
                VarLoc::Reg(r) => smallvec::smallvec![*dst, *r],
                _ => smallvec::smallvec![*dst],
            },
            Inst::FrameSet { .. }
            | Inst::FieldSet { .. }
            | Inst::ArrayPush { .. }
            | Inst::ArrayPushWord { .. }
            | Inst::Rescuing { .. }
            | Inst::MarkUsable { .. }
            | Inst::NoMatch { .. } => smallvec::smallvec![],
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
            | Inst::Take { src, .. }
            | Inst::Release { src }
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
            | Inst::Rescuing { src, .. }
            | Inst::MarkUsable { obj: src }
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
            Inst::ArrayWords { arr, .. } => *arr = f(*arr),
            Inst::ArrayNewWords { capacity, .. } => *capacity = f(*capacity),
            Inst::ArrayPushWord { arr, src, .. } => {
                *arr = f(*arr);
                *src = f(*src);
            }
            Inst::ArrayGetWord { arr, index, .. } | Inst::ArrayIndex { arr, index, .. } => {
                *arr = f(*arr);
                *index = f(*index);
            }
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
    pub fn uses(&self) -> Regs {
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
            | Inst::ClearRegs { .. } => smallvec::smallvec![],
            Inst::Move { src, .. }
            | Inst::Take { src, .. }
            | Inst::Release { src }
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
            | Inst::Rescuing { src, .. }
            | Inst::MarkUsable { obj: src }
            | Inst::NoMatch { src, .. } => smallvec::smallvec![*src],
            Inst::FieldGet { obj, .. } | Inst::FieldGetByName { obj, .. } => {
                smallvec::smallvec![*obj]
            }
            Inst::FieldSet { obj, src, .. } => smallvec::smallvec![*obj, *src],
            Inst::Call {
                recv,
                args,
                kw,
                kw_splat,
                block,
                ..
            } => {
                let mut v: Regs = recv.iter().copied().collect();
                v.extend(args.iter().copied());
                v.extend(kw.iter().map(|(_, r)| *r));
                v.extend(kw_splat.iter().copied());
                v.extend(block.iter().copied());
                v
            }
            Inst::OwnedCall { recv, args, kw, .. } => {
                let mut v: Regs = match recv {
                    VarLoc::Reg(r) => smallvec::smallvec![*r],
                    VarLoc::Field { obj, .. } => smallvec::smallvec![*obj],
                    VarLoc::Frame { .. } => smallvec::smallvec![],
                };
                v.extend(args.iter().copied());
                v.extend(kw.iter().map(|(_, r)| *r));
                v
            }
            Inst::BinOp { lhs, rhs, .. } => smallvec::smallvec![*lhs, *rhs],
            Inst::CaseEq { pattern, value, .. } => smallvec::smallvec![*pattern, *value],
            Inst::Equal { a, b, .. } => smallvec::smallvec![*a, *b],
            Inst::MethodRef { recv, .. } => smallvec::smallvec![*recv],
            Inst::MakeArray { items, .. } => items.iter().map(|i| i.reg).collect(),
            Inst::MakeHash { items, .. } => items
                .iter()
                .flat_map(|i| -> Regs {
                    match i {
                        HashItem::Pair(k, v) => smallvec::smallvec![*k, *v],
                        HashItem::Splat(r) => smallvec::smallvec![*r],
                    }
                })
                .collect(),
            Inst::MakeRange { lo, hi, .. } => lo.iter().chain(hi.iter()).copied().collect(),
            Inst::MakeRegexp { source, .. } => smallvec::smallvec![*source],
            Inst::Interpolate { parts, into, .. } => parts
                .iter()
                .filter_map(|p| match p {
                    StrPiece::Val(r) => Some(*r),
                    StrPiece::Lit(_) => None,
                })
                .chain(*into)
                .collect(),
            Inst::ArrayGet { arr, .. } | Inst::ArraySlice { arr, .. } => smallvec::smallvec![*arr],
            Inst::ArrayGetReg { arr, index, .. }
            | Inst::ArrayGetWord { arr, index, .. }
            | Inst::ArrayIndex { arr, index, .. } => smallvec::smallvec![*arr, *index],
            Inst::ArrayWords { arr, .. } => smallvec::smallvec![*arr],
            Inst::ArrayNewWords { capacity, .. } => smallvec::smallvec![*capacity],
            Inst::ArrayPushWord { arr, src, .. } => smallvec::smallvec![*arr, *src],
            Inst::ArraySliceReg { arr, from, to, .. } => smallvec::smallvec![*arr, *from, *to],
            Inst::ArrayPush { arr, src } => smallvec::smallvec![*arr, *src],
            Inst::HashGetSym { hash, .. } | Inst::HashRest { hash, .. } => {
                smallvec::smallvec![*hash]
            }
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

/// How an object stores a physical field: a value (two words), or,
/// for a field declared `Int`, `Float` or `Bool`, the machine word of
/// the number or boolean. What a word cannot hold (nil before the field
/// is assigned, a big integer) is marked in it and kept aside (see
/// `quarz_vm::value::Object`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum FieldKind {
    Value,
    Int,
    Float,
    Bool,
}

/// The size of a value in an object or a register (`quarz_vm` checks
/// it).
pub const VALUE_BYTES: u32 = 16;

impl FieldKind {
    pub fn of(ty: Option<&str>) -> FieldKind {
        match ty {
            Some("Int") => FieldKind::Int,
            Some("Float") => FieldKind::Float,
            Some("Bool") => FieldKind::Bool,
            _ => FieldKind::Value,
        }
    }

    pub fn bytes(self) -> u32 {
        match self {
            FieldKind::Value => VALUE_BYTES,
            _ => 8,
        }
    }
}

/// Where an object of a class keeps its physical fields, after its
/// header: each field's kind and byte offset, then, when some field is a
/// machine word, the word that points at what those words cannot hold.
/// The interpreter and compiled code agree through this one function; a
/// subclass's fields extend its superclass's, so they start the same.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldSlots {
    pub kinds: Vec<FieldKind>,
    pub offsets: Vec<u32>,
    /// The offset of the word for what is kept aside, if any.
    pub aside: Option<u32>,
    /// The bytes of it all.
    pub size: u32,
}

pub fn field_slots(fields: &[RtField]) -> FieldSlots {
    let kinds: Vec<FieldKind> = fields
        .iter()
        .map(|f| FieldKind::of(f.ty.as_deref()))
        .collect();
    let mut offsets = Vec::with_capacity(kinds.len());
    let mut size = 0;
    for k in &kinds {
        offsets.push(size);
        size += k.bytes();
    }
    let aside = kinds.iter().any(|k| *k != FieldKind::Value).then(|| {
        size += 8;
        size - 8
    });
    FieldSlots {
        kinds,
        offsets,
        aside,
        size,
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtClass {
    pub name: String,
    pub kind: RtClassKind,
    pub superclass: Option<ClassId>,
    /// Membership: every class and module the class's values are (its
    /// superclasses, its own includes, and every extension's include,
    /// scoped and conditional ones too: `World::runtime_ancestors`), in
    /// resolution order, starting with the class itself. For `is_a?`,
    /// conformance through a module type, and the walks that take the
    /// override table's pairs (`Interp::find_override`); never for a
    /// lookup by name, which `lookup` serves.
    pub ancestors: Vec<ClassId>,
    /// Dispatch by name: the classes and modules whose methods a lookup by
    /// name may find (`World::lookup_ancestors`): `ancestors` without the
    /// modules of scoped or conditional extensions, which override none
    /// of the class's or its ancestors' methods (docs/01 §7). For
    /// `Interp::find_method` (natives' calls by name: `puts`, `hash`, `==`)
    /// and `deinitialize`.
    pub lookup: Vec<ClassId>,
    /// The physical fields, in layout order (inherited first): a data
    /// value held by value contributes its own physical fields.
    pub fields: Vec<RtField>,
    /// The declared fields, with where each lives.
    #[serde(default)]
    pub ivars: Vec<RtIvar>,
    /// No field needs an `initialize` to assign it, so a module's
    /// `initialize` may make one (`World::has_fields_to_assign`).
    #[serde(default)]
    pub module_init: bool,
    /// The `initialize` this class is built with where a class method it
    /// inherits calls `new` passing what the first element's parameters
    /// take (`None`: nothing): the checker's choice among its overloads
    /// (`Output::inherited_inits`), before `Interp::receiver_class_init`'s
    /// own rule.
    #[serde(default)]
    pub inherited_inits: Vec<(Option<MethodId>, MethodId)>,
    /// Methods declared by the class, by name (overloads in declaration
    /// order).
    #[serde(serialize_with = "sorted")]
    pub methods: HashMap<String, Vec<MethodId>>,
    /// `def self.` methods, by name.
    #[serde(serialize_with = "sorted")]
    pub singleton_methods: HashMap<String, Vec<MethodId>>,
    /// Class-side dispatch: the classes and modules whose `def self.`
    /// methods are this class's class methods, in lookup order (the class,
    /// the modules it brings itself, its superclass, the modules that one
    /// brings, ...): `World::resolution` in the declared view (an
    /// extension's include brings witnesses, `class_ext_impls`, not class
    /// methods, #504). The VM's class-side walks read it (#536 step 2).
    pub class_side: Vec<ClassId>,
    /// Whether this class's values are made by the runtime, not by `new`
    /// (`World::built_by_runtime`, #535).
    #[serde(default)]
    pub built_by_runtime: bool,
    /// Nested classes by short name.
    #[serde(serialize_with = "sorted")]
    pub members: HashMap<String, ClassId>,
    pub variants: Vec<ClassId>,
    pub variant_of: Option<ClassId>,
    /// Instances compare and hash structurally (data, variants).
    pub structural: bool,
    /// The class declares a `==` or `hash` with a body (not the
    /// prelude's natives): its instances, and its descendants', are
    /// compared by them as hash keys and set members.
    #[serde(default)]
    pub declares_eq_hash: bool,
    pub is_exception: bool,
    /// `abstract class`: never instantiated.
    #[serde(default)]
    pub is_abstract: bool,
    /// Every value of the class is an object (`World::instances_are_objects`).
    #[serde(default)]
    pub objects: bool,
    pub file: u32,
    /// A library cog's root module: the cog's `[cog] name` and `version`,
    /// what `Cog#name` and `Cog#version` give.
    #[serde(default)]
    pub cog: Option<(String, String)>,
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
    /// A native's default when it is a literal: a call that names a later
    /// parameter by keyword passes it in its place (`Time.utc(2024, hour:
    /// 5)`), the native reading its arguments by position.
    #[serde(default)]
    pub default: Option<Constant>,
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
    /// The positional shape (`RtMethod::shape_of`): two methods of one
    /// shape other than `NO_SHAPE` take the same positional arguments and
    /// block, nothing else, so a call laid out for one can run the other's
    /// body as is (#561).
    #[serde(default = "no_shape")]
    pub shape: u32,
    pub name: String,
    pub owner: ClassId,
    pub singleton: bool,
    pub params: Vec<RtParam>,
    pub has_block: bool,
    /// The block's type as `same_signature` compares it (`None` where it
    /// mentions the method's own type parameters, or with no block).
    #[serde(default)]
    pub block_ty: Option<String>,
    pub func: Option<FuncId>,
    /// `Type#name` / `Type.name` for natives.
    pub native_key: Option<String>,
    pub synth: RtSynth,
    pub is_abstract: bool,
    pub is_extension: bool,
    /// Another method of the owner has the same name.
    pub overloaded: bool,
    /// Some descendant of the owner (or an extension on one) declares a
    /// method of this name, so dynamic dispatch may pick it instead: a
    /// name-based superset of the override table (`overrides`), deciding
    /// only whether a call dispatches at all; #536 step 4 derives it from
    /// one dispatch predicate.
    pub overridden: bool,
    pub fast_op: Option<FastOp>,
    pub file: u32,
    /// The declared return type's name, when known.
    #[serde(default)]
    pub ret: Option<String>,
    /// The override table's entry (`World::overrides`, the one pairing
    /// rule `World::replaces`, #536): every method of an ancestor (or of an
    /// extension of one) this one replaces at run time, and for a class
    /// method the `Type` methods it replaces on its class object. The
    /// single source every reader takes (the interpreter's dispatch,
    /// devirtualization, the checker); with `RtWorld::include_overrides`
    /// and `class_include_overrides` for a module's method in a class
    /// including it.
    #[serde(default)]
    pub overrides: Vec<MethodId>,
    /// For a native: the classes in its result and block types, whose
    /// instances (or those of their descendants) it may make and hand
    /// out (see `shake`).
    #[serde(default)]
    pub makes: Vec<ClassId>,
    /// A method `def_method` generated with `keywords:` (docs/14 §5):
    /// its body takes one argument, the hash of the keywords a call
    /// passed (`Interp::bind_params`), not its parameters one by one.
    #[serde(default)]
    pub keyword_hash: bool,
}

/// The shape of a method with a parameter other than a positional one.
pub const NO_SHAPE: u32 = u32::MAX;

fn no_shape() -> u32 {
    NO_SHAPE
}

impl RtMethod {
    /// A method's positional shape: its number of parameters and whether
    /// it takes a block, when every parameter is positional; `NO_SHAPE`
    /// otherwise (a rest, keywords).
    pub fn shape_of(params: &[RtParam], has_block: bool) -> u32 {
        if params.iter().all(|p| p.kind == RtParamKind::Positional) && params.len() < (1 << 30) {
            ((params.len() as u32) << 1) | u32::from(has_block)
        } else {
            NO_SHAPE
        }
    }

    /// Whether this method's body can run a call laid out for `other`'s:
    /// the same shape, positional only (`shape_of`).
    pub fn same_shape(&self, other: &RtMethod) -> bool {
        self.shape != NO_SHAPE && self.shape == other.shape
    }

    /// Whether this method takes every keyword call `other` takes (as an
    /// override or an implementation of it must, docs/01 §3): each of
    /// `other`'s keywords by name, optional where it is, a `**rest` where
    /// it has one, and no other keyword it requires (one with a default
    /// only beside no `**rest`).
    pub fn keywords_accept(&self, other: &RtMethod) -> bool {
        let kw = |m: &RtMethod| -> Vec<(String, bool)> {
            m.params
                .iter()
                .filter(|p| p.kind == RtParamKind::KeywordOnly)
                .map(|p| (p.name.clone(), p.has_default))
                .collect()
        };
        let rest = |m: &RtMethod| m.params.iter().any(|p| p.kind == RtParamKind::KeywordRest);
        let (mine, theirs) = (kw(self), kw(other));
        // (Each by name: a `**rest` taking one in place of a keyword, or
        // the other's `**rest` feeding a keyword of this one, would let a
        // value of another type through.)
        theirs
            .iter()
            .all(|(n, optional)| match mine.iter().find(|(m, _)| m == n) {
                Some((_, o)) => *o || !optional,
                None => false,
            })
            && mine.iter().all(|(n, optional)| {
                theirs.iter().any(|(t, _)| t == n) || (*optional && !rest(other))
            })
            && rest(other) == rest(self)
    }

    /// The parameters given by position (and `*rest`), in order.
    pub fn positional_params(&self) -> impl Iterator<Item = &RtParam> {
        self.params
            .iter()
            .filter(|p| matches!(p.kind, RtParamKind::Positional | RtParamKind::Rest))
    }

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
    #[serde(serialize_with = "sorted")]
    pub methods: HashMap<String, Vec<MethodId>>,
    /// Active everywhere (the prelude's): its methods take part in
    /// dispatch by name. Any other applies only where it is visible (by
    /// `using`, or a top-level one in its program or cog), which the
    /// checker resolves statically.
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
    pub integer: ClassId,
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
    /// `Cog`: the class of a cog's root module as a value (docs/10 §6).
    #[serde(default)]
    pub cog: ClassId,
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
    pub bytes_match_data: ClassId,
    pub standard_error: ClassId,
    /// `Comparable` and `Enumerable`, whose requirements the gated sends
    /// dispatch (`Interp::send_requirement`, #599).
    #[serde(default)]
    pub comparable: ClassId,
    #[serde(default)]
    pub enumerable: ClassId,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct RtWorld {
    pub classes: Vec<RtClass>,
    #[serde(with = "dropped")]
    pub methods: Vec<RtMethod>,
    pub consts: Vec<RtConst>,
    pub extensions: Vec<RtExtension>,
    /// Abstract methods an extension's method implements for a class
    /// (class, abstract method, implementation): its conformance, which
    /// holds wherever the value goes.
    pub ext_impls: Vec<(ClassId, MethodId, MethodId)>,
    /// (class, module's class method, its witness): what runs in place of
    /// a module's class method for a class conforming to the module
    /// through an extension (`World::class_ext_impls`, #504).
    #[serde(default)]
    pub class_ext_impls: Vec<(ClassId, MethodId, MethodId)>,
    /// (class or module, abstract method, the extension's method): the
    /// method an extension that targets the class gives for the abstract
    /// method, where the extension is active everywhere or makes its
    /// target conform to the method's module (`rescan_extensions`: the
    /// rescan the interpreter made at run time, `Interp::ext_impl`, made
    /// once here, #536 step 3). Sorted by class and method
    /// (`extension_impl`). The runtime reads it before `ext_impls`.
    #[serde(default)]
    pub ext_rescan: Vec<(ClassId, MethodId, MethodId)>,
    /// The checker's witness record (`World::witness_record`, #536 step
    /// 3): (class, abstract module method, its witness), the witness as
    /// recorded, before its resolution for the receiver. Sorted. Every
    /// abstract key of `override_rows` reads it (`build_witness_rows`); a
    /// key it lacks is an internal error.
    #[serde(default)]
    pub witness_record: Vec<(ClassId, MethodId, Option<MethodId>)>,
    /// (class, module method, what runs): for an abstract method, the
    /// record's witness resolved for the class (`witness_record`); for one
    /// with a body, `find_override`; for every key `in_witness_rows`
    /// admits, the method itself when nothing replaces it
    /// (`build_witness_rows`). Sorted. The runtime reads it for those
    /// keys; a key without a row is an internal error.
    #[serde(default)]
    pub override_rows: Vec<(ClassId, MethodId, MethodId)>,
    /// (class, abstract module method, its witness for a call by name):
    /// the record's witness for every abstract key of `override_rows`, as
    /// `override_rows` resolves it. Sorted.
    #[serde(default)]
    pub witness_rows: Vec<(ClassId, MethodId, Option<MethodId>)>,
    /// (class, module class method, what runs on the class object):
    /// `class_method_override` for every key `in_class_override_rows`
    /// admits, the method itself when nothing replaces it
    /// (`build_witness_rows`). Sorted. The runtime reads it for those keys;
    /// a key without a row is an internal error.
    #[serde(default)]
    pub class_override_rows: Vec<(ClassId, MethodId, MethodId)>,
    /// (class, overridden, overriding): the class-relative part of the
    /// override table (`World::include_overrides`, #536): a method of a
    /// module the class includes over a later ancestor's (its superclass's
    /// or an earlier-included module's), and an abstract one of such a
    /// module with what implements it later.
    #[serde(default)]
    pub include_overrides: Vec<(ClassId, MethodId, MethodId)>,
    /// (class, overridden, overriding): the same on the class side
    /// (`World::class_include_overrides`, #536).
    #[serde(default)]
    pub class_include_overrides: Vec<(ClassId, MethodId, MethodId)>,
    /// Top-level classes and modules by name.
    #[serde(serialize_with = "sorted")]
    pub top: HashMap<String, ClassId>,
    pub builtin: RtBuiltin,
    /// Display names by file index (0 = the prelude).
    pub file_names: Vec<String>,
    /// Each file's main pseudo-class (its top-level object's class), by
    /// file index.
    #[serde(default)]
    pub file_mains: Vec<Option<ClassId>>,
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

    /// The row of `ext_rescan` for class `anc` and abstract method `abs`.
    pub fn extension_impl(&self, anc: ClassId, abs: MethodId) -> Option<MethodId> {
        self.ext_rescan
            .binary_search_by_key(&(anc, abs), |(c, a, _)| (*c, *a))
            .ok()
            .map(|i| self.ext_rescan[i].2)
    }

    /// The extension's method that implements abstract method `abs` for
    /// class `anc` itself: the one an extension that makes it conform
    /// (`include`) gives (`ext_rescan`), else the one found where the class
    /// was declared (`ext_impls`).
    pub fn ext_impl(&self, anc: ClassId, abs: MethodId) -> Option<MethodId> {
        self.extension_impl(anc, abs).or_else(|| {
            self.ext_impls
                .iter()
                .find(|(c, a, _)| *c == anc && *a == abs)
                .map(|(_, _, i)| *i)
        })
    }

    /// A method of `cid` (or of an ancestor before the owner of `mid`)
    /// that overrides `mid`: same name, and the same signature when the
    /// name is overloaded.
    pub fn find_override<'m>(
        &self,
        method: &dyn Fn(MethodId) -> &'m RtMethod,
        cid: ClassId,
        mid: MethodId,
    ) -> Option<MethodId> {
        self.find_override_in(method, cid, mid, true)
    }

    /// `find_override`, with its abstract branch (`branch`) or without it
    /// (#536 step 3's S3, item (b): `same_without_branch` compares the
    /// two, for one CI run before the branch is deleted).
    fn find_override_in<'m>(
        &self,
        method: &dyn Fn(MethodId) -> &'m RtMethod,
        cid: ClassId,
        mid: MethodId,
        branch: bool,
    ) -> Option<MethodId> {
        let m = method(mid);
        for anc in &self.class(cid).ancestors {
            let anc = *anc;
            // (An abstract method stands in for none: what implements it
            // for this class may come later, `World::ext_impls`.)
            if anc == m.owner && !m.is_abstract {
                return None;
            }
            // A file's top-level `def`s are functions, not overrides of
            // `Object`'s methods (docs/01 §1).
            if self.class(anc).kind == RtClassKind::Main {
                continue;
            }
            // An abstract method an extension implements for this class
            // (its conformance), unless the class defines its own.
            let own = self.class(anc).methods.contains_key(&m.name);
            if m.is_abstract && branch {
                // What the checker found implements it for this class by
                // signature (an inherited method, past an overload of the
                // name here), then an extension's.
                if let Some((_, _, i)) = self
                    .ext_impls
                    .iter()
                    .find(|(c, a, _)| *c == anc && *a == mid)
                {
                    // A class's or a module's method runs for the receiver
                    // as a call typed through its owner does: the method
                    // that overrides it nearest the receiver, by this same
                    // function (#632); an extension's own is overridden by
                    // nothing.
                    // (Never through this branch again: what is resolved
                    // is not abstract.)
                    let found = if method(*i).is_extension || method(*i).is_abstract {
                        *i
                    } else {
                        self.find_override(method, cid, *i).unwrap_or(*i)
                    };
                    self.same_without_branch(method, cid, mid, found);
                    return Some(found);
                }
                if !own {
                    if let Some(i) = self.ext_impl(anc, mid) {
                        self.same_without_branch(method, cid, mid, i);
                        return Some(i);
                    }
                }
            }
            let mut candidates: Vec<MethodId> = Vec::new();
            for ext in &self.extensions {
                if ext.target == anc && self.extension_dispatches(ext, m.owner) {
                    if let Some(ids) = ext.methods.get(&m.name) {
                        // (Of `m`'s side: an extension keeps both sides'
                        // methods in one table, #590.)
                        candidates
                            .extend(ids.iter().filter(|i| method(**i).singleton == m.singleton));
                    }
                }
            }
            if let Some(ids) = self.class(anc).methods.get(&m.name) {
                candidates.extend(ids);
            }
            // (An abstract one stands in for none, the method's own too;
            // whether one replaces `mid` is the override table's answer
            // alone, #536.)
            candidates.retain(|c| !method(*c).is_abstract);
            if candidates.is_empty() {
                continue;
            }
            // A module's method over it where a class of the receiver's
            // includes the module (`World::include_overrides`).
            let ancestors = &self.class(cid).ancestors;
            if let Some(o) = candidates.iter().find(|c| {
                self.include_overrides
                    .iter()
                    .any(|(k, o, by)| *o == mid && by == *c && ancestors.contains(k))
            }) {
                return Some(*o);
            }
            // What the override table says replaces it (`RtMethod::overrides`,
            // `World::overrides`): any other is an overload, so keep looking.
            if let Some(o) = candidates
                .iter()
                .find(|c| method(**c).overrides.contains(&mid))
            {
                return Some(*o);
            }
        }
        None
    }

    /// Whether (class `cid`, method `mid`) is a key of `override_rows`
    /// (and, when `mid` is abstract, of `witness_rows`): `cid` a class
    /// whose values exist (not a module, not a file's top level), `mid`
    /// an instance method a module among `cid`'s ancestors declares. The
    /// one definition of the key set: the rows are built over it, and a
    /// lookup of a key in it finds a row or is an internal error.
    pub fn in_witness_rows<'m>(
        &self,
        method: &dyn Fn(MethodId) -> &'m RtMethod,
        cid: ClassId,
        mid: MethodId,
    ) -> bool {
        let c = self.class(cid);
        let m = method(mid);
        !matches!(c.kind, RtClassKind::Module | RtClassKind::Main)
            && !m.singleton
            && self.class(m.owner).kind == RtClassKind::Module
            && c.ancestors.contains(&m.owner)
            && self
                .class(m.owner)
                .methods
                .get(&m.name)
                .is_some_and(|ids| ids.contains(&mid))
    }

    /// Fill `override_rows` and `witness_rows` over every key
    /// `in_witness_rows` admits (the witness record's entry, or `find_override` for
    /// each), and `class_override_rows` over every key
    /// `in_class_override_rows` admits (`class_method_override`),
    /// evaluated once. Called where `rescan_extensions` is, after
    /// it (`ext_impl` reads its table): by `quarz_lower::rtworld::build`
    /// and at the end of `shake`, never by the runtime.
    pub fn build_witness_rows(&mut self) {
        let mut rows: Vec<(ClassId, MethodId, MethodId)> = Vec::new();
        let mut witnesses: Vec<(ClassId, MethodId, Option<MethodId>)> = Vec::new();
        {
            let method = |id: MethodId| &self.methods[id as usize];
            for (cid, c) in self.classes.iter().enumerate() {
                let cid = cid as ClassId;
                for anc in &c.ancestors {
                    let a = self.class(*anc);
                    if a.kind != RtClassKind::Module {
                        continue;
                    }
                    for &mid in a.methods.values().flatten() {
                        if method(mid).owner != *anc || !self.in_witness_rows(&method, cid, mid) {
                            continue;
                        }
                        // (An abstract method: the record's witness, resolved
                        // for the class, #536 step 3's S2; a key the record
                        // lacks is an internal error.)
                        if method(mid).is_abstract {
                            let w = self.recorded_witness(&method, cid, mid);
                            rows.push((cid, mid, w.unwrap_or(mid)));
                            witnesses.push((cid, mid, w));
                            continue;
                        }
                        let found = self.find_override(&method, cid, mid).unwrap_or(mid);
                        rows.push((cid, mid, found));
                    }
                }
            }
        }
        let mut class_rows: Vec<(ClassId, MethodId, MethodId)> = Vec::new();
        {
            let method = |id: MethodId| &self.methods[id as usize];
            for (cid, c) in self.classes.iter().enumerate() {
                let cid = cid as ClassId;
                for anc in &c.ancestors {
                    let a = self.class(*anc);
                    if a.kind != RtClassKind::Module {
                        continue;
                    }
                    for &mid in a.singleton_methods.values().flatten() {
                        if method(mid).owner != *anc
                            || !self.in_class_override_rows(&method, cid, mid)
                        {
                            continue;
                        }
                        let found = self.class_method_override(&method, cid, mid).unwrap_or(mid);
                        class_rows.push((cid, mid, found));
                    }
                }
            }
        }
        rows.sort_unstable();
        rows.dedup();
        witnesses.sort_unstable();
        witnesses.dedup();
        class_rows.sort_unstable();
        class_rows.dedup();
        self.override_rows = rows;
        self.witness_rows = witnesses;
        self.class_override_rows = class_rows;
    }

    /// #536 step 3's S3, item (b), for one CI run before the deletion of
    /// `find_override`'s abstract branch: since S2 the rows answer every
    /// module's requirement, so the branch is reached only by
    /// `Interp::override_for` for an abstract class's requirement on a
    /// dynamic call. There `find_override` without the branch must give the
    /// method the branch gives (`found`): the deletion keeps every answer.
    /// A different one is an internal error naming both.
    fn same_without_branch<'m>(
        &self,
        method: &dyn Fn(MethodId) -> &'m RtMethod,
        cid: ClassId,
        mid: MethodId,
        found: MethodId,
    ) {
        let without = self.find_override_in(method, cid, mid, false);
        if without != Some(found) {
            let name = |i: MethodId| {
                let x = method(i);
                format!("{}#{}", self.class(x.owner).name, x.name)
            };
            unreachable!(
                "internal error: `{}` on `{}`: the abstract branch gives `{}`, the override table `{}`",
                name(mid),
                self.class(cid).name,
                name(found),
                without.map_or("none".to_string(), name)
            );
        }
    }

    /// The witness of abstract method `abs` for class `cid` by the record
    /// (`witness_record`), resolved for `cid` as a call typed through its
    /// owner is: a class's or module's method by `find_override`, an
    /// extension's own method as is (#654's rule).
    pub fn recorded_witness<'m>(
        &self,
        method: &dyn Fn(MethodId) -> &'m RtMethod,
        cid: ClassId,
        abs: MethodId,
    ) -> Option<MethodId> {
        let Ok(i) = self
            .witness_record
            .binary_search_by_key(&(cid, abs), |(c, m, _)| (*c, *m))
        else {
            panic!(
                "internal error: the witness record has no entry for `{}`'s `{}`",
                self.class(cid).name,
                method(abs).name
            )
        };
        self.witness_record[i].2.map(|w| {
            if method(w).is_extension || method(w).is_abstract {
                w
            } else {
                self.find_override(method, cid, w).unwrap_or(w)
            }
        })
    }

    /// The row of `override_rows` for (`cid`, `mid`).
    pub fn override_row(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        self.override_rows
            .binary_search_by_key(&(cid, mid), |(c, m, _)| (*c, *m))
            .ok()
            .map(|i| self.override_rows[i].2)
    }

    /// The row of `witness_rows` for (`cid`, `abs`): `None` when the key
    /// has no row, else the witness (or none).
    pub fn witness_row(&self, cid: ClassId, abs: MethodId) -> Option<Option<MethodId>> {
        self.witness_rows
            .binary_search_by_key(&(cid, abs), |(c, m, _)| (*c, *m))
            .ok()
            .map(|i| self.witness_rows[i].2)
    }

    /// The witness of module class method `mid` for class `cid` (#504):
    /// recorded for the nearest class up its superclass chain (an
    /// extension's target, never a module: an extension of a module
    /// includes nothing, rule B), as the instance side's `ext_impls` reach
    /// it.
    pub fn class_witness(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        let w = self;
        // (`RtClass::class_side`, `World::class_side_order`: the checker's
        // order.)
        w.class(cid).class_side.iter().find_map(|k| {
            w.class_ext_impls
                .iter()
                .find(|(x, o, _)| x == k && *o == mid)
                .map(|(_, _, by)| *by)
        })
    }

    /// Whether class `cid` or a superclass includes `module` itself (its
    /// class methods are on `cid`'s class side, `RtClass::class_side`).
    pub fn includes_on_class_side(&self, cid: ClassId, module: ClassId) -> bool {
        self.class(cid).class_side.contains(&module)
    }

    /// The modules class `c` (`cid` or a superclass of it) brings to `cid`'s
    /// class side, in lookup order: the entries after `c` in
    /// `RtClass::class_side` up to the next class (#536 step 2).
    pub fn class_side_modules(&self, cid: ClassId, c: ClassId) -> Vec<ClassId> {
        let world = self;
        let side = &world.class(cid).class_side;
        // (`c` is `cid` or a class up its chain, always in it: a missing
        // entry is an internal error, never an empty part.)
        let at = side.iter().position(|k| *k == c).unwrap_or_else(|| {
            panic!(
                "internal error: `{}` is not on `{}`'s class side",
                world.class(c).name,
                world.class(cid).name
            )
        });
        side[at + 1..]
            .iter()
            .copied()
            .take_while(|k| world.class(*k).kind == RtClassKind::Module)
            .collect()
    }

    /// The class method of `cid` (or of a superclass below the owner of
    /// `mid`) that overrides the class method `mid`.
    pub fn class_method_override<'m>(
        &self,
        method: &dyn Fn(MethodId) -> &'m RtMethod,
        cid: ClassId,
        mid: MethodId,
    ) -> Option<MethodId> {
        let m = method(mid);
        // (An abstract one is passed over: an implementation after it in
        // the lookup order, a superclass's or another module's, runs.)
        // (Whether one replaces it: the override table alone, #536.)
        let replaces = |id: MethodId| {
            let im = method(id);
            !im.is_abstract && im.overrides.contains(&mid)
        };
        let mut found = None;
        // (A module's class method reaches only the classes that include the
        // module themselves: an extension's include brings no class
        // methods, #494. Elsewhere, through a `Type[M]` value holding such a
        // class, the module's own runs.)
        let module_owner = self.class(m.owner).kind == RtClassKind::Module;
        if module_owner && !self.includes_on_class_side(cid, m.owner) {
            // A class conforming through an extension: the witness its
            // conformance recorded, the nearest up the chain (a subclass
            // conforming on its own has its own), run as is (#504).
            // (Fixed: the witness runs for the class and its subclasses
            // alike; the module's default is the module's own.)
            if let Some(by) = self.class_witness(cid, mid) {
                found = (by != mid).then_some(by);
            }
            return found;
        }
        let mut cur = Some(cid);
        'chain: while let Some(c) = cur {
            if c == m.owner && !m.is_abstract {
                break;
            }
            let class = self.class(c);
            if let Some(ids) = class.singleton_methods.get(&m.name) {
                if let Some(id) = ids.iter().copied().find(|&id| replaces(id)) {
                    found = Some(id);
                    break;
                }
            }
            // A module's class method the class's includes put in its place
            // (over a superclass's or an earlier-included module's, docs/01
            // §6, `World::class_include_overrides`): before the walk below,
            // which stops at the module that declares `mid`.
            if let Some(&(_, _, by)) = self
                .class_include_overrides
                .iter()
                .find(|(k, o, _)| *k == c && *o == mid)
            {
                found = Some(by);
                break;
            }
            // A module's class method (`include`, docs/01 §6): the
            // modules the class includes, the last first, up to the one
            // that declares it.
            for module in &self.class_side_modules(cid, c) {
                if *module == m.owner {
                    if m.is_abstract {
                        continue;
                    }
                    break 'chain;
                }
                let mc = self.class(*module);
                if let Some(ids) = mc.singleton_methods.get(&m.name) {
                    if let Some(id) = ids
                        .iter()
                        .copied()
                        .find(|&id| method(id).owner == *module && replaces(id))
                    {
                        found = Some(id);
                        break 'chain;
                    }
                }
            }
            cur = class.superclass;
        }
        found
    }

    /// Whether (class `cid`, class method `mid`) is a key of
    /// `class_override_rows`: `cid` a class (not a module, not a file's top
    /// level), `mid` a class method a module among `cid`'s ancestors
    /// declares. The one definition of the key set: the rows are built over
    /// it, and a lookup of a key in it finds a row or is an internal error.
    pub fn in_class_override_rows<'m>(
        &self,
        method: &dyn Fn(MethodId) -> &'m RtMethod,
        cid: ClassId,
        mid: MethodId,
    ) -> bool {
        let c = self.class(cid);
        let m = method(mid);
        !matches!(c.kind, RtClassKind::Module | RtClassKind::Main)
            && m.singleton
            && self.class(m.owner).kind == RtClassKind::Module
            && c.ancestors.contains(&m.owner)
            && self
                .class(m.owner)
                .singleton_methods
                .get(&m.name)
                .is_some_and(|ids| ids.contains(&mid))
    }

    /// Every witness row as a line (`kind class method answer`, by id),
    /// tagged with `stage`: what `QUARZ_WITNESS_NET=rows` prints where the
    /// rows are built and after `shake`, so that the two can be compared.
    pub fn witness_row_lines(&self, stage: &str) -> Vec<String> {
        let mut out = Vec::new();
        for (c, m, by) in &self.override_rows {
            out.push(format!("witness-rows {stage} override {c} {m} {by}"));
        }
        for (c, m, by) in &self.witness_rows {
            let by = by.map_or("-".to_string(), |b| b.to_string());
            out.push(format!("witness-rows {stage} witness {c} {m} {by}"));
        }
        for (c, m, by) in &self.class_override_rows {
            out.push(format!("witness-rows {stage} class {c} {m} {by}"));
        }
        out
    }

    /// The row of `class_override_rows` for (`cid`, `mid`).
    pub fn class_override_row(&self, cid: ClassId, mid: MethodId) -> Option<MethodId> {
        self.class_override_rows
            .binary_search_by_key(&(cid, mid), |(c, m, _)| (*c, *m))
            .ok()
            .map(|i| self.class_override_rows[i].2)
    }

    /// Fill `ext_rescan`: `rescan` for every class an extension targets
    /// and every abstract method of the name of one of that extension's
    /// methods (no other pair can have an answer). Called in two places
    /// only, never by the runtime: by `quarz_lower::rtworld::build`, over
    /// the world as built (each REPL input builds the whole world again,
    /// so the table is made anew there too), and at the end of `shake`,
    /// which clears the names of the methods it drops and removes them
    /// from the extensions: a compiled program's runtime used to rescan
    /// that shaken world, so the table is made again over it, and names
    /// no dropped method. (It lives here rather than in the lowering
    /// because `shake` is in this crate.)
    pub fn rescan_extensions(&mut self) {
        let mut abstract_by_name: HashMap<&str, Vec<MethodId>> = HashMap::default();
        for (id, m) in self.methods.iter().enumerate() {
            if m.is_abstract {
                abstract_by_name
                    .entry(m.name.as_str())
                    .or_default()
                    .push(id as MethodId);
            }
        }
        let mut keys: Vec<(ClassId, MethodId)> = Vec::new();
        for ext in &self.extensions {
            for name in ext.methods.keys() {
                for abs in abstract_by_name.get(name.as_str()).into_iter().flatten() {
                    keys.push((ext.target, *abs));
                }
            }
        }
        keys.sort_unstable();
        keys.dedup();
        let rows: Vec<(ClassId, MethodId, MethodId)> = keys
            .into_iter()
            .filter_map(|(anc, abs)| self.rescan(anc, abs).map(|i| (anc, abs, i)))
            .collect();
        self.ext_rescan = rows;
    }

    /// The extension's method that implements abstract method `abs` for
    /// class `anc` itself: the one an extension that makes it conform
    /// (`include`), or is active everywhere, gives. (Moved as it was from
    /// the interpreter's `ext_impl`, which made this scan at run time.)
    fn rescan(&self, anc: ClassId, abs: MethodId) -> Option<MethodId> {
        let m = self.method(abs);
        // (Of the extension's methods of the name, one that takes what the
        // abstract method's callers pass, as the checker's `implements`; an
        // overload of another arity is not it.)
        let (amin, amax) = m.positional_arity();
        let takes = |i: MethodId| {
            let c = self.method(i);
            let (cmin, cmax) = c.positional_arity();
            // (Of `abs`'s side, #590.)
            !c.is_abstract
                && c.singleton == m.singleton
                && c.has_block == m.has_block
                && cmin <= amin
                && cmax >= amax
                && c.keywords_accept(m)
        };
        for ext in &self.extensions {
            if ext.target == anc && self.extension_dispatches(ext, m.owner) {
                if let Some(ids) = ext.methods.get(&m.name) {
                    let exact = ids
                        .iter()
                        .find(|i| takes(**i) && self.same_signature(**i, abs));
                    if let Some(i) = exact.or_else(|| ids.iter().find(|i| takes(**i))) {
                        return Some(*i);
                    }
                }
            }
        }
        None
    }

    /// Whether `a` stands in for `b` by signature, for `rescan`'s choice
    /// among an extension's methods only (overrides read
    /// `RtMethod::overrides`). (Moved as it was from the interpreter.)
    fn same_signature(&self, a: MethodId, b: MethodId) -> bool {
        let (a, b) = (self.method(a), self.method(b));
        let same_ty = |p: &RtParam, q: &RtParam| p.ty == q.ty || p.ty.is_none() || q.ty.is_none();
        a.positional_params().count() == b.positional_params().count()
            && a.positional_params()
                .zip(b.positional_params())
                .all(|(p, q)| p.kind == q.kind && same_ty(p, q))
            && a.keywords_accept(b)
            // (Both with a block or neither, as the checker has it:
            // `block_ty` is `None` for no block too.)
            && a.has_block == b.has_block
            && (a.block_ty == b.block_ty || a.block_ty.is_none() || b.block_ty.is_none())
            && a.params
                .iter()
                .filter(|p| matches!(p.kind, RtParamKind::KeywordOnly | RtParamKind::KeywordRest))
                .all(|p| {
                    // (By name, and `**rest` with `**rest`.)
                    b.params
                        .iter()
                        .find(|q| {
                            q.kind == p.kind
                                && (q.kind == RtParamKind::KeywordRest || q.name == p.name)
                        })
                        .is_none_or(|q| same_ty(p, q))
                })
    }

    /// Membership at run time: whether a value of class `sub` is a `sup`
    /// (`RtClass::ancestors`, every conformance, an extension's too, #515,
    /// and nothing else). `is_a?`, `as`/`as?`, `case`/`in` class patterns,
    /// `rescue` and the typed checks (`QUARZ_VERIFY`, compiled code's "a
    /// value not of its static type") read it; never method lookup, which
    /// reads `RtClass::lookup` (#536 step 2).
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
            shape: NO_SHAPE,
            name: String::new(),
            owner: 0,
            singleton: false,
            params: Vec::new(),
            has_block: false,
            block_ty: None,
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
            makes: Vec::new(),
            keyword_hash: false,
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

impl Droppable for FuncInfo {
    fn is_dropped(&self) -> bool {
        self.name.is_empty()
    }

    fn dropped() -> Self {
        // As `shake::empty_function`'s, without building a body.
        FuncInfo {
            name: String::new(),
            kind: FuncKind::TopLevel,
            file: 0,
            nregs: 1,
            frame_size: 0,
            param_kinds: Vec::new(),
            kw_names: Vec::new(),
            arity: 0,
            consts: Vec::new(),
            inlined: Vec::new(),
            facts: FrameFacts::default(),
        }
    }
}

/// What a compiled program carries of its module: the functions without
/// their bodies (its machine code runs them), the methods apart.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Image {
    pub world: RtWorld,
    #[serde(with = "dropped")]
    pub functions: Vec<FuncInfo>,
    pub units: Vec<Unit>,
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

/// The encoding of a module embedded in a compiled program (read once at
/// its start-up).
fn bincode_config() -> impl bincode::config::Config {
    bincode::config::legacy()
}

pub fn encode(module: &Module) -> Vec<u8> {
    bincode::serde::encode_to_vec(module, bincode_config()).expect("serializing QIR")
}

pub fn encode_image(image: &Image) -> Vec<u8> {
    bincode::serde::encode_to_vec(image, bincode_config()).expect("serializing a program")
}

pub fn decode_image(bytes: &[u8]) -> Result<Image, String> {
    bincode::serde::decode_from_slice(bytes, bincode_config())
        .map(|(image, _)| image)
        .map_err(|e| e.to_string())
}

pub fn decode(bytes: &[u8]) -> Result<Module, String> {
    bincode::serde::decode_from_slice(bytes, bincode_config())
        .map(|(module, _)| module)
        .map_err(|e| e.to_string())
}

/// One method, encoded apart (a compiled program decodes each the first
/// time it is needed: see `quarz_vm::methods`).
pub fn encode_method(m: &RtMethod) -> Vec<u8> {
    bincode::serde::encode_to_vec(m, bincode_config()).expect("serializing a method")
}

pub fn decode_method(bytes: &[u8]) -> Result<RtMethod, String> {
    bincode::serde::decode_from_slice(bytes, bincode_config())
        .map(|(m, _)| m)
        .map_err(|e| e.to_string())
}

pub mod dump;
pub mod live;
pub mod shake;
