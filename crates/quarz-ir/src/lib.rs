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
use std::collections::HashMap;

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
    Frame { depth: u32, slot: u32 },
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
    },
    FieldSet {
        obj: Reg,
        index: u32,
        src: Reg,
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
    SymbolProc {
        dst: Reg,
        name: u32,
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
    Interpolate {
        dst: Reg,
        parts: Vec<StrPiece>,
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtField {
    pub name: String,
    /// The default value's initializer (run with `self` = the new object).
    pub default: Option<FuncId>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RtClass {
    pub name: String,
    pub kind: RtClassKind,
    pub superclass: Option<ClassId>,
    /// Method resolution order, starting with the class itself.
    pub ancestors: Vec<ClassId>,
    /// All fields in layout order (inherited first).
    pub fields: Vec<RtField>,
    /// Methods declared by the class, by name (overloads in declaration
    /// order).
    pub methods: HashMap<String, Vec<MethodId>>,
    /// Nested classes by short name.
    pub members: HashMap<String, ClassId>,
    pub variants: Vec<ClassId>,
    pub variant_of: Option<ClassId>,
    /// Instances compare and hash structurally (data, variants).
    pub structural: bool,
    pub is_exception: bool,
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
    pub fast_op: Option<FastOp>,
    pub file: u32,
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
pub fn encode(module: &Module) -> Vec<u8> {
    bincode::serialize(module).expect("serializing QIR")
}

pub fn decode(bytes: &[u8]) -> Result<Module, String> {
    bincode::deserialize(bytes).map_err(|e| e.to_string())
}

pub mod dump;
