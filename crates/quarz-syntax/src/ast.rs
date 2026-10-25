//! The abstract syntax tree.
//!
//! Every expression carries a [`NodeId`] so that later passes (type checking,
//! evaluation) can attach information in side tables without mutating the
//! tree. Declarations are expressions too, as in Ruby, so a file body and a
//! class body are both `Vec<Expr>`.

use crate::source::Span;
use serde::{Deserialize, Serialize};

pub type NodeId = u32;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Program {
    pub body: Vec<Expr>,
    pub span: Span,
    /// The documentation comments, by the line they document, in order.
    pub docs: Vec<crate::doc::Doc>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Expr {
    pub id: NodeId,
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum ExprKind {
    // ----- literals -----
    Nil,
    True,
    False,
    SelfRef,
    Int(IntLit),
    Float(f64),
    Str(Vec<StrPart>),
    /// `b"..."`, decoded.
    Bytes(Vec<u8>),
    Symbol(String),
    /// `:"..."` with interpolation.
    DSymbol(Vec<StrPart>),
    Regexp {
        parts: Vec<StrPart>,
        flags: String,
    },
    /// `[a, b, *c]`
    Array(Vec<Arg>),
    /// `{ a: 1, "b" => 2, **h }`
    Hash(Vec<HashEntry>),
    Range {
        lo: Option<Box<Expr>>,
        hi: Option<Box<Expr>>,
        exclusive: bool,
    },
    /// `->(x) { }`
    Lambda(Box<Block>),
    /// `__FILE__`, `__LINE__`, `__method__`
    Magic(Magic),

    // ----- variables and names -----
    /// A local variable that is known to be declared at this point.
    Local(String),
    IVar(String),
    Const(ConstPath),
    /// `Array[Int]` in expression position: a generic type used as a value
    /// (receiver of `.new` etc.).
    TypeApp(TypeExpr),

    // ----- calls -----
    Call(Box<Call>),
    /// `recv.:name`
    MethodRef {
        recv: Box<Expr>,
        name: String,
    },
    Yield(Vec<Arg>),
    Super {
        /// `None` for a bare `super` (forward the same arguments).
        args: Option<Vec<Arg>>,
        block: Option<Box<Block>>,
    },

    // ----- assignment -----
    Assign {
        target: Box<LValue>,
        value: Box<Expr>,
    },
    OpAssign {
        target: Box<LValue>,
        op: crate::token::OpAssign,
        value: Box<Expr>,
    },
    /// `a, b = ...`, `a, *b = ...`
    MultiAssign {
        targets: Vec<MultiTarget>,
        value: Box<Expr>,
    },
    /// `x: Int = value`
    TypedDecl {
        name: String,
        ty: TypeExpr,
        value: Box<Expr>,
    },

    // ----- operators with their own semantics -----
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),

    // ----- control flow -----
    If {
        cond: Box<Expr>,
        then: Vec<Expr>,
        els: Option<Vec<Expr>>,
    },
    While {
        cond: Box<Expr>,
        body: Vec<Expr>,
        /// `until`: loop while the condition is false.
        negate: bool,
        /// `begin ... end while cond`: run the body before the first test.
        do_while: bool,
    },
    Case {
        subject: Option<Box<Expr>>,
        whens: Vec<When>,
        els: Option<Vec<Expr>>,
    },
    CaseIn {
        subject: Box<Expr>,
        arms: Vec<InArm>,
        els: Option<Vec<Expr>>,
    },
    /// `value => pattern` (raises on failure) or `value in pattern`
    /// (returns a boolean).
    MatchPattern {
        value: Box<Expr>,
        pattern: Box<Pattern>,
        raises: bool,
    },
    Begin(Box<BeginBlock>),
    Return(Option<Box<Expr>>),
    Break(Option<Box<Expr>>),
    Next(Option<Box<Expr>>),
    Retry,
    /// A parenthesized sequence `(a; b)`.
    Seq(Vec<Expr>),
    /// `for … do … end`: both its expansions (see `ForExpr`).
    For(Box<ForExpr>),

    // ----- declarations -----
    ClassDef(Box<ClassDef>),
    ModuleDef(Box<ModuleDef>),
    DataDef(Box<DataDef>),
    EnumDef(Box<EnumDef>),
    ExtensionDef(Box<ExtensionDef>),
    MethodDef(Box<MethodDef>),
    FieldDecl(Box<FieldDecl>),
    /// `attr_reader :a, :b`
    AttrDecl {
        kind: AttrKind,
        names: Vec<String>,
    },
    /// `include M`, `extend M`
    Mixin {
        kind: MixinKind,
        types: Vec<TypeExpr>,
    },
    /// `private`, `private :a, :b`. (`private def ...` sets the modifier on
    /// the method instead.)
    Visibility {
        visibility: Visibility,
        names: Vec<String>,
    },
    Alias {
        new_name: String,
        old_name: String,
    },
    TypeAlias {
        name: String,
        type_params: Vec<TypeParam>,
        ty: TypeExpr,
    },
    ConstAssign {
        name: String,
        value: Box<Expr>,
    },
    Using(ConstPath),
    Require {
        path: String,
        relative: bool,
    },
    Extern {
        abi: String,
        decls: Vec<MethodDef>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntLit {
    pub digits: String,
    pub base: u8,
    /// The value when it fits in 64 bits (parsed once by the parser).
    pub value: Option<i64>,
}

impl IntLit {
    pub fn new(digits: String, base: u8) -> IntLit {
        let value = i64::from_str_radix(&digits, base as u32).ok();
        IntLit {
            digits,
            base,
            value,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Magic {
    File,
    Line,
    Method,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum StrPart {
    Lit(String),
    Interp(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstPath {
    /// `::Foo` (lookup from the top level).
    pub absolute: bool,
    /// `cog::Foo` (lookup in the current cog's root module); with no names,
    /// `cog` itself.
    pub cog: bool,
    pub names: Vec<String>,
}

impl ConstPath {
    pub fn simple(name: impl Into<String>) -> ConstPath {
        ConstPath {
            absolute: false,
            cog: false,
            names: vec![name.into()],
        }
    }

    pub fn last(&self) -> &str {
        self.names.last().map(String::as_str).unwrap_or("")
    }
}

impl std::fmt::Display for ConstPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.absolute {
            write!(f, "::")?;
        }
        if self.cog {
            write!(f, "cog")?;
            if !self.names.is_empty() {
                write!(f, "::")?;
            }
        }
        write!(f, "{}", self.names.join("::"))
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Call {
    pub recv: Option<Expr>,
    pub name: String,
    pub args: Vec<Arg>,
    pub block: Option<Block>,
    /// `recv&.name`
    pub safe_nav: bool,
    /// Whether the call was written with parentheses or arguments. `foo`
    /// alone (no receiver, no args) may be a local variable the checker
    /// cannot see; the parser already resolved locals, so this is a method
    /// call, but the flag helps error messages.
    pub has_parens: bool,
    /// Explicit method type arguments: `max_by[Person, Int](...)`.
    pub type_args: Vec<TypeExpr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Arg {
    Positional(Expr),
    Splat(Expr),
    Keyword {
        name: String,
        value: Expr,
        span: Span,
    },
    DoubleSplat(Expr),
    BlockPass(Expr),
}

impl Arg {
    pub fn span(&self) -> Span {
        match self {
            Arg::Positional(e) | Arg::Splat(e) | Arg::DoubleSplat(e) | Arg::BlockPass(e) => e.span,
            Arg::Keyword { span, .. } => *span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum HashEntry {
    Pair { key: Expr, value: Expr },
    DoubleSplat(Expr),
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Block {
    pub params: Params,
    pub body: Vec<Expr>,
    pub span: Span,
    /// `{ }` rather than `do ... end` (affects nothing semantically).
    pub braces: bool,
    /// The declared result of a lambda (`->(x: Int) -> Nil { }`); `None`
    /// for blocks.
    pub ret: Option<TypeExpr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum LValue {
    Local {
        name: String,
        span: Span,
    },
    IVar(String),
    Const(String),
    /// `recv.name = value` → `recv.name=(value)`
    Attr {
        recv: Expr,
        name: String,
        safe_nav: bool,
    },
    /// `recv[args] = value` → `recv.[]=(args, value)`
    Index {
        recv: Expr,
        args: Vec<Arg>,
    },
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum MultiTarget {
    Single(LValue),
    Splat(Option<LValue>),
    Nested(Vec<MultiTarget>),
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct When {
    pub conds: Vec<Arg>,
    pub body: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct InArm {
    pub pattern: Pattern,
    pub guard: Option<Guard>,
    pub body: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Guard {
    pub cond: Expr,
    /// `unless` guard.
    pub negate: bool,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BeginBlock {
    pub body: Vec<Expr>,
    pub rescues: Vec<Rescue>,
    pub else_body: Option<Vec<Expr>>,
    pub ensure: Option<Vec<Expr>>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Rescue {
    pub classes: Vec<TypeExpr>,
    pub var: Option<String>,
    pub body: Vec<Expr>,
    pub span: Span,
}

// ----- patterns -----

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Pattern {
    pub span: Span,
    pub kind: PatternKind,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum PatternKind {
    /// A literal or other value compared with `===`.
    Value(Expr),
    /// `^x`, `^(expr)`
    Pin(Expr),
    /// A variable binding (including `_`).
    Bind(String),
    /// `pat => name`
    Capture(Box<Pattern>, String),
    Alt(Vec<Pattern>),
    /// A constant used as a type test: `in Int`, `in Shape::Circle`.
    Const(ConstPath),
    /// `Const(...)` / `Const[...]` with an array-style sub-pattern.
    ConstArray(ConstPath, Box<ArrayPattern>),
    /// `Const(key: pat, ...)` with a hash-style sub-pattern.
    ConstHash(ConstPath, Box<HashPattern>),
    Array(ArrayPattern),
    /// `[*, x, *]`
    Find {
        pre_rest: Option<String>,
        middle: Vec<Pattern>,
        post_rest: Option<String>,
    },
    Hash(HashPattern),
    Range {
        lo: Option<Expr>,
        hi: Option<Expr>,
        exclusive: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ArrayPattern {
    pub pre: Vec<Pattern>,
    /// `Some(None)` for an anonymous `*`, `Some(Some(name))` for `*name`.
    pub rest: Option<Option<String>>,
    pub post: Vec<Pattern>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct HashPattern {
    pub pairs: Vec<HashPatternPair>,
    /// `**rest` / `**nil`
    pub rest: Option<HashPatternRest>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct HashPatternPair {
    pub key: String,
    /// `None` for `key:` alone, which binds `key`.
    pub pattern: Option<Pattern>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HashPatternRest {
    Bind(String),
    Nil,
}

// ----- types -----

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TypeExpr {
    pub span: Span,
    pub kind: TypeExprKind,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum TypeExprKind {
    /// `Int`, `Foo::Bar`, `Array[Int]`
    Named {
        path: ConstPath,
        args: Vec<TypeExpr>,
    },
    Nilable(Box<TypeExpr>),
    Union(Vec<TypeExpr>),
    Tuple(Vec<TypeExpr>),
    Proc {
        /// `Recv.(A) -> R`: the block runs with `self` = a `Recv`.
        recv: Option<Box<TypeExpr>>,
        params: Vec<TypeExpr>,
        ret: Box<TypeExpr>,
        /// `shareable (A) -> R`: a procedure any task may call.
        shareable: bool,
    },
    SelfType,
    Nothing,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TypeParam {
    pub name: String,
    pub variance: Variance,
    pub bounds: Vec<TypeExpr>,
    /// `U >: T`: a lower bound (method type parameters only).
    pub lower: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Variance {
    Invariant,
    Covariant,
    Contravariant,
}

// ----- declarations -----

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Params {
    pub list: Vec<Param>,
}

impl Params {
    pub fn empty() -> Params {
        Params { list: Vec::new() }
    }

    pub fn block_param(&self) -> Option<&Param> {
        self.list.iter().find(|p| p.kind == ParamKind::Block)
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Param {
    pub name: String,
    pub kind: ParamKind,
    pub ty: Option<TypeExpr>,
    pub default: Option<Expr>,
    /// `def initialize(@x: Int)`: also assigns the field.
    pub assigns_ivar: bool,
    /// `&: (A) -> R using M`: extensions active inside a block literal
    /// passed for this (block) parameter.
    pub usings: Vec<ConstPath>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ParamKind {
    /// Before `*`: positional or keyword.
    Positional,
    /// `*rest`
    Rest,
    /// After `*`.
    KeywordOnly,
    /// `**opts`
    KeywordRest,
    /// `&block`
    Block,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Public,
    Protected,
    Private,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MethodDef {
    pub name: String,
    pub singleton: bool,
    pub type_params: Vec<TypeParam>,
    pub params: Params,
    pub ret: Option<TypeExpr>,
    /// `None` for `abstract def` and `native def`.
    pub body: Option<Vec<Expr>>,
    pub is_abstract: bool,
    pub is_native: bool,
    pub visibility: Option<Visibility>,
    pub span: Span,
}

/// A `for` comprehension, in the two expansions the checker chooses
/// between: `comprehension`, the chain of `flat_map`/`filter`/`map` whose
/// value is the collection of the body's values, and `each`, nested
/// `each` calls (a guard an `if` around the rest), for a `for` whose value
/// is not used and whose sources all have `each`: it builds nothing. The
/// code written in the `for` (sources, guards, body) is the same nodes in
/// both; only one expansion is checked and lowered.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ForExpr {
    pub comprehension: Expr,
    pub each: Expr,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ClassDef {
    pub name: ConstPath,
    pub type_params: Vec<TypeParam>,
    pub superclass: Option<TypeExpr>,
    pub body: Vec<Expr>,
    pub is_abstract: bool,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ModuleDef {
    pub name: ConstPath,
    pub type_params: Vec<TypeParam>,
    pub body: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct DataDef {
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub fields: Vec<FieldDecl>,
    pub body: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct EnumDef {
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub variants: Vec<Variant>,
    pub body: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ExtensionDef {
    pub target: TypeExpr,
    pub type_params: Vec<TypeParam>,
    pub body: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FieldDecl {
    pub name: String,
    pub ty: TypeExpr,
    pub mutable: bool,
    pub default: Option<Expr>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AttrKind {
    Reader,
    Writer,
    Accessor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MixinKind {
    Include,
    Extend,
}
