//! What the compile-time reflection natives (`Type#fields` and friends,
//! docs/14) read: the checker's declarations, which the compiler hands
//! the interpreter it runs `static` statements with. A running program
//! has none (the natives are compile-time only), and a compiled program
//! embeds nothing for them.

use quarz_ir::{ClassId, FuncId};

use crate::interp::Interp;
use crate::value::Value;

/// A field as `Meta::Field` shows it: the declared type's class (type
/// arguments erased, `Object` for a type parameter or a union).
pub struct ReflectField {
    pub name: String,
    pub ty: ClassId,
    pub mutable: bool,
    pub default: bool,
}

/// How a parameter is passed, as `Meta::ParamKind`'s variants are
/// declared: `Required`, `Optional`, `Rest`, `Keyword`, `Block`.
#[derive(Clone, Copy)]
pub enum ReflectKind {
    Required,
    Optional,
    Rest,
    Keyword,
    Block,
}

pub struct ReflectParam {
    pub name: String,
    pub ty: ClassId,
    pub kind: ReflectKind,
}

/// A method's signature as `Meta::MethodSig` shows it.
pub struct ReflectMethod {
    pub name: String,
    pub params: Vec<ReflectParam>,
    pub ret: ClassId,
    pub is_static: bool,
}

pub trait Reflect {
    /// The class's fields, its own and inherited, in declaration order.
    fn fields(&self, class: ClassId) -> Vec<ReflectField>;
    /// The class's instance methods, its own and inherited, in
    /// declaration order (an overriding method once).
    fn methods(&self, class: ClassId) -> Vec<ReflectMethod>;
    /// `Meta::ClassDef#def_method` (docs/14 §5): a method to generate,
    /// recorded for the compiler, or why it cannot be (the message of
    /// the exception raised at the call). Its result is the generation's
    /// position among the statement's (for the method's handle).
    fn generate(&self, interp: &Interp, request: GenRequest) -> Result<usize, String>;
    /// `Meta::ClassDef#def_field`: a field to generate, with its default.
    fn def_field(&self, interp: &Interp, request: FieldRequest) -> Result<(), String>;
    /// `Meta::ClassDef#doc`: the documentation of the next generation.
    fn doc(&self, text: String);
    /// A handle `field_ref`/`method_ref` made (docs/14 §5), checked when
    /// the statement has run whether or not a generated method captures it.
    fn made_handle(&self, interp: &Interp, handle: &Value) -> Result<(), String>;
    /// Entering (`true`) or leaving a `static(...)` run inside a
    /// compile-time run (docs/14 §8).
    fn static_scope(&self, enter: bool);
    /// Why reflecting on `class` here is an error, if it is: inside a
    /// `static(...)` run, a class whose `static` statements (or an
    /// ancestor's) have not all run, whose members the value would see
    /// otherwise than the program's (docs/14 §8).
    fn reflect_refusal(&self, class: ClassId) -> Option<String>;
}

/// A field `def_field` asks for: its type is a class (without type
/// parameters), its default a value made at compile time.
pub struct FieldRequest {
    pub class: ClassId,
    pub name: String,
    pub ty: ClassId,
    pub default: Value,
    pub mutable: bool,
    pub reader: bool,
    pub writer: bool,
}

/// A method `def_method` asks for: the block lifted to it, with the
/// values it captured (`captures`: frame depth above the block's own,
/// slot, value; see `natives::concurrency::captured_slots`).
pub struct GenRequest {
    pub class: ClassId,
    pub name: String,
    /// The parameters' names (as many as the block takes).
    pub params: Vec<String>,
    pub singleton: bool,
    /// `public`, `private` or `protected`.
    pub visibility: String,
    pub func: FuncId,
    pub captures: Vec<(u32, u32, Value)>,
}
