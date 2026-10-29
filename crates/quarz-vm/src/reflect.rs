//! What the compile-time reflection natives (`Type#fields` and friends,
//! docs/14) read: the checker's declarations, which the compiler hands
//! the interpreter it runs `static` statements with. A running program
//! has none (the natives are compile-time only), and a compiled program
//! embeds nothing for them.

use quarz_ir::ClassId;

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
}
