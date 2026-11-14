//! Classes, modules, methods and constants, plus subtyping and method lookup.

use rustc_hash::FxHashMap as HashMap;
use std::rc::Rc;

use quarz_syntax::ast::{Expr, MethodDef, ParamKind, TypeExpr, Variance, Visibility};
use quarz_syntax::Span;

use crate::types::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ClassKind {
    Class,
    Module,
    Data,
    Enum,
    /// An enum variant: a data-like class whose superclass is the enum.
    Variant,
    /// The pseudo-class holding a file's top-level methods.
    Main,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TypeParamInfo {
    pub id: TypeParamId,
    pub name: String,
    pub variance: Variance,
    pub bounds: Vec<Type>,
    /// `U >: T` (method type parameters): `U` is at least `T`.
    pub lower: Option<Type>,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct FieldInfo {
    pub name: String,
    pub ty: Type,
    pub mutable: bool,
    pub default: Option<Rc<Expr>>,
    /// The default of a field a `static` statement generated
    /// (`Meta::ClassDef#def_field`, docs/14 §5): a value, not an
    /// expression.
    pub baked_default: Option<Baked>,
    pub span: Span,
}

impl FieldInfo {
    /// Whether the field has a default (written or generated): an
    /// `initialize` need not assign it.
    pub fn has_default(&self) -> bool {
        self.default.is_some() || self.baked_default.is_some()
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ParamInfo {
    pub name: String,
    pub kind: ParamKind,
    pub ty: Type,
    pub default: Option<Rc<Expr>>,
    /// `def initialize(@x: Int)`
    pub assigns_ivar: bool,
    pub span: Span,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct MethodInfo {
    pub id: MethodId,
    pub name: String,
    pub owner: ClassId,
    pub singleton: bool,
    pub type_params: Vec<TypeParamInfo>,
    pub params: Vec<ParamInfo>,
    /// The `&block` parameter: its name and proc type.
    pub block: Option<(String, Type)>,
    /// `&block: ((A) -> R)?`: the block may be left out, and the
    /// parameter is then `nil`.
    pub block_optional: bool,
    /// Extensions active inside a block literal passed to this method
    /// (`&: (A) -> R using M`).
    pub block_usings: Vec<ExtensionId>,
    /// Declared: a method without one returns nil.
    pub ret: Type,
    pub body: Option<Rc<MethodDef>>,
    pub is_abstract: bool,
    pub is_native: bool,
    /// `static def`: callable at compile time, by a class body's `static`
    /// statement (docs/14). A `static native def` only there.
    pub is_static: bool,
    pub visibility: Visibility,
    pub span: Span,
    /// The extension the method was declared in, if any.
    pub extension: Option<ExtensionId>,
    /// Number of local variable slots the body needs (set by the checker).
    pub frame_size: u32,
    /// Whether the body has been checked.
    pub checked: bool,
    /// Generated accessors and data-type methods.
    pub synth: Synth,
    /// For `alias`: the original method.
    pub alias_of: Option<MethodId>,
    /// Source file index (0 = prelude, 1 = the user program).
    pub file: u32,
    /// A method a `static` statement generated (`Meta::ClassDef#def_method`,
    /// docs/14 §5): its body is a block lifted to a method.
    pub generated: Option<Generated>,
    /// A class method that calls `new` on its receiver (`def self.run =
    /// new.perform`): called with an abstract class written as the
    /// receiver it is refused (#423). Part of the interface, so that
    /// callers in other files see it.
    #[serde(default)]
    pub builds_self: bool,
    /// A module's class method that depends on the class including the
    /// module, and why (`Self` in its signature, `new`, an abstract class
    /// method of the module it calls, or abstract itself): calling it on
    /// the module itself (`M.make`) is refused (#494). Part of the
    /// interface, so that callers in other files see it.
    #[serde(default)]
    pub needs_includer: Option<String>,
}

/// What a `static` statement's `def_method` recorded (docs/14 §5): the
/// block function the body is a copy of, with the values it captured
/// baked in where it read them, and where it was generated.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Generated {
    /// The block's function, in the compile-time lowering.
    pub func: u32,
    /// For each frame slot the block read outside itself (`depth` frames
    /// above its own, counted as `FrameGet` does), its value.
    pub captures: Vec<(u32, u32, Baked)>,
    /// The `static` statement: its file and position.
    pub by: (u32, Span),
    /// The block the body was lifted from (`quarz check --expand` shows
    /// it in place of the body).
    pub block: Span,
    /// The `doc` text given before `def_method`.
    pub doc: Option<String>,
    /// Made with `keywords:` (docs/14 §5): the method's keyword
    /// parameters are bound at run time as one `**` parameter, the hash
    /// of those a call passed, which the body (the block) takes.
    #[serde(default)]
    pub keywords: bool,
    /// Made by `def_initialize` (docs/14 §5): an `initialize` overload.
    #[serde(default)]
    pub initialize: bool,
    /// The `JSON.decode[T]` descriptors of the body whose `T` mentions a
    /// type parameter the method carries: where each marker is (the
    /// function, in the compile-time lowering, and the constant's index)
    /// and the descriptor with the statement's classes, which the
    /// method's lowering puts in its place.
    #[serde(default)]
    pub decode: Vec<(u32, u32, String)>,
}

/// A compile-time value a generated method embeds as a constant (docs/14
/// §5): what is immutable and has a literal or a construction without
/// code of its own. Anything else cannot be captured by a lifted block.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Baked {
    Nil,
    Bool(bool),
    Int(i64),
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
    /// A class object (a `Type[T]` value).
    Class(ClassId),
    /// An enum variant without fields.
    Variant(ClassId),
    Array(Vec<Baked>),
    Hash(Vec<(Baked, Baked)>),
    Range {
        lo: Option<Box<Baked>>,
        hi: Option<Box<Baked>>,
        exclusive: bool,
    },
    /// A `data` value or a variant with fields: the class and its fields
    /// in layout order, set without running `initialize`.
    Data(ClassId, Vec<Baked>),
}

/// Methods generated by the compiler rather than written by the user.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Synth {
    None,
    /// `attr_reader` / data field reader.
    FieldGet(String),
    /// `attr_writer`.
    FieldSet(String),
    /// The constructor of a data type or enum variant.
    DataInit,
    /// `with(field: value)` on a data type.
    DataWith,
    /// `to_h` on a data type.
    DataToH,
}

impl MethodInfo {
    /// The key under which the runtime registers a native implementation:
    /// `Int#+` for instance methods, `Int.parse` for singleton methods.
    pub fn native_key(&self, world: &World) -> String {
        let owner = &world.classes[self.owner as usize].name;
        let sep = if self.singleton { "." } else { "#" };
        format!("{owner}{sep}{}", self.name)
    }

    /// Whether this method takes every keyword call `other` takes (as an
    /// override or an implementation of it must, docs/01 §3): each of
    /// `other`'s keywords by name, optional where it is, a `**rest` where
    /// it has one, and no other keyword it requires (one with a default
    /// only beside no `**rest`) (`RtMethod::keywords_accept`).
    pub fn keywords_accept(&self, other: &MethodInfo) -> bool {
        let kw = |m: &MethodInfo| -> Vec<(String, bool)> {
            m.params
                .iter()
                .filter(|p| p.kind == ParamKind::KeywordOnly)
                .map(|p| (p.name.clone(), p.default.is_some()))
                .collect()
        };
        let rest = |m: &MethodInfo| m.params.iter().any(|p| p.kind == ParamKind::KeywordRest);
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
    pub fn positional_params(&self) -> Vec<&ParamInfo> {
        self.params
            .iter()
            .filter(|p| matches!(p.kind, ParamKind::Positional | ParamKind::Rest))
            .collect()
    }

    pub fn positional_arity(&self) -> (usize, usize) {
        let mut min = 0;
        let mut max = 0;
        for p in &self.params {
            match p.kind {
                ParamKind::Positional => {
                    max += 1;
                    if p.default.is_none() {
                        min += 1;
                    }
                }
                ParamKind::Rest => max = usize::MAX,
                _ => {}
            }
        }
        (min, max)
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ConstInfo {
    pub id: ConstId,
    pub name: String,
    pub owner: Option<ClassId>,
    pub ty: Option<Type>,
    pub value: Option<Rc<Expr>>,
    pub span: Span,
    /// Set while the initializer is being checked.
    pub checking: bool,
    pub file: u32,
}

/// A `static` statement of a class or module body: a call, on the class
/// being declared, of a `static def` of a dependency (docs/14).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct StaticStmt {
    /// The class or module whose body holds it.
    pub class: ClassId,
    pub file: u32,
    pub expr: Rc<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TypeAliasInfo {
    pub name: String,
    pub owner: Option<ClassId>,
    pub type_params: Vec<TypeParamInfo>,
    pub expr: TypeExpr,
    pub resolved: Option<Type>,
    /// The file that declares it.
    #[serde(default)]
    pub file: u32,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ExtensionInfo {
    pub id: ExtensionId,
    /// The module the extension is declared in (activated by `using`).
    pub module: Option<ClassId>,
    pub target: ClassId,
    pub type_params: Vec<TypeParamInfo>,
    /// The target's type arguments in terms of `type_params`.
    pub target_args: Vec<Type>,
    pub includes: Vec<Type>,
    pub methods: HashMap<String, Vec<MethodId>>,
    pub span: Span,
    /// Prelude extensions are active everywhere.
    pub always_active: bool,
    /// An extension declared at a file's top level (in a library cog, its
    /// root module's body) is active in the files of its group
    /// (`UnitGroup`): the application's or script's, the cog's, the
    /// standard library module's; not in the prelude, nor in other groups.
    pub group: Option<UnitGroup>,
    /// The file that declares it.
    #[serde(default)]
    pub file: u32,
}

/// The files a file belongs with (`World::file_groups`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum UnitGroup {
    /// The application's files, or a script and the files it requires.
    App,
    /// A library cog's files, by index.
    Cog(u32),
    /// A standard library module, by file.
    Std(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Member {
    Class(ClassId),
    Const(ConstId),
    Alias(u32),
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ClassInfo {
    pub id: ClassId,
    /// Qualified name, e.g. `Shape::Circle`.
    pub name: String,
    pub kind: ClassKind,
    pub type_params: Vec<TypeParamInfo>,
    pub superclass: Option<Type>,
    pub includes: Vec<Type>,
    pub fields: Vec<FieldInfo>,
    pub methods: HashMap<String, Vec<MethodId>>,
    pub singleton_methods: HashMap<String, Vec<MethodId>>,
    /// Nested classes, constants and type aliases.
    pub members: HashMap<String, Member>,
    /// The enclosing namespace (`class A::B`: A).
    pub parent: Option<ClassId>,
    /// The namespace whose body holds the declaration: the parent, but for
    /// a qualified declaration (`class A::B` at a file's top level), whose
    /// code sees A's names but not its `using`s nor its own extensions
    /// (`Checker::extensions_at`).
    #[serde(default)]
    pub lexical: Option<ClassId>,
    pub is_abstract: bool,
    pub variants: Vec<ClassId>,
    pub variant_of: Option<ClassId>,
    pub extensions: Vec<ExtensionId>,
    pub span: Span,
    pub shareable: Option<bool>,
    /// For a `data`, enum or variant: whether what it holds may be
    /// released observably (see `World::release_observable`), computed
    /// once.
    pub observable: Option<bool>,
    /// Whether `initialize` is generated (data, variants).
    pub auto_initialize: bool,
    /// Source file index (0 = prelude, 1 = the user program).
    pub file: u32,
    /// Extensions activated by `using` inside the class body (for a
    /// file's main pseudo-class, at its top level), each with the
    /// position of its `using`: in effect from there to the end of the
    /// body (`Checker::usings_at`).
    pub usings: Vec<(u32, ExtensionId)>,
    /// For the root module of a library cog: the cog's index in
    /// `World::cogs`.
    pub cog: Option<u32>,
}

/// A cog (package) of the movement being checked.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct CogInfo {
    /// `[cog] name` and `version`, what `Cog#name` and `Cog#version` give.
    pub name: String,
    pub version: String,
    /// The module its declarations live in; `None` for the application,
    /// whose declarations are at the top level.
    pub root: Option<ClassId>,
    /// Its dependencies by the keys of its manifest, bound to their root
    /// modules in its scope.
    pub imports: HashMap<String, ClassId>,
}

impl ClassInfo {
    pub fn short_name(&self) -> &str {
        self.name.rsplit("::").next().unwrap_or(&self.name)
    }
}

/// Ids of the classes the checker needs to know by name.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Builtin {
    /// `Cog`: the type of a cog's root module as a value (docs/10 §6).
    pub cog: ClassId,
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
    pub kernel: ClassId,
    pub exception: ClassId,
    pub standard_error: ClassId,
    pub comparable: ClassId,
    pub enumerable: ClassId,
    pub class_: ClassId,
    /// The prelude's `type Class = Type[Object]`.
    pub class_alias: u32,
    /// `Meta::ClassDef`, the `self` of a `static` statement (docs/14).
    pub meta_classdef: ClassId,
    /// `Meta::Expr` and `Meta::MethodRef`, a quoted block's tree, and
    /// `Quoted` (docs/14 §6).
    pub meta_expr: ClassId,
    pub meta_method_ref: ClassId,
    pub quoted: ClassId,
    /// `Meta::FieldRef`, a handle to a field (docs/14 §5).
    pub meta_field_ref: ClassId,
    /// `Meta::Method`, a handle to a method (docs/14 §5).
    pub meta_method: ClassId,
    pub shareable: ClassId,
    pub task: ClassId,
    pub channel: ClassId,
    pub atom: ClassId,
    pub scope: ClassId,
    pub duration: ClassId,
    pub bytes: ClassId,
    pub time: ClassId,
    pub array_builder: ClassId,
    pub bytes_builder: ClassId,
    pub hash_builder: ClassId,
    pub string_builder: ClassId,
    pub set_builder: ClassId,
    pub match_data: ClassId,
    pub bytes_match_data: ClassId,
}

/// The deepest `is_subtype` recursion: a defensive limit (expansive
/// inheritance, which would recurse without end, is refused at the class:
/// `Declarer::check_expansive_inheritance`).
const SUBTYPE_DEPTH: u32 = 256;

/// A conformance of a class to a module (`World::conformances`): its
/// source (`None` an own include, else the extension and the index of its
/// include), the module, and its arguments in the class's parameters.
pub type Conformance = (Option<(ExtensionId, usize)>, ClassId, Vec<Type>);

/// A class-side witness of an extension's conformance
/// (`World::class_ext_impls`).
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ClassWitness {
    /// The extension whose include makes the conformance.
    pub ext: ExtensionId,
    pub class: ClassId,
    /// The module, with its arguments as the extension includes it.
    pub module: ClassId,
    pub args: Vec<Type>,
    /// The module's class method, and what runs in its place.
    pub method: MethodId,
    pub by: MethodId,
}

/// A method of a module a class includes over one of its superclass's
/// (`World::include_overrides_of`), or a module's class method over a
/// superclass's class method (`World::class_include_overrides_of`).
pub struct IncludeOverride {
    pub class: ClassId,
    pub overridden: MethodId,
    /// How the overridden method's parameters are seen from the class.
    pub overridden_subst: HashMap<TypeParamId, Type>,
    pub by: MethodId,
    pub by_subst: HashMap<TypeParamId, Type>,
    /// The module whose include brings `by`.
    pub module: ClassId,
}

/// Which extensions' conformances a resolution order takes
/// (`World::resolution`, #536 step 2): one relation, these views of it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum View {
    /// The extensions active where the checker asks (docs/01 §7: static
    /// conformance is lexical): static subtyping, static lookup on a
    /// value's type. The one view that reads the active set.
    Static,
    /// Every extension's include, whichever are active: membership at run
    /// time (`RtClass::ancestors`, `is_a?`, `as`, patterns, typed checks).
    Runtime,
    /// Own includes and the modules of top-level unconditional extensions
    /// (on the classes their cog declares): dispatch by name
    /// (`RtClass::lookup`, decision (h)).
    Lookup,
    /// `Runtime`, then the conditional extensions' modules with their bound
    /// assumed: what a class's methods may override (the override table).
    Override,
    /// The class's own declarations only: what it must implement itself.
    Declared,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct World {
    /// A type not yet known passes the Shareable checks: set only while
    /// an overloaded call is tried again as if it were known
    /// (`Checker::resolve_pretyped`).
    #[serde(skip)]
    pub undecided_passes: std::cell::Cell<bool>,
    /// How many Shareable checks refused a type only because it is not
    /// yet known (`refuse_undecided`).
    #[serde(skip)]
    pub undecided_refusals: std::cell::Cell<u64>,
    /// The last conditional extension bound a check could not decide
    /// because a type argument is not inferred yet (`extension_bounds_hold`,
    /// #519), said in a diagnostic.
    #[serde(skip)]
    pub undecided_bound: std::cell::RefCell<Option<String>>,
    /// The same, kept for an overloaded call's choice
    /// (`Checker::resolve_pretyped`), which clears it.
    #[serde(skip)]
    pub undecided_bound_seen: std::cell::RefCell<Option<String>>,
    /// How many of `undecided_refusals` were such bounds (the others are
    /// Shareable checks): an overloaded call's error names the bound only
    /// when no Shareable check refused.
    #[serde(skip)]
    pub undecided_bound_refusals: std::cell::Cell<u64>,
    #[serde(skip)]
    subtype_depth: std::cell::Cell<u32>,
    /// The subtype questions being answered: one met again is answered
    /// no (inductively; without expansive inheritance the questions are
    /// finitely many, so a search that keeps none open again ends).
    #[serde(skip)]
    subtype_open: std::cell::RefCell<Vec<(Type, Type)>>,
    /// The documentation comments of every file, by the line they
    /// document (spans are unique across files), in order. (Not encoded
    /// with the world: `PreludeState` keeps them apart.)
    #[serde(skip)]
    pub docs: Vec<quarz_syntax::doc::Doc>,
    /// `Program::it_hints` of every file, by the call's span.
    #[serde(skip)]
    pub it_hints: HashMap<(u32, u32), String>,
    pub classes: Vec<ClassInfo>,
    pub methods: Vec<MethodInfo>,
    pub consts: Vec<ConstInfo>,
    pub aliases: Vec<TypeAliasInfo>,
    pub extensions: Vec<ExtensionInfo>,
    pub top: HashMap<String, Member>,
    pub builtin: Builtin,
    /// Extensions activated by `using` in the current lexical scope. A
    /// cell, so that a question can be asked under another set from `&self`
    /// (`with_active`, #606); the checker sets it through `get_mut`.
    pub active_extensions: std::cell::RefCell<Vec<ExtensionId>>,
    pub(crate) next_type_param: TypeParamId,
    pub type_param_names: HashMap<TypeParamId, String>,
    /// The lower bounds of method type parameters (`U >: T`).
    pub lower_bounds: HashMap<TypeParamId, Type>,
    /// Type parameters made by a test narrowing a `T` (`in Box` on a
    /// `T`): a value that is both, with both as bounds.
    pub(crate) narrowed_params: HashMap<TypeParamId, Vec<Type>>,
    pub(crate) narrowed_by: HashMap<(TypeParamId, Type), TypeParamId>,
    /// While checking the body of a method whose signature mentions
    /// `Self`: the class `Self` is bounded by (there, `Self` is that class
    /// or a subclass, not known which).
    pub self_bound: Option<Type>,
    /// The type parameters whose shareability is being decided
    /// (`is_shareable`: bounds may be cyclic).
    #[serde(skip)]
    pub(crate) shareable_params: Vec<TypeParamId>,
    /// The parameters taken as Shareable while their own class bound's
    /// arguments are checked (`U <: B[U]`, `B` promising: every `U` is a
    /// `B`, Shareable whatever the cycle).
    #[serde(skip)]
    shareable_assumed: Vec<TypeParamId>,
    /// The `data` types and enums whose observability is being computed
    /// (`data_observable`), and whether a computation leaned on one of
    /// them (its negative answer then holds only once they are done).
    observable_pending: Vec<ClassId>,
    observable_tentative: bool,
    /// The classes `class_shareable` is deciding, and whether an answer
    /// assumed one of them.
    #[serde(skip)]
    shareable_pending: Vec<ClassId>,
    #[serde(skip)]
    shareable_tentative: bool,
    /// The classes decided Shareable in the current outermost run, under
    /// an assumption (`class_shareable`).
    #[serde(skip)]
    shareable_provisional: Vec<ClassId>,
    /// The instances of `data` types and enums whose fields
    /// `instance_shareable` is judging: met again (a recursive type),
    /// taken as Shareable, as their fields decide.
    #[serde(skip)]
    shareable_instances: Vec<Type>,
    /// The lowest index of `shareable_instances` an answer leaned on (an
    /// instance met again), while judging one: an answer leaning on none
    /// below the instance's own is definite.
    #[serde(skip)]
    shareable_instance_floor: usize,
    /// The definite answers (`instance_shareable`), so that a type reached
    /// by many paths is judged once.
    #[serde(skip)]
    shareable_instance_known: HashMap<Type, bool>,
    /// Likewise for `data_fields_shareable`, which subtyping calls.
    #[serde(skip)]
    shareable_instances_seen: std::cell::RefCell<Vec<Type>>,
    #[serde(skip)]
    shareable_seen_floor: std::cell::Cell<usize>,
    #[serde(skip)]
    shareable_seen_known: std::cell::RefCell<HashMap<Type, bool>>,
    /// The cogs of the movement (empty for a script).
    pub cogs: Vec<CogInfo>,
    /// Names the application declares or imports at the top level: a
    /// library cog does not see them.
    pub app_names: rustc_hash::FxHashSet<String>,
    /// The files of the standard library (`require "json"`): their
    /// modules are not the program's to add to.
    pub std_files: rustc_hash::FxHashSet<u32>,
    /// Each user file's group (`UnitGroup`); the prelude has none.
    pub file_groups: HashMap<u32, UnitGroup>,
    /// The pseudo-class of each file's top-level methods, by file index
    /// (set by the checker for the files of a run).
    #[serde(skip)]
    pub file_mains: Vec<Option<ClassId>>,
    /// The files whose top-level `def`s each file sees, its own first
    /// (docs/01 §1): every file of its cog, or a script's and those it
    /// requires (transitively). A file without an entry sees its own.
    pub function_scopes: HashMap<u32, Vec<u32>>,
    /// The `static` statements of class and module bodies (docs/14), in
    /// the order they are declared: run at compile time, after the
    /// declarations, by the cog they belong to.
    pub static_stmts: Vec<StaticStmt>,
    /// Classes whose conformance (the abstract methods they must
    /// implement) is checked after the `static` statements of their file
    /// ran, not when they are declared: one of their ancestors has
    /// statements, which may generate the implementations (docs/14 §5).
    pub conformance_deferred: Vec<ClassId>,
    /// Abstract methods an extension's method implements for a class
    /// (class, abstract method, implementation), found where the class is
    /// declared: conformance holds wherever the value goes.
    pub ext_impls: Vec<(ClassId, MethodId, MethodId)>,
    /// The class-side witnesses of extensions' conformances (#504): for a
    /// class that conforms to a module through an extension's `include`,
    /// each class method of the module that the extension's own `def
    /// self.` or the class's own (or a superclass's) implements or
    /// overrides, checked at the extension. A call of the module's class
    /// method through a `Type[M]` value holding the class runs the
    /// witness; an extension takes no other part in dynamic dispatch
    /// (docs/01 §7).
    pub class_ext_impls: Vec<ClassWitness>,
    /// `ancestors` remembered while the classes do not change (checking;
    /// `freeze_ancestors`): a lookup computed them again and again.
    #[serde(skip)]
    ancestors_memo: AncestorsMemo,
}

type AncestorsKey = (ClassId, Vec<Type>, Vec<ExtensionId>);
type AncestorList = std::rc::Rc<Vec<(ClassId, Vec<Type>)>>;

#[derive(Debug, Default)]
struct AncestorsMemo {
    on: bool,
    map: std::cell::RefCell<HashMap<AncestorsKey, AncestorList>>,
}

/// A copy of the world starts with nothing remembered.
impl Clone for AncestorsMemo {
    fn clone(&self) -> Self {
        AncestorsMemo {
            on: self.on,
            map: Default::default(),
        }
    }
}

/// The modules found for a module and its type arguments in one walk of
/// the ancestors.
type ModuleCache = HashMap<(ClassId, Vec<Type>), Vec<(ClassId, Vec<Type>)>>;

impl World {
    pub fn new() -> World {
        World::default()
    }

    /// Take a file's documentation comments (docs/13-doc-comments.md).
    pub fn add_docs(&mut self, docs: &[quarz_syntax::doc::Doc]) {
        if docs.is_empty() {
            return;
        }
        self.docs.extend(docs.iter().cloned());
        self.docs.sort_by_key(|d| d.line.start);
    }

    /// The documentation of the declaration that starts at `span`.
    pub fn doc_at(&self, span: Span) -> Option<&quarz_syntax::doc::Doc> {
        quarz_syntax::doc::doc_at(&self.docs, span.start)
    }

    pub fn class(&self, id: ClassId) -> &ClassInfo {
        &self.classes[id as usize]
    }

    pub fn class_mut(&mut self, id: ClassId) -> &mut ClassInfo {
        &mut self.classes[id as usize]
    }

    pub fn method(&self, id: MethodId) -> &MethodInfo {
        &self.methods[id as usize]
    }

    /// The span of the `static` statement that generated a method (docs/14
    /// §5): with `def_method`, or as an accessor of a `def_field`'s field
    /// (which has a baked default and the statement's span).
    pub fn generated_by(&self, id: MethodId) -> Option<Span> {
        let m = self.method(id);
        if let Some(g) = &m.generated {
            return Some(g.by.1);
        }
        if let Synth::FieldGet(f) | Synth::FieldSet(f) = &m.synth {
            let field = self.class(m.owner).fields.iter().find(|x| &x.name == f)?;
            if field.baked_default.is_some() && field.span == m.span {
                return Some(m.span);
            }
        }
        None
    }

    pub fn method_mut(&mut self, id: MethodId) -> &mut MethodInfo {
        &mut self.methods[id as usize]
    }

    pub fn add_class(&mut self, mut info: ClassInfo) -> ClassId {
        let id = self.classes.len() as ClassId;
        info.id = id;
        self.classes.push(info);
        id
    }

    pub fn add_method(&mut self, mut info: MethodInfo) -> MethodId {
        let id = self.methods.len() as MethodId;
        info.id = id;
        let owner = info.owner;
        let singleton = info.singleton;
        let name = info.name.clone();
        let ext = info.extension;
        self.methods.push(info);
        match ext {
            Some(ext) => {
                self.extensions[ext as usize]
                    .methods
                    .entry(name)
                    .or_default()
                    .push(id);
            }
            None => {
                let class = &mut self.classes[owner as usize];
                let table = if singleton {
                    &mut class.singleton_methods
                } else {
                    &mut class.methods
                };
                table.entry(name).or_default().push(id);
            }
        }
        id
    }

    /// Whether the `i`th type parameter of `cid` takes `Object` without
    /// admitting a wrong value: covariant (values only come out), with
    /// bounds `Object` meets, the class's parameters all being `Object`
    /// (docs/02 §6, §7: a class test or pattern without arguments narrows
    /// to such a class with `Object` arguments).
    pub fn param_admits_object(&self, cid: ClassId, i: usize) -> bool {
        let class = self.class(cid);
        let Some(p) = class.type_params.get(i) else {
            return false;
        };
        if p.variance != Variance::Covariant {
            return false;
        }
        let object = Type::class(self.builtin.object);
        let args: Vec<Type> = class.type_params.iter().map(|_| object.clone()).collect();
        let subst = self.class_subst(cid, &args);
        p.bounds.iter().all(|b| {
            let b = b.subst(&subst);
            !matches!(&b, Type::Class(bid, _) if *bid == self.builtin.shareable)
                && self.is_subtype(&object, &b)
        })
    }

    /// The type of a `T` that a test found to be a `bound` too: a type
    /// parameter bounded by both (still a `T`, with `bound`'s methods).
    pub fn narrowed_param(&mut self, base: TypeParamId, bound: &Type) -> Type {
        if let Some(id) = self.narrowed_by.get(&(base, bound.clone())) {
            return Type::Param(*id);
        }
        let id = self.next_type_param;
        self.next_type_param += 1;
        let name = format!(
            "{} & {}",
            self.type_param_names
                .get(&base)
                .cloned()
                .unwrap_or_default(),
            self.type_name(bound)
        );
        self.type_param_names.insert(id, name);
        self.narrowed_params
            .insert(id, vec![Type::Param(base), bound.clone()]);
        self.narrowed_by.insert((base, bound.clone()), id);
        Type::Param(id)
    }

    /// The type parameters class tests made (`T & C`), each with its
    /// bounds (the `T` and the `C`).
    pub fn narrowed_params(&self) -> impl Iterator<Item = (TypeParamId, &[Type])> {
        self.narrowed_params
            .iter()
            .map(|(id, b)| (*id, b.as_slice()))
    }

    /// A type parameter's name (`T`, or `T & C` for a narrowed one).
    pub fn type_param_name(&self, id: TypeParamId) -> String {
        self.type_param_names.get(&id).cloned().unwrap_or_default()
    }

    /// `t` with each narrowed type parameter (`T & C`) back to its `T`,
    /// for types that outlive the branch of the test (variables, inferred
    /// types).
    pub fn erase_narrowed(&self, t: &Type) -> Type {
        if self.narrowed_params.is_empty() {
            return t.clone();
        }
        match t {
            Type::Param(p) => match self.narrowed_params.get(p) {
                Some(bounds) => match bounds.first() {
                    Some(base) => self.erase_narrowed(base),
                    None => t.clone(),
                },
                None => t.clone(),
            },
            Type::Class(id, args) => {
                Type::Class(*id, args.iter().map(|a| self.erase_narrowed(a)).collect())
            }
            Type::ClassObject(id, args) => {
                Type::ClassObject(*id, args.iter().map(|a| self.erase_narrowed(a)).collect())
            }
            Type::TypeOf(t) => Type::type_of(self.erase_narrowed(t)),
            Type::Union(ms) => Type::union_of(ms.iter().map(|m| self.erase_narrowed(m)).collect()),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|m| self.erase_narrowed(m)).collect()),
            Type::Proc(rc, ps, r, sh, kws) => Type::Proc(
                rc.as_ref().map(|t| Box::new(self.erase_narrowed(t))),
                ps.iter().map(|p| self.erase_narrowed(p)).collect(),
                Box::new(self.erase_narrowed(r)),
                *sh,
                ProcKw::map(kws, |t| self.erase_narrowed(t)),
            ),
            Type::Nothing | Type::Void | Type::Var(_) => t.clone(),
        }
    }

    /// The class a narrowed type parameter was found to be, if any.
    pub fn narrowed_class(&self, id: TypeParamId) -> Option<Type> {
        let bounds = self.narrowed_params.get(&id)?;
        bounds.iter().find_map(|b| match b {
            Type::Class(..) => Some(b.clone()),
            Type::Param(p) => self.narrowed_class(*p),
            _ => None,
        })
    }

    pub fn new_type_param(&mut self, name: &str, variance: Variance) -> TypeParamInfo {
        let id = self.next_type_param;
        self.next_type_param += 1;
        self.type_param_names.insert(id, name.to_string());
        TypeParamInfo {
            id,
            name: name.to_string(),
            variance,
            bounds: Vec::new(),
            lower: None,
        }
    }

    pub fn blank_class(
        name: String,
        kind: ClassKind,
        parent: Option<ClassId>,
        span: Span,
    ) -> ClassInfo {
        ClassInfo {
            id: 0,
            name,
            kind,
            type_params: Vec::new(),
            superclass: None,
            includes: Vec::new(),
            fields: Vec::new(),
            methods: HashMap::default(),
            singleton_methods: HashMap::default(),
            members: HashMap::default(),
            parent,
            lexical: parent,
            is_abstract: false,
            variants: Vec::new(),
            variant_of: None,
            extensions: Vec::new(),
            span,
            shareable: None,
            observable: None,
            auto_initialize: false,
            file: 0,
            usings: Vec::new(),
            cog: None,
        }
    }

    // ----- convenience types --------------------------------------------

    pub fn nil(&self) -> Type {
        Type::class(self.builtin.nil)
    }

    pub fn bool_(&self) -> Type {
        Type::class(self.builtin.bool_)
    }

    pub fn int(&self) -> Type {
        Type::class(self.builtin.int)
    }

    pub fn integer(&self) -> Type {
        Type::class(self.builtin.integer)
    }

    pub fn float(&self) -> Type {
        Type::class(self.builtin.float)
    }

    pub fn string(&self) -> Type {
        Type::class(self.builtin.string)
    }

    pub fn symbol(&self) -> Type {
        Type::class(self.builtin.symbol)
    }

    pub fn object(&self) -> Type {
        Type::class(self.builtin.object)
    }

    pub fn array_of(&self, t: Type) -> Type {
        Type::Class(self.builtin.array, vec![t])
    }

    pub fn hash_of(&self, k: Type, v: Type) -> Type {
        Type::Class(self.builtin.hash, vec![k, v])
    }

    pub fn nilable(&self, t: Type) -> Type {
        Type::union_of(vec![t, self.nil()])
    }

    pub fn is_nil_type(&self, t: &Type) -> bool {
        matches!(t, Type::Class(id, _) if *id == self.builtin.nil)
    }

    /// Whether `a` and `b` are the same type, `Void` being `Nil`.
    pub fn same_type(&self, a: &Type, b: &Type) -> bool {
        a == b || self.devoid(a) == self.devoid(b)
    }

    /// `t` with `Nil` for every `Void` in it.
    pub fn devoid(&self, t: &Type) -> Type {
        match t {
            Type::Void => self.nil(),
            Type::Nothing | Type::Param(_) | Type::Var(_) => t.clone(),
            Type::Class(id, args) => {
                Type::Class(*id, args.iter().map(|a| self.devoid(a)).collect())
            }
            Type::ClassObject(id, args) => {
                Type::ClassObject(*id, args.iter().map(|a| self.devoid(a)).collect())
            }
            Type::TypeOf(t) => Type::type_of(self.devoid(t)),
            Type::Union(ms) => Type::union_of(ms.iter().map(|m| self.devoid(m)).collect()),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|m| self.devoid(m)).collect()),
            Type::Proc(rc, ps, r, sh, kws) => Type::Proc(
                rc.as_ref().map(|t| Box::new(self.devoid(t))),
                ps.iter().map(|p| self.devoid(p)).collect(),
                Box::new(self.devoid(r)),
                *sh,
                ProcKw::map(kws, |t| self.devoid(t)),
            ),
        }
    }

    /// `Nil` for `Void`: what a caller sees of a result, and how `Void`
    /// compares (`(A) -> Void` and `(A) -> Nil` are the same type).
    pub fn unvoid(&self, t: &Type) -> Type {
        match t {
            Type::Void => self.nil(),
            t => t.clone(),
        }
    }

    pub fn is_object(&self, t: &Type) -> bool {
        matches!(t, Type::Class(id, _) if *id == self.builtin.object)
    }

    // ----- names -----------------------------------------------------------

    pub fn type_name(&self, t: &Type) -> String {
        match t {
            Type::Nothing => "Nothing".to_string(),
            Type::Void => "Void".to_string(),
            Type::Class(id, args) => {
                let name = &self.class(*id).name;
                if args.is_empty() {
                    name.clone()
                } else {
                    format!(
                        "{name}[{}]",
                        args.iter()
                            .map(|a| self.type_name(a))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
            Type::ClassObject(id, args) => {
                format!("Type[{}]", self.type_name(&Type::Class(*id, args.clone())))
            }
            Type::TypeOf(t) => format!("Type[{}]", self.type_name(t)),
            Type::Union(ms) => {
                if ms.len() == 2 && self.is_nil_type(&ms[1]) {
                    return format!("{}?", self.type_name(&ms[0]));
                }
                if ms.len() == 2 && self.is_nil_type(&ms[0]) {
                    return format!("{}?", self.type_name(&ms[1]));
                }
                ms.iter()
                    .map(|m| self.type_name(m))
                    .collect::<Vec<_>>()
                    .join(" | ")
            }
            Type::Tuple(ts) => format!(
                "[{}]",
                ts.iter()
                    .map(|t| self.type_name(t))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Type::Proc(rc, ps, r, sh, kws) => format!(
                "{}{}({}) -> {}",
                if *sh { "shareable " } else { "" },
                rc.as_ref()
                    .map(|t| format!("{}.", self.type_name(t)))
                    .unwrap_or_default(),
                ps.iter()
                    .map(|t| self.type_name(t))
                    .chain((!kws.is_empty()).then(|| "*".to_string()))
                    // (An optional keyword, of a block's or a lambda's
                    // own type, shows its default as `_`.)
                    .chain(kws.iter().map(|k| format!(
                        "{}: {}{}",
                        k.name,
                        self.type_name(&k.ty),
                        if k.required { "" } else { " = _" }
                    )))
                    .collect::<Vec<_>>()
                    .join(", "),
                self.type_name(r)
            ),
            Type::Param(id) if *id == u32::MAX => "Self".to_string(),
            Type::Param(id) => self
                .type_param_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("T{id}")),
            Type::Var(v) => format!("?{v}"),
        }
    }

    // ----- hierarchy ----------------------------------------------------------

    /// Substitution map for a class's own type parameters.
    pub fn class_subst(&self, id: ClassId, args: &[Type]) -> HashMap<TypeParamId, Type> {
        let class = self.class(id);
        class
            .type_params
            .iter()
            .zip(args.iter().cloned())
            .map(|(p, a)| (p.id, a))
            .collect()
    }

    /// Whether `sub_id` is `sup_id` or inherits from / includes it
    /// (nominally, ignoring type arguments).
    pub fn class_is_a(&self, sub_id: ClassId, sup_id: ClassId) -> bool {
        if sub_id == sup_id || sup_id == self.builtin.object {
            return true;
        }
        self.ancestors(sub_id, &[])
            .iter()
            .any(|(id, _)| *id == sup_id)
    }

    /// The method resolution order of class `id` with `args` (#536 step
    /// 2): the one computation of the relation. The class itself, the
    /// modules it includes (the last included first, each with what it
    /// includes), the modules extensions make it conform to (each
    /// extension's includes ordered alike, after the class's own, #523),
    /// then its superclass's; each with its type arguments in terms of
    /// `args`. A class's class side is the same order (its class methods
    /// and its modules'). `view` names which extensions' conformances are
    /// in it; every other ancestry question is a view of this.
    pub fn resolution(&self, id: ClassId, args: &[Type], view: View) -> Vec<(ClassId, Vec<Type>)> {
        if view == View::Override {
            return self.override_resolution(id, args);
        }
        // (Membership's order: the top-level extensions' modules in the walk,
        // the scoped ones' after it: `find_override` walks it.)
        if view == View::Runtime {
            return self.ordered_under(id, args, &self.all_conformance_extensions(), false, false);
        }
        // (The checker's order is the same with the extensions active where
        // it asks: a call resolves to what runs, `using` or not.)
        if view == View::Static {
            return self.ordered_under(id, args, &self.conformance_extensions(), false, true);
        }

        self.ancestors_under(id, args, self.view_extensions(view))
    }

    /// `resolution(id, args, View::Static)` with each entry's source: the
    /// active scoped or conditional extension whose include put the module
    /// there, or `None` (the class, its own includes, its top-level
    /// extensions' modules, its superclasses'). Two modules of different
    /// active extensions on the same target, neither in the other's
    /// ancestry, give a call they both answer no order (#577).
    pub fn resolution_sources(
        &self,
        id: ClassId,
        args: &[Type],
    ) -> Vec<(ClassId, Vec<Type>, Option<ExtensionId>)> {
        let exts = self.conformance_extensions();
        let mut out = self.ordered_sources(id, args, &exts, false, true);
        self.credit_conditional(id, args, &exts, &mut out);
        out
    }

    /// `resolution_sources`' credit of a module only a top-level
    /// conditional extension brings (whose bound holds for the target's
    /// arguments here) to that extension: lexical only, as a scoped one's
    /// (#577). Apart from the plain static order, which needs none of it.
    fn credit_conditional(
        &self,
        c: ClassId,
        own: &[Type],
        exts: &[ExtensionId],
        out: &mut [(ClassId, Vec<Type>, Option<ExtensionId>)],
    ) {
        let top = self.walked_extensions(exts);
        // (A module only a top-level conditional extension brings is, as a
        // scoped one's, lexical only: its source is that extension, #577;
        // one the class's own includes or a top-level unconditional
        // extension bring keeps none, ordered as the class's own, #523.)
        let conditional = |e: &ExtensionId| {
            self.extensions[*e as usize]
                .type_params
                .iter()
                .any(|tp| !tp.bounds.is_empty())
        };
        if !top.iter().any(conditional) {
            return;
        }
        let plain: Vec<ExtensionId> = top.iter().copied().filter(|e| !conditional(e)).collect();
        let walked: Vec<ClassId> = self
            .ancestors_under(c, own, plain)
            .into_iter()
            .map(|(k, _)| k)
            .collect();
        // (One whose bound holds for the target's arguments here: an
        // extension that does not apply brings nothing.)
        let applying: Vec<ExtensionId> = top
            .iter()
            .copied()
            .filter(conditional)
            .filter(|e| {
                let ext = &self.extensions[*e as usize];
                out.iter()
                    .any(|(t, targs, _)| *t == ext.target && self.extension_bounds_hold(ext, targs))
            })
            .collect();
        if applying.is_empty() {
            return;
        }
        for entry in out.iter_mut() {
            let k = entry.0;
            if walked.contains(&k) {
                continue;
            }
            let found = applying.iter().copied().find(|e| {
                self.extensions[*e as usize]
                    .includes
                    .iter()
                    .any(|inc| match inc {
                        Type::Class(mid, margs) => {
                            *mid == k
                                || self
                                    .ancestors_under(*mid, margs, Vec::new())
                                    .iter()
                                    .any(|(a, _)| *a == k)
                        }
                        _ => false,
                    })
            });
            if found.is_some() {
                entry.2 = found;
            }
        }
    }

    /// The extensions whose conformances `view` takes. `View::Static`'s is
    /// the one read of the active set for conformance (`active_extension_ids`).
    pub fn view_extensions(&self, view: View) -> Vec<ExtensionId> {
        match view {
            View::Static => self.conformance_extensions(),
            View::Runtime | View::Override => self.all_conformance_extensions(),
            View::Lookup => self.top_level_conformance_extensions(),
            View::Declared => Vec::new(),
        }
    }

    /// The static view (`View::Static`): the resolution order as the checker
    /// sees it where it asks, the extensions active there making the class
    /// conform (docs/01 §7, lexical): static subtyping and lookup on a
    /// value's static type.
    pub fn ancestors(&self, id: ClassId, args: &[Type]) -> Vec<(ClassId, Vec<Type>)> {
        self.resolution(id, args, View::Static)
    }

    /// `ancestors` with the conformances of extensions `exts`, remembered
    /// alike.
    fn ancestors_under(
        &self,
        id: ClassId,
        args: &[Type],
        exts: Vec<ExtensionId>,
    ) -> Vec<(ClassId, Vec<Type>)> {
        if !self.ancestors_memo.on {
            return self.ancestors_with(id, args, &exts);
        }
        // (A walk that met a bound not known yet is not remembered: it
        // counts the refusal each time, and answers otherwise when made
        // as if the types were known, #519.)
        let undecided = args.iter().any(|t| t.has_vars());
        let key = (id, args.to_vec(), exts);
        if let Some(found) = self.ancestors_memo.map.borrow().get(&key) {
            return found.as_ref().clone();
        }
        let refusals = self.undecided_refusals.get();
        let found = self.ancestors_with(id, args, &key.2);
        if undecided && (self.undecided_passes.get() || self.undecided_refusals.get() != refusals) {
            return found;
        }
        self.ancestors_memo
            .map
            .borrow_mut()
            .insert(key, std::rc::Rc::new(found.clone()));
        found
    }

    /// Remember `ancestors` from now on (`true`: the classes and their
    /// headers no longer change) or forget them (`false`).
    pub fn freeze_ancestors(&mut self, on: bool) {
        self.ancestors_memo.on = on;
        self.ancestors_memo.map.get_mut().clear();
    }

    /// The modules class `id` itself brings to its resolution order (not
    /// those its superclass brings already), in the declared view
    /// (`View::Declared`): those its own `include`s bring, whose abstract
    /// class methods the class must implement (an extension's are
    /// required at the extension, #504).
    pub fn class_modules_included(&self, id: ClassId, args: &[Type]) -> Vec<(ClassId, Vec<Type>)> {
        Self::own_modules(self, id, self.resolution(id, args, View::Declared))
    }

    /// Whether a run-time test "a value of class `c` is an `m`" is answered
    /// exactly by the membership table the run time reads
    /// (`RtClass::ancestors`, `resolution(c, [], View::Runtime)`, by the
    /// class alone) for every value of `c` whose type arguments are
    /// `args` (those its static type fixes; unfixed ones as `c`'s own
    /// parameters) (#515): the table's answer, the answer for every such
    /// instantiation (`View::Runtime` with `args`, bounds checked) and for
    /// some (`View::Override` with `args`, bounds assumed where an
    /// argument mentions a parameter) all agree. An approximation that
    /// errs toward refusing (the assumed bounds err toward pairing, #556
    /// makes them exact), never toward accepting.
    pub fn runtime_test_exact(&self, c: ClassId, args: &[Type], m: ClassId) -> bool {
        let has = |v: View, a: &[Type]| self.resolution(c, a, v).iter().any(|(k, _)| *k == m);
        let run = has(View::Runtime, &[]);
        let all = has(View::Runtime, args);
        let some = has(View::Override, args);
        run == all && all == some
    }

    /// Whether a conditional extension brings module `m`, directly or
    /// through what it includes: only then may a run-time test against `m`
    /// depend on type arguments (`runtime_test_exact`).
    pub fn conditionally_included(&self, m: ClassId) -> bool {
        // (What an include brings, with every extension's, conditional
        // ones' bounds assumed: an extension of a module it includes too.)
        let brings = |k: ClassId, ka: &[Type]| {
            k == m
                || self
                    .resolution(k, ka, View::Override)
                    .iter()
                    .any(|(a, _)| *a == m)
        };
        self.extensions.iter().any(|e| {
            e.type_params.iter().any(|tp| !tp.bounds.is_empty())
                && e.includes.iter().any(|inc| match inc {
                    Type::Class(k, ka) => brings(*k, ka),
                    _ => false,
                })
        })
    }

    /// Class `id`'s own type parameters, as arguments.
    pub fn own_args(&self, id: ClassId) -> Vec<Type> {
        self.class(id)
            .type_params
            .iter()
            .map(|p| Type::Param(p.id))
            .collect()
    }

    /// The declared view (`View::Declared`) of class `id` with its own
    /// parameters: what its own declarations give it.
    pub fn ancestors_with_no_extensions(&self, id: ClassId) -> Vec<(ClassId, Vec<Type>)> {
        self.resolution(id, &self.own_args(id), View::Declared)
    }

    /// The arguments `margs` (written in extension `ext`'s parameters) of a
    /// module the extension includes, in the parameters of class `frame`:
    /// the extension's target, a subclass of it, or (a module target) a
    /// class including it.
    pub fn conformance_args(
        &self,
        ext: ExtensionId,
        margs: &[Type],
        frame: ClassId,
    ) -> Option<Vec<Type>> {
        let e = &self.extensions[ext as usize];
        let own: Vec<Type> = self
            .class(e.target)
            .type_params
            .iter()
            .map(|p| Type::Param(p.id))
            .collect();
        let esubst = self.extension_subst(e, &own);
        let in_target: Vec<Type> = margs.iter().map(|t| t.subst(&esubst)).collect();
        if frame == e.target {
            return Some(in_target);
        }
        let targs = self
            .ancestors_with_no_extensions(frame)
            .into_iter()
            .find(|(k, _)| *k == e.target)?
            .1;
        let tsubst = self.class_subst(e.target, &targs);
        Some(in_target.iter().map(|t| t.subst(&tsubst)).collect())
    }

    /// The class side of class `c` in lookup order: the class, the modules
    /// it brings itself (the last included first), its superclass, the
    /// modules that one brings, ... (`resolution` in the declared view: an
    /// extension's include brings witnesses, not class methods, #504). The
    /// one order class-side dispatch, the witnesses' lookup (#504) and the
    /// checker's questions about it go by; `RtClass::class_side` ships it.
    /// The class-side order of extension `ext`'s target in which its
    /// class-side witnesses are looked for (#669's decision (y)): the
    /// class's order with `ext` alone active (`resolution(.., View::Static)`
    /// under it; the prelude's always-active extensions are part of every
    /// order): the class's own class methods, its own includes, `ext`'s
    /// includes (the last written first, each with what it brings), then a
    /// superclass's with its includes. No other extension is in it, active
    /// where `ext` is declared or not: an extension completes its
    /// conformance itself, from its own methods, the modules it includes
    /// and the target's own side (R0, #635; D, #601), so another
    /// extension's module (a sibling's, ambiguous with `ext`'s, #577, or a
    /// superclass's scoped one) never supplies its witness. (A top-level
    /// unconditional extension's module, which the instance side's
    /// dispatch counts and the class side's does not, is #681.) The
    /// witness is the first that fits in this order with one filter, a
    /// method the requirement itself overrides being none (#680,
    /// `Declarer::check_extension_class_side`).
    pub fn class_side_with(&self, ext: ExtensionId) -> Vec<(ClassId, Vec<Type>)> {
        let target = self.extensions[ext as usize].target;
        self.with_active(vec![ext], || self.resolution(target, &[], View::Static))
    }

    pub fn class_side_order(&self, c: ClassId) -> Vec<ClassId> {
        self.resolution(c, &[], View::Declared)
            .into_iter()
            .map(|(k, _)| k)
            .collect()
    }

    /// The modules class `cur` (`c` or a superclass of it) brings to `c`'s
    /// class side, in lookup order: the entries after `cur` in
    /// `class_side_order(c)` up to the next class (`Interp`'s twin).
    pub fn class_side_modules(&self, c: ClassId, cur: ClassId) -> Vec<ClassId> {
        let side = self.class_side_order(c);
        // (`cur` is `c` or a class up its chain, always in it: a missing
        // entry is an internal error, never an empty part.)
        let at = side.iter().position(|k| *k == cur).unwrap_or_else(|| {
            panic!(
                "internal error: `{}` is not on `{}`'s class side",
                self.class(cur).name,
                self.class(c).name
            )
        });
        side[at + 1..]
            .iter()
            .copied()
            .take_while(|k| self.class(*k).kind == ClassKind::Module)
            .collect()
    }

    /// The class of `c`'s superclass chain whose part of
    /// `class_side_order(c)` holds `k`: `k` itself, or the class that
    /// brings module `k` (an own include, or one an include brings).
    pub fn class_side_owner(&self, c: ClassId, k: ClassId) -> Option<ClassId> {
        let side = self.class_side_order(c);
        let at = side.iter().position(|x| *x == k)?;
        side[..=at]
            .iter()
            .rev()
            .copied()
            .find(|x| self.class(*x).kind != ClassKind::Module)
    }

    /// Every conformance of class `c` to a module, with the module's
    /// arguments in `c`'s own parameters: its own includes (along the
    /// chain, with what they include; `None`), and each include of every
    /// extension whose target is one of `conformance_sources(c)`, with the
    /// modules it brings (`Some((extension, index of the include))`).
    /// The witness record (#536 step 3, S1): for every class `C` with
    /// values and every abstract instance requirement `r` of a module `M`
    /// it conforms to, the method that runs for `r` on `C`'s values, and
    /// the extension whose conformance it is (`None`: `C`'s own). The
    /// rules, each from the decision it comes from (S2 makes this the run
    /// time's rule):
    ///
    /// 1. **One conformance per module.** `C`'s own if it has `M` on its
    ///    own side (an own include, a superclass's, or a top-level
    ///    unconditional extension's module in its dispatch); else the
    ///    extension's whose target is nearest `C` up its chain. (D2 of
    ///    2026-11-12 and rule A, #636: for a module the class has itself,
    ///    the class's own conformance holds; an extension's method is then
    ///    an extension method, chosen statically.)
    /// 2. **Below the conformance's class**, in `C`'s dispatch by name
    ///    (`View::Lookup`: a top-level unconditional extension's modules
    ///    included, as rule 1's own side, #672), a method that the override
    ///    table pairs with `r` under `C`'s declaration view
    ///    (`World::overrides`, or `C`'s `include_overrides_of`) replaces the
    ///    witness. A method the table does not pair is no override, and the
    ///    witness runs; nor is an extension's own method, a witness only of
    ///    the conformance its extension makes (#665's decision (α)).
    ///    (Addendum (A)'s rule 1 with #606's decision (a); step 1's
    ///    decision (4): the witness is dispatched for the receiver.)
    /// 3. **`C`'s own conformance:** the first method in `C`'s dispatch by
    ///    name (`resolution(C, …, View::Lookup)`) that the override table
    ///    pairs with `r`, or that takes `r`'s calls by type, its result
    ///    included (a concrete method further up, the declarer's
    ///    `inherited_impls`); else none. (Step 1's relation; rule A: an
    ///    extension's own method is never it. A method taking the calls by
    ///    arity only is no witness: the arity-only last resort is dropped,
    ///    the decision of 2026-11-14 on #536.)
    /// 4. **An extension's conformance:** the extension's own method that
    ///    takes `r`'s calls by type, its result included; else the witness
    ///    R0 recorded for its target (`ext_impls`): the first in the order
    ///    a call on the target sees with the extension active
    ///    (`resolution(…, View::Static)`), of the target's own side and the
    ///    extension's modules. (R0, #635; #654, #658; addendum (A)'s rule 2:
    ///    the extension that makes the conformance supplies its method,
    ///    #529.)
    ///
    /// A witness that is a class's or module's method is resolved for a
    /// receiver below it as `find_override` resolves it (#654).
    pub fn witness_record(
        &self,
    ) -> Vec<(ClassId, MethodId, Option<MethodId>, Option<ExtensionId>)> {
        let mut out = Vec::new();
        let n = self.classes.len() as ClassId;
        for c in 0..n {
            let kind = self.class(c).kind;
            if matches!(kind, ClassKind::Module | ClassKind::Main) {
                continue;
            }
            // (The class's dispatch by name: its own side and the modules
            // of the top-level unconditional extensions, which take part in
            // it, docs/01 §7. Every rule reads this one order, #672.)
            let lookup = self.resolution(c, &self.own_args(c), View::Lookup);
            for (src, m, margs) in self.chosen_conformances(c) {
                let rsubst = self.class_subst(m, &margs);
                let reqs: Vec<MethodId> = self
                    .class(m)
                    .methods
                    .values()
                    .flatten()
                    .copied()
                    .filter(|&r| {
                        let rm = self.method(r);
                        rm.owner == m && rm.is_abstract && !rm.singleton
                    })
                    .collect();
                for r in reqs {
                    let rm = self.method(r);
                    let by_type = |i: MethodId, subst: &HashMap<TypeParamId, Type>| {
                        let im = self.method(i);
                        i != r
                            && !im.is_abstract
                            && !im.singleton
                            && im.name == rm.name
                            && self.takes_place_of(im, subst, rm, &rsubst)
                    };
                    // A class below the conformance's class (an extension's
                    // target, or the class including the module): its own
                    // method the override table says replaces the
                    // requirement runs first. (An extension's own method is
                    // a witness only of the conformance its extension
                    // makes, #665's decision (α): not here.)
                    let upto = match src {
                        Some((e, _)) => Some(self.extensions[e as usize].target),
                        None => lookup
                            .iter()
                            .find(|(k, _)| {
                                self.class(*k).includes.iter().any(|t| {
                                    matches!(t, Type::Class(i, _) if *i == m || self.ancestor_ids(*i).contains(&m))
                                })
                            })
                            .map(|(k, _)| *k),
                    };
                    // (Below the conformance's class, a method replaces the
                    // witness only if the override table pairs it with the
                    // requirement under the class's declaration view:
                    // addendum (A)'s rule 1 with #606's decision (a); the
                    // class's own includes count.)
                    // (The class's own pairs: a module it includes over the
                    // requirement, `include_overrides_of`, in its view.)
                    let paired_here: Vec<MethodId> = self
                        .include_overrides_of(c)
                        .into_iter()
                        .filter(|io| io.overridden == r)
                        .map(|io| io.by)
                        .collect();
                    let below = lookup
                        .iter()
                        .map(|(k, _)| *k)
                        .take_while(|k| Some(*k) != upto)
                        .find_map(|k| {
                            self.class(k).methods.get(&rm.name).and_then(|ids| {
                                ids.iter().copied().find(|&i| {
                                    let im = self.method(i);
                                    im.owner == k
                                        && !im.is_abstract
                                        && (self.overrides(i).contains(&r)
                                            || paired_here.contains(&i))
                                })
                            })
                        });
                    let w = below.or_else(|| match src {
                        Some((e, _)) => {
                            let ext = &self.extensions[e as usize];
                            let targs = lookup
                                .iter()
                                .find(|(k, _)| *k == ext.target)
                                .map(|(_, a)| a.clone())
                                .unwrap_or_default();
                            let esubst = self.extension_subst(ext, &targs);
                            ext.methods
                                .get(&rm.name)
                                .and_then(|ids| ids.iter().copied().find(|&i| by_type(i, &esubst)))
                                .or_else(|| {
                                    self.ext_impls
                                        .iter()
                                        .find(|(k, a, _)| *k == ext.target && *a == r)
                                        .map(|(_, _, i)| *i)
                                })
                        }
                        // (The class's own conformance: `own_witness`.)
                        None => self.own_witness_in(&lookup, r, &rsubst, &paired_here),
                    });
                    out.push((c, r, w, src.map(|(e, _)| e)));
                }
            }
        }
        out
    }

    /// The witness of requirement `r` (an abstract instance method of a
    /// module) for class `c`'s own conformance to its module (the witness
    /// record's rule 3, which the declarer records, #536 step 3): the first
    /// method in `c`'s dispatch by name (`View::Lookup`) that the override
    /// table pairs with `r` (`overrides`, or `c`'s own include pairs,
    /// `include_overrides_of`), or that takes `r`'s calls by type (a
    /// method's own type parameters standing for `r`'s), its result
    /// included, each seen with the class's own arguments for its owner
    /// (a concrete method further up: `B2#m` for `C2 < B2; include
    /// M2[Int]`). None: nothing implements it (a method taking the calls
    /// by arity only is no witness, the decision of 2026-11-14 on #536).
    pub fn own_witness(&self, c: ClassId, r: MethodId) -> Option<MethodId> {
        let m = self.method(r).owner;
        let lookup = self.resolution(c, &self.own_args(c), View::Lookup);
        let margs = lookup
            .iter()
            .find(|(k, _)| *k == m)
            .map(|(_, a)| a.clone())
            .unwrap_or_default();
        let paired: Vec<MethodId> = self
            .include_overrides_of(c)
            .into_iter()
            .filter(|io| io.overridden == r)
            .map(|io| io.by)
            .collect();
        self.own_witness_in(&lookup, r, &self.class_subst(m, &margs), &paired)
    }

    /// `own_witness` in `lookup`, `c`'s dispatch by name, with `rsubst`,
    /// the module's arguments there, and `paired`, the methods `c`'s own
    /// include pairs put over `r` (`include_overrides_of`).
    fn own_witness_in(
        &self,
        lookup: &[(ClassId, Vec<Type>)],
        r: MethodId,
        rsubst: &HashMap<TypeParamId, Type>,
        paired: &[MethodId],
    ) -> Option<MethodId> {
        let rm = self.method(r);
        lookup.iter().find_map(|(k, kargs)| {
            let ks = self.class_subst(*k, kargs);
            self.class(*k).methods.get(&rm.name).and_then(|ids| {
                ids.iter().copied().find(|&i| {
                    let im = self.method(i);
                    // (A method's own type parameters stand for the
                    // requirement's, in order, as an override's do,
                    // `Declarer::check_implementation`.)
                    let mut ks = ks.clone();
                    if im.type_params.len() == rm.type_params.len() {
                        for (p, q) in im.type_params.iter().zip(&rm.type_params) {
                            ks.insert(p.id, Type::Param(q.id));
                        }
                    }
                    im.owner == *k
                        && !im.is_abstract
                        && (self.overrides(i).contains(&r)
                            || paired.contains(&i)
                            || (i != r
                                && !im.singleton
                                && self.takes_place_of(im, &ks, rm, rsubst)))
                })
            })
        })
    }

    /// The conformance that holds for class `c`, one per module (the
    /// witness record's rule 1): `c`'s own if it has the module on its own
    /// side (D2, rule A), else the extension's whose target is nearest `c`
    /// up its dispatch by name (`View::Lookup`). An extension's own method
    /// is a witness only of the conformance it chooses (#665's decision
    /// (α)): a subclass conforming through its own extension (#517's
    /// per-class rule) takes that one, not its superclass's extension's.
    pub fn chosen_conformances(&self, c: ClassId) -> Vec<Conformance> {
        let lookup = self.resolution(c, &self.own_args(c), View::Lookup);
        let pos = |s: &Option<(ExtensionId, usize)>| match s {
            None => 0,
            Some((e, _)) => {
                let t = self.extensions[*e as usize].target;
                lookup
                    .iter()
                    .position(|(k, _)| *k == t)
                    .map_or(usize::MAX, |p| p + 1)
            }
        };
        let mut chosen: Vec<Conformance> = Vec::new();
        for (src, m, margs) in self.conformances(c) {
            match chosen.iter().position(|(_, x, _)| *x == m) {
                Some(at) if pos(&src) < pos(&chosen[at].0) => chosen[at] = (src, m, margs),
                Some(_) => {}
                None => chosen.push((src, m, margs)),
            }
        }
        chosen
    }

    pub fn conformances(&self, c: ClassId) -> Vec<Conformance> {
        let mut out: Vec<Conformance> = self
            .ancestors_with_no_extensions(c)
            .into_iter()
            .filter(|(m, _)| self.class(*m).kind == ClassKind::Module)
            .map(|(m, a)| (None, m, a))
            .collect();
        let sources = self.class_side_order(c);
        for (k, e) in self.extensions.iter().enumerate() {
            if !sources.contains(&e.target) {
                continue;
            }
            for (i, t) in e.includes.iter().enumerate() {
                let Type::Class(m, a) = t else { continue };
                let Some(args) = self.conformance_args(k as ExtensionId, a, c) else {
                    continue;
                };
                for (x, xa) in self.ancestors(*m, &args) {
                    if self.class(x).kind == ClassKind::Module {
                        out.push((Some((k as ExtensionId, i)), x, xa));
                    }
                }
            }
        }
        out
    }

    /// How a message names extension `id`: by the module it is declared
    /// in, or as a top-level one.
    pub fn extension_label(&self, id: ExtensionId) -> String {
        let e = &self.extensions[id as usize];
        let target = &self.class(e.target).name;
        match e.module {
            Some(m) => format!("`extension {target}` in `{}`", self.class(m).name),
            None => format!("a top-level `extension {target}`"),
        }
    }

    fn own_modules(
        &self,
        id: ClassId,
        side: Vec<(ClassId, Vec<Type>)>,
    ) -> Vec<(ClassId, Vec<Type>)> {
        if self.class(id).kind == ClassKind::Module {
            return Vec::new();
        }
        side.into_iter()
            .skip(1)
            .take_while(|(c, _)| self.class(*c).kind == ClassKind::Module)
            .collect()
    }

    /// The extensions that add conformances, looked up once per walk.
    fn conformance_extensions(&self) -> Vec<ExtensionId> {
        self.active_extension_ids()
            .into_iter()
            .filter(|e| !self.extensions[*e as usize].includes.is_empty())
            .collect()
    }

    /// `ancestors`, with the conformances of `exts` only. As in Ruby,
    /// including a module that is already there (through a module
    /// included before, or the superclass chain with the same type
    /// arguments) does nothing, so it stays below what included it
    /// first; one included with other arguments (`Comparable[B]` below
    /// `A`'s `Comparable[A]`) comes first and replaces the superclass's.
    fn ancestors_with(
        &self,
        id: ClassId,
        args: &[Type],
        exts: &[ExtensionId],
    ) -> Vec<(ClassId, Vec<Type>)> {
        let mut out = Vec::new();
        let mut cache = HashMap::default();
        self.class_ancestors(id, args, exts, &mut Vec::new(), &mut cache, &mut out);
        out
    }

    fn class_ancestors(
        &self,
        id: ClassId,
        args: &[Type],
        exts: &[ExtensionId],
        chain: &mut Vec<ClassId>,
        cache: &mut ModuleCache,
        out: &mut Vec<(ClassId, Vec<Type>)>,
    ) {
        // A superclass cycle (an error) ends the walk.
        if chain.contains(&id) {
            return;
        }
        chain.push(id);
        let mut own = vec![(id, args.to_vec())];
        own.extend(self.modules_of(id, args, exts, cache));
        let class = self.class(id);
        let mut sup = Vec::new();
        match class
            .superclass
            .as_ref()
            .map(|s| s.subst(&self.class_subst(id, args)))
        {
            Some(Type::Class(sid, sargs)) => {
                self.class_ancestors(sid, &sargs, exts, chain, cache, &mut sup)
            }
            Some(_) => {}
            None => {
                if id != self.builtin.object && class.kind != ClassKind::Module {
                    self.class_ancestors(self.builtin.object, &[], exts, chain, cache, &mut sup)
                }
            }
        }
        own.retain(|e| !sup.contains(e));
        sup.retain(|(c, _)| !own.iter().any(|(o, _)| o == c));
        out.extend(own);
        out.extend(sup);
    }

    /// The modules of `id` in order (not `id` itself): each module it
    /// includes, in the order of the includes, goes in front of those
    /// before it, with the modules that one brings that are not there
    /// yet; then those active extensions make it conform to. Computed
    /// once per module and arguments in a walk (`cache`), so that a
    /// diamond of modules costs no more than a tree.
    fn modules_of(
        &self,
        id: ClassId,
        args: &[Type],
        exts: &[ExtensionId],
        cache: &mut ModuleCache,
    ) -> Vec<(ClassId, Vec<Type>)> {
        let key = (id, args.to_vec());
        if let Some(found) = cache.get(&key) {
            return found.clone();
        }
        // An include cycle (an error) ends here.
        cache.insert(key.clone(), Vec::new());
        let class = self.class(id);
        let subst = self.class_subst(id, args);
        let mut out: Vec<(ClassId, Vec<Type>)> = Vec::new();
        let has =
            |out: &[(ClassId, Vec<Type>)], m: ClassId| m == id || out.iter().any(|(c, _)| *c == m);
        for inc in &class.includes {
            if let Type::Class(mid, margs) = inc.subst(&subst) {
                if has(&out, mid) {
                    continue;
                }
                let mut brought = vec![(mid, margs.clone())];
                brought.extend(self.modules_of(mid, &margs, exts, cache));
                brought.retain(|(c, _)| !has(&out, *c));
                brought.extend(out);
                out = brought;
            }
        }
        for ext_id in exts {
            let ext = &self.extensions[*ext_id as usize];
            if ext.target != id || !self.extension_bounds_hold(ext, args) {
                continue;
            }
            let esubst = self.extension_subst(ext, args);
            // (Its includes as a class's own: the last written first, each
            // with what it brings, after the class's own, #523.)
            let mut mine: Vec<(ClassId, Vec<Type>)> = Vec::new();
            for inc in &ext.includes {
                if let Type::Class(mid, margs) = inc.subst(&esubst) {
                    if has(&out, mid) || mine.iter().any(|(c, _)| *c == mid) {
                        continue;
                    }
                    let mut brought = vec![(mid, margs.clone())];
                    brought.extend(self.modules_of(mid, &margs, exts, cache));
                    brought.retain(|(c, _)| !has(&out, *c) && !mine.iter().any(|(k, _)| k == c));
                    brought.extend(mine);
                    mine = brought;
                }
            }
            out.extend(mine);
        }
        cache.insert(key, out.clone());
        out
    }

    /// Whether a conditional extension (`extension Box[T <: Int]`) applies
    /// to its target with `args`, the arguments the class has at this
    /// point of a walk (a subclass's instantiation of it along the
    /// superclass chain, #516): every bound holds for its argument. With
    /// no arguments (a bare class), it applies.
    ///
    /// A bound against an argument not inferred yet (at any depth, or a
    /// bound naming one) is undecided (#519's decision (i), 2026-11-14):
    /// one that can never hold (`may_be_subtype`) fails; one that still
    /// can is counted as a refusal of a type not yet known
    /// (`refuse_undecided`, said in `undecided_bound`) and does not hold,
    /// so the conformance is refused on the spot, and an overloaded call
    /// that a candidate's conformance would decide is an error at the
    /// call (`Checker::resolve_pretyped`), never another overload. While
    /// such a call is tried again as if the types were known
    /// (`undecided_passes`), it holds where it still can.
    pub fn extension_bounds_hold(&self, ext: &ExtensionInfo, args: &[Type]) -> bool {
        if args.is_empty() || ext.type_params.iter().all(|tp| tp.bounds.is_empty()) {
            return true;
        }
        let subst = self.extension_subst(ext, args);
        ext.type_params.iter().all(|tp| match subst.get(&tp.id) {
            None => true,
            Some(t) => tp.bounds.iter().all(|b| {
                let b = b.subst(&subst);
                if !t.has_vars() && !b.has_vars() {
                    return self.is_subtype(t, &b);
                }
                if !self.may_be_subtype(t, &b) {
                    return false;
                }
                if !self.refuse_undecided() {
                    return true;
                }
                self.undecided_bound_refusals
                    .set(self.undecided_bound_refusals.get() + 1);
                let target = self.type_name(&Type::Class(ext.target, ext.target_args.clone()));
                let said = format!(
                    "`{target}`'s extension applies only where `{} <: {}`, which is not known for `{}` here; write the type argument (as `{}[...]`)",
                    self.type_param_name(tp.id),
                    self.type_name(&b),
                    self.type_name(t),
                    self.class(ext.target).name
                );
                *self.undecided_bound_seen.borrow_mut() = Some(said.clone());
                *self.undecided_bound.borrow_mut() = Some(said);
                false
            }),
        })
    }

    /// Whether `t` can still be a subtype of `b` once their inference
    /// variables are inferred (an argument not inferred yet, at any depth,
    /// or a bound naming one), approximated by two fills: `is_subtype`
    /// with every variable filled with `Nothing`, or with every variable
    /// filled with `Object` (the same fill on both sides). So
    /// `Bx[Array[?]]` may meet `T <: Array[Int]` (`Array` is covariant)
    /// and `Bx[Array[Array[?]]]` never can; a variable in an invariant
    /// position can only if a fill fits. (An approximation in the
    /// accepting direction, used only to tell a bound that can never hold
    /// from one not known yet, which `extension_bounds_hold` refuses, #519.)
    fn may_be_subtype(&self, t: &Type, b: &Type) -> bool {
        if !t.has_vars() && !b.has_vars() {
            return self.is_subtype(t, b);
        }
        let object = Type::class(self.builtin.object);
        self.is_subtype(&t.fill_vars(&Type::Nothing), &b.fill_vars(&Type::Nothing))
            || self.is_subtype(&t.fill_vars(&object), &b.fill_vars(&object))
    }

    /// Whether `m` (its types through `msubst`) takes `o`'s place: it
    /// takes every call `o` takes (`takes_calls_of`) and returns what `o`
    /// returns, `o`'s result through `osubst` (an implementation by type,
    /// its result included: R0's acceptance and witness, the witness
    /// record's, the class side's candidates, #656).
    pub fn takes_place_of(
        &self,
        m: &MethodInfo,
        msubst: &HashMap<TypeParamId, Type>,
        o: &MethodInfo,
        osubst: &HashMap<TypeParamId, Type>,
    ) -> bool {
        self.takes_calls_of(m, msubst, o, osubst)
            && self.is_subtype(&m.ret.subst(msubst), &o.ret.subst(osubst))
    }

    /// The classes of `ancestors(id, ..)`, in the same order, without
    /// their type arguments (for lookups by name).
    /// Whether `m` (its types through `msubst`) takes every call `o` (its
    /// types through `osubst`) takes: as many positional parameters or
    /// more (the others optional), each at least as wide, the block of a
    /// type at least as wide, and every keyword call
    /// (`MethodInfo::keywords_accept`), each keyword at least as wide.
    pub fn takes_calls_of(
        &self,
        m: &MethodInfo,
        msubst: &HashMap<TypeParamId, Type>,
        o: &MethodInfo,
        osubst: &HashMap<TypeParamId, Type>,
    ) -> bool {
        let wider = |t: &Type, u: &Type| {
            let (t, u) = (t.subst(osubst), u.subst(msubst));
            t == u || self.is_subtype(&t, &u)
        };
        let (ps, qs) = (o.positional_params(), m.positional_params());
        let blocks = match (&o.block, &m.block) {
            (Some((_, b)), Some((_, c))) => wider(b, c),
            (None, None) => true,
            _ => false,
        };
        let keyword = |p: &ParamInfo, q: &ParamInfo| {
            p.kind == q.kind
                && (p.kind == ParamKind::KeywordRest
                    || (p.kind == ParamKind::KeywordOnly && p.name == q.name))
        };
        blocks
            && ps.len() <= qs.len()
            && ps
                .iter()
                .zip(&qs)
                .all(|(p, q)| p.kind == q.kind && wider(&p.ty, &q.ty))
            && qs[ps.len()..]
                .iter()
                .all(|q| q.default.is_some() || q.kind == ParamKind::Rest)
            && m.keywords_accept(o)
            && o.params
                .iter()
                .filter(|p| matches!(p.kind, ParamKind::KeywordOnly | ParamKind::KeywordRest))
                .all(|p| {
                    m.params
                        .iter()
                        .find(|q| keyword(p, q))
                        .is_none_or(|q| wider(&p.ty, &q.ty))
                })
    }

    /// The overrides a class's include makes: a method of a module the
    /// class includes itself comes before its superclass's methods and
    /// overrides one whose calls it takes, both seen through the class's
    /// ancestors (`Comparable[A]#<` over a `B#<(other: A)`), as
    /// (class, overridden, overriding). The runtime dispatches by it
    /// (`Interp::find_override`) and the checker checks it.
    pub fn include_overrides(&self) -> Vec<(ClassId, MethodId, MethodId)> {
        self.classes
            .iter()
            .flat_map(|c| self.include_overrides_of(c.id))
            .map(|o| (o.class, o.overridden, o.by))
            .collect()
    }

    /// `include_overrides` for class `id`, each side with how it is seen
    /// from the class. A module's methods are its own and those of its
    /// always-active (prelude) extensions, which the runtime takes too
    /// (`Interp::find_override`). Asked under the class's declaration view
    /// (`declaration_view`, #606).
    pub fn include_overrides_of(&self, id: ClassId) -> Vec<IncludeOverride> {
        self.with_active(self.declaration_view(id), || {
            self.include_overrides_here(id)
        })
    }

    /// `include_overrides_of` under the extensions active now.
    fn include_overrides_here(&self, id: ClassId) -> Vec<IncludeOverride> {
        let mut out: Vec<IncludeOverride> = Vec::new();
        let c = self.class(id);
        // (Only a class or module with includes of its own, or that an
        // extension's include makes conform, has pairs: what its
        // superclass includes is the superclass's.)
        if c.includes.is_empty()
            && !self
                .extensions
                .iter()
                .any(|e| e.target == id && !e.includes.is_empty())
        {
            return out;
        }
        // (A module too: its own includes' pairs hold in every class
        // including it, #536; it has no superclass.)
        let inherited = match &c.superclass {
            Some(Type::Class(sup, _)) => self.walked_ids(*sup),
            _ if c.kind == ClassKind::Module => Vec::new(),
            _ => return out,
        };
        // (The names the superclass chain has methods of, once: a module's
        // method of another name overrides nothing.)
        // (With the conditional extensions' modules, their bound assumed:
        // a module the class includes overrides one of theirs as the
        // class's own method does, docs/01 §7.)
        let ancestors = self.own_ancestors(c.id);
        // (Every ancestor's names: a module's method may override a
        // superclass's or an earlier-included module's, #536.)
        let names: rustc_hash::FxHashSet<&str> = ancestors
            .iter()
            .flat_map(|(s, _)| self.class(*s).methods.keys().map(|n| n.as_str()))
            .collect();
        let overriding = self.overriding_modules(c.id);
        for (xpos, (x, xargs)) in ancestors.iter().enumerate() {
            if self.class(*x).kind != ClassKind::Module
                || inherited.contains(x)
                || !overriding.contains(x)
            {
                continue;
            }
            // The module's methods, and its prelude extensions', of such a
            // name, each with how its parameters are seen from the class.
            let mut mine: Vec<(MethodId, usize)> = Vec::new();
            let mut substs: Vec<HashMap<TypeParamId, Type>> = Vec::new();
            for (name, ids) in &self.class(*x).methods {
                if names.contains(name.as_str()) {
                    for &mm in ids {
                        if self.method(mm).owner == *x {
                            mine.push((mm, 0));
                        }
                    }
                }
            }
            if !mine.is_empty() {
                substs.push(self.class_subst(*x, xargs));
            }
            for e in self
                .extensions
                .iter()
                .filter(|e| e.target == *x && e.always_active)
            {
                let before = mine.len();
                for (name, ids) in &e.methods {
                    if names.contains(name.as_str()) {
                        mine.extend(ids.iter().map(|mm| (*mm, substs.len())));
                    }
                }
                if mine.len() > before {
                    let mut esubst = HashMap::default();
                    for (ta, xa) in e.target_args.iter().zip(xargs) {
                        if let Type::Param(p) = ta {
                            esubst.insert(*p, xa.clone());
                        }
                    }
                    substs.push(esubst);
                }
            }
            if mine.is_empty() {
                continue;
            }
            let x_own = self.walked_ids(*x);
            for (mm, at) in mine {
                let msubst = &substs[at];
                let m = self.method(mm);
                // (A constructor's chain is no override: `initialize` and
                // `deinitialize` are the class's, run by `new` and `super`.)
                if m.is_abstract
                    || (!m.singleton && matches!(m.name.as_str(), "initialize" | "deinitialize"))
                {
                    continue;
                }
                // (Any ancestor after the module in the class's lookup
                // order, outside the module's own ancestry: the superclass
                // chain, or a module included before it.)
                for (s, sargs) in &ancestors[xpos + 1..] {
                    if x_own.contains(s) {
                        continue;
                    }
                    let base = self.class_subst(*s, sargs);
                    let Some(os) = self.class(*s).methods.get(&m.name) else {
                        continue;
                    };
                    for &o in os {
                        let om = self.method(o);
                        // (Their type parameters as the overriding one's,
                        // in order.)
                        if om.type_params.len() != m.type_params.len() {
                            continue;
                        }
                        let mut ssubst = base.clone();
                        for (p, q) in om.type_params.iter().zip(&m.type_params) {
                            ssubst.insert(p.id, Type::Param(q.id));
                        }
                        if om.singleton == m.singleton
                            && self.replaces_seen(mm, msubst, o, &ssubst)
                            && !out.iter().any(|e| e.overridden == o)
                            && !self.replaced_before(&ancestors[..xpos], o, false)
                        {
                            out.push(IncludeOverride {
                                class: c.id,
                                overridden: o,
                                overridden_subst: ssubst.clone(),
                                by: mm,
                                by_subst: msubst.clone(),
                                module: *x,
                            });
                        }
                    }
                }
            }
        }
        // An abstract method of a module the class includes is replaced by
        // what implements it later in the class's lookup order (a
        // superclass's, or a module's included before it): the first that
        // takes its calls (#536; the runtime passes the abstract one over).
        for (xpos, (x, xargs)) in ancestors.iter().enumerate() {
            if self.class(*x).kind != ClassKind::Module || inherited.contains(x) {
                continue;
            }
            let x_own = self.walked_ids(*x);
            let asubst = self.class_subst(*x, xargs);
            for ids in self.class(*x).methods.values() {
                for &am in ids {
                    let a = self.method(am);
                    // (Not when something before the module in the lookup
                    // order, the class's own method, implements it: that
                    // runs, and pairs with it as an override.)
                    if a.owner != *x
                        || !a.is_abstract
                        || out.iter().any(|e| e.overridden == am)
                        || self.replaced_before(&ancestors[..xpos], am, false)
                    {
                        continue;
                    }
                    'later: for (s, sargs) in &ancestors[xpos + 1..] {
                        if x_own.contains(s) {
                            continue;
                        }
                        let Some(os) = self.class(*s).methods.get(&a.name) else {
                            continue;
                        };
                        for &o in os {
                            let om = self.method(o);
                            if om.owner != *s
                                || om.is_abstract
                                || om.type_params.len() != a.type_params.len()
                            {
                                continue;
                            }
                            let mut ssubst = self.class_subst(*s, sargs);
                            for (p, q) in om.type_params.iter().zip(&a.type_params) {
                                ssubst.insert(p.id, Type::Param(q.id));
                            }
                            if self.replaces_seen(o, &ssubst, am, &asubst) {
                                out.push(IncludeOverride {
                                    class: c.id,
                                    overridden: am,
                                    overridden_subst: asubst.clone(),
                                    by: o,
                                    by_subst: ssubst,
                                    module: *x,
                                });
                                break 'later;
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// The overrides a class's includes make on its class side: a module's
    /// class method comes after the class's own class methods and before
    /// its superclass's (docs/01 §6), and overrides a superclass's class
    /// method whose calls it takes, both seen through the class's
    /// ancestors, as (class, overridden, overriding). The runtime
    /// dispatches by it (`Interp::class_method_override`) and the checker
    /// checks it.
    pub fn class_include_overrides(&self) -> Vec<(ClassId, MethodId, MethodId)> {
        self.classes
            .iter()
            .flat_map(|c| self.class_include_overrides_of(c.id))
            .map(|o| (o.class, o.overridden, o.by))
            .collect()
    }

    /// `class_include_overrides` for class `id`, each side with how it is
    /// seen from the class (`module` is the included module, or the one it
    /// includes, that declares `by`). Asked under the class's declaration
    /// view (`declaration_view`, #606).
    pub fn class_include_overrides_of(&self, id: ClassId) -> Vec<IncludeOverride> {
        self.with_active(self.declaration_view(id), || {
            self.class_include_overrides_here(id)
        })
    }

    /// `class_include_overrides_of` under the extensions active now.
    fn class_include_overrides_here(&self, id: ClassId) -> Vec<IncludeOverride> {
        let mut out: Vec<IncludeOverride> = Vec::new();
        let c = self.class(id);
        // (A module too: its own includes' pairs, #536.)
        if c.includes.is_empty() || (c.superclass.is_none() && c.kind != ClassKind::Module) {
            return out;
        }
        let own: Vec<Type> = c.type_params.iter().map(|p| Type::Param(p.id)).collect();
        // The superclasses, with their arguments as the class sees them.
        let supers: Vec<(ClassId, Vec<Type>)> = self
            .ancestors(id, &own)
            .into_iter()
            .filter(|(s, _)| *s != id && self.class(*s).kind != ClassKind::Module)
            .collect();
        // The class's own class methods come first: one that overrides `o`
        // as the runtime takes it (`Interp::class_method_override`) is the
        // one, an overload of the name is not.
        // (The override table, #536.)
        let overridden_by_own = |o: MethodId| {
            c.singleton_methods
                .get(&self.method(o).name)
                .is_some_and(|mine| {
                    mine.iter()
                        .any(|&a| self.method(a).owner == id && self.overrides(a).contains(&o))
                })
        };
        // (The last module included first, as the runtime; the class's own
        // includes: an extension's take no part in dispatch, #504.)
        let modules = self.class_modules_included(id, &own);
        for (xpos, (x, xargs)) in modules.iter().enumerate() {
            let (x, xargs) = (*x, xargs.clone());
            // (Over a superclass's, or a module included before it, outside
            // its own ancestry, #536.)
            let x_own = self.walked_ids(x);
            let later: Vec<(ClassId, Vec<Type>)> = modules[xpos + 1..]
                .iter()
                .filter(|(k, _)| !x_own.contains(k))
                .cloned()
                .chain(supers.iter().cloned())
                .collect();
            let msubst = self.class_subst(x, &xargs);
            for ids in self.class(x).singleton_methods.values() {
                for &mm in ids {
                    let m = self.method(mm);
                    if m.owner != x || m.is_abstract || m.extension.is_some() {
                        continue;
                    }
                    for (s, sargs) in &later {
                        let Some(os) = self.class(*s).singleton_methods.get(&m.name) else {
                            continue;
                        };
                        let base = self.class_subst(*s, sargs);
                        for &o in os {
                            let om = self.method(o);
                            if om.owner != *s
                                || om.extension.is_some()
                                || om.synth != Synth::None
                                || om.name == "new"
                                || om.type_params.len() != m.type_params.len()
                            {
                                continue;
                            }
                            // (Their type parameters as the overriding
                            // one's, in order.)
                            let mut ssubst = base.clone();
                            for (p, q) in om.type_params.iter().zip(&m.type_params) {
                                ssubst.insert(p.id, Type::Param(q.id));
                            }
                            if self.replaces_seen(mm, &msubst, o, &ssubst)
                                && !out.iter().any(|e| e.overridden == o)
                                && !overridden_by_own(o)
                                && !self.replaced_before(&modules[..xpos], o, true)
                            {
                                out.push(IncludeOverride {
                                    class: id,
                                    overridden: o,
                                    overridden_subst: ssubst,
                                    by: mm,
                                    by_subst: msubst.clone(),
                                    module: x,
                                });
                            }
                        }
                    }
                }
            }
        }
        // An abstract class method of a module the class includes is
        // replaced by what implements it later on its class side (a
        // superclass's class method, or one of a module included before
        // it): the first that takes its calls (#536).
        for (xpos, (x, xargs)) in modules.iter().enumerate() {
            let x_own = self.walked_ids(*x);
            let asubst = self.class_subst(*x, xargs);
            let later: Vec<(ClassId, Vec<Type>)> = modules[xpos + 1..]
                .iter()
                .filter(|(k, _)| !x_own.contains(k))
                .cloned()
                .chain(supers.iter().cloned())
                .collect();
            for ids in self.class(*x).singleton_methods.values() {
                for &am in ids {
                    let a = self.method(am);
                    if a.owner != *x || !a.is_abstract || out.iter().any(|e| e.overridden == am) {
                        continue;
                    }
                    'later: for (s, sargs) in &later {
                        let Some(os) = self.class(*s).singleton_methods.get(&a.name) else {
                            continue;
                        };
                        for &o in os {
                            let om = self.method(o);
                            if om.owner != *s
                                || om.is_abstract
                                || om.type_params.len() != a.type_params.len()
                            {
                                continue;
                            }
                            let mut ssubst = self.class_subst(*s, sargs);
                            for (p, q) in om.type_params.iter().zip(&a.type_params) {
                                ssubst.insert(p.id, Type::Param(q.id));
                            }
                            if self.replaces_seen(o, &ssubst, am, &asubst) {
                                out.push(IncludeOverride {
                                    class: id,
                                    overridden: am,
                                    overridden_subst: asubst.clone(),
                                    by: o,
                                    by_subst: ssubst,
                                    module: *x,
                                });
                                break 'later;
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// `class_is_a` in the run-time view (`View::Runtime`: every
    /// extension's conformance, whichever are active): for the lowering,
    /// which must not depend on where it runs (#554, #536 step 2).
    pub fn class_is_a_at_run_time(&self, sub_id: ClassId, sup_id: ClassId) -> bool {
        sub_id == sup_id
            || sup_id == self.builtin.object
            || self
                .resolution(sub_id, &[], View::Runtime)
                .iter()
                .any(|(id, _)| *id == sup_id)
    }

    /// `ancestor_ids` in the run-time view (`class_is_a_at_run_time`).
    pub fn ancestor_ids_at_run_time(&self, id: ClassId) -> Vec<ClassId> {
        self.resolution(id, &[], View::Runtime)
            .into_iter()
            .map(|(c, _)| c)
            .collect()
    }

    pub fn ancestor_ids(&self, id: ClassId) -> Vec<ClassId> {
        self.ancestors(id, &[])
            .into_iter()
            .map(|(c, _)| c)
            .collect()
    }

    /// Whether two methods have the same signature: parameters (kinds
    /// and types) and block, their own type parameters renamed in order.
    pub fn same_signature(&self, a: &MethodInfo, b: &MethodInfo) -> bool {
        if a.type_params.len() != b.type_params.len() {
            return false;
        }
        let rename: HashMap<TypeParamId, Type> = b
            .type_params
            .iter()
            .zip(&a.type_params)
            .map(|(q, p)| (q.id, Type::Param(p.id)))
            .collect();
        let same = |t: &Type, u: &Type| self.same_type(t, &u.subst(&rename));
        a.type_params.iter().zip(&b.type_params).all(|(p, q)| {
            p.bounds.len() == q.bounds.len()
                && p.bounds.iter().zip(&q.bounds).all(|(x, y)| same(x, y))
        }) && match (&a.block, &b.block) {
            (Some((_, t)), Some((_, u))) => same(t, u),
            (None, None) => true,
            _ => false,
        } && a.block_optional == b.block_optional
            && a.params.len() == b.params.len()
            && a.params.iter().zip(&b.params).all(|(p, q)| {
                // A call binds keyword-only parameters by name, so
                // their names tell overloads apart.
                p.kind == q.kind
                    && same(&p.ty, &q.ty)
                    && (p.kind != ParamKind::KeywordOnly || p.name == q.name)
            })
    }

    /// Whether a call of `mid` with an implicit receiver passes no `self`
    /// of the caller: a built-in `Kernel` function (one an `extension
    /// Kernel` adds is a method), or a top-level `def`, a function, which
    /// has no `self` (docs/01 §2).
    pub fn takes_no_self(&self, mid: MethodId) -> bool {
        let m = self.method(mid);
        (m.is_native && m.owner == self.builtin.kernel)
            || self.class(m.owner).kind == ClassKind::Main
    }

    /// The pseudo-class of `file`'s top-level methods.
    pub fn file_main(&self, file: u32) -> Option<ClassId> {
        self.file_mains.get(file as usize).copied().flatten()
    }

    /// The extensions of `class`'s `using`s (in its body; for a file's
    /// main pseudo-class, at the top level) in effect at `pos` in `file`:
    /// those written before it, a `using` being in effect from its
    /// statement to the end of the body (docs/01 §7). (Code of another
    /// file, a generated method's body, has them all.)
    fn usings_at(&self, class: ClassId, file: u32, pos: u32) -> Vec<ExtensionId> {
        let c = self.class(class);
        c.usings
            .iter()
            .filter(|(at, _)| c.file != file || *at < pos)
            .map(|(_, e)| *e)
            .collect()
    }

    /// The extensions active in code written at `pos` in `file`, in the
    /// body of `lexical` (a class or module; `None`: the top level): the
    /// `using`s before `pos` there, in the namespaces it is nested in and
    /// at the file's top level, its group's top-level extensions, and the
    /// extensions the modules it is in declare (`own_extensions`).
    pub fn extensions_active_at(
        &self,
        lexical: Option<ClassId>,
        file: u32,
        pos: u32,
    ) -> Vec<ExtensionId> {
        let mut active = Vec::new();
        let mut ns = lexical;
        while let Some(n) = ns {
            active.extend(self.usings_at(n, file, pos));
            ns = self.class(n).lexical;
        }
        active.extend(self.file_extensions(file, pos));
        active.extend(self.own_extensions(lexical));
        let mut seen = rustc_hash::FxHashSet::default();
        active.retain(|e| seen.insert(*e));
        active
    }

    /// The extensions a module declares are in effect inside its body
    /// (so they see each other for calls; two of one class reach each
    /// other, so a `super` in one taking the other's method is an error,
    /// #585): those of `class` and of the modules it is nested in.
    fn own_extensions(&self, class: Option<ClassId>) -> Vec<ExtensionId> {
        let mut out = Vec::new();
        let mut ns = class;
        while let Some(n) = ns {
            let c = self.class(n);
            out.extend(c.extensions.iter().copied());
            ns = c.lexical;
        }
        out
    }

    /// The extensions active at `pos` in `file` from its top level: its
    /// `using`s before `pos`, and its group's top-level extensions.
    pub fn file_extensions(&self, file: u32, pos: u32) -> Vec<ExtensionId> {
        let mut active = self
            .file_main(file)
            .map(|fm| self.usings_at(fm, file, pos))
            .unwrap_or_default();
        for e in self.group_extensions(file) {
            if !active.contains(&e) {
                active.push(e);
            }
        }
        active
    }

    /// The relation "extension `a` reaches `b`" over the extensions of
    /// `target` (#585): `b` is active where `a` is declared
    /// (`extensions_active_at`, a method-level `using` taking no part), so
    /// a `super` in `a`'s methods may take one of `b`'s. Each extension with
    /// those it reaches; one `extensions_active_at` per extension.
    pub fn reach_graph(&self, target: ClassId) -> Vec<(ExtensionId, Vec<ExtensionId>)> {
        let exts: Vec<ExtensionId> = self
            .extensions
            .iter()
            .filter(|e| e.target == target)
            .map(|e| e.id)
            .collect();
        exts.iter()
            .map(|&a| {
                let ea = &self.extensions[a as usize];
                let active: rustc_hash::FxHashSet<ExtensionId> = self
                    .extensions_active_at(ea.module, ea.file, ea.span.start)
                    .into_iter()
                    .collect();
                let reached = exts
                    .iter()
                    .copied()
                    .filter(|b| *b != a && active.contains(b))
                    .collect();
                (a, reached)
            })
            .collect()
    }

    /// The cycles of `graph` (`reach_graph`): each extension with its
    /// component, the extensions it reaches and that reach it back, directly
    /// or through others, itself included: no order between them (#585).
    /// Kosaraju's two passes, linear in the graph.
    pub fn reach_components(
        graph: &[(ExtensionId, Vec<ExtensionId>)],
    ) -> HashMap<ExtensionId, usize> {
        let index: HashMap<ExtensionId, usize> = graph
            .iter()
            .enumerate()
            .map(|(i, (k, _))| (*k, i))
            .collect();
        let n = graph.len();
        let fwd: Vec<Vec<usize>> = graph
            .iter()
            .map(|(_, next)| next.iter().filter_map(|y| index.get(y).copied()).collect())
            .collect();
        let mut rev: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (i, next) in fwd.iter().enumerate() {
            for &j in next {
                rev[j].push(i);
            }
        }
        // (Finish order of a depth-first walk, iterative.)
        let mut done = vec![false; n];
        let mut order = Vec::with_capacity(n);
        for start in 0..n {
            if done[start] {
                continue;
            }
            done[start] = true;
            let mut stack = vec![(start, 0)];
            while let Some((v, i)) = stack.pop() {
                if i < fwd[v].len() {
                    stack.push((v, i + 1));
                    let w = fwd[v][i];
                    if !done[w] {
                        done[w] = true;
                        stack.push((w, 0));
                    }
                } else {
                    order.push(v);
                }
            }
        }
        // (The reversed graph, in reverse finish order: one component each.)
        let mut comp = vec![usize::MAX; n];
        let mut count = 0;
        for &start in order.iter().rev() {
            if comp[start] != usize::MAX {
                continue;
            }
            comp[start] = count;
            let mut stack = vec![start];
            while let Some(v) = stack.pop() {
                for &w in &rev[v] {
                    if comp[w] == usize::MAX {
                        comp[w] = count;
                        stack.push(w);
                    }
                }
            }
            count += 1;
        }
        graph
            .iter()
            .enumerate()
            .map(|(i, (k, _))| (*k, comp[i]))
            .collect()
    }

    /// The extensions active throughout `file`: those declared at the top
    /// level of its group's files.
    pub fn group_extensions(&self, file: u32) -> Vec<ExtensionId> {
        let Some(group) = self.file_groups.get(&file) else {
            return Vec::new();
        };
        self.extensions
            .iter()
            .filter(|e| e.group.as_ref() == Some(group))
            .map(|e| e.id)
            .collect()
    }

    /// `f` evaluated with `set` as the active extensions (`active_extensions`),
    /// the previous set restored after: a relation asked under a given view
    /// (a class's declaration view, `group_extensions`, #606).
    pub fn with_active<R>(&self, set: Vec<ExtensionId>, f: impl FnOnce() -> R) -> R {
        let saved = self.active_extensions.replace(set);
        let r = f();
        self.active_extensions.replace(saved);
        r
    }

    pub fn active_extension_ids(&self) -> Vec<ExtensionId> {
        let mut ids: Vec<ExtensionId> = self
            .extensions
            .iter()
            .filter(|e| e.always_active)
            .map(|e| e.id)
            .collect();
        for id in self.active_extensions.borrow().iter() {
            if !ids.contains(id) {
                ids.push(*id);
            }
        }
        ids
    }

    /// Map an extension's type parameters to the receiver's type arguments
    /// (`extension Array[T <: X]` applied to `Array[Int]` gives `T := Int`).
    pub fn extension_subst(
        &self,
        ext: &ExtensionInfo,
        args: &[Type],
    ) -> HashMap<TypeParamId, Type> {
        let mut map = HashMap::default();
        for (targ, arg) in ext.target_args.iter().zip(args.iter()) {
            if let Type::Param(pid) = targ {
                map.insert(*pid, arg.clone());
            }
        }
        map
    }

    /// Superclass chain for singleton method lookup (class methods are
    /// inherited; modules do not inherit).
    pub fn superclass_chain(&self, id: ClassId) -> Vec<ClassId> {
        let mut out = vec![id];
        let mut cur = id;
        while let Some(Type::Class(sid, _)) = &self.class(cur).superclass {
            if out.contains(sid) {
                break;
            }
            out.push(*sid);
            cur = *sid;
        }
        out
    }

    /// Whether a field of type `t` without a default may be left unassigned
    /// (nil): its type admits `nil` (`Object` does). A type parameter's
    /// never does, whatever its bounds (upper ones: `G[T <: Object?]` may
    /// be a `G[Int]`); `T?` does.
    pub fn field_may_stay_nil(&self, t: &Type) -> bool {
        match t {
            Type::Class(c, _) => *c == self.builtin.nil || *c == self.builtin.object,
            Type::Union(ms) => ms
                .iter()
                .any(|m| matches!(m, Type::Class(c, _) if *c == self.builtin.nil)),
            _ => false,
        }
    }

    /// Whether a class has fields that an `initialize` must assign (docs/01
    /// §3): every field of a data type or a variant; otherwise one without
    /// a default whose type does not admit `nil` (a type parameter's may
    /// not), its own or (`inherited`) its superclasses' too. Which
    /// `initialize` may make it goes by this, in the checker and at run
    /// time.
    pub fn has_fields_to_assign(&self, id: ClassId, inherited: bool) -> bool {
        if matches!(self.class(id).kind, ClassKind::Data | ClassKind::Variant) {
            return true;
        }
        let needs = |f: &FieldInfo| !f.has_default() && !self.field_may_stay_nil(&f.ty);
        if inherited {
            self.all_fields(id).iter().any(|(f, _)| needs(f))
        } else {
            self.class(id).fields.iter().any(needs)
        }
    }

    /// Fields of a class including inherited ones, superclass fields first.
    pub fn all_fields(&self, id: ClassId) -> Vec<(FieldInfo, HashMap<TypeParamId, Type>)> {
        let mut chain = self.superclass_chain(id);
        chain.reverse();
        let mut out = Vec::new();
        let mut subst: HashMap<TypeParamId, Type> = HashMap::default();
        // Walk from the root down, composing substitutions.
        let mut substs: Vec<HashMap<TypeParamId, Type>> = Vec::new();
        {
            // Compute, for each class in the chain (from `id` upward), the
            // substitution of its params in terms of `id`'s params.
            let mut cur = id;
            let mut cur_subst: HashMap<TypeParamId, Type> = HashMap::default();
            let mut per_class = vec![(cur, cur_subst.clone())];
            while let Some(sup) = &self.class(cur).superclass {
                if let Type::Class(sid, sargs) = sup.subst(&cur_subst) {
                    cur_subst = self.class_subst(sid, &sargs);
                    per_class.push((sid, cur_subst.clone()));
                    cur = sid;
                } else {
                    break;
                }
            }
            per_class.reverse();
            for (_, s) in per_class {
                substs.push(s);
            }
        }
        for (i, cid) in chain.iter().enumerate() {
            if let Some(s) = substs.get(i) {
                subst = s.clone();
            }
            for f in &self.class(*cid).fields {
                out.push((f.clone(), subst.clone()));
            }
        }
        out
    }

    pub fn field_index(&self, id: ClassId, name: &str) -> Option<usize> {
        self.all_fields(id).iter().position(|(f, _)| f.name == name)
    }

    pub fn find_field(
        &self,
        id: ClassId,
        name: &str,
    ) -> Option<(FieldInfo, HashMap<TypeParamId, Type>)> {
        self.all_fields(id)
            .into_iter()
            .find(|(f, _)| f.name == name)
    }

    // ----- subtyping ---------------------------------------------------------

    /// Whether `a[aargs]`, a `data` type, enum or variant, is Shareable by
    /// its fields (`class_shareable`, computed when declarations end:
    /// `ensure_shareable_known`) and its arguments.
    pub fn derived_shareable(&self, a: ClassId, aargs: &[Type]) -> bool {
        let class = self.class(a);
        matches!(
            class.kind,
            ClassKind::Data | ClassKind::Enum | ClassKind::Variant
        ) && class.shareable == Some(true)
            && (aargs.is_empty() || self.data_fields_shareable(a, aargs))
    }

    /// Whether a value of `t`, a field's type, is Shareable, as
    /// `is_shareable` says but from what is decided already (for
    /// subtyping): a `shareable` procedure type, a class value, a union
    /// or tuple of such, or a `Shareable` (a type parameter by its
    /// bounds).
    fn holds_shareable(&self, t: &Type) -> bool {
        match t {
            Type::Nothing | Type::Void | Type::ClassObject(..) | Type::TypeOf(_) => true,
            Type::Proc(_, _, _, shareable, _) => *shareable,
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().all(|m| self.holds_shareable(m)),
            _ => self.is_subtype(t, &Type::class(self.builtin.shareable)),
        }
    }

    /// Whether the fields of `data` type, enum or variant `id`, with its
    /// type arguments `args` put in, are all `Shareable` (docs/03 §5): a
    /// `T` only inside a `shareable` procedure type, or a `Type[T]`, makes
    /// any argument fit. An instance met again while it is judged (a
    /// recursive type) counts as Shareable: its fields decide.
    pub fn data_fields_shareable(&self, id: ClassId, args: &[Type]) -> bool {
        let key = Type::Class(id, args.to_vec());
        if let Some(&known) = self.shareable_seen_known.borrow().get(&key) {
            return known;
        }
        let hit = self
            .shareable_instances_seen
            .borrow()
            .iter()
            .position(|t| *t == key);
        if let Some(at) = hit {
            self.shareable_seen_floor
                .set(self.shareable_seen_floor.get().min(at));
            return true;
        }
        // The class again with other arguments: by its arguments, as
        // `instance_shareable` does.
        if self
            .shareable_instances_seen
            .borrow()
            .iter()
            .any(|t| matches!(t, Type::Class(c, _) if *c == id))
        {
            let shareable = Type::class(self.builtin.shareable);
            return args.iter().all(|a| {
                if a.has_vars() {
                    !self.refuse_undecided()
                } else {
                    self.is_subtype(a, &shareable)
                }
            });
        }
        let at = self.shareable_instances_seen.borrow().len();
        self.shareable_instances_seen.borrow_mut().push(key.clone());
        let floor = self.shareable_seen_floor.replace(usize::MAX);
        let class = self.class(id);
        let mut by_args = self.class_subst(id, args);
        if let Some(e) = class.variant_of {
            by_args.extend(self.class_subst(e, args));
        }
        let fits = |t: &Type| {
            if t.has_vars() {
                !self.refuse_undecided()
            } else {
                self.holds_shareable(t)
            }
        };
        let mut ok = self
            .all_fields(id)
            .into_iter()
            .all(|(f, subst)| fits(&f.ty.subst(&subst).subst(&by_args)));
        if ok && class.kind == ClassKind::Enum {
            ok = class
                .variants
                .clone()
                .into_iter()
                .all(|v| self.data_fields_shareable(v, args));
        }
        self.shareable_instances_seen.borrow_mut().pop();
        // Definite unless it leaned on an instance further out (a negative
        // always is), and not for undecided arguments or ones mentioning
        // a type parameter (`Self`: the class asking).
        let leaned = self.shareable_seen_floor.get();
        if (!ok || leaned >= at) && !args.iter().any(|a| a.has_vars() || a.mentions_any_param()) {
            self.shareable_seen_known.borrow_mut().insert(key, ok);
        }
        self.shareable_seen_floor.set(floor.min(leaned));
        ok
    }

    /// Compute `class_shareable` for the `data` types and enums, which
    /// `derived_shareable` reads.
    pub fn ensure_shareable_known(&mut self, ids: &[ClassId]) {
        for &id in ids {
            if matches!(
                self.class(id).kind,
                ClassKind::Data | ClassKind::Enum | ClassKind::Variant
            ) {
                self.class_shareable(id);
            }
        }
    }

    /// `sub <: sup` for types without unresolved inference variables (a
    /// `Var` is only a subtype of itself).
    /// Whether `a[aargs]` seen as `b` keeps `b`'s Shareable promise: a
    /// type Shareable by its arguments (a built-in collection, a `data`
    /// type, an enum) is a Shareable `b` only when they are (docs/03): an
    /// `Array[() -> Int]` is no `Shareable`.
    /// Whether a Shareable check refuses a type only because it is not yet
    /// known (counted, for `Checker::resolve_pretyped`).
    pub fn refuse_undecided(&self) -> bool {
        if self.undecided_passes.get() {
            return false;
        }
        self.undecided_refusals
            .set(self.undecided_refusals.get() + 1);
        true
    }

    pub fn keeps_shareable(&self, a: ClassId, aargs: &[Type], b: ClassId) -> bool {
        if aargs.is_empty() || self.shareable_promise(b).is_none() {
            return true;
        }
        let by_args = |c: ClassId| {
            self.is_value_class(c)
                || matches!(
                    self.class(c).kind,
                    ClassKind::Data | ClassKind::Enum | ClassKind::Variant
                )
        };
        // (Seen as one that carries the arguments, `Array[T]` as
        // `Array[U]`, its own rules apply.)
        if !by_args(a) || by_args(b) {
            return true;
        }
        // A `data` type or an enum: by its fields with the arguments in.
        if !self.is_value_class(a) {
            return self.data_fields_shareable(a, aargs);
        }
        let shareable = Type::class(self.builtin.shareable);
        aargs.iter().all(|t| {
            if t.has_vars() {
                !self.refuse_undecided()
            } else {
                self.is_subtype(t, &shareable)
            }
        })
    }

    /// Whether `Type` includes the module `m` (one without type
    /// parameters, `Shareable`): then every class value is an `m`.
    pub fn type_includes(&self, m: ClassId) -> bool {
        m != self.builtin.class_
            && self.class(m).kind == ClassKind::Module
            && self.class(m).type_params.is_empty()
            && self
                .ancestors(self.builtin.class_, &[self.object()])
                .iter()
                .any(|(anc, _)| *anc == m)
    }

    pub fn is_subtype(&self, sub: &Type, sup: &Type) -> bool {
        if sub == sup || sub.is_nothing() {
            return true;
        }
        let depth = self.subtype_depth.get();
        if depth >= SUBTYPE_DEPTH {
            return false;
        }
        let key = (sub.clone(), sup.clone());
        if self.subtype_open.borrow().contains(&key) {
            return false;
        }
        self.subtype_open.borrow_mut().push(key);
        self.subtype_depth.set(depth + 1);
        let r = self.is_subtype_at(sub, sup);
        self.subtype_depth.set(depth);
        self.subtype_open.borrow_mut().pop();
        r
    }

    fn is_subtype_at(&self, sub: &Type, sup: &Type) -> bool {
        if sub == sup || sub.is_nothing() {
            return true;
        }
        if matches!(sub, Type::Void) || matches!(sup, Type::Void) {
            return self.is_subtype(&self.unvoid(sub), &self.unvoid(sup));
        }
        if self.is_object(sup) {
            return true;
        }
        match (sub, sup) {
            (Type::Union(ms), _) => ms.iter().all(|m| self.is_subtype(m, sup)),
            (_, Type::Union(ms)) => ms.iter().any(|m| self.is_subtype(sub, m)),
            (Type::Class(a, aargs), Type::Class(b, bargs)) => {
                for (anc, anc_args) in self.ancestors(*a, aargs) {
                    if anc == *b {
                        return self.args_compatible(*b, &anc_args, bargs)
                            && self.keeps_shareable(*a, aargs, *b);
                    }
                }
                // A `data` type or enum Shareable by its fields is a
                // `Shareable` without including it (docs/03), given
                // Shareable arguments.
                *b == self.builtin.shareable && self.derived_shareable(*a, aargs)
            }
            // `Type[A] <: Type[B]` when `A <: B` (arguments included; the
            // run-time values carry none, `new` is typed only where the
            // class is written).
            (Type::ClassObject(..) | Type::TypeOf(_), Type::ClassObject(..) | Type::TypeOf(_)) => {
                match (sub.instance_of(), sup.instance_of()) {
                    (Some(a), Some(b)) => self.is_subtype(&a, &b),
                    _ => false,
                }
            }
            // A cog's root module as a value is a `Cog` (docs/10 §6).
            (Type::ClassObject(a, _), Type::Class(b, _))
                if *b == self.builtin.cog && self.class(*a).cog.is_some() =>
            {
                true
            }
            (Type::ClassObject(..) | Type::TypeOf(_), Type::Class(b, bargs))
                if *b == self.builtin.class_ =>
            {
                match (sub.instance_of(), bargs.first()) {
                    (Some(a), Some(arg)) => self.is_subtype(&a, arg),
                    _ => true,
                }
            }
            // A class value is a `Type`, so what `Type` includes it is
            // too: a `Shareable`.
            (Type::ClassObject(..) | Type::TypeOf(_), Type::Class(b, _))
                if self.type_includes(*b) =>
            {
                true
            }
            // `Meta::ClassDef[X]` is a `Type[X]`.
            (Type::Class(..), Type::ClassObject(..) | Type::TypeOf(_)) => {
                match (self.class_object_instance(sub), sup.instance_of()) {
                    (Some(a), Some(b)) => self.is_subtype(&a, &b),
                    _ => false,
                }
            }
            (Type::Tuple(xs), Type::Tuple(ys)) => {
                xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.is_subtype(x, y))
            }
            (Type::Tuple(xs), Type::Class(b, bargs)) if *b == self.builtin.array => {
                let elem = Type::union_of(xs.clone());
                bargs.len() == 1 && self.is_subtype(&elem, &bargs[0])
            }
            // Tuples compare element by element (`[2, "a"] < [2, "b"]`).
            (Type::Tuple(xs), Type::Class(b, bargs)) if *b == self.builtin.comparable => {
                match bargs.as_slice() {
                    [Type::Tuple(ys)] => {
                        xs.len() == ys.len()
                            && xs
                                .iter()
                                .zip(ys)
                                .all(|(x, y)| self.is_subtype(x, &Type::Class(*b, vec![y.clone()])))
                    }
                    _ => false,
                }
            }
            // (Seen as an array of its elements, also for the Shareable
            // promise: `[counter, 1]` is no `Shareable`.)
            (Type::Tuple(xs), Type::Class(b, _)) => {
                self.class_is_a(self.builtin.array, *b)
                    && self.keeps_shareable(self.builtin.array, &[Type::union_of(xs.clone())], *b)
            }
            (Type::Proc(ra, ps, r, sa, ka), Type::Proc(rb, qs, s, sb, kb)) => {
                // A shareable procedure is a procedure; not the reverse.
                if *sb && !*sa {
                    return false;
                }
                // Keywords by name, contravariant (docs/02 §9).
                match ProcKw::accepts(ka, kb) {
                    Some(pairs) if pairs.iter().all(|(v, t)| self.is_subtype(t, v)) => {}
                    _ => return false,
                }
                // Receivers, like parameters, are contravariant.
                let recv_ok = match (ra, rb) {
                    (None, None) => true,
                    (Some(a), Some(b)) => self.is_subtype(b, a),
                    _ => false,
                };
                recv_ok
                    && ps.len() == qs.len()
                    && ps.iter().zip(qs).all(|(p, q)| self.is_subtype(q, p))
                    && self.is_subtype(r, s)
            }
            (Type::Proc(..), Type::Class(b, _)) => *b == self.builtin.proc_,
            // `U >: T`: what is a `T` is a `U`.
            (_, Type::Param(u))
                if self
                    .param_lower(*u)
                    .is_some_and(|l| self.is_subtype(sub, l)) =>
            {
                true
            }
            (Type::Param(p), _) => {
                let bounds = self.param_bounds(*p);
                bounds.iter().any(|b| self.is_subtype(b, sup))
            }
            _ => false,
        }
    }

    /// The lower bound of a method type parameter (`U >: T`).
    fn param_lower(&self, id: TypeParamId) -> Option<&Type> {
        self.lower_bounds.get(&id)
    }

    /// Whether a value of type parameter `id` may be `nil` or `false`:
    /// unless one of its bounds holds neither (`T <: Int`). A bound that
    /// names type parameters is not decided here (`Comparable[T]` may be
    /// what `Bool` includes), so it does not rule them out.
    pub fn param_may_be_falsy(&self, id: TypeParamId) -> bool {
        let (nil, bool_) = (self.nil(), self.bool_());
        !self.param_bounds(id).iter().any(|b| {
            !b.mentions_any_param()
                && !b.has_vars()
                && !self.is_subtype(&nil, b)
                && !self.is_subtype(&bool_, b)
        })
    }

    /// The interpreter's `same_signature` (with the same block presence):
    /// what replaces a method on the class side
    /// (`Interp::class_side_override`).
    pub fn same_signature_at_run_time(&self, m: MethodId, o: MethodId) -> bool {
        let (m, om) = (self.method(m), self.method(o));
        let (ps, qs) = (om.positional_params(), m.positional_params());
        // (The shape first, cheap: the types, by name, only for a match.)
        if om.block.is_some() != m.block.is_some()
            || ps.len() != qs.len()
            || ps.iter().zip(&qs).any(|(p, q)| p.kind != q.kind)
        {
            return false;
        }
        let same = |p: &ParamInfo, q: &ParamInfo| self.same_at_run_time(om, &p.ty, m, &q.ty);
        let blocks = match (&om.block, &m.block) {
            (Some((_, b)), Some((_, c))) => self.same_at_run_time(om, b, m, c),
            (None, None) => true,
            _ => false,
        };
        blocks
            && ps.len() == qs.len()
            && ps
                .iter()
                .zip(&qs)
                .all(|(p, q)| p.kind == q.kind && same(p, q))
            // (Each keyword shared, the same.)
            && m.keywords_accept(om)
            && om
                .params
                .iter()
                .filter(|p| matches!(p.kind, ParamKind::KeywordOnly | ParamKind::KeywordRest))
                .all(|p| {
                    m.params
                        .iter()
                        .find(|q| {
                            q.kind == p.kind
                                && (p.kind == ParamKind::KeywordRest || q.name == p.name)
                        })
                        .is_none_or(|q| same(p, q))
                })
    }

    /// Whether `t` of `om` and `u` of `m` are the same type for the runtime
    /// (`RtParam::ty`): one that mentions its method's own type parameters
    /// or `Self` matches anything, any other is compared as written.
    fn same_at_run_time(&self, om: &MethodInfo, t: &Type, m: &MethodInfo, u: &Type) -> bool {
        fn open(m: &MethodInfo, t: &Type) -> bool {
            match t {
                Type::Param(p) => {
                    *p == crate::declare::SELF_PARAM || m.type_params.iter().any(|tp| tp.id == *p)
                }
                Type::Var(_) => true,
                Type::Class(_, args) | Type::ClassObject(_, args) => {
                    args.iter().any(|a| open(m, a))
                }
                Type::Union(ts) | Type::Tuple(ts) => ts.iter().any(|a| open(m, a)),
                Type::TypeOf(t) => open(m, t),
                Type::Proc(r, ps, ret, _, kws) => {
                    r.as_deref().is_some_and(|r| open(m, r))
                        || ps.iter().any(|a| open(m, a))
                        || open(m, ret)
                        || kws.iter().any(|k| open(m, &k.ty))
                }
                Type::Nothing | Type::Void => false,
            }
        }
        let (t, u) = (self.devoid(t), self.devoid(u));
        open(om, &t)
            || open(m, &u)
            // (A class's type parameter by its id, as `rtworld::rt_sig_type`.)
            || if t.mentions_any_param() || u.mentions_any_param() {
                t == u
            } else {
                self.type_name(&t) == self.type_name(&u)
            }
    }

    /// Whether method `m` replaces method `o` at run time, `o` being
    /// declared in ancestor `a` with `aargs` as `m`'s owner sees it: the
    /// one pairing rule of the override relation (#536 step 1; docs/01 §3).
    /// Same name and side (the caller's lookup); `o`'s positional
    /// parameters, substituted, each at least as wide in `m` (of the same
    /// kind), `m`'s extra ones optional or rest; a block exactly when `o`
    /// has one, of a type at least as wide; every keyword call `o` takes
    /// (`MethodInfo::keywords_accept`), each shared keyword at least as
    /// wide; or the same signature for the runtime
    /// (`same_signature_at_run_time`: a type mentioning a method's own
    /// type parameter, `Self` or an inference variable matches). Result
    /// types are not part of it: a pair is then checked as an override
    /// (`check_override_pair`).
    pub fn replaces(&self, m: MethodId, o: MethodId, a: ClassId, aargs: &[Type]) -> bool {
        self.replaces_seen(m, &HashMap::default(), o, &self.class_subst(a, aargs))
    }

    /// `replaces` with both sides' types seen through substitutions (a
    /// module's method in a class including it: `msubst` its arguments
    /// there; `osubst` the overridden one's owner's, with the method type
    /// parameters renamed by the caller): the widening rule
    /// (`takes_calls_of`) or the same signature for the runtime.
    pub fn replaces_seen(
        &self,
        m: MethodId,
        msubst: &HashMap<TypeParamId, Type>,
        o: MethodId,
        osubst: &HashMap<TypeParamId, Type>,
    ) -> bool {
        let (mi, oi) = (self.method(m), self.method(o));
        self.takes_calls_of(mi, msubst, oi, osubst) || self.same_signature_at_run_time(m, o)
    }

    /// Whether a method of one of `earlier` (ancestors before a module in a
    /// class's lookup order, on the instance or the class side) already
    /// replaces `o` there, by being it or by its own table entry: a later
    /// module's method then does not (#536: `M3` including `M1` puts its
    /// `k` in `M1.k`'s place before `M2`'s does).
    fn replaced_before(
        &self,
        earlier: &[(ClassId, Vec<Type>)],
        o: MethodId,
        singleton: bool,
    ) -> bool {
        let name = &self.method(o).name;
        earlier.iter().any(|(y, _)| {
            let yc = self.class(*y);
            let table = if singleton {
                &yc.singleton_methods
            } else {
                &yc.methods
            };
            table.get(name).is_some_and(|ids| {
                ids.iter().any(|&k| {
                    let km = self.method(k);
                    km.owner == *y && !km.is_abstract && (k == o || self.overrides(k).contains(&o))
                })
            })
        })
    }

    /// The override table's entry for method `m`: the methods of its
    /// owner's ancestors (with its own type parameters) it replaces
    /// (`replaces`). What `RtMethod::overrides` ships and every reader
    /// takes (#536 step 1). Asked under its owner's declaration view
    /// (`declaration_view`, #606), whatever is active where it is asked.
    pub fn overrides(&self, m: MethodId) -> Vec<MethodId> {
        let owner = self.method(m).owner;
        self.with_active(self.declaration_view(owner), || self.overrides_here(m))
    }

    /// `overrides` under the extensions active now.
    fn overrides_here(&self, m: MethodId) -> Vec<MethodId> {
        let ancs = self.own_ancestors(self.method(m).owner);
        self.overrides_with(
            m,
            &ancs,
            &self.type_classes(),
            &self.extension_methods_by_target(),
        )
    }

    /// Class `c`'s ancestors with its own type parameters, then the
    /// modules its classes' conditional extensions include, their bounds
    /// assumed: what its methods may override (the override table and its
    /// check, `check_override_returns`).
    pub fn own_ancestors(&self, c: ClassId) -> Vec<(ClassId, Vec<Type>)> {
        self.resolution(c, &self.own_args(c), View::Override)
    }

    /// `View::Override` of class `id` with `args`.
    fn override_resolution(&self, id: ClassId, args: &[Type]) -> Vec<(ClassId, Vec<Type>)> {
        self.override_under(id, args, &self.all_conformance_extensions())
    }

    /// The ancestors of class `id` the runtime looks methods up in
    /// (`RtClass::ancestors`): as `ancestors` with no arguments, with every
    /// extension's include (`all_conformance_extensions`), the same set the
    /// override table takes, so the two cannot disagree (#554).
    pub fn runtime_ancestors(&self, id: ClassId) -> Vec<(ClassId, Vec<Type>)> {
        self.resolution(id, &[], View::Runtime)
    }

    /// The modules of class `c`'s ancestry whose methods may override the
    /// class's or its ancestors' (docs/01 §7): those its own includes bring
    /// (a superclass's too) and those an unconditional extension at the top
    /// level includes, active everywhere in its cog or application. A
    /// scoped (module-body) or conditional extension's module is
    /// overridden by the class's own methods and includes, and overrides
    /// none of them (#504's rule, (e)).
    pub fn overriding_modules(&self, c: ClassId) -> Vec<ClassId> {
        let top = self.top_level_conformance_extensions();
        let own: Vec<Type> = self
            .class(c)
            .type_params
            .iter()
            .map(|tp| Type::Param(tp.id))
            .collect();
        self.ancestors_under(c, &own, top)
            .into_iter()
            .map(|(a, _)| a)
            .filter(|a| self.class(*a).kind == ClassKind::Module)
            .collect()
    }

    /// The unconditional extensions at the top level of a cog or the
    /// application with includes: those
    /// whose modules override the class's or its ancestors' methods
    /// (docs/01 §7).
    fn top_level_conformance_extensions(&self) -> Vec<ExtensionId> {
        self.extensions
            .iter()
            .filter(|e| {
                // (At the top level of the application, no namespace; or
                // of a library cog, its root module, which holds its files'
                // top level, as `ExtensionInfo::group` has it, and then
                // only on a class the cog declares: a cog cannot
                // monkey-patch its users' or std's classes, docs/10.)
                !e.includes.is_empty()
                    && match e.module {
                        None => true,
                        Some(ns) => {
                            self.cogs.iter().any(|c| c.root == Some(ns))
                                && self.encloses(ns, e.target)
                        }
                    }
                    && e.type_params.iter().all(|tp| tp.bounds.is_empty())
            })
            .map(|e| e.id)
            .collect()
    }

    /// Whether namespace `ns` holds class `c`, at any depth (`c`'s
    /// `parent` chain reaches it).
    fn encloses(&self, ns: ClassId, c: ClassId) -> bool {
        let mut at = self.class(c).parent;
        while let Some(p) = at {
            if p == ns {
                return true;
            }
            at = self.class(p).parent;
        }
        false
    }

    /// The ancestors of class `id` a lookup by name may find methods in
    /// (`RtClass::lookup`): its own includes along the chain and the
    /// modules of unconditional top-level extensions, in resolution order;
    /// not the modules of scoped or conditional extensions, which are in
    /// `runtime_ancestors` (membership) but override nothing of the
    /// class's (docs/01 §7, `overriding_modules`).
    pub fn lookup_ancestors(&self, id: ClassId) -> Vec<ClassId> {
        self.resolution(id, &[], View::Lookup)
            .into_iter()
            .map(|(a, _)| a)
            .collect()
    }

    /// Every extension with includes, not the ones active where this is
    /// asked: conformance holds everywhere, and the override table must not
    /// depend on which file was checked last, or on a warm cache.
    pub fn all_conformance_extensions(&self) -> Vec<ExtensionId> {
        self.extensions
            .iter()
            .filter(|e| !e.includes.is_empty())
            .map(|e| e.id)
            .collect()
    }

    /// `own_ancestors` with `all_conformance_extensions` found once.
    pub fn own_ancestors_under(
        &self,
        c: ClassId,
        exts: &[ExtensionId],
    ) -> Vec<(ClassId, Vec<Type>)> {
        self.override_under(c, &self.own_args(c), exts)
    }

    /// `View::Override`'s walk with `exts` found once: the runtime view, then
    /// the conditional extensions' modules with their bound assumed.
    fn override_under(
        &self,
        c: ClassId,
        own: &[Type],
        exts: &[ExtensionId],
    ) -> Vec<(ClassId, Vec<Type>)> {
        self.ordered_under(c, own, exts, true, false)
    }

    /// The order of `View::Runtime` and `View::Override`: dispatch's
    /// (`View::Lookup`'s), then every other extension's modules appended;
    /// `assume`: a conditional extension's bound taken as met where the
    /// arguments mention a parameter (the override table), else only where
    /// it holds (membership).
    /// Of `exts`, the top-level ones (conditional ones too), whose modules
    /// keep their place in `ordered_under`'s walk.
    fn walked_extensions(&self, exts: &[ExtensionId]) -> Vec<ExtensionId> {
        let mut top: Vec<ExtensionId> = exts
            .iter()
            .copied()
            .filter(|e| {
                let ext = &self.extensions[*e as usize];
                ext.module.is_none_or(|ns| {
                    self.cogs.iter().any(|c| c.root == Some(ns)) && self.encloses(ns, ext.target)
                })
            })
            .collect();
        // (The unconditional ones first, their modules with the class's own
        // includes, in front of a conditional one's, whatever the order of
        // declaration; each kind in its own order, #523; #588.)
        top.sort_by_key(|e| {
            self.extensions[*e as usize]
                .type_params
                .iter()
                .any(|tp| !tp.bounds.is_empty())
        });
        top
    }

    /// The classes and modules in the walked part of `id`'s run-time and
    /// override order (`ordered_under` before the appended modules): what
    /// is already there at a superclass, or in a module's own ancestry,
    /// for the include tables. Independent of the extensions active where
    /// the checker is (a table built in the checker's process and one
    /// decoded from the cache are the same).
    fn walked_ids(&self, id: ClassId) -> Vec<ClassId> {
        let top = self.walked_extensions(&self.all_conformance_extensions());
        self.ancestors_under(id, &self.own_args(id), top)
            .into_iter()
            .map(|(c, _)| c)
            .collect()
    }

    fn ordered_under(
        &self,
        c: ClassId,
        own: &[Type],
        exts: &[ExtensionId],
        assume: bool,
        lexical: bool,
    ) -> Vec<(ClassId, Vec<Type>)> {
        self.ordered_sources(c, own, exts, assume, lexical)
            .into_iter()
            .map(|(k, a, _)| (k, a))
            .collect()
    }

    /// `ordered_under`, each entry with the extension whose include put it
    /// there after the walk (a scoped or conditional one; `None` for the
    /// walk itself: the class, its own includes, its top-level extensions'
    /// modules, its superclasses').
    fn ordered_sources(
        &self,
        c: ClassId,
        own: &[Type],
        exts: &[ExtensionId],
        assume: bool,
        lexical: bool,
    ) -> Vec<(ClassId, Vec<Type>, Option<ExtensionId>)> {
        // (The order is dispatch's, `View::Lookup`'s: the class's own
        // includes and the top-level unconditional extensions' modules; a
        // module another extension brings at a superclass does not count
        // as already there, so it does not move an own include down.)
        // (The top-level extensions, conditional ones too, whose bounds the
        // walk checks as the static view does: their modules keep their
        // place, so a call resolves statically as it runs, (e); the scoped
        // ones' modules are appended. The appending loop goes over every
        // extension, for the conditional modules `assume` adds.)
        let top = self.walked_extensions(exts);
        let rest: Vec<ExtensionId> = exts.to_vec();
        let mut out = self.ancestors_under(c, own, top);
        let mut src: Vec<Option<ExtensionId>> = vec![None; out.len()];
        // (Then the modules of the other extensions, scoped or conditional,
        // which a class's own methods and includes override and which
        // override nothing of theirs (docs/01 §7): after everything else.
        // A conditional extension's where its bound holds, or with its
        // bound assumed wherever the arguments mention the class's own
        // parameters, not for concrete ones that fail it, `Box[String]`'s
        // (an approximation of "the bound holds for some instantiation"
        // that errs toward pairing, #556). Until no module is added: one
        // may include a module another extension targets.)
        let mut seen = 0;
        while seen < out.len() {
            let (a, args) = out[seen].clone();
            seen += 1;
            // (`lexical`: where the next active extension's modules go: after
            // the modules of the class part the target is in (the class's own
            // includes and its top-level extensions' modules, which override
            // any extension's, docs/01 §7; for a module target, those of the
            // class including it), before the next class up the chain; after
            // the earlier active extensions' (the first active extension's
            // in front).)
            let mut ext_end = seen;
            if lexical
                && rest
                    .iter()
                    .any(|e| self.extensions[*e as usize].target == a)
            {
                while ext_end < out.len() && self.class(out[ext_end].0).kind == ClassKind::Module {
                    ext_end += 1;
                }
            }
            for e in &rest {
                let ext = &self.extensions[*e as usize];
                if ext.target != a {
                    continue;
                }
                let conditional = ext.type_params.iter().any(|tp| !tp.bounds.is_empty());
                if conditional
                    && !self.extension_bounds_hold(ext, &args)
                    && !(assume && args.iter().any(|t| t.mentions_any_param()))
                {
                    continue;
                }
                let esubst = self.extension_subst(ext, &args);
                let ext_start = ext_end;
                for inc in &ext.includes {
                    if let Type::Class(mid, margs) = inc.subst(&esubst) {
                        let mut brought = vec![(mid, margs.clone())];
                        brought.extend(
                            self.ancestors_under(mid, &margs, exts.to_vec())
                                .into_iter()
                                .skip(1),
                        );
                        // (`lexical`, the checker's view where a scoped
                        // extension is active: its modules right after its
                        // target (after earlier active extensions' ones),
                        // the last include first, as an own include's
                        // (docs/01 §7: they hide the superclass's methods
                        // there); still never moving a module already in
                        // the order.)
                        let mut at = ext_start;
                        for b in brought {
                            if !out.iter().any(|(x, _)| *x == b.0) {
                                if lexical {
                                    out.insert(at, b);
                                    src.insert(at, Some(*e));
                                    at += 1;
                                    ext_end += 1;
                                } else {
                                    out.push(b);
                                    src.push(Some(*e));
                                }
                            }
                        }
                    }
                }
            }
        }
        out.into_iter()
            .zip(src)
            .map(|((k, a), e)| (k, a, e))
            .collect()
    }

    /// The override table for every method (`overrides`), the classes that
    /// are `Type`s found once: what the lowering ships.
    pub fn override_table(&self) -> Vec<Vec<MethodId>> {
        let types = self.type_classes();
        let exts = self.extension_methods_by_target();
        // (Each owner's ancestors once.)
        let conf = self.all_conformance_extensions();
        let mut ancs: HashMap<ClassId, Vec<(ClassId, Vec<Type>)>> = HashMap::default();
        (0..self.methods.len() as MethodId)
            .map(|m| {
                let owner = self.method(m).owner;
                let a = ancs
                    .entry(owner)
                    .or_insert_with(|| self.own_ancestors_under(owner, &conf));
                // (Under the owner's declaration view, as `overrides`.)
                self.with_active(self.declaration_view(owner), || {
                    self.overrides_with(m, a, &types, &exts)
                })
            })
            .collect()
    }

    /// The extensions active where class `c` is declared: those at the top
    /// level of its group's files (`group_extensions`). The view the
    /// override table and the include pairs are asked under (#606), the
    /// one the declarer checks a class's overrides with.
    pub fn declaration_view(&self, c: ClassId) -> Vec<ExtensionId> {
        self.group_extensions(self.class(c).file)
    }

    /// `Type` and its subclasses (`Meta::ClassDef`), the classes of class
    /// objects, each with its ancestors in its own type parameter (the
    /// class, substituted for it per class method).
    #[allow(clippy::type_complexity)]
    fn type_classes(&self) -> Vec<(Option<TypeParamId>, Vec<(ClassId, Vec<Type>)>)> {
        self.classes
            .iter()
            .filter(|k| k.id == self.builtin.class_ || self.class_is_a(k.id, self.builtin.class_))
            .map(|k| {
                let param = (k.type_params.len() == 1).then(|| k.type_params[0].id);
                let args: Vec<Type> = param.iter().map(|p| Type::Param(*p)).collect();
                (param, self.ancestors(k.id, &args))
            })
            .collect()
    }

    #[allow(clippy::type_complexity)]
    fn overrides_with(
        &self,
        m: MethodId,
        ancs: &[(ClassId, Vec<Type>)],
        type_classes: &[(Option<TypeParamId>, Vec<(ClassId, Vec<Type>)>)],
        ext_methods: &HashMap<(ClassId, &str), Vec<MethodId>>,
    ) -> Vec<MethodId> {
        let mi = self.method(m);
        // A top-level `def` is a function: it overrides nothing (docs/01 §1).
        if self.class(mi.owner).kind == ClassKind::Main {
            return Vec::new();
        }
        let own: Vec<Type> = self
            .class(mi.owner)
            .type_params
            .iter()
            .map(|tp| Type::Param(tp.id))
            .collect();
        let mut out = self.overridden_methods_in_with(mi, ancs, ext_methods);
        // A class method replaces, on its class object, the instance methods
        // of `Type` (and a subclass's, `Meta::ClassDef`'s, whose value a
        // static def's `self` is; and their ancestors) of the name it takes
        // the calls of, each seen with the class as its argument
        // (`Interp::class_side_override`).
        // (Only a name some class object's class has an instance method
        // of.)
        if mi.singleton
            && type_classes.iter().any(|(_, ancs)| {
                ancs.iter()
                    .any(|(anc, _)| self.class(*anc).methods.contains_key(&mi.name))
            })
        {
            let class_ty = Type::Class(mi.owner, own);
            for (param, ancs) in type_classes {
                let subst: HashMap<TypeParamId, Type> =
                    param.iter().map(|p| (*p, class_ty.clone())).collect();
                for (anc, aargs) in ancs {
                    let Some(ids) = self.class(*anc).methods.get(&mi.name) else {
                        continue;
                    };
                    let aargs: Vec<Type> = aargs.iter().map(|t| t.subst(&subst)).collect();
                    for &o in ids {
                        // (`Meta::ClassDef#type` is never replaced: in
                        // static code `type` is always the reflection's,
                        // the class as a `Type[Self]`, which no class
                        // method can be for every subclass, #553.)
                        if *anc == self.builtin.meta_classdef && mi.name == "type" {
                            continue;
                        }
                        if !out.contains(&o) && self.replaces(m, o, *anc, &aargs) {
                            out.push(o);
                        }
                    }
                }
            }
        }
        out
    }

    /// The methods extensions give each class (any extension), by target
    /// and name.
    fn extension_methods_by_target(&self) -> HashMap<(ClassId, &str), Vec<MethodId>> {
        let mut map: HashMap<(ClassId, &str), Vec<MethodId>> = HashMap::default();
        for e in &self.extensions {
            for (name, ids) in &e.methods {
                map.entry((e.target, name.as_str()))
                    .or_default()
                    .extend(ids.iter().copied());
            }
        }
        map
    }

    fn overridden_methods_in_with(
        &self,
        m: &MethodInfo,
        ancs: &[(ClassId, Vec<Type>)],
        ext_methods: &HashMap<(ClassId, &str), Vec<MethodId>>,
    ) -> Vec<MethodId> {
        let mut out = Vec::new();
        for (anc, anc_args) in ancs {
            let anc = *anc;
            if anc == m.owner {
                continue;
            }
            let ac = self.class(anc);
            let table = if m.singleton {
                &ac.singleton_methods
            } else {
                &ac.methods
            };
            // (And the methods extensions give the ancestor, any extension:
            // the runtime replaces one by a subclass's own of the
            // signature wherever it is called from.)
            let ext_ids = ext_methods
                .get(&(anc, m.name.as_str()))
                .into_iter()
                .flatten()
                .copied()
                .filter(|&x| self.method(x).singleton == m.singleton);
            let ids: Vec<MethodId> = table
                .get(&m.name)
                .into_iter()
                .flatten()
                .copied()
                .chain(ext_ids)
                .collect();
            if ids.is_empty() {
                continue;
            }
            // (The ancestor's arguments, once per ancestor with a method of
            // the name.)
            let subst = self.class_subst(anc, anc_args);
            let none = HashMap::default();
            for pid in ids {
                if pid != m.id
                    && !out.contains(&pid)
                    && self.replaces_seen(m.id, &none, pid, &subst)
                {
                    out.push(pid);
                }
            }
        }
        out
    }

    /// For a call's table (`Output::union_calls`) whose members are all
    /// class objects, which no class test tells apart (`Type[Kind] |
    /// Type[T]`): the class method all the methods found override, if any
    /// (`overridden_class_method`). A call of it dispatches on the
    /// receiver's class, so the receiver's own runs.
    pub fn class_object_base(&self, table: &[(Type, MethodId)]) -> Option<MethodId> {
        if table.is_empty()
            || !table
                .iter()
                .all(|(t, _)| matches!(t, Type::ClassObject(..) | Type::TypeOf(_)))
        {
            return None;
        }
        let mut methods: Vec<MethodId> = table.iter().map(|(_, k)| *k).collect();
        methods.sort_unstable();
        methods.dedup();
        if methods.len() < 2 {
            return None;
        }
        self.overridden_class_method(&methods)
            .or_else(|| self.included_class_object_base(table))
    }

    /// For class objects only (`Type[A] | Type[B]`): a class method (a
    /// class's, or a module's a class includes, docs/01 §6) that the
    /// run-time lookup from each member's class reaches as that member's
    /// method (`Interp::class_method_override`): `M.k` for `A.k` and `C.k`
    /// on two subclasses of a class that includes `M`, or for `A.k` and
    /// `M.k` itself on a subclass without its own.
    fn included_class_object_base(&self, table: &[(Type, MethodId)]) -> Option<MethodId> {
        let mut entries: Vec<(ClassId, MethodId)> = Vec::new();
        for (t, k) in table {
            // (A type parameter's class object, `Type[T]` with `T <: A`,
            // as `Type[A]`, whose value may be any class below `A` too: so
            // that the result does not depend on whether a check of the
            // call with class objects came first, #324.)
            let c = match t {
                Type::ClassObject(c, _) => *c,
                Type::TypeOf(inner) => match &**inner {
                    Type::Param(p) => self.class_bound(*p)?,
                    _ => return None,
                },
                _ => return None,
            };
            let i = self.method(*k);
            if i.extension.is_some() || !i.singleton {
                return None;
            }
            entries.push((c, *k));
        }
        let name = &self.method(entries[0].1).name;
        // Candidates in the first member's lookup order, the most derived
        // first.
        self.lookup_methods(&Type::ClassObject(entries[0].0, Vec::new()), name)
            .into_iter()
            .map(|(b, _)| b)
            .find(|&b| {
                let bi = self.method(b);
                // (Another module's method of the signature, which the
                // lookup may find too, is not on each class's side.)
                bi.extension.is_none()
                    && bi.singleton
                    && entries.iter().all(|&(c, k)| {
                        self.same_signature(self.method(k), bi)
                            && self.class_side_dispatch(c, b) == Some(k)
                    })
            })
    }

    /// The class a type parameter's values are below, as a lookup on it
    /// finds its methods: its first bound that is a class (not a module),
    /// through the bounds of a parameter it is bounded by (a narrowed
    /// one's).
    fn class_bound(&self, p: TypeParamId) -> Option<ClassId> {
        let mut work = vec![p];
        let mut seen = Vec::new();
        while let Some(p) = work.pop() {
            if seen.contains(&p) {
                continue;
            }
            seen.push(p);
            let bounds = self.param_bounds(p);
            if let Some(c) = bounds.iter().find_map(|b| match b {
                Type::Class(c, _) if self.class(*c).kind != ClassKind::Module => Some(*c),
                _ => None,
            }) {
                return Some(c);
            }
            work.extend(bounds.iter().rev().filter_map(|b| match b {
                Type::Param(q) => Some(*q),
                _ => None,
            }));
        }
        None
    }

    /// What a call of class method `b` (a class's or a module's) on the
    /// class object `c` runs, as the runtime finds it: the class's own
    /// class method of `b`'s signature, then one of a module it includes
    /// (the last first), then the superclass's; `None` where `b` is not
    /// on `c`'s class side.
    pub fn class_side_dispatch(&self, c: ClassId, b: MethodId) -> Option<MethodId> {
        let bi = self.method(b);
        // (Whether one replaces `b`: the override table, #536.)
        let hit = |m: MethodId| m == b || self.overrides(m).contains(&b);
        let in_module = self.class(bi.owner).kind == ClassKind::Module;
        let chain = self.superclass_chain(c);
        // (A class's class method is looked for below its owner only, a
        // module's in a class including the module.)
        if !in_module && !chain.contains(&bi.owner)
            || in_module && !self.class_side_order(c).contains(&bi.owner)
        {
            return None;
        }
        // (An abstract `b` is passed over: what comes after it runs, as the
        // runtime finds it.)
        for cur in chain {
            if cur == bi.owner && !bi.is_abstract {
                return Some(b);
            }
            let class = self.class(cur);
            if let Some(ids) = class.singleton_methods.get(&bi.name) {
                if let Some(&m) = ids.iter().find(|&&m| {
                    let mi = self.method(m);
                    mi.owner == cur && !mi.is_abstract && hit(m)
                }) {
                    return Some(m);
                }
            }
            // (A module's class method the class's includes put in `b`'s
            // place, before the walk below, as the runtime.)
            if let Some(e) = self
                .class_include_overrides_of(cur)
                .into_iter()
                .find(|e| e.overridden == b)
            {
                return Some(e.by);
            }
            // (As the runtime: the class's own includes, #504; its part of
            // `class_side_order`, `RtClass::class_side`.)
            for module in self.class_side_modules(c, cur) {
                if module == bi.owner {
                    if bi.is_abstract {
                        continue;
                    }
                    return Some(b);
                }
                if let Some(ids) = self.class(module).singleton_methods.get(&bi.name) {
                    if let Some(&f) = ids.iter().find(|&&f| {
                        let fi = self.method(f);
                        fi.owner == module && !fi.is_abstract && hit(f)
                    }) {
                        return Some(f);
                    }
                }
            }
        }
        None
    }

    /// The class method that each of `methods` is or overrides (an
    /// ancestor's of the same signature; class methods, none an
    /// extension's), the most derived such one: `Kind.k` for `Kind.k` and
    /// `SubKind.k`, and for two siblings' overrides of it.
    pub fn overridden_class_method(&self, methods: &[MethodId]) -> Option<MethodId> {
        // (A class method, or a method of `Type` itself, which every class
        // object answers and a class method of its name and signature
        // overrides: `P.name` over `Type#name`, #562.)
        let class_ = self.builtin.class_;
        let plain = |k: MethodId| {
            let i = self.method(k);
            i.extension.is_none() && (i.singleton || i.owner == class_)
        };
        if !methods.iter().all(|&k| plain(k)) {
            return None;
        }
        let name = &self.method(methods[0]).name;
        let mut candidates: Vec<MethodId> = Vec::new();
        for &k in methods {
            let owner = self.method(k).owner;
            for (c, _) in self.lookup_methods(&Type::ClassObject(owner, Vec::new()), name) {
                if plain(c) && !candidates.contains(&c) {
                    candidates.push(c);
                }
            }
        }
        // (The override table, #536.)
        let overrides =
            |k: MethodId, base: MethodId| k == base || self.overrides(k).contains(&base);
        let bases: Vec<MethodId> = candidates
            .into_iter()
            .filter(|&b| methods.iter().all(|&k| overrides(k, b)))
            .collect();
        // The most derived (each base's owner is an ancestor of the others').
        bases.iter().copied().find(|&b| {
            bases
                .iter()
                .all(|&o| self.class_is_a(self.method(b).owner, self.method(o).owner))
        })
    }

    /// The classes (not modules) a type parameter is bounded by, through
    /// narrowed ones.
    fn bound_classes(&self, id: TypeParamId, out: &mut Vec<ClassId>) {
        for b in self.param_bounds(id) {
            match b {
                Type::Class(c, _) if self.class(c).kind == ClassKind::Class => out.push(c),
                Type::Param(q) => self.bound_classes(q, out),
                _ => {}
            }
        }
    }

    /// A narrowed `T & C`'s methods, gathered from its bounds, ordered as
    /// the class of every value that passes the test orders their owners
    /// (overrides before what they override): a class before its
    /// ancestors, a module before a class that does not include it (a
    /// value's class includes the module below that class); owners neither
    /// orders keep the order found (a stable topological sort). Then the
    /// ancestors of the most derived class among the bounds in its own
    /// order (a value's class orders them so: two modules it includes),
    /// after the others (modules a value's class includes below it).
    fn most_derived_first(
        &self,
        param: TypeParamId,
        mut found: Vec<(MethodId, HashMap<TypeParamId, Type>)>,
    ) -> Vec<(MethodId, HashMap<TypeParamId, Type>)> {
        // (By the ancestors themselves: `class_is_a` has every module
        // below `Object`, which may include one.)
        let is_a = |a: ClassId, b: ClassId| a != b && self.ancestor_ids(a).contains(&b);
        let before = |a: ClassId, b: ClassId| {
            is_a(a, b)
                || (self.class(a).kind == ClassKind::Module
                    && self.class(b).kind != ClassKind::Module
                    && !is_a(b, a))
        };
        let owner = |m: &(MethodId, HashMap<TypeParamId, Type>)| self.method(m.0).owner;
        let mut out = Vec::with_capacity(found.len());
        while !found.is_empty() {
            let i = (0..found.len())
                .find(|&i| !found.iter().any(|y| before(owner(y), owner(&found[i]))))
                .unwrap_or(0);
            out.push(found.remove(i));
        }
        // The most derived class among the bounds (through narrowed ones):
        // a value's class is below it, and orders its ancestors as it does,
        // after the modules it includes below it.
        let mut classes = Vec::new();
        self.bound_classes(param, &mut classes);
        let derived = classes
            .iter()
            .copied()
            .find(|&c| classes.iter().all(|&x| c == x || is_a(c, x)));
        if let Some(c) = derived {
            let order = self.ancestor_ids(c);
            out.sort_by_key(|m| order.iter().position(|x| *x == self.method(m.0).owner));
        }
        out
    }

    pub(crate) fn param_bounds(&self, id: TypeParamId) -> Vec<Type> {
        if let Some(bounds) = self.narrowed_params.get(&id) {
            return bounds.clone();
        }
        if id == u32::MAX {
            return self.self_bound.iter().cloned().collect();
        }
        for c in &self.classes {
            for p in &c.type_params {
                if p.id == id {
                    return p.bounds.clone();
                }
            }
        }
        for m in &self.methods {
            for p in &m.type_params {
                if p.id == id {
                    return p.bounds.clone();
                }
            }
        }
        for e in &self.extensions {
            for p in &e.type_params {
                if p.id == id {
                    return p.bounds.clone();
                }
            }
        }
        Vec::new()
    }

    fn args_compatible(&self, class: ClassId, sub_args: &[Type], sup_args: &[Type]) -> bool {
        if sub_args.len() != sup_args.len() {
            return sub_args.is_empty() || sup_args.is_empty();
        }
        let params = &self.class(class).type_params;
        sub_args
            .iter()
            .zip(sup_args)
            .enumerate()
            .all(|(i, (a, b))| match params.get(i).map(|p| p.variance) {
                Some(Variance::Covariant) => self.is_subtype(a, b),
                Some(Variance::Contravariant) => self.is_subtype(b, a),
                _ => a == b || (self.is_subtype(a, b) && self.is_subtype(b, a)),
            })
    }

    /// Least upper bound used for joining branches: absorbs subtypes into
    /// supertypes, otherwise forms a union.
    /// The element type of a tuple used as an array: the join of its
    /// element types (`[Circle, Rect]` is an `Array[Shape]`).
    pub fn tuple_element(&self, ts: &[Type]) -> Type {
        ts.iter().fold(Type::Nothing, |acc, t| self.join(&acc, t))
    }

    pub fn join(&self, a: &Type, b: &Type) -> Type {
        if a.is_nothing() {
            return b.clone();
        }
        if b.is_nothing() {
            return a.clone();
        }
        if let Some(e) = self.common_enum(a, b) {
            return e;
        }
        if self.is_subtype(a, b) {
            return b.clone();
        }
        if self.is_subtype(b, a) {
            return a.clone();
        }
        self.simplify_union(Type::union_of(vec![a.clone(), b.clone()]))
    }

    /// Two distinct variants of one enum join to the enum itself.
    fn common_enum(&self, a: &Type, b: &Type) -> Option<Type> {
        let (Type::Class(x, xargs), Type::Class(y, _)) = (a, b) else {
            return None;
        };
        if x == y {
            return None;
        }
        let ex = self.class(*x).variant_of;
        let ey = self.class(*y).variant_of;
        match (ex, ey) {
            (Some(e1), Some(e2)) if e1 == e2 => Some(Type::Class(e1, xargs.clone())),
            (Some(e1), None) if e1 == *y => Some(b.clone()),
            (None, Some(e2)) if e2 == *x => Some(a.clone()),
            _ => None,
        }
    }

    /// Remove union members subsumed by other members, and collapse
    /// variants of one enum into the enum.
    pub fn simplify_union(&self, t: Type) -> Type {
        let Type::Union(ms) = t else { return t };
        let mut ms = ms;
        // Collapse variants.
        let mut i = 0;
        while i < ms.len() {
            let mut merged = false;
            for j in (i + 1)..ms.len() {
                if let Some(e) = self.common_enum(&ms[i], &ms[j]) {
                    ms[i] = e;
                    ms.remove(j);
                    merged = true;
                    break;
                }
            }
            if !merged {
                i += 1;
            }
        }
        let mut kept: Vec<Type> = Vec::new();
        for m in &ms {
            if ms
                .iter()
                .any(|o| o != m && self.is_subtype(m, o) && !self.is_subtype(o, m))
            {
                continue;
            }
            if !kept.contains(m) {
                kept.push(m.clone());
            }
        }
        Type::union_of(kept)
    }

    // ----- method lookup --------------------------------------------------------

    /// Candidate methods for `recv.name`, in resolution order, each with the
    /// substitution of the owner's (or extension's) type parameters.
    pub fn lookup_methods(
        &self,
        recv: &Type,
        name: &str,
    ) -> Vec<(MethodId, HashMap<TypeParamId, Type>)> {
        let mut out = Vec::new();
        match recv {
            Type::Class(id, args) => {
                // `Meta::ClassDef[X]`: the class methods of `X` first, as
                // on a `Type[X]`; but not for `type`, always the
                // reflection's in static code, whatever class methods of
                // the name `X` has (#553).
                let reflection = *id == self.builtin.meta_classdef && name == "type";
                if let Some(instance) = self.class_object_instance(recv).filter(|_| !reflection) {
                    for found in self.lookup_methods(&Type::type_of(instance), name) {
                        if !out.iter().any(|(m, _)| *m == found.0) {
                            out.push(found);
                        }
                    }
                }
                let mut own = Vec::new();
                // A file's top-level object answers `Object`'s methods:
                // its class holds the file's top-level `def`s, which are
                // functions, not methods (docs/01 §1).
                if self.class(*id).kind == ClassKind::Main {
                    self.lookup_instance_methods(self.builtin.object, &[], name, &mut own);
                } else {
                    self.lookup_instance_methods(*id, args, name, &mut own);
                }
                // A value of a module type is an object too.
                if self.class(*id).kind == ClassKind::Module {
                    self.lookup_instance_methods(self.builtin.object, &[], name, &mut own);
                }
                for found in own {
                    if !out.iter().any(|(m, _)| *m == found.0) {
                        out.push(found);
                    }
                }
            }
            Type::ClassObject(id, args) => {
                let exts = self.active_extension_ids();
                // Each superclass's type arguments, for its class methods
                // (`E < G[Int]`: `G.mk(x: T)` takes an `Int` on `E`) and
                // its extensions'.
                let ancs = self.ancestors(*id, args);
                // The class side (docs/01 §6): each class's own class
                // methods, then those of the modules it includes, the last
                // first (each with what it includes), then the
                // superclass's.
                for (cid, cargs) in self.ancestors(*id, args) {
                    let class = self.class(cid);
                    // (An included module's, or the module's own when the
                    // receiver is one; an extension's class methods of a
                    // module are the module's own, not its includers'.)
                    if class.kind == ClassKind::Module {
                        for ext_id in &exts {
                            let ext = &self.extensions[*ext_id as usize];
                            if ext.target != cid || cid != *id {
                                continue;
                            }
                            if let Some(ids) = ext.methods.get(name) {
                                let esubst = self.extension_subst(ext, &cargs);
                                for m in ids.iter().filter(|m| self.method(**m).singleton) {
                                    out.push((*m, esubst.clone()));
                                }
                            }
                        }
                        if let Some(ids) = class.singleton_methods.get(name) {
                            let msubst = self.class_subst(cid, &cargs);
                            for m in ids {
                                out.push((*m, msubst.clone()));
                            }
                        }
                        continue;
                    }
                    let subst = if cid == *id {
                        self.class_subst(cid, args)
                    } else {
                        match ancs.iter().find(|(a, _)| *a == cid) {
                            Some((_, aargs)) => self.class_subst(cid, aargs),
                            None => HashMap::default(),
                        }
                    };
                    // An active extension's class methods (`def self.x`),
                    // before the class's own.
                    for ext_id in &exts {
                        let ext = &self.extensions[*ext_id as usize];
                        if ext.target != cid {
                            continue;
                        }
                        if let Some(ids) = ext.methods.get(name) {
                            // (The extension's own type parameters, for the
                            // class's arguments.)
                            let ext_args = ancs
                                .iter()
                                .find(|(a, _)| *a == cid)
                                .map_or(&[][..], |(_, a)| &a[..]);
                            let esubst = self.extension_subst(ext, ext_args);
                            for m in ids.iter().filter(|m| self.method(**m).singleton) {
                                out.push((*m, esubst.clone()));
                            }
                        }
                    }
                    if let Some(ids) = class.singleton_methods.get(name) {
                        for m in ids {
                            out.push((*m, subst.clone()));
                        }
                    }
                }
                // A cog's root module: `Cog`'s methods (its `name`, its
                // `version`), before `Type`'s (docs/10 §6).
                if self.class(*id).cog.is_some() {
                    let own = self.class(self.builtin.cog).methods.get(name);
                    out.extend(own.into_iter().flatten().map(|m| (*m, HashMap::default())));
                }
                // Class objects are objects too: `Type[T]`'s methods.
                let instance = Type::Class(*id, args.clone());
                self.lookup_instance_methods(self.builtin.class_, &[instance], name, &mut out);
            }
            Type::TypeOf(t) => {
                // For `T <: Bound`, the bound's class methods (`Self` being
                // `T`), before `Type[T]`'s own, as for a class object and
                // at run time: a class bound's, and a module bound's `def
                // self.` methods, which every class `T` admits has (it
                // includes the module; through an extension, the module's
                // own run, #494), abstract ones too (#501). Several bounds
                // give each one's.
                if let Type::Param(p) = &**t {
                    // (Through a bound that is a parameter, its bounds:
                    // `[U <: M, T <: U]`; each parameter once.)
                    let mut bounds = Vec::new();
                    let mut work = vec![*p];
                    let mut seen = Vec::new();
                    while let Some(q) = work.pop() {
                        if seen.contains(&q) {
                            continue;
                        }
                        seen.push(q);
                        for b in self.param_bounds(q) {
                            match b {
                                Type::Param(r) => work.push(r),
                                b => bounds.push(b),
                            }
                        }
                    }
                    for b in bounds {
                        let Type::Class(bid, bargs) = &b else {
                            continue;
                        };
                        if self.class(*bid).kind == ClassKind::Module {
                            let on = Type::ClassObject(*bid, bargs.clone());
                            for found in self.lookup_methods(&on, name) {
                                let fm = self.method(found.0);
                                if fm.singleton
                                    && self.class(fm.owner).kind == ClassKind::Module
                                    && !out.iter().any(|(m, _)| *m == found.0)
                                {
                                    out.push(found);
                                }
                            }
                            continue;
                        }
                        for found in
                            self.lookup_methods(&Type::ClassObject(*bid, bargs.clone()), name)
                        {
                            if !out.iter().any(|(m, _)| *m == found.0) {
                                out.push(found);
                            }
                        }
                    }
                }
                let mut own = Vec::new();
                self.lookup_instance_methods(self.builtin.class_, &[(**t).clone()], name, &mut own);
                for found in own {
                    if !out.iter().any(|(m, _)| *m == found.0) {
                        out.push(found);
                    }
                }
            }
            Type::Tuple(ts) => {
                let elem = self.tuple_element(ts);
                self.lookup_instance_methods(self.builtin.array, &[elem], name, &mut out);
            }
            Type::Proc(..) => {
                self.lookup_instance_methods(self.builtin.proc_, &[], name, &mut out);
            }
            Type::Param(p) => {
                let bounds = self.param_bounds(*p);
                for b in bounds {
                    match &b {
                        // (Each method once: a narrowed `T`'s class and
                        // `T` itself, or two bounds, share ancestors.)
                        Type::Class(bid, bargs) => {
                            let mut found = Vec::new();
                            self.lookup_instance_methods(*bid, bargs, name, &mut found);
                            for f in found {
                                if !out.iter().any(|(m, _)| *m == f.0) {
                                    out.push(f);
                                }
                            }
                        }
                        // A narrowed `T` has `T`'s methods too.
                        Type::Param(_) => {
                            for found in self.lookup_methods(&b, name) {
                                if !out.iter().any(|(m, _)| *m == found.0) {
                                    out.push(found);
                                }
                            }
                        }
                        _ => {}
                    }
                }
                if !out.is_empty() && self.narrowed_params.contains_key(p) {
                    return self.most_derived_first(*p, out);
                }
                // A value of any type is an object: `Object`'s methods, but
                // once (a class bound's ancestors have them already, and the
                // same method twice made a call ambiguous).
                let mut object = Vec::new();
                self.lookup_instance_methods(self.builtin.object, &[], name, &mut object);
                for found in object {
                    if !out.iter().any(|(m, _)| *m == found.0) {
                        out.push(found);
                    }
                }
            }
            Type::Void => return self.lookup_methods(&self.nil(), name),
            Type::Union(_) | Type::Nothing | Type::Var(_) => {}
        }
        out
    }

    fn lookup_instance_methods(
        &self,
        id: ClassId,
        args: &[Type],
        name: &str,
        out: &mut Vec<(MethodId, HashMap<TypeParamId, Type>)>,
    ) {
        let exts = self.active_extension_ids();
        for (anc, anc_args) in self.ancestors(id, args) {
            // Extensions on this ancestor take precedence over its own
            // methods (lexically scoped override).
            for ext_id in &exts {
                let ext = &self.extensions[*ext_id as usize];
                if ext.target != anc {
                    continue;
                }
                if let Some(ids) = ext.methods.get(name) {
                    let esubst = self.extension_subst(ext, &anc_args);
                    for m in ids.iter().filter(|m| !self.method(**m).singleton) {
                        out.push((*m, esubst.clone()));
                    }
                }
            }
            if let Some(ids) = self.class(anc).methods.get(name) {
                let subst = self.class_subst(anc, &anc_args);
                for m in ids {
                    out.push((*m, subst.clone()));
                }
            }
        }
    }

    /// Resolve a constant path relative to a namespace, walking outward.
    /// Inside a library cog the walk ends at its root module, then its
    /// imports, then the top level without the application's names.
    pub fn resolve_member(&self, scope: Option<ClassId>, name: &str) -> Option<Member> {
        let mut cur = scope;
        let mut in_library = false;
        while let Some(cid) = cur {
            if let Some(m) = self.class(cid).members.get(name) {
                return Some(*m);
            }
            // Members of ancestors (inherited constants).
            for anc in self.ancestor_ids(cid) {
                if let Some(m) = self.class(anc).members.get(name) {
                    return Some(*m);
                }
            }
            if let Some(cog) = self.class(cid).cog {
                if let Some(root) = self.cogs[cog as usize].imports.get(name) {
                    return Some(Member::Class(*root));
                }
                in_library = true;
            }
            cur = self.class(cid).parent;
        }
        if in_library && self.app_names.contains(name) {
            return None;
        }
        self.top.get(name).copied()
    }

    /// The first name of an absolute path (`::X`) in `scope`: the top
    /// level as the code there sees it. Inside a library cog, the keys of
    /// its own manifest, then the top level without the application's
    /// names (its own declarations are `cog::X`); elsewhere, the top
    /// level. A cog's `::X` thus means what its own manifest says, whatever
    /// the application calls its cogs, and reaches a key or a standard
    /// class that a declaration of the cog hides (docs/10 §6).
    pub fn resolve_absolute(&self, scope: Option<ClassId>, name: &str) -> Option<Member> {
        let Some(root) = self.cog_root(scope) else {
            return self.top.get(name).copied();
        };
        if let Some(cog) = self.class(root).cog {
            if let Some(dep) = self.cogs[cog as usize].imports.get(name) {
                return Some(Member::Class(*dep));
            }
        }
        if self.app_names.contains(name) {
            return None;
        }
        self.top.get(name).copied()
    }

    /// The root module of the library cog that `scope` is in; `None` in
    /// the application, a script or the standard library.
    pub fn cog_root(&self, scope: Option<ClassId>) -> Option<ClassId> {
        let mut cur = scope;
        while let Some(cid) = cur {
            if self.class(cid).cog.is_some() {
                return Some(cid);
            }
            cur = self.class(cid).parent;
        }
        None
    }

    /// The first step of a `cog::` path (or `cog` itself, with no names):
    /// a member of the cog's root module, or of the top level in the
    /// application.
    pub fn resolve_cog_path_start(
        &self,
        scope: Option<ClassId>,
        path: &quarz_syntax::ast::ConstPath,
    ) -> Result<Member, String> {
        let root = self.cog_root(scope);
        let Some(first) = path.names.first() else {
            return match root {
                Some(root) => Ok(Member::Class(root)),
                None => Err(
                    "`cog` is the top level here (the application or a script), not a module"
                        .to_string(),
                ),
            };
        };
        // (A library's own declarations, then its manifest's keys.)
        let found = match root {
            Some(root) => self.class(root).members.get(first).copied().or_else(|| {
                let cog = self.class(root).cog?;
                self.cogs[cog as usize]
                    .imports
                    .get(first)
                    .map(|d| Member::Class(*d))
            }),
            None => self.top.get(first).copied(),
        };
        found.ok_or_else(|| match root {
            Some(root) => format!(
                "unknown constant `{first}` in `cog` ({})",
                self.class(root).name
            ),
            None => format!("unknown constant `{first}` at the top level"),
        })
    }

    /// A constant whose initializer is a constant path naming a class or
    /// module (`Short = Some::Long::Name`) stands for that class in
    /// constant paths and types; any other member is returned unchanged.
    /// For an instance type of a subclass of `Type` (`Meta::ClassDef[X]`,
    /// docs/14), the class it stands for: `X`. `None` for other types.
    pub fn class_object_instance(&self, t: &Type) -> Option<Type> {
        let Type::Class(id, args) = t else {
            return None;
        };
        // `Meta::ClassDef` is the one subclass of `Type` (the declarer
        // refuses others), so this is a comparison, not an ancestor walk.
        if *id != self.builtin.meta_classdef {
            return None;
        }
        self.ancestors(*id, args)
            .into_iter()
            .find(|(a, _)| *a == self.builtin.class_)
            .and_then(|(_, aa)| aa.first().cloned())
    }

    /// Whether a `static` statement in `file` may run a `static def`
    /// declared in `callee_file` (docs/14 §2): one of the standard
    /// library, of a cog the file's cog depends on (transitively), or, in
    /// a script, of a file loaded before it. `Err` names where the callee
    /// is.
    pub fn static_callee_allowed(&self, file: u32, callee_file: u32) -> Result<(), String> {
        let group = |f: u32| self.file_groups.get(&f).cloned();
        let callee = group(callee_file);
        if callee_file == 0 || matches!(callee, Some(UnitGroup::Std(_))) {
            return Ok(());
        }
        match (group(file), callee) {
            (Some(UnitGroup::Cog(a)), Some(UnitGroup::Cog(b))) if a == b => {
                Err("this cog".to_string())
            }
            (Some(UnitGroup::Cog(a)), Some(UnitGroup::Cog(b))) => {
                if self.cog_depends_on(a, b) {
                    Ok(())
                } else {
                    Err(format!(
                        "the cog `{}`, which this cog does not depend on",
                        self.cogs[b as usize].name
                    ))
                }
            }
            // The application depends on every cog of its movement.
            (Some(UnitGroup::App), Some(UnitGroup::Cog(_))) => Ok(()),
            (_, Some(UnitGroup::App)) if !self.cogs.is_empty() => {
                Err("the application".to_string())
            }
            // A script: the files it (transitively) requires are loaded
            // before it.
            _ => {
                if callee_file < file {
                    Ok(())
                } else {
                    Err("this file".to_string())
                }
            }
        }
    }

    /// Whether cog `a` imports cog `b`, directly or through its imports.
    fn cog_depends_on(&self, a: u32, b: u32) -> bool {
        let index_of_root = |root: ClassId| {
            self.cogs
                .iter()
                .position(|c| c.root == Some(root))
                .map(|i| i as u32)
        };
        let mut seen = vec![false; self.cogs.len()];
        let mut work = vec![a];
        while let Some(c) = work.pop() {
            if c as usize >= seen.len() || seen[c as usize] {
                continue;
            }
            seen[c as usize] = true;
            for root in self.cogs[c as usize].imports.values() {
                if let Some(i) = index_of_root(*root) {
                    if i == b {
                        return true;
                    }
                    work.push(i);
                }
            }
        }
        false
    }

    pub fn through_alias(&self, member: Member) -> Member {
        let mut member = member;
        // A chain of aliases is followed a few steps (a cycle is not
        // followed at all: its initializer fails when it runs).
        for _ in 0..16 {
            let Member::Const(id) = member else {
                return member;
            };
            match self.const_alias_step(id) {
                Some(next) => member = next,
                None => return member,
            }
        }
        member
    }

    fn const_alias_step(&self, id: ConstId) -> Option<Member> {
        let info = &self.consts[id as usize];
        let quarz_syntax::ast::ExprKind::Const(path) = &info.value.as_ref()?.kind else {
            return None;
        };
        let mut member = if path.cog {
            self.resolve_cog_path_start(info.owner, path).ok()?
        } else if path.absolute {
            self.resolve_absolute(info.owner, path.names.first()?)?
        } else {
            self.resolve_member(info.owner, path.names.first()?)?
        };
        for name in path.names.get(1..).unwrap_or_default() {
            let Member::Class(cid) = self.through_alias_shallow(member) else {
                return None;
            };
            member = self.class(cid).members.get(name).copied().or_else(|| {
                self.ancestor_ids(cid)
                    .into_iter()
                    .find_map(|anc| self.class(anc).members.get(name).copied())
            })?;
        }
        match member {
            Member::Class(_) => Some(member),
            Member::Const(c) if c != id => Some(member),
            _ => None,
        }
    }

    /// One step of `through_alias`, for the prefixes of an alias's own path.
    fn through_alias_shallow(&self, member: Member) -> Member {
        match member {
            Member::Const(id) => self.const_alias_step(id).unwrap_or(member),
            _ => member,
        }
    }

    /// The top-level class or module called `name`, if any.
    pub fn top_class(&self, name: &str) -> Option<ClassId> {
        match self.top.get(name).copied() {
            Some(Member::Class(id)) => Some(id),
            _ => None,
        }
    }

    pub fn member_in(&self, scope: Option<ClassId>, name: &str) -> Option<Member> {
        match scope {
            Some(cid) => self.class(cid).members.get(name).copied(),
            None => self.top.get(name).copied(),
        }
    }

    /// The `deinitialize` instances of `id` run when released: the first
    /// in its ancestors (a module's too).
    pub fn deinitializer(&self, id: ClassId) -> Option<MethodId> {
        let args: Vec<Type> = self
            .class(id)
            .type_params
            .iter()
            .map(|p| Type::Param(p.id))
            .collect();
        self.ancestors(id, &args).into_iter().find_map(|(a, _)| {
            self.class(a)
                .methods
                .get("deinitialize")
                .and_then(|ms| ms.iter().copied().find(|m| !self.method(*m).singleton))
        })
    }

    pub fn is_exception_class(&self, id: ClassId) -> bool {
        self.class_is_a(id, self.builtin.exception)
    }

    /// Whether every value of class `id` (its subclasses' included) is an
    /// object, one allocation of a header and fields: a `data` type, an
    /// enum or a variant, an exception, or a class all of whose
    /// ancestors are `Object`, modules, exceptions or classes declared
    /// outside the prelude. Not `Object` itself, nor a module or a
    /// built-in class (their values may be numbers, strings, arrays...).
    /// Compiled code relies on it to read such a value's allocation
    /// without a tag test (`RtClass::objects`).
    pub fn instances_are_objects(&self, id: ClassId) -> bool {
        let class = self.class(id);
        match class.kind {
            ClassKind::Data | ClassKind::Enum | ClassKind::Variant => true,
            ClassKind::Class => {
                id != self.builtin.object
                    && self.ancestors(id, &[]).iter().all(|(a, _)| {
                        let ac = self.class(*a);
                        *a == self.builtin.object
                            || ac.kind == ClassKind::Module
                            || self.is_exception_class(*a)
                            || (ac.file != 0 && ac.kind == ClassKind::Class)
                    })
            }
            ClassKind::Module | ClassKind::Main => false,
        }
    }

    /// Whether a value of type `t` is immutable for the `!` rule (docs/01,
    /// assignment): `x.foo!` rebinds `x` only then (a `foo!` of its own
    /// is called as any method). The built-in immutable types (docs/03
    /// §2), tuples, class objects, and a class whose values are objects (`data`, enums,
    /// exceptions, the program's classes) with no `var` field, judged on
    /// the class named (a subclass that adds one does not change it); a
    /// union when every member is, a type parameter when a bound is.
    /// Not Shareable's notion: a field may hold a mutable object here.
    pub fn bang_immutable(&self, t: &Type) -> bool {
        match t {
            Type::Class(id, _) => self.immutable_class(*id),
            // A class object (`Type[T]`, `T` a class or a parameter) holds no
            // state to change.
            Type::Tuple(_) | Type::ClassObject(..) | Type::TypeOf(_) => true,
            Type::Union(ms) => ms.iter().all(|m| self.bang_immutable(m)),
            Type::Param(p) => self.param_bounds(*p).iter().any(|b| self.bang_immutable(b)),
            _ => false,
        }
    }

    /// `bang_immutable` for the values of class `id`.
    fn immutable_class(&self, id: ClassId) -> bool {
        let b = &self.builtin;
        [
            b.nil, b.bool_, b.int, b.integer, b.float, b.string, b.symbol, b.array, b.hash, b.set,
            b.range, b.regexp, b.bytes, b.class_,
        ]
        .contains(&id)
            || self.instances_are_objects(id) && self.all_fields(id).iter().all(|(f, _)| !f.mutable)
    }

    /// Whether values of the type may be shared between tasks.
    pub fn is_shareable(&mut self, t: &Type) -> bool {
        match t {
            Type::Nothing | Type::Void => true,
            Type::Class(id, args) => {
                let id = *id;
                if !self.class_shareable(id) {
                    return false;
                }
                // A handle's type arguments are no values (docs/14 §5).
                if id == self.builtin.meta_field_ref || id == self.builtin.meta_method {
                    return true;
                }
                if args.is_empty() {
                    return true;
                }
                // The built-in containers (and a `Quoted`, as its
                // procedure type) hold what their arguments say.
                if self.is_value_class(id) || id == self.builtin.quoted {
                    return args.clone().iter().all(|a| self.is_shareable(a));
                }
                match self.class(id).kind {
                    // A `data` type or an enum holds its fields, with the
                    // arguments put in (docs/03 §5): `ModelOps[T]` whose
                    // only `T` is in a `shareable` procedure type is
                    // Shareable whatever `T` is.
                    ClassKind::Data | ClassKind::Enum | ClassKind::Variant => {
                        self.instance_shareable(id, args)
                    }
                    // A class that promises Shareable keeps the promise for
                    // every argument: its fields were checked for any
                    // (`shareable_violation`).
                    ClassKind::Class | ClassKind::Main => true,
                    // A module's includers need not have (a `data` type
                    // including `Shareable` too is Shareable by its
                    // fields): by its arguments.
                    ClassKind::Module => args.clone().iter().all(|a| self.is_shareable(a)),
                }
            }
            Type::ClassObject(_, _) | Type::TypeOf(_) => true,
            Type::Union(ms) | Type::Tuple(ms) => ms.clone().iter().all(|m| self.is_shareable(m)),
            Type::Proc(_, _, _, shareable, _) => *shareable,
            // `Self`: as shareable as the class it stands for.
            Type::Param(p) if *p == u32::MAX => match self.self_bound.clone() {
                Some(b) => self.is_shareable(&b),
                None => false,
            },
            // A parameter is Shareable when a bound makes every type it
            // admits Shareable: `Shareable` itself, a class or module that
            // promises it (its descendants and includers must keep the
            // promise: `check_shareable_promise`), or a `data` type or
            // enum, which nothing extends, that is Shareable; another
            // parameter, by its own bounds.
            Type::Param(p) => {
                if self.shareable_assumed.contains(p) {
                    return true;
                }
                if self.shareable_params.contains(p) {
                    return false;
                }
                let bounds = self.param_bounds(*p);
                self.shareable_params.push(*p);
                let r = bounds.iter().any(|b| match b {
                    Type::Class(id, args) => {
                        let id = *id;
                        if id == self.builtin.shareable {
                            return true;
                        }
                        // (A built-in value class, `Int`, has no
                        // subclasses either.)
                        let closed =
                            matches!(self.class(id).kind, ClassKind::Data | ClassKind::Enum)
                                || self.is_value_class(id);
                        if self.shareable_promise(id).is_some() || closed {
                            self.shareable_assumed.push(*p);
                            let r = self.is_shareable(&Type::Class(id, args.clone()));
                            self.shareable_assumed.pop();
                            r
                        } else {
                            false
                        }
                    }
                    // (A parameter met again, through cyclic bounds, is
                    // not taken as Shareable.)
                    // (Its own arm guards against a cycle.)
                    Type::Param(_) => self.is_shareable(b),
                    _ => false,
                });
                self.shareable_params.pop();
                r
            }
            Type::Var(_) => true,
        }
    }

    /// Whether the fields of `data` type, enum or variant `id` are
    /// Shareable with its type arguments `args` put in (an enum's, its
    /// variants'). An instance met again while it is judged (a recursive
    /// type) counts as Shareable: its fields decide.
    fn instance_shareable(&mut self, id: ClassId, args: &[Type]) -> bool {
        let key = Type::Class(id, args.to_vec());
        if let Some(&known) = self.shareable_instance_known.get(&key) {
            return known;
        }
        if let Some(at) = self.shareable_instances.iter().position(|t| *t == key) {
            // (An assumption, as `class_shareable`'s for a class it is
            // deciding: not kept if that one turns out not Shareable.)
            if !self.shareable_pending.is_empty() {
                self.shareable_tentative = true;
            }
            self.shareable_instance_floor = self.shareable_instance_floor.min(at);
            return true;
        }
        // The class again with other arguments (`data N[T] = (n:
        // N[Array[T]]?, v: T)`, whose instances grow): by its arguments,
        // which holds whenever they are Shareable, and ends.
        if self
            .shareable_instances
            .iter()
            .any(|t| matches!(t, Type::Class(c, _) if *c == id))
        {
            return args.to_vec().iter().all(|a| self.is_shareable(a));
        }
        let at = self.shareable_instances.len();
        // (A positive answer leaning on a class being decided, an
        // assumption, is not definite: `shareable_tentative`.)
        let tentative = std::mem::take(&mut self.shareable_tentative);
        self.shareable_instances.push(key.clone());
        let floor = std::mem::replace(&mut self.shareable_instance_floor, usize::MAX);
        let provisional_from = self.shareable_provisional.len();
        let class = self.class(id);
        let mut by_args = self.class_subst(id, args);
        if let Some(e) = class.variant_of {
            by_args.extend(self.class_subst(e, args));
        }
        let variants = if class.kind == ClassKind::Enum {
            class.variants.clone()
        } else {
            Vec::new()
        };
        let mut ok = true;
        for (f, subst) in self.all_fields(id) {
            let ty = f.ty.subst(&subst).subst(&by_args);
            if !self.is_shareable(&ty) {
                ok = false;
                break;
            }
        }
        if ok {
            for v in variants {
                if !self.instance_shareable(v, args) {
                    ok = false;
                    break;
                }
            }
        }
        self.shareable_instances.pop();
        // What was decided Shareable meanwhile may have leaned on this
        // instance: not, if it is not (as `class_shareable` does).
        if !ok {
            self.shareable_provisional.truncate(provisional_from);
        }
        // Definite unless it leaned on an instance further out: a negative
        // always is (assumptions only add positives).
        let leaned = self.shareable_instance_floor;
        let assumed = self.shareable_tentative;
        self.shareable_tentative = tentative || assumed;
        // (Not for arguments mentioning a type parameter, `Self`
        // included: the answer depends on where it is asked, the
        // parameter's bounds and what is assumed of it.)
        if (!ok || (leaned >= at && !assumed)) && !args.iter().any(|a| a.mentions_any_param()) {
            self.shareable_instance_known.insert(key, ok);
        }
        self.shareable_instance_floor = floor.min(leaned);
        ok
    }

    /// Whether no class can inherit from `id` (a `data` type, an enum
    /// variant, a built-in value class): there `Self` is the class itself
    /// (docs/01 §3). (Not an enum: its variants are its subclasses.)
    pub fn has_no_subclass(&self, id: ClassId) -> bool {
        matches!(self.class(id).kind, ClassKind::Data | ClassKind::Variant)
            || self.is_value_class(id)
            || id == self.builtin.integer
    }

    /// Whether class `id` is never made by a plain construct (#535): a
    /// class whose values the runtime builds, or that declares a native
    /// `self.new`, or a subclass of one (`TCPSocket < IO`, a user's
    /// `class MyR < Random`: their objects need the runtime's state too),
    /// is not (a built-in value, `is_value_class`; a class
    /// object; `Proc`, `Integer`; the prelude's `IO`, `File`,
    /// `Channel::Selector`, `Process::Child`; and any class with a native
    /// `self.new`: a module's `new` reaching `Array` built "an Array that is
    /// not one", reaching `Random` a `Random` without its state, the
    /// probes behind that arm). The one rule the checker's refusal of
    /// `new`, the inherited-constructor rule and the runtime's guard
    /// (`RtClass::built_by_runtime`) read; written `new` on such a class
    /// resolves to its own `self.new` where it has one.
    pub fn built_by_runtime(&self, id: ClassId) -> bool {
        self.superclass_chain(id)
            .into_iter()
            .any(|c| self.built_by_runtime_itself(c))
    }

    /// `built_by_runtime` for class `id` itself, not its superclasses.
    fn built_by_runtime_itself(&self, id: ClassId) -> bool {
        let b = &self.builtin;
        let class = self.class(id);
        let runtime_made = [b.proc_, b.integer].contains(&id)
            || (class.file == 0
                && ["IO", "File", "Channel::Selector", "Process::Child"]
                    .contains(&class.name.as_str()));
        // (And a class whose `self.new` is native: its values are the
        // runtime's, `Array`, `Random`, ...)
        let native_new = class.singleton_methods.get("new").is_some_and(|ids| {
            ids.iter().any(|&m| {
                let mi = self.method(m);
                mi.owner == id && mi.is_native
            })
        });
        self.is_value_class(id) || self.class_is_a(id, b.class_) || runtime_made || native_new
    }

    /// The built-in classes whose values are the runtime's own (no user
    /// fields, no `deinitialize`): what they hold is their type
    /// arguments.
    pub fn is_value_class(&self, id: ClassId) -> bool {
        let b = &self.builtin;
        [
            b.nil,
            b.bool_,
            b.int,
            b.float,
            b.string,
            b.symbol,
            b.array,
            b.hash,
            b.set,
            b.range,
            b.regexp,
            b.class_,
            b.task,
            b.channel,
            b.atom,
            b.scope,
            b.duration,
            b.bytes,
            b.time,
            b.array_builder,
            b.bytes_builder,
            b.hash_builder,
            b.string_builder,
            b.set_builder,
            b.match_data,
            b.bytes_match_data,
        ]
        .contains(&id)
    }

    /// Whether releasing a value of the type may be observed: it may hold
    /// an IO handle (closed when released) or an object whose class
    /// defines `deinitialize`. A local variable of such a type lives to
    /// the end of its scope instead of its last use. Every class and
    /// module type may (a subclass may define `deinitialize` or hold a
    /// socket; subclasses are not looked at, as for Shareable), and so
    /// may a procedure (what it captured), an enumerator and a type
    /// parameter; the built-in value classes hold what their type
    /// arguments say, and a `data` type or enum what its fields do.
    pub fn release_observable(&mut self, t: &Type) -> bool {
        match t {
            Type::Nothing
            | Type::Void
            | Type::ClassObject(_, _)
            | Type::TypeOf(_)
            | Type::Var(_) => false,
            Type::Class(id, args) => {
                let id = *id;
                let own = if self.is_value_class(id) {
                    false
                } else {
                    match self.class(id).kind {
                        ClassKind::Data | ClassKind::Enum | ClassKind::Variant => {
                            self.data_observable(id)
                        }
                        ClassKind::Class | ClassKind::Module | ClassKind::Main => true,
                    }
                };
                own || args.clone().iter().any(|a| self.release_observable(a))
            }
            Type::Union(ms) | Type::Tuple(ms) => {
                ms.clone().iter().any(|m| self.release_observable(m))
            }
            Type::Proc(..) | Type::Param(_) => true,
        }
    }

    /// Whether the fields of a `data` type, enum (any variant) or variant
    /// may hold something released observably, its own type parameters
    /// aside (`release_observable` looks at the arguments).
    fn data_observable(&mut self, id: ClassId) -> bool {
        if let Some(o) = self.class(id).observable {
            return o;
        }
        // A type it holds holds it again: not on that account.
        if self.observable_pending.contains(&id) {
            self.observable_tentative = true;
            return false;
        }
        self.observable_pending.push(id);
        let class = self.class(id);
        let enum_params = class.variant_of.map(|e| self.class(e).type_params.clone());
        let erase: HashMap<TypeParamId, Type> = class
            .type_params
            .iter()
            .chain(enum_params.iter().flatten())
            .map(|p| (p.id, Type::Nothing))
            .collect();
        let mut result = false;
        for (f, subst) in self.all_fields(id) {
            let ty = f.ty.subst(&subst).subst(&erase);
            if self.release_observable(&ty) {
                result = true;
                break;
            }
        }
        if !result && self.class(id).kind == ClassKind::Enum {
            for v in self.class(id).variants.clone() {
                if self.data_observable(v) {
                    result = true;
                    break;
                }
            }
        }
        self.observable_pending.pop();
        // A negative answer that assumed an enclosing type's is kept only
        // once the outermost is done.
        if result || self.observable_pending.is_empty() || !self.observable_tentative {
            self.class_mut(id).observable = Some(result);
        }
        if self.observable_pending.is_empty() {
            self.observable_tentative = false;
        }
        result
    }

    /// Whether values of class `id` (with any Shareable type arguments)
    /// may be shared. A `data` type, enum or variant is when its fields
    /// allow it (an enum: all its variants); a class or module only when
    /// it promises so with `include Shareable` (itself or an ancestor),
    /// which `declare` holds every class to where it is defined, so that
    /// a value of a Shareable type is Shareable whatever subclass it is
    /// of. (Deriving it from the fields of a class would make it depend
    /// on subclasses defined anywhere in the program.)
    fn class_shareable(&mut self, id: ClassId) -> bool {
        if let Some(s) = self.class(id).shareable {
            return s;
        }
        // A `Quoted[P]` is as shareable as `P` (docs/14 §6): a block given
        // for a `shareable` procedure type captures shareable values only,
        // which its `captures` (an `Array[Object]`) then hold.
        if id == self.builtin.quoted {
            return true;
        }
        // A type it holds holds it again: Shareable on that account, but a
        // positive answer that assumed an enclosing type's is kept only
        // once the outermost is done (as `data_observable`'s negative
        // ones): `data A = (b: B?, c: Counter)` with `data B = (a: A?)`
        // must not leave `B` Shareable.
        if self.shareable_pending.contains(&id) {
            self.shareable_tentative = true;
            return true;
        }
        // Decided Shareable already in this outermost run (each class once
        // per run: without this, mutually recursive types take time
        // exponential in their number).
        if self.shareable_provisional.contains(&id) {
            // (Itself an assumption until the outermost is decided: what
            // leans on it is not definite either, `instance_shareable`.)
            self.shareable_tentative = true;
            return true;
        }
        self.shareable_pending.push(id);
        let provisional_from = self.shareable_provisional.len();
        let result = match self.class(id).kind {
            ClassKind::Module => self.shareable_promise(id).is_some(),
            ClassKind::Class => {
                self.shareable_promise(id).is_some() && self.shareable_violation(id).is_none()
            }
            ClassKind::Data | ClassKind::Enum | ClassKind::Variant | ClassKind::Main => {
                self.shareable_violation(id).is_none()
            }
        };
        self.shareable_pending.pop();
        // What was decided Shareable while this one was being decided may
        // have leaned on it: not, if it is not (decided again when next
        // asked, with this answer known). A caller may drop a negative
        // answer (a parameter's other bound), so the outermost's answer
        // alone does not tell.
        if !result {
            self.shareable_provisional.truncate(provisional_from);
        }
        if !result || self.shareable_pending.is_empty() || !self.shareable_tentative {
            self.class_mut(id).shareable = Some(result);
        } else {
            self.shareable_provisional.push(id);
        }
        if self.shareable_pending.is_empty() {
            // The provisional positives hold if the outermost does: a type
            // it holds that is not Shareable makes it not Shareable either.
            for c in std::mem::take(&mut self.shareable_provisional) {
                if result {
                    self.class_mut(c).shareable = Some(true);
                }
            }
            self.shareable_tentative = false;
        }
        result
    }

    /// The class or module whose `include Shareable` class `id` inherits
    /// (`id` itself when it includes it directly), if any: `id` and all
    /// its descendants must then be Shareable.
    pub fn shareable_promise(&self, id: ClassId) -> Option<ClassId> {
        let marker = self.builtin.shareable;
        if id == marker {
            return Some(marker);
        }
        let ids: Vec<ClassId> = self
            .ancestors_with(id, &[], &[])
            .into_iter()
            .map(|(c, _)| c)
            .collect();
        if !ids.contains(&marker) {
            return None;
        }
        ids.into_iter().find(|&a| {
            self.class(a)
                .includes
                .iter()
                .any(|i| matches!(i, Type::Class(c, _) if *c == marker))
        })
    }

    /// Why the values of class `id` could not be shared, judging by what
    /// it holds (`None` when they could): its own type parameters count
    /// as Shareable, since a use of the class checks its type arguments.
    pub fn shareable_violation(&mut self, id: ClassId) -> Option<String> {
        let ids: Vec<ClassId> = self
            .ancestors_with(id, &[], &[])
            .into_iter()
            .map(|(c, _)| c)
            .collect();
        let marked = ids.iter().any(|&a| {
            self.class(a).kind == ClassKind::Module && self.class(a).name == "Unshareable"
        });
        if marked {
            return Some("it is Unshareable".to_string());
        }
        // A variant's fields may also use its enum's parameters.
        let class = self.class(id);
        let enum_params = class.variant_of.map(|e| self.class(e).type_params.clone());
        let erase: HashMap<TypeParamId, Type> = class
            .type_params
            .iter()
            .chain(enum_params.iter().flatten())
            .map(|p| (p.id, Type::Nothing))
            .collect();
        // A class that promises Shareable keeps the promise for every
        // instance, whatever its arguments: a parameter in a field's type
        // must be Shareable by its bounds (docs/03). (A `data` type or an
        // enum is Shareable by its arguments instead, as a collection.)
        // (So does a `data` type or an enum that takes the promise from a
        // module: the module's methods see its values as the module's
        // type, which carries no arguments.)
        let marker = self.builtin.shareable;
        let promised = match self.shareable_promise(id) {
            Some(via) => {
                class.kind == ClassKind::Class
                    || (via != marker && self.class(via).kind == ClassKind::Module)
            }
            None => false,
        };
        let own: Vec<TypeParamId> = class
            .type_params
            .iter()
            .chain(enum_params.iter().flatten())
            .map(|p| p.id)
            .collect();
        for (f, subst) in self.all_fields(id) {
            if f.mutable {
                return Some(format!("its field `@{}` is `var`", f.name));
            }
            let ty = f.ty.subst(&subst);
            if promised {
                for &p in &own {
                    // (Only where the argument can make the field's value
                    // non-Shareable: not in a `Type[T]` or a shareable
                    // procedure's type.)
                    let unshareable = Type::proc_(None, Vec::new(), Box::new(Type::Nothing), false);
                    let witness: HashMap<TypeParamId, Type> =
                        [(p, unshareable)].into_iter().collect();
                    if ty.mentions_param(p)
                        && !self.is_shareable(&ty.subst(&witness).subst(&erase))
                        && !self.is_shareable(&Type::Param(p))
                    {
                        let name = self.type_param_name(p);
                        return Some(format!(
                            "its parameter `{name}` may be a non-Shareable type (its field `@{}` holds one): bound it `{name} <: Shareable`",
                            f.name
                        ));
                    }
                }
            }
            let ty = ty.subst(&erase);
            if !self.is_shareable(&ty) {
                return Some(format!(
                    "its field `@{}` has the non-shareable type {}",
                    f.name,
                    self.type_name(&ty)
                ));
            }
        }
        if self.class(id).kind == ClassKind::Enum {
            for v in self.class(id).variants.clone() {
                if let Some(why) = self.shareable_violation(v) {
                    return Some(format!(
                        "its variant `{}`: {why}",
                        self.class(v).short_name()
                    ));
                }
            }
        }
        None
    }
}
