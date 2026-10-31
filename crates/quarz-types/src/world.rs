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
    pub extends: Vec<Type>,
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

/// A method of a module a class includes over one of its superclass's
/// (`World::include_overrides_of`).
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
    pub classes: Vec<ClassInfo>,
    pub methods: Vec<MethodInfo>,
    pub consts: Vec<ConstInfo>,
    pub aliases: Vec<TypeAliasInfo>,
    pub extensions: Vec<ExtensionInfo>,
    pub top: HashMap<String, Member>,
    pub builtin: Builtin,
    /// Extensions activated by `using` in the current lexical scope.
    pub active_extensions: Vec<ExtensionId>,
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
            Type::Proc(rc, ps, r, sh) => Type::Proc(
                rc.as_ref().map(|t| Box::new(self.erase_narrowed(t))),
                ps.iter().map(|p| self.erase_narrowed(p)).collect(),
                Box::new(self.erase_narrowed(r)),
                *sh,
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
            extends: Vec::new(),
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
            Type::Proc(rc, ps, r, sh) => Type::Proc(
                rc.as_ref().map(|t| Box::new(self.devoid(t))),
                ps.iter().map(|p| self.devoid(p)).collect(),
                Box::new(self.devoid(r)),
                *sh,
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
            Type::Proc(rc, ps, r, sh) => format!(
                "{}{}({}) -> {}",
                if *sh { "shareable " } else { "" },
                rc.as_ref()
                    .map(|t| format!("{}.", self.type_name(t)))
                    .unwrap_or_default(),
                ps.iter()
                    .map(|t| self.type_name(t))
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

    /// The method resolution order: the class itself, its included modules
    /// (last included first), then the superclass chain, each with the type
    /// arguments expressed in terms of the given `args`. Retroactive
    /// conformance from active extensions is included.
    pub fn ancestors(&self, id: ClassId, args: &[Type]) -> Vec<(ClassId, Vec<Type>)> {
        let exts = self.conformance_extensions();
        if !self.ancestors_memo.on {
            return self.ancestors_with(id, args, &exts);
        }
        let key = (id, args.to_vec(), exts);
        if let Some(found) = self.ancestors_memo.map.borrow().get(&key) {
            return found.as_ref().clone();
        }
        let found = self.ancestors_with(id, args, &key.2);
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
            if ext.target != id {
                continue;
            }
            let esubst = self.extension_subst(ext, args);
            for inc in &ext.includes {
                if let Type::Class(mid, margs) = inc.subst(&esubst) {
                    if has(&out, mid) {
                        continue;
                    }
                    out.push((mid, margs.clone()));
                    for m in self.modules_of(mid, &margs, exts, cache) {
                        if !has(&out, m.0) {
                            out.push(m);
                        }
                    }
                }
            }
        }
        cache.insert(key, out.clone());
        out
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
    /// (`Interp::find_override`).
    pub fn include_overrides_of(&self, id: ClassId) -> Vec<IncludeOverride> {
        let mut out: Vec<IncludeOverride> = Vec::new();
        let c = self.class(id);
        if c.kind == ClassKind::Module {
            return out;
        }
        let Some(Type::Class(sup, _)) = &c.superclass else {
            return out;
        };
        let inherited = self.ancestor_ids(*sup);
        // (The names the superclass chain has methods of, once: a module's
        // method of another name overrides nothing.)
        let names: rustc_hash::FxHashSet<&str> = inherited
            .iter()
            .flat_map(|s| self.class(*s).methods.keys().map(|n| n.as_str()))
            .collect();
        let own: Vec<Type> = c.type_params.iter().map(|p| Type::Param(p.id)).collect();
        let ancestors = self.ancestors(c.id, &own);
        for (x, xargs) in &ancestors {
            if self.class(*x).kind != ClassKind::Module || inherited.contains(x) {
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
            let x_own = self.ancestor_ids(*x);
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
                for (s, sargs) in &ancestors {
                    if !inherited.contains(s) || x_own.contains(s) {
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
                            && self.takes_calls_of(m, msubst, om, &ssubst)
                            && !out.iter().any(|e| e.overridden == o)
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
        out
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
    /// Kernel` adds is a method), or a top-level `def`, which runs with
    /// its file's top-level object (docs/01 §1).
    pub fn takes_no_self(&self, mid: MethodId) -> bool {
        let m = self.method(mid);
        (m.is_native && m.owner == self.builtin.kernel)
            || self.class(m.owner).kind == ClassKind::Main
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

    pub fn active_extension_ids(&self) -> Vec<ExtensionId> {
        let mut ids: Vec<ExtensionId> = self
            .extensions
            .iter()
            .filter(|e| e.always_active)
            .map(|e| e.id)
            .collect();
        for id in &self.active_extensions {
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
            && aargs
                .iter()
                .all(|t| self.is_subtype(t, &Type::class(self.builtin.shareable)))
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
        let shareable = Type::class(self.builtin.shareable);
        aargs.iter().all(|t| {
            if t.has_vars() {
                !self.refuse_undecided()
            } else {
                self.is_subtype(t, &shareable)
            }
        })
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
            (Type::Proc(ra, ps, r, sa), Type::Proc(rb, qs, s, sb)) => {
                // A shareable procedure is a procedure; not the reverse.
                if *sb && !*sa {
                    return false;
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

    fn param_bounds(&self, id: TypeParamId) -> Vec<Type> {
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
                // on a `Type[X]`.
                if let Some(instance) = self.class_object_instance(recv) {
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
                // Each superclass's type arguments, for its extensions'.
                let ancs = if exts.is_empty() {
                    Vec::new()
                } else {
                    self.ancestors(*id, args)
                };
                for cid in self.superclass_chain(*id) {
                    let class = self.class(cid);
                    let subst = if cid == *id {
                        self.class_subst(cid, args)
                    } else {
                        HashMap::default()
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
                    // (The last module extended first, docs/01 §6.)
                    for ext in class.extends.iter().rev() {
                        if let Type::Class(mid, margs) = ext {
                            let msubst = self.class_subst(*mid, margs);
                            if let Some(ids) = self.class(*mid).methods.get(name) {
                                for m in ids {
                                    out.push((*m, msubst.clone()));
                                }
                            }
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
                // For `T <: Bound` with a class bound, the bound's class
                // methods (`Self` being `T`), before `Type[T]`'s own, as
                // for a class object and at run time; a module's singleton
                // methods are not inherited by the classes that include it.
                if let Type::Param(p) = &**t {
                    for b in self.param_bounds(*p) {
                        let Type::Class(bid, bargs) = &b else {
                            continue;
                        };
                        if self.class(*bid).kind == ClassKind::Module {
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
                for b in self.param_bounds(*p) {
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
                    return out;
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
        let found = match root {
            Some(root) => self.class(root).members.get(first).copied(),
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
            self.top.get(path.names.first()?).copied()?
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

    /// Whether values of the type may be shared between tasks.
    pub fn is_shareable(&mut self, t: &Type) -> bool {
        match t {
            Type::Nothing | Type::Void => true,
            Type::Class(id, args) => {
                let id = *id;
                if !self.class_shareable(id) {
                    return false;
                }
                // Generic containers are shareable when their arguments are.
                args.clone().iter().all(|a| self.is_shareable(a))
            }
            Type::ClassObject(_, _) | Type::TypeOf(_) => true,
            Type::Union(ms) | Type::Tuple(ms) => ms.clone().iter().all(|m| self.is_shareable(m)),
            Type::Proc(_, _, _, shareable) => *shareable,
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
                    let unshareable = Type::Proc(None, Vec::new(), Box::new(Type::Nothing), false);
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
