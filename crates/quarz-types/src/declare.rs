//! Declaration collection (phase 1) and header resolution (phase 2).
//!
//! Phase 1 walks the programs and registers every class, module, data,
//! enum, extension, constant and type alias by name, so that phase 2 can
//! resolve superclasses, includes, field types and method signatures in any
//! order.

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::rc::Rc;

use quarz_syntax::ast::*;
use quarz_syntax::{Diagnostic, Span};

use crate::types::*;
use crate::world::*;

/// Reserved type parameter id standing for the receiver's type in method
/// signatures (`-> Self`).
pub const SELF_PARAM: TypeParamId = u32::MAX;

/// A type-expression resolution scope.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct TypeScope {
    /// Namespace for constant lookup.
    pub namespace: Option<ClassId>,
    /// Type parameters in scope, innermost last.
    pub params: Vec<(String, TypeParamId)>,
    /// What `self` resolves to (`None` → the `SELF_PARAM` marker).
    pub self_type: Option<Type>,
}

impl TypeScope {
    pub fn with_params(&self, params: &[TypeParamInfo]) -> TypeScope {
        let mut scope = self.clone();
        for p in params {
            scope.params.push((p.name.clone(), p.id));
        }
        scope
    }
}

/// Work items remembered from phase 1 for phase 2.
struct PendingClass<'ast> {
    id: ClassId,
    body: &'ast [Expr],
    def: PendingDef<'ast>,
}

enum PendingDef<'ast> {
    Class(&'ast ClassDef),
    Module(&'ast ModuleDef),
    Data(&'ast DataDef),
    Enum(&'ast EnumDef),
    Variant(&'ast Variant),
    Main,
    /// A library cog's file, contributing its `def self.` methods to the
    /// cog's root module (the file index, for diagnostics).
    CogRoot(u32),
}

struct PendingExtension<'ast> {
    id: ExtensionId,
    def: &'ast ExtensionDef,
    namespace: Option<ClassId>,
    file: u32,
}

impl Default for Declarer<'_> {
    fn default() -> Self {
        Declarer::new()
    }
}

pub struct Declarer<'ast> {
    pub world: World,
    /// Diagnostics tagged with the file index they refer to.
    pub diagnostics: Vec<(u32, Diagnostic)>,
    file: u32,
    pending: Vec<PendingClass<'ast>>,
    pending_ext: Vec<PendingExtension<'ast>>,
    /// The user's compilation units (files), in load order.
    pub units: Vec<UnitDecl<'ast>>,
    class_usings: HashMap<ClassId, Vec<(&'ast ConstPath, u32)>>,
    builtins_resolved: bool,
    /// The modules extensions include, where (extension, module, span,
    /// file), checked once fields are known (`check_shareable_extensions`).
    ext_includes: Vec<(ExtensionId, Type, Span, u32)>,
    /// While collecting a file of the application of a movement: its
    /// top-level names are hidden from library cogs.
    in_app: bool,
    /// `class A::B` / `module A::B` (at a file's top level): collected once
    /// every other declaration has been (see `collect_deferred`), as
    /// declarations are hoisted: `A` may be declared later, in this file or
    /// another.
    deferred: Vec<Deferred<'ast>>,
    /// The deferred declaration being collected now (not deferred again).
    collecting: Option<*const Expr>,
    /// Collecting the deferred declarations for the last time: an unknown
    /// namespace is now an error.
    final_pass: bool,
}

/// A qualified declaration waiting for its namespace (`Declarer::deferred`).
struct Deferred<'ast> {
    expr: &'ast Expr,
    namespace: Option<ClassId>,
    prelude: bool,
    file: u32,
    in_app: bool,
}

/// The name a deferred declaration declares.
fn deferred_path(expr: &Expr) -> &ConstPath {
    match &expr.kind {
        ExprKind::ClassDef(def) => &def.name,
        ExprKind::ModuleDef(def) => &def.name,
        _ => unreachable!("only classes and modules are deferred"),
    }
}

/// Whether a call could be answered by either of two methods with these
/// parameters: their numbers of positional arguments meet (an override, at
/// run time, is chosen by name and number of arguments).
/// Whether `t` mentions `Self` (the `SELF_PARAM` marker), whose meaning
/// an override changes.
fn contains_self(t: &Type) -> bool {
    match t {
        Type::Param(p) => *p == SELF_PARAM,
        Type::Class(_, args)
        | Type::ClassObject(_, args)
        | Type::Tuple(args)
        | Type::Union(args) => args.iter().any(contains_self),
        Type::TypeOf(t) => contains_self(t),
        Type::Proc(recv, ps, r, _) => {
            recv.as_deref().is_some_and(contains_self)
                || ps.iter().any(contains_self)
                || contains_self(r)
        }
        _ => false,
    }
}

fn arities_meet(a: &[ParamInfo], b: &[ParamInfo]) -> bool {
    let range = |ps: &[ParamInfo]| {
        let mut min = 0;
        let mut max = 0usize;
        for p in ps {
            match p.kind {
                ParamKind::Positional if p.default.is_none() => {
                    min += 1;
                    max = max.saturating_add(1);
                }
                ParamKind::Positional => max = max.saturating_add(1),
                ParamKind::Rest => max = usize::MAX,
                _ => {}
            }
        }
        (min, max)
    };
    let ((amin, amax), (bmin, bmax)) = (range(a), range(b));
    amin <= bmax && bmin <= amax
}

/// A cog of the movement, as the declarer needs it.
#[derive(Clone, Debug)]
pub struct CogDecl {
    pub name: String,
    /// The module its declarations live in; `None` for the application.
    pub module: Option<String>,
    /// Dependencies: the key of the manifest and the index of the cog.
    pub imports: Vec<(String, u32)>,
}

/// A file's top-level: its pseudo-class for top-level methods, its
/// statements and its `using`s.
pub struct UnitDecl<'ast> {
    pub file: u32,
    pub main: ClassId,
    pub body: Vec<&'ast Expr>,
    /// The `using`s at the file's top level, with their positions.
    pub usings: Vec<(&'ast ConstPath, u32)>,
}

impl<'ast> Declarer<'ast> {
    pub fn new() -> Declarer<'ast> {
        Declarer::with_world(World::new())
    }

    /// A declarer adding to an existing world (REPL inputs). Builtins are
    /// looked up again only when the world is empty.
    pub fn with_world(mut world: World) -> Declarer<'ast> {
        world.freeze_ancestors(false);
        let builtins_resolved = !world.classes.is_empty();
        Declarer {
            builtins_resolved,
            world,
            diagnostics: Vec::new(),
            file: 0,
            pending: Vec::new(),
            pending_ext: Vec::new(),
            units: Vec::new(),
            class_usings: HashMap::default(),
            ext_includes: Vec::new(),
            in_app: false,
            deferred: Vec::new(),
            collecting: None,
            final_pass: false,
        }
    }

    /// Create the root module of every library cog and bind each cog's
    /// dependency keys: in a library's scope (`CogInfo::imports`), or at
    /// the top level for the application. Called after the prelude, before
    /// the cogs' files.
    /// A key that is also a name of the prelude or the standard library
    /// is an error, reported against `file` (the application's main file).
    pub fn declare_cogs(&mut self, cogs: &[CogDecl], file: u32) {
        let saved = self.file;
        self.file = file;
        for cog in cogs {
            for (key, _) in &cog.imports {
                let std = crate::load::std_exports()
                    .iter()
                    .any(|(_, names)| names.iter().any(|n| n == key));
                if std || self.world.top.contains_key(key) {
                    self.error(
                        format!(
                            "the dependency `{key}` of cog `{}` has the name of a built-in or standard library constant; give it another key in Cog.toml",
                            cog.name
                        ),
                        Span::empty(0),
                    );
                }
            }
        }
        self.file = saved;
        for (i, cog) in cogs.iter().enumerate() {
            let root = cog.module.as_ref().map(|module| {
                let mut info =
                    World::blank_class(module.clone(), ClassKind::Module, None, Span::empty(0));
                info.cog = Some(i as u32);
                info.superclass = None;
                self.world.add_class(info)
            });
            self.world.cogs.push(CogInfo {
                name: cog.name.clone(),
                root,
                imports: HashMap::default(),
            });
        }
        for (i, cog) in cogs.iter().enumerate() {
            for (key, dep) in &cog.imports {
                let Some(root) = self.world.cogs[*dep as usize].root else {
                    continue;
                };
                if cog.module.is_some() {
                    self.world.cogs[i].imports.insert(key.clone(), root);
                } else {
                    self.world.app_names.insert(key.clone());
                    self.world.top.insert(key.clone(), Member::Class(root));
                }
            }
        }
    }

    /// Register the declarations of a file of cog `cog` (an index into
    /// the cogs given to `declare_cogs`). A library's files are the body of
    /// its root module and hold declarations only; the application's are at
    /// the top level, and only `statements` allows statements in one.
    pub fn collect_cog_unit(
        &mut self,
        program: &'ast Program,
        file: u32,
        cog: u32,
        statements: bool,
    ) {
        // (An application's file goes through `collect_unit`, which
        // takes its docs.)
        let Some(root) = self.world.cogs[cog as usize].root else {
            self.in_app = true;
            self.collect_unit(program, file);
            self.in_app = false;
            if !statements {
                let body = std::mem::take(&mut self.units.last_mut().unwrap().body);
                for expr in body {
                    self.error(
                        "statements of the application go in src/main.qz; its other files hold declarations only",
                        expr.span,
                    );
                }
            }
            return;
        };
        self.world.add_docs(&program.docs);
        self.file = file;
        self.world.file_groups.insert(file, UnitGroup::Cog(cog));
        let mut main = World::blank_class(
            "main".to_string(),
            ClassKind::Main,
            Some(root),
            program.span,
        );
        main.file = file;
        let id = self.world.add_class(main);
        self.pending.push(PendingClass {
            id,
            body: &program.body,
            def: PendingDef::Main,
        });
        self.pending.push(PendingClass {
            id: root,
            body: &program.body,
            def: PendingDef::CogRoot(file),
        });
        self.units.push(UnitDecl {
            file,
            main: id,
            body: Vec::new(),
            usings: Vec::new(),
        });
        for expr in &program.body {
            match &expr.kind {
                // A file's `using`s and requires are its own.
                ExprKind::Using(path) => self
                    .units
                    .last_mut()
                    .unwrap()
                    .usings
                    .push((path, expr.span.start)),
                ExprKind::Require { .. } => {}
                _ => {
                    if !self.collect_item(expr, Some(root), false) {
                        self.error(
                            "a cog's files hold declarations only (classes, modules, methods, constants); statements belong to the application's src/main.qz",
                            expr.span,
                        );
                    }
                }
            }
        }
    }

    fn error(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics
            .push((self.file, Diagnostic::error(message, span)));
    }

    // ----- phase 1 ---------------------------------------------------------

    /// Register the declarations of the prelude.
    pub fn collect_prelude(&mut self, program: &'ast Program) {
        self.file = 0;
        self.world.add_docs(&program.docs);
        for expr in &program.body {
            self.collect_item(expr, None, true);
        }
    }

    /// Register the declarations of a user file (file index `file`, 1 or
    /// more); its other statements become the unit's body.
    pub fn collect_unit(&mut self, program: &'ast Program, file: u32) {
        self.file = file;
        self.world.add_docs(&program.docs);
        let group = if self.world.std_files.contains(&file) {
            UnitGroup::Std(file)
        } else {
            UnitGroup::App
        };
        self.world.file_groups.insert(file, group);
        let mut main = World::blank_class("main".to_string(), ClassKind::Main, None, program.span);
        main.file = file;
        let id = self.world.add_class(main);
        self.pending.push(PendingClass {
            id,
            body: &program.body,
            def: PendingDef::Main,
        });
        self.units.push(UnitDecl {
            file,
            main: id,
            body: Vec::new(),
            usings: Vec::new(),
        });
        for expr in &program.body {
            if !self.collect_item(expr, None, false) {
                self.units.last_mut().unwrap().body.push(expr);
            }
        }
    }

    /// Register the declarations of further input for an existing unit
    /// (REPL): new methods join its main class, other statements become the
    /// new body.
    pub fn collect_into_unit(&mut self, program: &'ast Program, file: u32, main: ClassId) {
        self.file = file;
        self.world.add_docs(&program.docs);
        self.world.file_groups.insert(file, UnitGroup::App);
        self.pending.push(PendingClass {
            id: main,
            body: &program.body,
            def: PendingDef::Main,
        });
        self.units.push(UnitDecl {
            file,
            main,
            body: Vec::new(),
            usings: Vec::new(),
        });
        for expr in &program.body {
            if !self.collect_item(expr, None, false) {
                self.units.last_mut().unwrap().body.push(expr);
            }
        }
    }

    /// Returns whether the expression was a declaration.
    fn collect_item(
        &mut self,
        expr: &'ast Expr,
        namespace: Option<ClassId>,
        prelude: bool,
    ) -> bool {
        // A qualified name goes at a file's top level, and waits for the
        // other declarations (hoisting).
        let qualified = match &expr.kind {
            ExprKind::ClassDef(def) => Some(&def.name),
            ExprKind::ModuleDef(def) => Some(&def.name),
            _ => None,
        };
        if let Some(path) = qualified {
            if (path.names.len() > 1 || path.absolute || path.cog)
                && !(namespace.is_none() || self.world.cogs.iter().any(|c| c.root == namespace))
            {
                self.error(
                    format!(
                        "`{path}` is declared inside another declaration: a qualified name is declared at a file's top level"
                    ),
                    expr.span,
                );
                return true;
            }
            if path.names.len() > 1
                && !self.final_pass
                && self.collecting != Some(expr as *const Expr)
            {
                self.deferred.push(Deferred {
                    expr,
                    namespace,
                    prelude,
                    file: self.file,
                    in_app: self.in_app,
                });
                return true;
            }
        }
        match &expr.kind {
            ExprKind::ClassDef(def) => {
                let Some(id) =
                    self.declare_named(&def.name, ClassKind::Class, namespace, expr.span)
                else {
                    return true;
                };
                self.world.class_mut(id).is_abstract = def.is_abstract;
                self.collect_body(id, &def.body, prelude);
                self.pending.push(PendingClass {
                    id,
                    body: &def.body,
                    def: PendingDef::Class(def),
                });
            }
            ExprKind::ModuleDef(def) => {
                let Some(id) =
                    self.declare_named(&def.name, ClassKind::Module, namespace, expr.span)
                else {
                    return true;
                };
                self.collect_body(id, &def.body, prelude);
                self.pending.push(PendingClass {
                    id,
                    body: &def.body,
                    def: PendingDef::Module(def),
                });
            }
            ExprKind::DataDef(def) => {
                let path = ConstPath::simple(def.name.clone());
                let Some(id) = self.declare_named(&path, ClassKind::Data, namespace, expr.span)
                else {
                    return true;
                };
                self.world.class_mut(id).auto_initialize = true;
                self.collect_body(id, &def.body, prelude);
                self.pending.push(PendingClass {
                    id,
                    body: &def.body,
                    def: PendingDef::Data(def),
                });
            }
            ExprKind::EnumDef(def) => {
                let path = ConstPath::simple(def.name.clone());
                let Some(id) = self.declare_named(&path, ClassKind::Enum, namespace, expr.span)
                else {
                    return true;
                };
                self.world.class_mut(id).is_abstract = true;
                // The enum first: its body's methods replace the
                // variants' generated ones (`declare_data_methods`).
                let mut variants = Vec::new();
                for variant in &def.variants {
                    let vpath = ConstPath::simple(variant.name.clone());
                    if let Some(vid) =
                        self.declare_named(&vpath, ClassKind::Variant, Some(id), variant.span)
                    {
                        self.world.class_mut(vid).variant_of = Some(id);
                        self.world.class_mut(vid).auto_initialize = true;
                        self.world.class_mut(id).variants.push(vid);
                        variants.push(PendingClass {
                            id: vid,
                            body: &[],
                            def: PendingDef::Variant(variant),
                        });
                    }
                }
                self.collect_body(id, &def.body, prelude);
                self.pending.push(PendingClass {
                    id,
                    body: &def.body,
                    def: PendingDef::Enum(def),
                });
                self.pending.extend(variants);
            }
            ExprKind::ExtensionDef(def) => {
                let id = self.world.extensions.len() as ExtensionId;
                self.world.extensions.push(ExtensionInfo {
                    id,
                    module: namespace,
                    target: 0,
                    type_params: Vec::new(),
                    target_args: Vec::new(),
                    includes: Vec::new(),
                    methods: HashMap::default(),
                    span: expr.span,
                    always_active: prelude,
                    file: self.file,
                    group: (!prelude
                        && namespace
                            .is_none_or(|ns| self.world.cogs.iter().any(|c| c.root == Some(ns))))
                    .then(|| self.world.file_groups.get(&self.file).copied())
                    .flatten(),
                });
                if let Some(ns) = namespace {
                    self.world.class_mut(ns).extensions.push(id);
                }
                self.pending_ext.push(PendingExtension {
                    id,
                    def,
                    namespace,
                    file: self.file,
                });
            }
            ExprKind::ConstAssign { name, value } => {
                let id = self.world.consts.len() as ConstId;
                self.world.consts.push(ConstInfo {
                    id,
                    name: name.clone(),
                    owner: namespace,
                    ty: None,
                    value: Some(Rc::new((**value).clone())),
                    span: expr.span,
                    checking: false,
                    file: self.file,
                });
                self.register_member(namespace, name, Member::Const(id), expr.span);
            }
            ExprKind::TypeAlias {
                name,
                type_params,
                ty,
            } => {
                let params = self.new_type_params(type_params);
                let id = self.world.aliases.len() as u32;
                self.world.aliases.push(TypeAliasInfo {
                    name: name.clone(),
                    owner: namespace,
                    type_params: params,
                    expr: ty.clone(),
                    resolved: None,
                    file: self.file,
                });
                self.register_member(namespace, name, Member::Alias(id), expr.span);
            }
            ExprKind::Using(path) => match namespace {
                Some(ns) => self
                    .class_usings
                    .entry(ns)
                    .or_default()
                    .push((path, expr.span.start)),
                None => {
                    if let Some(unit) = self.units.last_mut() {
                        unit.usings.push((path, expr.span.start));
                    }
                }
            },
            ExprKind::Require { .. } => {
                // The standard library is implicit; other files are not
                // supported yet.
            }
            ExprKind::Extern { .. } => {
                self.error(
                    "extern declarations are not supported by the interpreter yet",
                    expr.span,
                );
            }
            ExprKind::MethodDef(_)
            | ExprKind::FieldDecl(_)
            | ExprKind::AttrDecl { .. }
            | ExprKind::Mixin { .. }
            | ExprKind::Visibility { .. }
            | ExprKind::Alias { .. } => {
                // Handled in phase 2 with the enclosing class (top-level
                // methods belong to the main class).
                return namespace.is_some() || matches!(expr.kind, ExprKind::MethodDef(_));
            }
            _ => return false,
        }
        true
    }

    /// The namespace a declaration of `path` goes into (`None` for the
    /// top level), or the first part of its prefix that is not declared.
    /// The first part is looked up as any constant is, outwards from
    /// `namespace` (from the top level for `::A::B`, the cog's root for
    /// `cog::A::B`); the others in the namespace before them only.
    fn resolve_prefix<'p>(
        &self,
        path: &'p ConstPath,
        namespace: Option<ClassId>,
    ) -> Result<Option<ClassId>, &'p str> {
        let (mut ns, outwards) = if path.absolute {
            (None, false)
        } else if path.cog {
            (self.world.cog_root(namespace), false)
        } else {
            (namespace, true)
        };
        let prefixes = &path.names[..path.names.len().saturating_sub(1)];
        for (i, prefix) in prefixes.iter().enumerate() {
            let found = if i == 0 && outwards {
                self.world.resolve_member(ns, prefix)
            } else {
                self.world.member_in(ns, prefix)
            };
            match found {
                Some(Member::Class(id)) => ns = Some(id),
                _ => return Err(prefix),
            }
        }
        Ok(ns)
    }

    fn namespace_of(
        &self,
        path: &ConstPath,
        namespace: Option<ClassId>,
    ) -> Option<Option<ClassId>> {
        self.resolve_prefix(path, namespace).ok()
    }

    /// Collect the deferred qualified declarations, in passes: each pass
    /// collects, in the order they were met, those whose namespace is
    /// declared when it starts (so a duplicate is reported on the later
    /// one), which may declare the namespace of others. Then those left
    /// are reported as unknown namespaces. All are at a file's top level:
    /// the first part of each is looked up from there, where none of them
    /// declares, so the order they are collected in cannot change where
    /// one goes.
    fn collect_deferred(&mut self) {
        loop {
            let todo = std::mem::take(&mut self.deferred);
            let ready: Vec<bool> = todo
                .iter()
                .map(|d| {
                    self.namespace_of(deferred_path(d.expr), d.namespace)
                        .is_some()
                })
                .collect();
            if !ready.contains(&true) {
                self.deferred = todo;
                break;
            }
            for (d, ready) in todo.into_iter().zip(ready) {
                if ready {
                    self.collect_one(d);
                } else {
                    self.deferred.push(d);
                }
            }
        }
        for d in std::mem::take(&mut self.deferred) {
            self.final_pass = true;
            self.collect_one(d);
            self.final_pass = false;
        }
    }

    fn collect_one(&mut self, d: Deferred<'ast>) {
        self.file = d.file;
        self.in_app = d.in_app;
        self.collecting = Some(d.expr as *const Expr);
        self.collect_item(d.expr, d.namespace, d.prelude);
        self.collecting = None;
        self.in_app = false;
    }

    fn collect_body(&mut self, id: ClassId, body: &'ast [Expr], prelude: bool) {
        for expr in body {
            if self.collect_item(expr, Some(id), prelude) {
                continue;
            }
            // A call on the class being declared (`has_many Comment`) is a
            // `static` statement, run at compile time (docs/14), in a
            // class or module body outside the prelude.
            let kind = self.world.class(id).kind;
            let is_call = matches!(&expr.kind, ExprKind::Call(call) if call.recv.is_none());
            if is_call && !prelude && matches!(kind, ClassKind::Class | ClassKind::Module) {
                self.world.static_stmts.push(StaticStmt {
                    class: id,
                    file: self.file,
                    expr: Rc::new(expr.clone()),
                    span: expr.span,
                });
                continue;
            }
            self.error("only declarations are allowed in a class body", expr.span);
        }
    }

    fn declare_named(
        &mut self,
        path: &ConstPath,
        kind: ClassKind,
        namespace: Option<ClassId>,
        span: Span,
    ) -> Option<ClassId> {
        if let Some(msg) = path
            .names
            .last()
            .and_then(|n| quarz_syntax::reserved_type_name(n))
        {
            self.error(msg, span);
            return None;
        }
        // A library cog declares only inside its root module: `::X` would
        // be the application's top level.
        if path.absolute && self.world.cog_root(namespace).is_some() {
            self.error(
                "a cog declares only in its root module: `::` would declare at the application's top level",
                span,
            );
            return None;
        }
        // `class A::B` nests B in A (A must exist, see `resolve_prefix`).
        let ns = match self.resolve_prefix(path, namespace) {
            Ok(ns) => ns,
            Err(prefix) => {
                self.error(format!("unknown namespace `{prefix}`"), span);
                return None;
            }
        };
        // A qualified declaration adds to the program's own classes and
        // modules only, of its cog: not to a built-in or standard library
        // one, nor to another cog's.
        if let Some(target) = ns.filter(|_| path.names.len() > 1) {
            if self.file != 0
                && !self.world.std_files.contains(&self.file)
                && !self.own_namespace(target, namespace)
            {
                let info = self.world.class(target);
                let whose = if self.world.cogs.iter().any(|c| c.root == Some(target)) {
                    "it is another cog's"
                } else if info.file == 0 {
                    "it is built in"
                } else if self.world.std_files.contains(&info.file) {
                    "it is in the standard library"
                } else {
                    "it is another cog's"
                };
                self.error(
                    format!(
                        "cannot declare in `{}`: {whose}, and a qualified declaration adds only to this cog's own classes and modules",
                        info.name
                    ),
                    span,
                );
                return None;
            }
        }
        let short = path.last().to_string();
        // A cog's files are the body of its root module already: `module
        // Httpx` (or `module cog::Httpx`) in the `Httpx` cog would reopen
        // it.
        if kind == ClassKind::Module {
            // The cog this declaration is in: not a dependency's root
            // reached by a qualified name.
            if let Some(root) = ns.filter(|n| self.world.cog_root(namespace) == Some(*n)) {
                if self.world.class(root).name == short {
                    self.error(
                        format!(
                            "`{short}` is this cog's root module: its files are its body already, and it cannot be reopened"
                        ),
                        span,
                    );
                    return None;
                }
            }
        }
        // Nor a dependency's (its key in the manifest), which any
        // declaration of that name would shadow.
        if path.names.len() == 1 && self.shadows_dependency(namespace, &short) {
            self.dependency_error(&short, span);
            return None;
        }
        if let Some(existing) = self.world.member_in(ns, &short) {
            let written = path.names.join("::");
            match existing {
                Member::Class(id) => {
                    let existing = self.world.class(id);
                    let message = match (existing.kind, kind) {
                        // A module of the program's own: the way to add to
                        // it. Not a built-in module, nor a dependency's
                        // root (another cog's declarations).
                        (ClassKind::Module, ClassKind::Module)
                            if self.own_namespace(id, namespace) =>
                        {
                            // Its name from a file's top level (in a cog,
                            // the root module's body).
                            let root = self.world.cog_root(namespace);
                            let full = root
                                .and_then(|r| {
                                    existing
                                        .name
                                        .strip_prefix(&format!("{}::", self.world.class(r).name))
                                })
                                .unwrap_or(&existing.name);
                            format!(
                                "`{written}` is already defined; modules cannot be reopened (to add to it from elsewhere, declare `class {full}::Name` or `module {full}::Name`)"
                            )
                        }
                        (ClassKind::Module, ClassKind::Module) => {
                            format!("`{written}` is already defined; modules cannot be reopened")
                        }
                        (k, ClassKind::Class) if k != ClassKind::Module => format!(
                            "`{written}` is already defined; classes cannot be reopened (use `extension`)"
                        ),
                        _ => format!("`{written}` is already defined"),
                    };
                    self.error(message, span);
                }
                _ => self.error(format!("`{short}` is already defined"), span),
            }
            return None;
        }
        let full = match ns {
            Some(ns) => format!("{}::{}", self.world.class(ns).name, short),
            None => short.clone(),
        };
        let mut info = World::blank_class(full, kind, ns, span);
        info.file = self.file;
        let id = self.world.add_class(info);
        self.register_member(ns, &short, Member::Class(id), span);
        Some(id)
    }

    /// Whether class or module `id` is the program's own, declared in the
    /// cog `namespace` is in: not built in (nor the prelude's), not the
    /// standard library's, not a cog's root module, nor in another cog.
    fn own_namespace(&self, id: ClassId, namespace: Option<ClassId>) -> bool {
        let info = self.world.class(id);
        info.file != 0
            && !self.world.std_files.contains(&info.file)
            && !self.world.cogs.iter().any(|c| c.root == Some(id))
            && self.world.cog_root(Some(id)) == self.world.cog_root(namespace)
    }

    /// Whether `name`, declared in `namespace`, is a dependency's key of
    /// the cog whose root module `namespace` is: a declaration of that name
    /// there would shadow the dependency.
    fn shadows_dependency(&self, namespace: Option<ClassId>, name: &str) -> bool {
        namespace
            .filter(|n| self.world.cogs.iter().any(|c| c.root == Some(*n)))
            .and_then(|n| self.world.class(n).cog)
            .is_some_and(|c| self.world.cogs[c as usize].imports.contains_key(name))
    }

    fn dependency_error(&mut self, name: &str, span: Span) {
        self.error(
            format!(
                "`{name}` is a dependency of this cog (a key of its Cog.toml): another cog's module cannot be reopened or shadowed"
            ),
            span,
        );
    }

    fn register_member(
        &mut self,
        namespace: Option<ClassId>,
        name: &str,
        member: Member,
        span: Span,
    ) {
        if let Some(msg) = quarz_syntax::reserved_type_name(name) {
            self.error(msg, span);
            return;
        }
        if self.shadows_dependency(namespace, name) {
            self.dependency_error(name, span);
            return;
        }
        if namespace.is_none() && self.in_app {
            self.world.app_names.insert(name.to_string());
        }
        let table = match namespace {
            Some(ns) => &mut self.world.class_mut(ns).members,
            None => &mut self.world.top,
        };
        if table.contains_key(name) {
            self.error(format!("`{name}` is already defined"), span);
            return;
        }
        table.insert(name.to_string(), member);
    }

    // ----- phase 2 ---------------------------------------------------------

    pub fn resolve_headers(&mut self) {
        self.collect_deferred();
        if !self.builtins_resolved {
            self.find_builtins();
            self.builtins_resolved = true;
        }

        // Type parameters first, so that bounds and superclasses may refer
        // to them in any order.
        let pending = std::mem::take(&mut self.pending);
        for p in &pending {
            let (params, _) = match p.def {
                PendingDef::Class(d) => (&d.type_params, ()),
                PendingDef::Module(d) => (&d.type_params, ()),
                PendingDef::Data(d) => (&d.type_params, ()),
                PendingDef::Enum(d) => (&d.type_params, ()),
                PendingDef::Variant(_) | PendingDef::Main | PendingDef::CogRoot(_) => continue,
            };
            let infos: Vec<TypeParamInfo> = self.new_type_params(params);
            self.world.class_mut(p.id).type_params = infos;
        }
        // Variants share the enum's parameters.
        for p in &pending {
            if let PendingDef::Variant(_) = p.def {
                let enum_id = self.world.class(p.id).variant_of.unwrap();
                let params = self.world.class(enum_id).type_params.clone();
                self.world.class_mut(p.id).type_params = params;
            }
        }
        let pending_ext = std::mem::take(&mut self.pending_ext);
        for e in &pending_ext {
            let infos: Vec<TypeParamInfo> = self.new_type_params(&e.def.type_params);
            self.world.extensions[e.id as usize].type_params = infos;
        }

        // Bounds, superclasses, includes, fields and methods.
        for p in &pending {
            self.file = self.pending_file(p);
            self.resolve_class_header(p);
        }
        for e in &pending_ext {
            self.file = e.file;
            self.resolve_extension(e);
        }
        self.check_expansive_inheritance(
            &pending.iter().map(|p| p.id).collect::<Vec<_>>(),
            &pending_ext.iter().map(|e| e.id).collect::<Vec<_>>(),
        );
        for p in &pending {
            self.file = self.pending_file(p);
            self.resolve_class_members(p);
        }
        for e in &pending_ext {
            self.file = e.file;
            self.resolve_extension_members(e);
        }
        self.resolve_usings();
        // (Before the checks below, which ask whether a `data` type is a
        // `Shareable`: `World::derived_shareable`.)
        let mut ids: Vec<ClassId> = pending.iter().map(|p| p.id).collect();
        for &id in &ids.clone() {
            ids.extend(self.world.class(id).variants.clone());
        }
        self.world.ensure_shareable_known(&ids);
        for p in &pending {
            self.file = self.pending_file(p);
            // The top-level extensions of the class's group are active
            // there (they may implement a module's methods for it).
            let file = self.world.class(p.id).file;
            self.world.active_extensions = self.world.group_extensions(file);
            self.check_conformance(p);
            self.check_shareable_promise(p.id);
            self.check_variance(p.id);
            self.check_kept_blocks(p.id);
            self.check_quoted_overrides(p.id);
            self.check_override_returns(p.id);
            self.check_copied_deinitialize(p.id);
            self.check_eq_with_hash(p.id);
            self.check_duplicate_methods(p.id);
            self.check_static_mixins(p);
            self.world.active_extensions.clear();
        }
        self.check_extensions_kept_blocks();
        self.check_extensions_duplicates();
        self.check_extensions_deinitialize();
        self.check_shareable_extensions();
        self.check_quoted_extensions();
        for e in &pending_ext {
            self.file = e.file;
            self.check_extension_static(e);
        }
    }

    /// A module with `static def`s (docs/14 §2) is extended, not
    /// included, and as `extend M[C]` with `C` the extending class itself:
    /// the `static def`s were checked with `self: Meta::ClassDef[T]` (`T`
    /// the module's first type parameter), which holds only where they
    /// run on `C` or a class under it.
    fn check_static_mixins(&mut self, p: &PendingClass<'ast>) {
        for expr in p.body {
            let ExprKind::Mixin { kind, types } = &expr.kind else {
                continue;
            };
            for t in types {
                // Resolved again: reported already if it does not resolve.
                let Some(Type::Class(mid, args)) = self.resolve_type_quietly(p.id, t) else {
                    continue;
                };
                if !self.has_static_defs(mid) {
                    continue;
                }
                let mname = self.world.class(mid).name.clone();
                // The class's own instance type, its type parameters as
                // they are (`Box[E]`, not `Box[Int]`): what is generated
                // goes into every `Box`.
                let instance = Type::Class(
                    p.id,
                    self.world
                        .class(p.id)
                        .type_params
                        .iter()
                        .map(|tp| Type::Param(tp.id))
                        .collect(),
                );
                let shown = self.world.type_name(&instance);
                match kind {
                    MixinKind::Include => self.error(
                        format!(
                            "`{mname}` has `static def`s, which run on a class: extend it (`extend {mname}[{shown}]`) rather than include it"
                        ),
                        t.span,
                    ),
                    MixinKind::Extend => {
                        let params = self.world.class(mid).type_params.clone();
                        if params.is_empty() {
                            continue;
                        }
                        if args.first() != Some(&instance) {
                            let mut want = args.clone();
                            want[0] = instance.clone();
                            let want = self.world.type_name(&Type::Class(mid, want));
                            self.error(
                                format!(
                                    "`{mname}` has `static def`s, which run on the class extending it: extend it as `{want}`"
                                ),
                                t.span,
                            );
                            continue;
                        }
                        // The `static def`s were checked under the bounds:
                        // the arguments must meet them, with the module's
                        // parameters taken as the arguments (`T <: Cmp[T]`).
                        let written = self.world.type_name(&Type::Class(mid, args.clone()));
                        let map: rustc_hash::FxHashMap<_, _> = params
                            .iter()
                            .map(|p| p.id)
                            .zip(args.iter().cloned())
                            .collect();
                        for (p, a) in params.iter().zip(&args) {
                            for b in &p.bounds {
                                let b = b.subst(&map);
                                if !self.world.is_subtype(a, &b) {
                                    let an = self.world.type_name(a);
                                    let bn = self.world.type_name(&b);
                                    self.error(
                                        format!(
                                            "`{written}`: `{an}` is not a `{bn}`, which `{mname}`'s `static def`s were checked for (`{}`)",
                                            p.name
                                        ),
                                        t.span,
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Whether a module declares `static def`s (docs/14 §2).
    fn has_static_defs(&self, module: ClassId) -> bool {
        let m = self.world.class(module);
        m.kind == ClassKind::Module
            && m.methods.values().flatten().any(|id| {
                let info = self.world.method(*id);
                info.owner == module && info.is_static && !info.is_native
            })
    }

    /// An extension declares no `static def` (its `self` would be typed by
    /// the module it extends, not by the class it runs on), and includes
    /// no module that has some (docs/14 §2).
    fn check_extension_static(&mut self, e: &PendingExtension<'ast>) {
        let ids: Vec<MethodId> = self.world.extensions[e.id as usize]
            .methods
            .values()
            .flatten()
            .copied()
            .collect();
        for id in ids {
            let m = self.world.method(id);
            if m.is_static && !m.is_native {
                let span = m.span;
                self.error(
                    "an extension cannot declare a `static def`: declare it in the class or module itself",
                    span,
                );
            }
        }
        let includes = self.world.extensions[e.id as usize].includes.clone();
        for t in includes {
            if let Type::Class(mid, _) = t {
                if self.has_static_defs(mid) {
                    let mname = self.world.class(mid).name.clone();
                    self.error(
                        format!(
                            "`{mname}` has `static def`s, which run on a class: an extension cannot include it"
                        ),
                        e.def.target.span,
                    );
                }
            }
        }
    }

    /// Expansive inheritance is an error (Kennedy and Pierce): with
    /// variance, `class C[X] < N[N[C[C[X]]]]` makes a subtype question
    /// whose sub-questions grow without end. The graph's nodes are the
    /// classes' parameter positions; a type application `D[.., a, ..]` in a
    /// class's superclass or includes (an extension's includes too, its
    /// parameters taken as the target class's) adds an edge from each of
    /// the class's parameters in `a` to `D`'s position, expansive when `a`
    /// nests the parameter in a class application, a tuple or a procedure
    /// (a union with it as a member does not grow: `T?`). A parameter that
    /// reaches itself through an expansive edge is refused at the class or
    /// extension declared now (`ids`, `exts`; the cycle may go through
    /// earlier files' classes), and the parent that makes it is dropped, so
    /// that what follows terminates. (`extend` is left out: a class's
    /// extended modules give class methods, not supertypes.)
    fn check_expansive_inheritance(&mut self, ids: &[ClassId], exts: &[ExtensionId]) {
        type Node = (ClassId, usize);
        #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        enum Slot {
            Super(ClassId),
            Include(ClassId, usize),
            Ext(ExtensionId, usize),
        }
        type Edges = HashMap<Node, Vec<(Node, bool, Slot)>>;
        fn nests(a: &Type, p: TypeParamId) -> bool {
            match a {
                Type::Param(_) => false,
                Type::Union(ms) => ms.iter().any(|m| nests(m, p)),
                _ => a.mentions_param(p),
            }
        }
        fn walk(t: &Type, params: &[TypeParamId], from: ClassId, slot: Slot, edges: &mut Edges) {
            match t {
                Type::Class(d, args) | Type::ClassObject(d, args) => {
                    for (j, a) in args.iter().enumerate() {
                        for (i, p) in params.iter().enumerate() {
                            if a.mentions_param(*p) {
                                edges.entry((from, i)).or_default().push((
                                    (*d, j),
                                    nests(a, *p),
                                    slot,
                                ));
                            }
                        }
                        walk(a, params, from, slot, edges);
                    }
                }
                Type::Union(ms) | Type::Tuple(ms) => {
                    for m in ms {
                        walk(m, params, from, slot, edges);
                    }
                }
                Type::Proc(rc, ps, r, _) => {
                    for x in rc
                        .iter()
                        .map(|b| &**b)
                        .chain(ps)
                        .chain(std::iter::once(&**r))
                    {
                        walk(x, params, from, slot, edges);
                    }
                }
                Type::TypeOf(x) => walk(x, params, from, slot, edges),
                _ => {}
            }
        }
        let mut edges: Edges = HashMap::default();
        for cid in 0..self.world.classes.len() as ClassId {
            let class = self.world.class(cid);
            if class.type_params.is_empty() {
                continue;
            }
            let params: Vec<TypeParamId> = class.type_params.iter().map(|p| p.id).collect();
            if let Some(t) = &class.superclass {
                walk(t, &params, cid, Slot::Super(cid), &mut edges);
            }
            for (k, t) in class.includes.iter().enumerate() {
                walk(t, &params, cid, Slot::Include(cid, k), &mut edges);
            }
        }
        for (e, ext) in self.world.extensions.iter().enumerate() {
            let target = self.world.class(ext.target);
            if target.type_params.is_empty() || ext.includes.is_empty() {
                continue;
            }
            let params: Vec<TypeParamId> = target.type_params.iter().map(|p| p.id).collect();
            // The extension's parameters as the target's, where its target
            // arguments are bare parameters.
            let subst: HashMap<TypeParamId, Type> = ext
                .target_args
                .iter()
                .zip(&params)
                .filter_map(|(a, p)| match a {
                    Type::Param(q) => Some((*q, Type::Param(*p))),
                    _ => None,
                })
                .collect();
            for (k, t) in ext.includes.iter().enumerate() {
                walk(
                    &t.subst(&subst),
                    &params,
                    ext.target,
                    Slot::Ext(e as ExtensionId, k),
                    &mut edges,
                );
            }
        }
        let new_slot = |slot: &Slot| match slot {
            Slot::Super(c) | Slot::Include(c, _) => ids.contains(c),
            Slot::Ext(e, _) => exts.contains(e),
        };
        // Every expansive edge's cycle (an old one may be closed by a new
        // edge, in the REPL), refused at a slot declared now: the
        // expansive one if new, else the first new edge on the cycle.
        let mut refused: Vec<(Slot, ClassId, usize, Vec<ClassId>)> = Vec::new();
        let sources: Vec<Node> = edges.keys().copied().collect();
        for src in sources {
            for &(to, expansive, slot) in edges[&src].clone().iter() {
                if !expansive {
                    continue;
                }
                let mut seen: HashSet<Node> = HashSet::default();
                let mut prev: HashMap<Node, (Node, Slot)> = HashMap::default();
                let mut queue = std::collections::VecDeque::from([to]);
                seen.insert(to);
                let mut found = false;
                while let Some(u) = queue.pop_front() {
                    if u == src {
                        found = true;
                        break;
                    }
                    for &(v, _, sl) in edges.get(&u).map(|v| v.as_slice()).unwrap_or(&[]) {
                        if seen.insert(v) {
                            prev.insert(v, (u, sl));
                            queue.push_back(v);
                        }
                    }
                }
                if found {
                    let mut through = vec![to.0];
                    let mut path_slots = Vec::new();
                    let mut u = src;
                    while let Some(&(p, sl)) = prev.get(&u) {
                        through.push(u.0);
                        path_slots.push(sl);
                        u = p;
                    }
                    let at = if new_slot(&slot) {
                        Some(slot)
                    } else {
                        path_slots.iter().rev().copied().find(|sl| new_slot(sl))
                    };
                    if let Some(at) = at {
                        refused.push((at, src.0, src.1, through));
                    }
                }
            }
        }
        refused.sort_by_key(|r| r.0);
        refused.dedup_by_key(|r| r.0);
        for (slot, cid, i, through) in &refused {
            let class = self.world.class(*cid).clone();
            let mut names: Vec<String> = Vec::new();
            for c in through {
                let n = self.world.class(*c).name.clone();
                if !names.contains(&n) {
                    names.push(n);
                }
            }
            let names: Vec<String> = names.iter().map(|n| format!("`{n}`")).collect();
            let params: Vec<String> = class
                .type_params
                .iter()
                .map(|p| self.world.type_param_name(p.id))
                .collect();
            let head = format!("{}[{}]", class.name, params.join(", "));
            let (decl, span, file) = match *slot {
                Slot::Super(_) => (
                    format!(
                        "{head} < {}",
                        self.world.type_name(class.superclass.as_ref().unwrap())
                    ),
                    class.span,
                    class.file,
                ),
                Slot::Include(_, k) => (
                    format!(
                        "{head} includes {}",
                        self.world.type_name(&class.includes[k])
                    ),
                    class.span,
                    class.file,
                ),
                Slot::Ext(e, k) => {
                    // (In the extension's own names.)
                    let ext = &self.world.extensions[e as usize];
                    let own: Vec<String> = ext
                        .type_params
                        .iter()
                        .map(|p| self.world.type_param_name(p.id))
                        .collect();
                    (
                        format!(
                            "extension {}[{}] includes {}",
                            self.world.class(ext.target).name,
                            own.join(", "),
                            self.world.type_name(&ext.includes[k])
                        ),
                        ext.span,
                        ext.file,
                    )
                }
            };
            let param = match *slot {
                Slot::Ext(e, _) if self.world.extensions[e as usize].target == *cid => {
                    match self.world.extensions[e as usize].target_args.get(*i) {
                        Some(Type::Param(q)) => self.world.type_param_name(*q),
                        _ => self.world.type_param_name(class.type_params[*i].id),
                    }
                }
                _ => self.world.type_param_name(class.type_params[*i].id),
            };
            // (Whose parameter, when the refused slot is another's.)
            let owner = match *slot {
                Slot::Super(c) | Slot::Include(c, _) => c,
                Slot::Ext(e, _) => self.world.extensions[e as usize].target,
            };
            let of = if owner == *cid {
                String::new()
            } else {
                format!(" of `{}`", class.name)
            };
            self.file = file;
            self.error(
                format!("`{decl}`: expansive inheritance, `{param}`{of} grows through {}; subtyping would not terminate", names.join(" and ")),
                span,
            );
        }
        // Drop the refused parents (includes from the last, so that the
        // others keep their indices).
        let mut slots: Vec<Slot> = refused.into_iter().map(|r| r.0).collect();
        slots.sort_by(|a, b| b.cmp(a));
        for slot in slots {
            match slot {
                Slot::Super(c) => self.world.class_mut(c).superclass = None,
                Slot::Include(c, k) => {
                    self.world.class_mut(c).includes.remove(k);
                }
                Slot::Ext(e, k) => {
                    let ty = self.world.extensions[e as usize].includes.remove(k);
                    // (Nor checked later as an included module.)
                    if let Some(at) = self.ext_includes.iter().position(|x| x.0 == e && x.1 == ty) {
                        self.ext_includes.remove(at);
                    }
                }
            }
        }
    }

    /// Whether two methods have the same signature: parameters (kinds
    /// and types) and block, their own type parameters renamed in order.
    fn same_signature(&self, a: &MethodInfo, b: &MethodInfo) -> bool {
        if a.type_params.len() != b.type_params.len() {
            return false;
        }
        let rename: HashMap<TypeParamId, Type> = b
            .type_params
            .iter()
            .zip(&a.type_params)
            .map(|(q, p)| (q.id, Type::Param(p.id)))
            .collect();
        let same = |t: &Type, u: &Type| self.world.same_type(t, &u.subst(&rename));
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

    /// Two methods of one name and the same signature (`same_signature`)
    /// in one class, module or extension: a call could not tell them
    /// apart, so one is an error (a `def` beside an accessor `attr_*`
    /// makes, or two `def`s). Other parameters make an overload (docs/01
    /// §9).
    fn duplicate_errors(&self, ids: &[MethodId], errors: &mut Vec<(String, Span, u32)>) {
        for (i, later) in ids.iter().enumerate() {
            let b = self.world.method(*later);
            if let Some(earlier) = ids[..i]
                .iter()
                .find(|e| self.same_signature(self.world.method(**e), b))
            {
                // Reported at the one the user wrote (a data type's
                // generated methods are declared after its own).
                let a = self.world.method(*earlier);
                let at = if b.synth != Synth::None { a } else { b };
                errors.push((
                    format!("`{}` is already defined with the same parameters", b.name),
                    at.span,
                    at.file,
                ));
            }
        }
    }

    fn check_duplicate_methods(&mut self, cid: ClassId) {
        let mut errors = Vec::new();
        let class = self.world.class(cid);
        for table in [&class.methods, &class.singleton_methods] {
            for ids in table.values() {
                self.duplicate_errors(ids, &mut errors);
            }
        }
        self.report_at(errors);
    }

    fn check_extensions_duplicates(&mut self) {
        let mut errors = Vec::new();
        for e in &self.world.extensions {
            for ids in e.methods.values() {
                self.duplicate_errors(ids, &mut errors);
            }
        }
        self.report_at(errors);
    }

    fn report_at(&mut self, errors: Vec<(String, Span, u32)>) {
        for (msg, span, file) in errors {
            let saved = self.file;
            self.file = file;
            self.error(msg, span);
            self.file = saved;
        }
    }

    /// `check_kept_blocks` for the methods of extensions: an extension's
    /// method found before its target's own may not keep a block the one
    /// it hides only yields to.
    fn check_extensions_kept_blocks(&mut self) {
        let mut errors = Vec::new();
        for e in &self.world.extensions {
            let ancestors = self.world.ancestor_ids(e.target);
            for ids in e.methods.values() {
                for mid in ids {
                    let m = self.world.method(*mid);
                    let Some((name, _)) = &m.block else { continue };
                    // (A constructor is never called through a parent's.)
                    if name == "&" || m.file == 0 || (m.name == "initialize" && !m.singleton) {
                        continue;
                    }
                    let hidden = ancestors.iter().find_map(|a| {
                        self.world
                            .class(*a)
                            .methods
                            .get(&m.name)?
                            .iter()
                            .copied()
                            .find(|o| {
                                let o = self.world.method(*o);
                                o.singleton == m.singleton
                                    && arities_meet(&o.params, &m.params)
                                    && o.block.as_ref().is_some_and(|(n, _)| n == "&")
                            })
                    });
                    if let Some(o) = hidden {
                        let owner = self.world.class(self.world.method(o).owner).name.clone();
                        errors.push((
                            m.file,
                            format!(
                                "`{}` cannot keep its block (`&{name}`): `{owner}#{}`, which it hides, only yields to it (`&:`), and callers rely on that",
                                m.name, m.name
                            ),
                            m.span,
                        ));
                    }
                }
            }
        }
        for (file, msg, span) in errors {
            self.file = file;
            self.error(msg, span);
        }
    }

    /// An override returns what the method it overrides does (or a
    /// subtype): a caller typed by the parent, or a native calling `to_s`
    /// or `==` by name, relies on it. A method without a return type
    /// returns nil, so it overrides none that returns a value.
    fn check_override_returns(&mut self, id: ClassId) {
        let class = self.world.class(id);
        let mine: Vec<MethodId> = class.methods.values().flatten().copied().collect();
        let args: Vec<Type> = class
            .type_params
            .iter()
            .map(|p| Type::Param(p.id))
            .collect();
        let ancestors: Vec<(ClassId, Vec<Type>)> = self
            .world
            .ancestors(id, &args)
            .into_iter()
            .filter(|(a, _)| *a != id)
            .collect();
        for mid in mine {
            let m = self.world.method(mid);
            // (The prelude specializes some of what it overrides, as Ruby:
            // `Hash#select` and `Hash#filter` give a `Hash`.)
            if m.owner != id
                || m.synth != Synth::None
                || m.file == 0
                || (!m.singleton && (m.name == "initialize" || m.name == "deinitialize"))
            {
                continue;
            }
            let mine_ret = m.ret.clone();
            // The nearest method of the name with the same parameters.
            let found = ancestors.iter().find_map(|(a, aargs)| {
                let mut subst = self.world.class_subst(*a, aargs);
                self.world
                    .class(*a)
                    .methods
                    .get(&m.name)?
                    .iter()
                    .copied()
                    .find(|o| {
                        let o = self.world.method(*o);
                        if o.type_params.len() != m.type_params.len() {
                            return false;
                        }
                        // Its type parameters as the override's, in order.
                        for (p, q) in o.type_params.iter().zip(&m.type_params) {
                            subst.insert(p.id, Type::Param(q.id));
                        }
                        o.singleton == m.singleton
                            && o.block.is_some() == m.block.is_some()
                            && o.params.len() == m.params.len()
                            && o.params.iter().zip(&m.params).all(|(p, q)| {
                                p.kind == q.kind
                                    && (p.kind != ParamKind::KeywordOnly || p.name == q.name)
                                    && self.world.same_type(&p.ty.subst(&subst), &q.ty)
                            })
                    })
                    .map(|o| (o, subst.clone()))
            });
            let Some((o, subst)) = found else { continue };
            let theirs = self.world.method(o).ret.clone();
            let theirs = theirs.subst(&subst);
            if contains_self(&theirs) || contains_self(&mine_ret) {
                continue;
            }
            if !self.world.is_subtype(&mine_ret, &theirs) {
                let owner = self.world.class(self.world.method(o).owner).name.clone();
                let (mname, span) = (m.name.clone(), m.span);
                let (mine_s, theirs_s) = (
                    self.world.type_name(&mine_ret),
                    self.world.type_name(&theirs),
                );
                let hint = if mine_ret == Type::Void {
                    " (a `-> Void` method, as one without a return type, returns nil)"
                } else {
                    ""
                };
                self.error(
                    format!(
                        "`{mname}` returns {mine_s} but `{owner}#{mname}`, which it overrides, returns {theirs_s}{hint}"
                    ),
                    span,
                );
            }
        }
    }

    /// Whether a method may keep its block is part of its signature: an
    /// anonymous block (`&:`) is only yielded to, and a caller relies on
    /// it (a narrowing holds across a call given a block that cannot run
    /// later). An override cannot name the block (`&blk`) to keep it.
    fn check_kept_blocks(&mut self, id: ClassId) {
        let class = self.world.class(id);
        let mine: Vec<MethodId> = class.methods.values().flatten().copied().collect();
        let ancestors: Vec<ClassId> = self
            .world
            .ancestor_ids(id)
            .into_iter()
            .filter(|a| *a != id)
            .collect();
        for mid in mine {
            let m = self.world.method(mid);
            let Some((name, _)) = &m.block else { continue };
            if name == "&" || m.owner != id || (m.name == "initialize" && !m.singleton) {
                continue;
            }
            let overridden = ancestors.iter().find_map(|a| {
                self.world
                    .class(*a)
                    .methods
                    .get(&m.name)?
                    .iter()
                    .copied()
                    .find(|o| {
                        let o = self.world.method(*o);
                        o.singleton == m.singleton
                            && arities_meet(&o.params, &m.params)
                            && o.block.as_ref().is_some_and(|(n, _)| n == "&")
                    })
            });
            if let Some(o) = overridden {
                let owner = self.world.class(self.world.method(o).owner).name.clone();
                let (mname, span) = (m.name.clone(), m.span);
                self.error(
                    format!(
                        "`{mname}` cannot keep its block (`&{name}`): `{owner}#{mname}`, which it overrides, only yields to it (`&:`), and callers rely on that"
                    ),
                    span,
                );
            }
        }
    }

    /// A method that overrides or implements another takes its block the
    /// same way, as a `Quoted` or as a procedure (docs/14 §6): a caller
    /// gives what the method it sees declares.
    fn check_quoted_overrides(&mut self, id: ClassId) {
        let quoted = self.world.builtin.quoted;
        let is_quoted = |t: &Type| matches!(t, Type::Class(c, _) if *c == quoted);
        // Only the lowering makes a `Quoted`, whose shareability and
        // `new` the checker trusts: no subclass.
        if matches!(&self.world.class(id).superclass, Some(Type::Class(c, _)) if *c == quoted) {
            let span = self.world.class(id).span;
            self.error(
                "`Quoted` cannot be subclassed: a `Quoted` is made from a block literal",
                span,
            );
        }
        let class = self.world.class(id);
        let mine: Vec<MethodId> = class
            .methods
            .values()
            .chain(class.singleton_methods.values())
            .flatten()
            .copied()
            .collect();
        let ancestors: Vec<ClassId> = self
            .world
            .ancestor_ids(id)
            .into_iter()
            .filter(|a| *a != id)
            .collect();
        for mid in mine {
            let m = self.world.method(mid);
            if m.owner != id {
                continue;
            }
            let mine_quoted = m.block.as_ref().is_some_and(|(_, t)| is_quoted(t));
            let other = ancestors.iter().find_map(|a| {
                let c = self.world.class(*a);
                let table = if m.singleton {
                    &c.singleton_methods
                } else {
                    &c.methods
                };
                table.get(&m.name)?.iter().copied().find(|o| {
                    let o = self.world.method(*o);
                    o.singleton == m.singleton
                        && arities_meet(&o.params, &m.params)
                        && o.block.is_some()
                        && m.block.is_some()
                        && o.block.as_ref().is_some_and(|(_, t)| is_quoted(t)) != mine_quoted
                })
            });
            if let Some(o) = other {
                let owner = self.world.class(self.world.method(o).owner).name.clone();
                let (mname, span) = (m.name.clone(), m.span);
                let how = |q: bool| if q { "a `Quoted`" } else { "a procedure" };
                self.error(
                    format!(
                        "`{mname}` takes its block as {}, but `{owner}#{mname}`, which it overrides, takes {}",
                        how(mine_quoted),
                        how(!mine_quoted)
                    ),
                    span,
                );
            }
        }
    }

    /// An extension's method that implements a module's method (one it
    /// includes, or one of its target's ancestors) takes its block as
    /// that one does, as a `Quoted` or as a procedure (docs/14 §6).
    fn check_quoted_extensions(&mut self) {
        let quoted = self.world.builtin.quoted;
        let is_quoted = |t: &Type| matches!(t, Type::Class(c, _) if *c == quoted);
        let mut errors: Vec<(String, Span, u32)> = Vec::new();
        for e in &self.world.extensions {
            let mut sources: Vec<ClassId> = e
                .includes
                .iter()
                .filter_map(|t| match t {
                    Type::Class(c, _) => Some(*c),
                    _ => None,
                })
                .collect();
            sources.extend(self.world.ancestor_ids(e.target));
            for ids in e.methods.values() {
                for &mid in ids {
                    let m = self.world.method(mid);
                    let Some((_, bt)) = &m.block else { continue };
                    let mine = is_quoted(bt);
                    let other = sources.iter().find_map(|c| {
                        let class = self.world.class(*c);
                        let table = if m.singleton {
                            &class.singleton_methods
                        } else {
                            &class.methods
                        };
                        table.get(&m.name)?.iter().copied().find(|o| {
                            let o = self.world.method(*o);
                            o.extension.is_none()
                                && arities_meet(&o.params, &m.params)
                                && o.block.as_ref().is_some_and(|(_, t)| is_quoted(t) != mine)
                        })
                    });
                    if let Some(o) = other {
                        let owner = self.world.class(self.world.method(o).owner).name.clone();
                        let how = |q: bool| if q { "a `Quoted`" } else { "a procedure" };
                        errors.push((
                            format!(
                                "`{}` takes its block as {}, but `{owner}#{}`, which it implements, takes {}",
                                m.name,
                                how(mine),
                                m.name,
                                how(!mine)
                            ),
                            m.span,
                            m.file,
                        ));
                    }
                }
            }
        }
        for (message, span, file) in errors {
            self.file = file;
            self.error(message, span);
        }
    }

    /// A covariant (`out`) type parameter may appear only where values
    /// come out (results, the parameters of a block the method takes,
    /// lower bounds), a contravariant (`in`) one only where they go in,
    /// and neither in a `var` field. `initialize`, class methods and
    /// private methods are not checked: they see the exact type.
    fn check_variance(&mut self, id: ClassId) {
        let class = self.world.class(id);
        let params: Vec<(TypeParamId, Variance, String)> = class
            .type_params
            .iter()
            .filter(|p| p.variance != Variance::Invariant)
            .map(|p| (p.id, p.variance, p.name.clone()))
            .collect();
        if params.is_empty() {
            return;
        }
        let class_name = class.name.clone();
        let mut found: Vec<(String, Span)> = Vec::new();
        // A value is one of its superclass and of the modules it includes:
        // their arguments are results (an upcast must keep it sound).
        let span = class.span;
        for t in class.superclass.iter().chain(&class.includes) {
            let owner = match t {
                Type::Class(c, _) => self.world.class(*c).name.clone(),
                _ => continue,
            };
            self.variance_walk(t, 1, &params, &mut |p, _| {
                found.push((
                    format!("`{p}` appears in the type arguments of `{owner}`"),
                    span,
                ))
            });
        }
        for f in &class.fields {
            // A field is read as a result (by its reader, by methods); a
            // `var` one is written too.
            let (pol, what) = if f.mutable {
                (0, "the `var` field")
            } else {
                (1, "a result position of the field")
            };
            self.variance_walk(&f.ty, pol, &params, &mut |p, _| {
                found.push((format!("`{p}` appears in {what} `@{}`", f.name), f.span))
            });
        }
        let methods: Vec<MethodId> = class.methods.values().flatten().copied().collect();
        for mid in methods {
            let m = self.world.method(mid);
            if m.owner != id
                || m.name == "initialize"
                || m.visibility == Visibility::Private
                || m.synth != Synth::None
            {
                continue;
            }
            let mut report = |p: &str, pol: i8| {
                let place = if pol > 0 {
                    "a result position"
                } else if pol < 0 {
                    "a parameter position"
                } else {
                    "an invariant position"
                };
                found.push((format!("`{p}` appears in {place} of `{}`", m.name), m.span));
            };
            for p in &m.params {
                self.variance_walk(&p.ty, -1, &params, &mut report);
            }
            if let Some((_, t)) = &m.block {
                self.variance_walk(t, -1, &params, &mut report);
            }
            self.variance_walk(&m.ret, 1, &params, &mut report);
            for tp in &m.type_params {
                for b in &tp.bounds {
                    self.variance_walk(b, -1, &params, &mut report);
                }
                if let Some(l) = &tp.lower {
                    self.variance_walk(l, 1, &params, &mut report);
                }
            }
        }
        found.sort_by_key(|(_, span)| span.start);
        found.dedup();
        for (what, span) in found {
            self.error(
                format!(
                    "{what}, against its variance in {class_name}{}",
                    if what.contains(" of `") && !what.contains("type arguments") {
                        " (take a method type parameter such as `[U >: T]` instead)"
                    } else {
                        ""
                    }
                ),
                span,
            );
        }
    }

    /// Report each variant type parameter of `params` that `t` uses
    /// against its variance, `pol` being 1 where values come out, -1
    /// where they go in and 0 where both.
    fn variance_walk(
        &self,
        t: &Type,
        pol: i8,
        params: &[(TypeParamId, Variance, String)],
        report: &mut dyn FnMut(&str, i8),
    ) {
        match t {
            Type::Param(p) => {
                if let Some((_, v, name)) = params.iter().find(|(id, _, _)| id == p) {
                    let ok = match v {
                        Variance::Covariant => pol > 0,
                        Variance::Contravariant => pol < 0,
                        Variance::Invariant => true,
                    };
                    if !ok {
                        report(name, pol);
                    }
                }
            }
            Type::Class(c, args) | Type::ClassObject(c, args) => {
                let cps = &self.world.class(*c).type_params;
                for (i, a) in args.iter().enumerate() {
                    let v = cps.get(i).map_or(Variance::Invariant, |p| p.variance);
                    let pol = match v {
                        Variance::Covariant => pol,
                        Variance::Contravariant => -pol,
                        Variance::Invariant => 0,
                    };
                    self.variance_walk(a, pol, params, report);
                }
            }
            Type::Union(ms) | Type::Tuple(ms) => {
                for m in ms {
                    self.variance_walk(m, pol, params, report);
                }
            }
            // `Type[T]` is covariant in `T`.
            Type::TypeOf(t) => self.variance_walk(t, pol, params, report),
            Type::Proc(recv, ps, r, _) => {
                if let Some(recv) = recv {
                    self.variance_walk(recv, -pol, params, report);
                }
                for p in ps {
                    self.variance_walk(p, -pol, params, report);
                }
                self.variance_walk(r, pol, params, report);
            }
            _ => {}
        }
    }

    /// The file a pending declaration is in (a cog's root module is in
    /// all of the cog's files).
    fn pending_file(&self, p: &PendingClass<'ast>) -> u32 {
        match p.def {
            PendingDef::CogRoot(file) => file,
            _ => self.world.class(p.id).file,
        }
    }

    /// A class that includes `Shareable`, or inherits it, must be
    /// Shareable by its fields: the promise covers every subclass, so
    /// that a value of a Shareable type is one whatever its class.
    fn check_shareable_promise(&mut self, id: ClassId) {
        let Some(via) = self.world.shareable_promise(id) else {
            return;
        };
        if self.world.class(id).kind == ClassKind::Module {
            return;
        }
        let Some(why) = self.world.shareable_violation(id) else {
            return;
        };
        let class = self.world.class(id);
        let promise = if via == id {
            "it includes `Shareable`".to_string()
        } else {
            format!("`{}` includes `Shareable`", self.world.class(via).name)
        };
        let message = format!(
            "`{}` must be Shareable, since {promise}, but {why}",
            class.name
        );
        let span = class.span;
        self.error(message, span);
    }

    /// A class defining `==` defines `hash` too, and the other way round:
    /// a hash's keys and a set's members are compared by them, and equal
    /// values must hash the same (a warning, as Rust's clippy has).
    fn check_eq_with_hash(&mut self, id: ClassId) {
        let class = self.world.class(id);
        // A module may bring one, the classes including it the other.
        if class.file == 0 || class.kind == ClassKind::Module {
            return;
        }
        let own = |name: &str| {
            class.methods.get(name).and_then(|ms| {
                ms.iter()
                    .copied()
                    .find(|m| !self.world.method(*m).singleton)
            })
        };
        let (eq, hash) = (own("=="), own("hash"));
        let (defined, missing, mid) = match (eq, hash) {
            (Some(m), None) => ("==", "hash", m),
            (None, Some(m)) => ("hash", "==", m),
            _ => return,
        };
        // One inherited with a body (not `Object`'s natives) goes with it.
        let inherited = self
            .world
            .ancestors(id, &[])
            .into_iter()
            .skip(1)
            .any(|(a, _)| {
                self.world.class(a).methods.get(missing).is_some_and(|ms| {
                    ms.iter().any(|m| {
                        let m = self.world.method(*m);
                        !m.singleton && !m.is_native && m.body.is_some()
                    })
                })
            });
        if inherited {
            return;
        }
        let span = self.world.method(mid).span;
        let name = class.name.clone();
        self.warning(
            format!("`{name}` defines `{defined}` but not `{missing}`: as a Hash key or a Set member, equal values must hash the same"),
            span,
        );
    }

    /// Whether instances of `id` are copied by the language or the
    /// implementation, so that a `deinitialize` would run once per copy: a
    /// `data` type, an enum or its variants, a built-in value class, and an
    /// exception class (copied when raised while referred to).
    fn copied_class(&self, id: ClassId) -> bool {
        matches!(
            self.world.class(id).kind,
            ClassKind::Data | ClassKind::Enum | ClassKind::Variant
        ) || self.world.is_value_class(id)
            || id == self.world.builtin.integer
            || self.world.is_exception_class(id)
    }

    /// The `deinitialize` module `ty` brings (itself or a module it
    /// includes), if any, outside the prelude.
    fn deinitializing_module(&self, ty: &Type) -> Option<ClassId> {
        let Type::Class(m, _) = ty else {
            return None;
        };
        let d = self.world.deinitializer(*m)?;
        let dm = self.world.method(d);
        (dm.file != 0).then_some(dm.owner)
    }

    /// A class whose instances are copied (`copied_class`) has no
    /// `deinitialize`, defined or included (a `data` type's or an enum's
    /// own `def` is refused where it is declared): it would run once per
    /// copy (docs/03 §4).
    fn check_copied_deinitialize(&mut self, id: ClassId) {
        if !self.copied_class(id) {
            return;
        }
        let class = self.world.class(id);
        let own = class.methods.get("deinitialize").and_then(|ms| {
            ms.iter()
                .copied()
                .find(|m| !self.world.method(*m).singleton)
        });
        if let Some(m) = own {
            // A data type's or an enum's is an error already.
            if self.world.is_exception_class(id) {
                let span = self.world.method(m).span;
                self.error(
                    "an exception class cannot define `deinitialize`: an exception is copied when raised while referred to, so it would run once per copy",
                    span,
                );
            }
            return;
        }
        let includes = class.includes.clone();
        let span = class.span;
        let name = class.name.clone();
        for inc in &includes {
            if let Some(owner) = self.deinitializing_module(inc) {
                let module = self.world.class(owner).name.clone();
                self.error(
                    format!("`{name}` cannot include `{module}`, which defines `deinitialize`: its values are copied, so it would run once per copy"),
                    span,
                );
                return;
            }
        }
    }

    /// `check_copied_deinitialize` for the modules extensions include: a
    /// copied class as the target, or a module some copied class includes
    /// (the prelude's too: `Exception` includes `Shareable`).
    fn check_extensions_deinitialize(&mut self) {
        for (ext, ty, span, file) in self.ext_includes.clone() {
            let Some(owner) = self.deinitializing_module(&ty) else {
                continue;
            };
            let target = self.world.extensions[ext as usize].target;
            let copied = if self.copied_class(target) {
                Some(target)
            } else {
                (0..self.world.classes.len() as ClassId).find(|&c| {
                    c != target
                        && self.copied_class(c)
                        && self
                            .world
                            .ancestors(c, &[])
                            .iter()
                            .any(|(a, _)| *a == target)
                })
            };
            let Some(copied) = copied else {
                continue;
            };
            self.file = file;
            let target_name = self.world.class(target).name.clone();
            let module = self.world.class(owner).name.clone();
            let message = if copied == target {
                format!("`{target_name}` cannot include `{module}`, which defines `deinitialize`: its values are copied, so it would run once per copy")
            } else {
                let by = self.world.class(copied).name.clone();
                format!("`{target_name}` cannot include `{module}`, which defines `deinitialize`: `{by}` includes `{target_name}`, and its values are copied, so it would run once per copy")
            };
            self.error(message, span);
        }
    }

    /// An extension that makes its target include a Shareable module
    /// promises that the target is Shareable: it must be by its fields.
    fn check_shareable_extensions(&mut self) {
        for (ext, ty, span, file) in std::mem::take(&mut self.ext_includes) {
            let Type::Class(mid, _) = ty else {
                continue;
            };
            if self.world.shareable_promise(mid).is_none() {
                continue;
            }
            let target = self.world.extensions[ext as usize].target;
            if let Some(why) = self.world.shareable_violation(target) {
                self.file = file;
                let message = format!(
                    "`{}` cannot include `{}`, which is Shareable: {why}",
                    self.world.class(target).name,
                    self.world.class(mid).name
                );
                self.error(message, span);
            }
        }
    }

    fn warning(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics
            .push((self.file, Diagnostic::warning(message, span)));
    }

    /// A concrete class must implement every abstract method it inherits
    /// or includes; a class that `extend`s a module must implement the
    /// module's abstract methods on its class side. Including a module
    /// that has no instance methods (a namespace) is pointless, and said
    /// so with a warning.
    /// The declaration-time checks of `classes` again, after a `static`
    /// statement generated members into one of them (docs/14 §5): each
    /// with its descendants and the classes that include it, since what
    /// they inherit changed.
    pub fn recheck_classes(&mut self, classes: &[ClassId]) {
        let mut todo: Vec<ClassId> = Vec::new();
        for &c in classes {
            if !todo.contains(&c) {
                todo.push(c);
            }
        }
        let mut i = 0;
        while i < todo.len() {
            let c = todo[i];
            i += 1;
            for k in &self.world.classes {
                let inherits = k.superclass.iter().chain(&k.includes).chain(&k.extends);
                if inherits
                    .clone()
                    .any(|t| matches!(t, Type::Class(id, _) if *id == c))
                    && !todo.contains(&k.id)
                {
                    todo.push(k.id);
                }
            }
        }
        todo.sort_unstable();
        for id in todo {
            let class = self.world.class(id);
            self.file = class.file;
            // The shareable promise is checked from scratch: a field may
            // have been added.
            self.world.class_mut(id).shareable = None;
            // (Known again at once for a `data` type or enum, which
            // `World::derived_shareable` reads.)
            self.world.ensure_shareable_known(&[id]);
            let file = self.world.class(id).file;
            self.world.active_extensions = self.world.group_extensions(file);
            // A class whose conformance waits for its file's statements
            // (`World::conformance_deferred`, docs/14 §5) is checked once
            // they all ran, not after each: a later one may generate what
            // it still lacks.
            if !self.world.conformance_deferred.contains(&id) {
                self.check_conformance_of(id);
            }
            self.check_shareable_promise(id);
            self.check_variance(id);
            self.check_kept_blocks(id);
            self.check_quoted_overrides(id);
            self.check_override_returns(id);
            self.check_copied_deinitialize(id);
            self.check_eq_with_hash(id);
            self.check_duplicate_methods(id);
            self.world.active_extensions.clear();
        }
    }

    fn check_conformance(&mut self, p: &PendingClass<'ast>) {
        // Namespace modules used as mixins.
        for expr in p.body {
            let ExprKind::Mixin { kind, types } = &expr.kind else {
                continue;
            };
            for t in types {
                let Some(Type::Class(mid, _)) = self.resolve_type_quietly(p.id, t) else {
                    continue;
                };
                let module = self.world.class(mid);
                if module.kind != ClassKind::Module {
                    continue;
                }
                let has_instance_side = !module.methods.is_empty() || !module.includes.is_empty();
                let has_class_side =
                    !module.singleton_methods.is_empty() || !module.members.is_empty();
                if !has_instance_side && has_class_side {
                    let verb = match kind {
                        MixinKind::Include => "including",
                        MixinKind::Extend => "extending",
                    };
                    self.warning(
                        format!(
                            "`{}` has no instance methods, so {verb} it adds nothing; \
                             it is a namespace, use `{}.name` and `{}::Name` instead",
                            module.name, module.name, module.name
                        ),
                        t.span,
                    );
                }
            }
        }
        // A class with `static` statements in an ancestor (itself
        // included) may get the implementations it lacks from them
        // (docs/14 §5): checked after they ran.
        let with_statements: Vec<ClassId> =
            self.world.static_stmts.iter().map(|s| s.class).collect();
        let deferred = !with_statements.is_empty()
            && self
                .world
                .ancestors(p.id, &[])
                .iter()
                .any(|(anc, _)| with_statements.contains(anc));
        if deferred {
            self.world.conformance_deferred.push(p.id);
        } else {
            self.check_conformance_of(p.id);
        }
    }

    /// The conformance of `classes`, deferred when they were declared
    /// (`World::conformance_deferred`), checked now.
    pub fn recheck_conformance(&mut self, classes: &[ClassId]) {
        for &id in classes {
            let class = self.world.class(id);
            self.file = class.file;
            let file = class.file;
            self.world.active_extensions = self.world.group_extensions(file);
            self.check_conformance_of(id);
            self.world.active_extensions.clear();
        }
    }

    /// The conformance of class `id` to what it inherits: the abstract
    /// methods its ancestors leave to it, implemented.
    fn check_conformance_of(&mut self, id: ClassId) {
        let class = self.world.class(id).clone();
        let concrete = match class.kind {
            ClassKind::Class => !class.is_abstract,
            ClassKind::Data | ClassKind::Variant => true,
            ClassKind::Module | ClassKind::Enum | ClassKind::Main => false,
        };
        if concrete {
            // Instance side: abstract methods of ancestors.
            let ancestors: Vec<ClassId> = self
                .world
                .ancestors(id, &[])
                .into_iter()
                .map(|(id, _)| id)
                .collect();
            let mut missing: Vec<(String, ClassId)> = Vec::new();
            let mut impls: Vec<(ClassId, MethodId, MethodId)> = Vec::new();
            for anc in &ancestors {
                for ids in self.world.class(*anc).methods.values() {
                    for mid in ids {
                        let m = self.world.method(*mid);
                        if !m.is_abstract {
                            continue;
                        }
                        match self.implementation(&ancestors, *mid) {
                            None => missing.push((m.name.clone(), *anc)),
                            // An extension's method (active where the class
                            // is declared) implements it: it does wherever
                            // the value goes (`World::ext_impls`).
                            Some(i) if self.world.method(i).extension.is_some() => {
                                impls.push((id, *mid, i));
                            }
                            Some(_) => {}
                        }
                    }
                }
            }
            self.world.ext_impls.extend(impls);
            missing.sort();
            missing.dedup();
            for (name, owner) in missing {
                self.error(
                    format!(
                        "`{}` must implement `{name}` (abstract in `{}`)",
                        class.name,
                        self.world.class(owner).name
                    ),
                    class.span,
                );
            }
        }
        // Class side: abstract methods of extended modules must be
        // implemented as singleton methods (or by another extended module).
        if class.kind != ClassKind::Module {
            let chain = self.world.superclass_chain(id);
            let mut extended: Vec<ClassId> = Vec::new();
            for cid in &chain {
                for ext in &self.world.class(*cid).extends {
                    if let Type::Class(mid, _) = ext {
                        for (anc, _) in self.world.ancestors(*mid, &[]) {
                            if !extended.contains(&anc) {
                                extended.push(anc);
                            }
                        }
                    }
                }
            }
            let mut missing: Vec<(String, ClassId)> = Vec::new();
            for mid in &extended {
                for ids in self.world.class(*mid).methods.values() {
                    for abs in ids {
                        let m = self.world.method(*abs);
                        if !m.is_abstract {
                            continue;
                        }
                        let on_class = chain.iter().any(|cid| {
                            self.world
                                .class(*cid)
                                .singleton_methods
                                .get(&m.name)
                                .is_some_and(|ids| ids.iter().any(|i| self.implements(*i, *abs)))
                        });
                        let on_module = extended.iter().any(|other| {
                            self.world
                                .class(*other)
                                .methods
                                .get(&m.name)
                                .is_some_and(|ids| ids.iter().any(|i| self.implements(*i, *abs)))
                        });
                        if !on_class && !on_module {
                            missing.push((m.name.clone(), *mid));
                        }
                    }
                }
            }
            missing.sort();
            missing.dedup();
            for (name, owner) in missing {
                self.error(
                    format!(
                        "`{}` must implement `self.{name}` (abstract in the extended module `{}`)",
                        class.name,
                        self.world.class(owner).name
                    ),
                    class.span,
                );
            }
        }
    }

    /// Whether a concrete method implementing `abstract_id` exists on one
    /// of `ancestors` (or an active extension of one of them).
    /// The method that implements `abstract_id` for a class with these
    /// ancestors: one of theirs, or an active extension's.
    fn implementation(&self, ancestors: &[ClassId], abstract_id: MethodId) -> Option<MethodId> {
        let name = &self.world.method(abstract_id).name;
        for anc in ancestors {
            if let Some(ids) = self.world.class(*anc).methods.get(name) {
                if let Some(i) = ids.iter().find(|i| self.implements(**i, abstract_id)) {
                    return Some(*i);
                }
            }
            for ext_id in self.world.active_extension_ids() {
                let ext = &self.world.extensions[ext_id as usize];
                if ext.target != *anc {
                    continue;
                }
                if let Some(ids) = ext.methods.get(name) {
                    if let Some(i) = ids.iter().find(|i| self.implements(**i, abstract_id)) {
                        return Some(*i);
                    }
                }
            }
        }
        None
    }

    /// Whether module `m` is `target` or includes it, directly or not
    /// (through the includes resolved so far, its extensions' too, which
    /// have no cycle).
    fn includes_module(&self, m: ClassId, target: ClassId) -> bool {
        let mut todo = vec![m];
        let mut seen: Vec<ClassId> = Vec::new();
        while let Some(c) = todo.pop() {
            if c == target {
                return true;
            }
            if seen.contains(&c) {
                continue;
            }
            seen.push(c);
            let exts = self.world.extensions.iter().filter(|e| e.target == c);
            for t in self
                .world
                .class(c)
                .includes
                .iter()
                .chain(exts.flat_map(|e| e.includes.iter()))
            {
                if let Type::Class(i, _) = t {
                    todo.push(*i);
                }
            }
        }
        false
    }

    /// A concrete method of the same name whose arity covers the abstract
    /// one's counts as its implementation.
    fn implements(&self, candidate: MethodId, abstract_id: MethodId) -> bool {
        let (c, a) = (self.world.method(candidate), self.world.method(abstract_id));
        if c.is_abstract || c.name != a.name {
            return false;
        }
        let (cmin, cmax) = c.positional_arity();
        let (amin, amax) = a.positional_arity();
        cmin <= amin && cmax >= amax && c.block.is_some() == a.block.is_some()
    }

    /// Resolve a type expression without reporting (the mixin was already
    /// resolved, and diagnosed, when the header was built).
    fn resolve_type_quietly(&mut self, class: ClassId, expr: &TypeExpr) -> Option<Type> {
        let before = self.diagnostics.len();
        let scope = self.class_scope(class);
        let t = self.resolve_type(expr, &scope);
        self.diagnostics.truncate(before);
        t
    }

    fn find_builtins(&mut self) {
        let get = |world: &World, name: &str| -> ClassId {
            match world.top.get(name) {
                Some(Member::Class(id)) => *id,
                _ => panic!("prelude does not define `{name}`"),
            }
        };
        let w = &self.world;
        let class_alias = match w.top.get("Class") {
            Some(Member::Alias(id)) => *id,
            _ => panic!("prelude does not define `type Class`"),
        };
        let meta = |name: &str| -> ClassId {
            match w.top.get("Meta") {
                Some(Member::Class(meta)) => match w.class(*meta).members.get(name) {
                    Some(Member::Class(id)) => *id,
                    _ => panic!("prelude does not define `Meta::{name}`"),
                },
                _ => panic!("prelude does not define `Meta`"),
            }
        };
        let meta_classdef = meta("ClassDef");
        let meta_expr = meta("Expr");
        let meta_method_ref = meta("MethodRef");
        let builtin = Builtin {
            class_alias,
            meta_classdef,
            meta_expr,
            meta_method_ref,
            quoted: get(w, "Quoted"),
            object: get(w, "Object"),
            nil: get(w, "Nil"),
            bool_: get(w, "Bool"),
            int: get(w, "Int"),
            integer: get(w, "Integer"),
            float: get(w, "Float"),
            string: get(w, "String"),
            symbol: get(w, "Symbol"),
            array: get(w, "Array"),
            hash: get(w, "Hash"),
            set: get(w, "Set"),
            range: get(w, "Range"),
            regexp: get(w, "Regexp"),
            proc_: get(w, "Proc"),
            kernel: get(w, "Kernel"),
            exception: get(w, "Exception"),
            standard_error: get(w, "StandardError"),
            comparable: get(w, "Comparable"),
            enumerable: get(w, "Enumerable"),
            class_: get(w, "Type"),
            shareable: get(w, "Shareable"),
            task: get(w, "Task"),
            channel: get(w, "Channel"),
            atom: get(w, "Atom"),
            scope: get(w, "Scope"),
            duration: get(w, "Duration"),
            bytes: get(w, "Bytes"),
            time: get(w, "Time"),
            array_builder: 0,
            bytes_builder: 0,
            hash_builder: 0,
            string_builder: 0,
            set_builder: 0,
            match_data: get(w, "MatchData"),
            bytes_match_data: 0,
        };
        self.world.builtin = builtin;
        let nested = |world: &World, outer: ClassId, name: &str| -> ClassId {
            match world.class(outer).members.get(name) {
                Some(Member::Class(id)) => *id,
                _ => panic!(
                    "prelude does not define `{name}` in `{}`",
                    world.class(outer).name
                ),
            }
        };
        self.world.builtin.array_builder = nested(&self.world, self.world.builtin.array, "Builder");
        self.world.builtin.hash_builder = nested(&self.world, self.world.builtin.hash, "Builder");
        self.world.builtin.string_builder =
            nested(&self.world, self.world.builtin.string, "Builder");
        self.world.builtin.set_builder = nested(&self.world, self.world.builtin.set, "Builder");
        self.world.builtin.bytes_builder = nested(&self.world, self.world.builtin.bytes, "Builder");
        self.world.builtin.bytes_match_data =
            nested(&self.world, self.world.builtin.bytes, "MatchData");
    }

    fn class_scope(&self, id: ClassId) -> TypeScope {
        let class = self.world.class(id);
        let params: Vec<(String, TypeParamId)> = class
            .type_params
            .iter()
            .map(|p| (p.name.clone(), p.id))
            .collect();
        TypeScope {
            namespace: Some(id),
            params,
            self_type: None,
        }
    }

    fn resolve_class_header(&mut self, p: &PendingClass<'ast>) {
        let id = p.id;
        let scope = self.class_scope(id);
        // Bounds.
        let type_param_exprs: Option<&Vec<TypeParam>> = match p.def {
            PendingDef::Class(d) => Some(&d.type_params),
            PendingDef::Module(d) => Some(&d.type_params),
            PendingDef::Data(d) => Some(&d.type_params),
            PendingDef::Enum(d) => Some(&d.type_params),
            _ => None,
        };
        if let Some(tps) = type_param_exprs {
            for (i, tp) in tps.iter().enumerate() {
                let bounds: Vec<Type> = tp
                    .bounds
                    .iter()
                    .filter_map(|b| self.resolve_type(b, &scope))
                    .collect();
                if let Some(l) = &tp.lower {
                    self.error(
                        "only a method's type parameters take a lower bound `>:`",
                        l.span,
                    );
                }
                self.world.class_mut(id).type_params[i].bounds = bounds;
            }
        }
        match p.def {
            PendingDef::Class(d) => {
                if let Some(sup) = &d.superclass {
                    if let Some(t) = self.resolve_type(sup, &scope) {
                        // `Type[X]` resolves to the class object of `X`; as
                        // a superclass it is the class `Type` itself, which
                        // only the prelude's `Meta::ClassDef` extends.
                        let class_ = self.world.builtin.class_;
                        let t = match t {
                            Type::TypeOf(inner) => Type::Class(class_, vec![*inner]),
                            Type::ClassObject(c, args) => {
                                Type::Class(class_, vec![Type::Class(c, args)])
                            }
                            t => t,
                        };
                        if matches!(&t, Type::Class(sid, _) if self.world.class_is_a(*sid, class_))
                            && self.world.class(id).file != 0
                        {
                            self.error("cannot inherit from `Type`", sup.span);
                        } else {
                            match &t {
                                Type::Class(sid, _)
                                    if (self.world.is_value_class(*sid)
                                        || *sid == self.world.builtin.integer)
                                        && !(*sid == class_ && self.world.class(id).file == 0) =>
                                {
                                    // Its values are built in: a subclass would
                                    // make objects the runtime cannot use as them.
                                    let name = self.world.class(*sid).name.clone();
                                    self.error(
                                        format!("cannot inherit from the built-in class `{name}`"),
                                        sup.span,
                                    );
                                }
                                Type::Class(sid, _)
                                    if matches!(self.world.class(*sid).kind, ClassKind::Class) =>
                                {
                                    // (The chains set so far have no cycle: one
                                    // through `id` would be closed by this one.)
                                    let mut c = Some(*sid);
                                    let mut cycle = false;
                                    while let Some(k) = c {
                                        if k == id {
                                            cycle = true;
                                            break;
                                        }
                                        c = match &self.world.class(k).superclass {
                                            Some(Type::Class(s, _)) => Some(*s),
                                            _ => None,
                                        };
                                    }
                                    if cycle {
                                        let name = self.world.class(id).name.clone();
                                        self.error(
                                            format!(
                                            "superclass cycle: `{name}` would inherit from itself"
                                        ),
                                            sup.span,
                                        );
                                    } else {
                                        self.world.class_mut(id).superclass = Some(t);
                                    }
                                }
                                Type::Class(sid, _) => {
                                    let class = self.world.class(*sid);
                                    let name = class.name.clone();
                                    let msg = match class.kind {
                                    ClassKind::Data => format!(
                                        "cannot inherit from data type `{name}`: a data type cannot be subclassed (include a module to share behaviour)"
                                    ),
                                    ClassKind::Enum => format!(
                                        "cannot inherit from enum `{name}`: its variants are the ones it declares"
                                    ),
                                    ClassKind::Variant => {
                                        format!("cannot inherit from enum variant `{name}`")
                                    }
                                    ClassKind::Module => format!(
                                        "cannot inherit from module `{name}`: include it instead"
                                    ),
                                    ClassKind::Class | ClassKind::Main => {
                                        format!("cannot inherit from `{name}`")
                                    }
                                };
                                    self.error(msg, sup.span);
                                }
                                _ => self.error("superclass must be a class", sup.span),
                            }
                        }
                    }
                }
            }
            PendingDef::Variant(_) => {
                let enum_id = self.world.class(id).variant_of.unwrap();
                let args: Vec<Type> = self
                    .world
                    .class(enum_id)
                    .type_params
                    .iter()
                    .map(|p| Type::Param(p.id))
                    .collect();
                self.world.class_mut(id).superclass = Some(Type::Class(enum_id, args));
            }
            _ => {}
        }
        if self.world.class(id).superclass.is_none()
            && id != self.world.builtin.object
            && !matches!(self.world.class(id).kind, ClassKind::Module)
        {
            self.world.class_mut(id).superclass = Some(self.world.object());
        }
        // Fields of data/variants come from the header.
        let header_fields: Option<&Vec<FieldDecl>> = match p.def {
            PendingDef::Data(d) => Some(&d.fields),
            PendingDef::Variant(v) => Some(&v.fields),
            _ => None,
        };
        if let Some(fields) = header_fields {
            for f in fields {
                if let Some(ty) = self.resolve_type(&f.ty, &scope) {
                    self.world.class_mut(id).fields.push(FieldInfo {
                        name: f.name.clone(),
                        ty,
                        mutable: false,
                        default: f.default.as_ref().map(|d| Rc::new(d.clone())),
                        baked_default: None,
                        span: f.span,
                    });
                }
            }
        }
        // Body-level items that affect the header: includes and fields.
        for expr in p.body {
            match &expr.kind {
                ExprKind::Mixin { kind, types } => {
                    for t in types {
                        let Some(ty) = self.resolve_type(t, &scope) else {
                            continue;
                        };
                        match &ty {
                            Type::Class(mid, _)
                                if self.world.class(*mid).kind == ClassKind::Module =>
                            {
                                match kind {
                                    MixinKind::Include if self.includes_module(*mid, id) => {
                                        let name = self.world.class(id).name.clone();
                                        self.error(
                                            format!(
                                                "cyclic include: `{name}` would include itself"
                                            ),
                                            t.span,
                                        );
                                    }
                                    MixinKind::Include => {
                                        self.world.class_mut(id).includes.push(ty)
                                    }
                                    MixinKind::Extend => self.world.class_mut(id).extends.push(ty),
                                }
                            }
                            _ => self.error("only modules can be included or extended", t.span),
                        }
                    }
                }
                ExprKind::FieldDecl(f) => {
                    if matches!(
                        self.world.class(id).kind,
                        ClassKind::Data | ClassKind::Variant | ClassKind::Module | ClassKind::Main
                    ) {
                        self.error("fields can only be declared in classes", f.span);
                        continue;
                    }
                    if self.world.class(id).fields.iter().any(|x| x.name == f.name) {
                        self.error(format!("field `@{}` is already declared", f.name), f.span);
                        continue;
                    }
                    if let Some(ty) = self.resolve_type(&f.ty, &scope) {
                        self.world.class_mut(id).fields.push(FieldInfo {
                            name: f.name.clone(),
                            ty,
                            mutable: f.mutable,
                            default: f.default.as_ref().map(|d| Rc::new(d.clone())),
                            baked_default: None,
                            span: f.span,
                        });
                    }
                }
                _ => {}
            }
        }
    }

    fn resolve_extension(&mut self, e: &PendingExtension<'ast>) {
        let ext = &self.world.extensions[e.id as usize];
        let mut scope = TypeScope {
            namespace: e.namespace,
            params: ext
                .type_params
                .iter()
                .map(|p| (p.name.clone(), p.id))
                .collect(),
            self_type: None,
        };
        // Bounds.
        for (i, tp) in e.def.type_params.iter().enumerate() {
            let bounds: Vec<Type> = tp
                .bounds
                .iter()
                .filter_map(|b| self.resolve_type(b, &scope))
                .collect();
            if let Some(l) = &tp.lower {
                self.error(
                    "only a method's type parameters take a lower bound `>:`",
                    l.span,
                );
            }
            self.world.extensions[e.id as usize].type_params[i].bounds = bounds;
        }
        let Some(target) = self.resolve_type(&e.def.target, &scope) else {
            return;
        };
        let Type::Class(tid, targs) = target else {
            self.error(
                "an extension target must be a class or module",
                e.def.target.span,
            );
            return;
        };
        scope.self_type = Some(Type::Class(tid, targs.clone()));
        self.world.extensions[e.id as usize].target = tid;
        self.world.extensions[e.id as usize].target_args = targs;
        for expr in &e.def.body {
            if let ExprKind::Mixin {
                kind: MixinKind::Include,
                types,
            } = &expr.kind
            {
                for t in types {
                    if let Some(ty) = self.resolve_type(t, &scope) {
                        if let Type::Class(mid, _) = &ty {
                            if self.includes_module(*mid, tid) {
                                let name = self.world.class(tid).name.clone();
                                self.error(
                                    format!("cyclic include: `{name}` would include itself"),
                                    t.span,
                                );
                                continue;
                            }
                        }
                        self.ext_includes
                            .push((e.id, ty.clone(), t.span, self.file));
                        self.world.extensions[e.id as usize].includes.push(ty);
                    }
                }
            }
        }
    }

    fn resolve_class_members(&mut self, p: &PendingClass<'ast>) {
        let id = p.id;
        let class_self = {
            let class = self.world.class(id);
            Type::Class(
                id,
                class
                    .type_params
                    .iter()
                    .map(|tp| Type::Param(tp.id))
                    .collect(),
            )
        };
        let mut scope = self.class_scope(id);
        scope.self_type = None; // `self` in signatures is the SELF_PARAM marker
        let mut visibility = Visibility::Public;
        let is_main = matches!(p.def, PendingDef::Main);
        if is_main {
            visibility = Visibility::Private;
        }
        // In a library cog's file, `def self.name` is a method of the
        // cog's root module and every other top-level method is the file's.
        let cog_root = matches!(p.def, PendingDef::CogRoot(_));
        let in_cog_file = is_main && self.world.cog_root(Some(id)).is_some();
        if cog_root {
            visibility = Visibility::Public;
        }
        for expr in p.body {
            if cog_root || in_cog_file {
                let singleton = matches!(&expr.kind, ExprKind::MethodDef(def) if def.singleton);
                if singleton != cog_root {
                    continue;
                }
            }
            match &expr.kind {
                ExprKind::MethodDef(def) => {
                    let vis = def.visibility.unwrap_or(visibility);
                    self.declare_method(id, None, def, vis, &scope, &class_self);
                }
                ExprKind::Visibility {
                    visibility: v,
                    names,
                } => {
                    if names.is_empty() {
                        visibility = *v;
                    } else {
                        for name in names {
                            let ids = self
                                .world
                                .class(id)
                                .methods
                                .get(name)
                                .cloned()
                                .unwrap_or_default();
                            if ids.is_empty() {
                                self.error(format!("undefined method `{name}`"), expr.span);
                            }
                            for mid in ids {
                                self.world.method_mut(mid).visibility = *v;
                            }
                        }
                    }
                }
                ExprKind::AttrDecl { kind, names } => {
                    for name in names {
                        let Some((field, _)) = self.world.find_field(id, name) else {
                            self.error(format!("no field `@{name}` for the accessor"), expr.span);
                            continue;
                        };
                        if matches!(kind, AttrKind::Reader | AttrKind::Accessor) {
                            self.add_synthetic(
                                id,
                                name.clone(),
                                vec![],
                                field.ty.clone(),
                                Synth::FieldGet(name.clone()),
                                expr.span,
                                visibility,
                            );
                        }
                        if matches!(kind, AttrKind::Writer | AttrKind::Accessor) {
                            if !field.mutable {
                                self.error(format!("`@{name}` is immutable; declare it with `var` to add a writer"), expr.span);
                                continue;
                            }
                            let param = ParamInfo {
                                name: "value".to_string(),
                                kind: ParamKind::Positional,
                                ty: field.ty.clone(),
                                default: None,
                                assigns_ivar: false,
                                span: expr.span,
                            };
                            self.add_synthetic(
                                id,
                                format!("{name}="),
                                vec![param],
                                field.ty.clone(),
                                Synth::FieldSet(name.clone()),
                                expr.span,
                                visibility,
                            );
                        }
                    }
                }
                ExprKind::Alias { new_name, old_name } => {
                    self.check_sealed(self.world.class(id).file, new_name, expr.span);
                    // An alias named `initialize` would skip definite
                    // assignment, and one of `initialize` would run it on
                    // a built object, assigning its immutable fields again.
                    if new_name == "initialize" || old_name == "initialize" {
                        self.error(
                            "`initialize` cannot be aliased: it runs only from `new` and `super`",
                            expr.span,
                        );
                        continue;
                    }
                    let ids = self
                        .world
                        .class(id)
                        .methods
                        .get(old_name)
                        .cloned()
                        .unwrap_or_default();
                    if ids.is_empty() {
                        self.error(
                            format!("undefined method `{old_name}` for alias"),
                            expr.span,
                        );
                    }
                    for mid in ids {
                        let mut info = self.world.method(mid).clone();
                        info.name = new_name.clone();
                        info.alias_of = Some(mid);
                        // Its errors (a duplicate, an override) are the
                        // `alias` line's.
                        info.span = expr.span;
                        info.file = self.file;
                        if !info.singleton {
                            self.check_equality_params(
                                new_name,
                                &info.params,
                                info.block.is_some(),
                                expr.span,
                            );
                        }
                        self.world.add_method(info);
                    }
                }
                _ => {}
            }
        }
        // Generated methods for data types and enum variants.
        if matches!(p.def, PendingDef::Data(_) | PendingDef::Variant(_)) {
            self.declare_data_methods(
                id,
                class_self.clone(),
                p.body
                    .first()
                    .map(|e| e.span)
                    .unwrap_or(self.world.class(id).span),
            );
        }
    }

    fn resolve_extension_members(&mut self, e: &PendingExtension<'ast>) {
        let ext = &self.world.extensions[e.id as usize];
        let target_self = Type::Class(ext.target, ext.target_args.clone());
        let scope = TypeScope {
            namespace: e.namespace,
            params: ext
                .type_params
                .iter()
                .map(|p| (p.name.clone(), p.id))
                .collect(),
            self_type: None,
        };
        let target = ext.target;
        for expr in &e.def.body {
            match &expr.kind {
                ExprKind::MethodDef(def) => {
                    let vis = def.visibility.unwrap_or(Visibility::Public);
                    self.declare_method(target, Some(e.id), def, vis, &scope, &target_self);
                }
                ExprKind::Mixin {
                    kind: MixinKind::Include,
                    ..
                } => {}
                _ => self.error(
                    "only methods and `include` are allowed in an extension",
                    expr.span,
                ),
            }
        }
    }

    /// `nil?` and `is_a?` are the prelude's only: the checker narrows
    /// types by them, and lowering relies on them, so a definition of its
    /// own (a method, an alias, a data field's reader) would make both
    /// wrong. `equal?` is identity, the one comparison a class cannot
    /// change.
    fn check_sealed(&mut self, file: u32, name: &str, span: Span) {
        if file == 0 {
            return;
        }
        if let Some(message) = sealed_name(name) {
            self.error(message, span);
        }
    }

    /// `==` and `!=` take one parameter, an `Object`: the runtime calls a
    /// class's own by name with any value (`x == y` with an operand typed
    /// `Object`, `Array#==`, `case`/`when`), so one taking less would
    /// receive a value not of its type. A method of another signature is not an override
    /// of `Object#==` but an overload, which the check for an `Object`
    /// parameter rules out as well.
    fn check_equality_params(&mut self, name: &str, params: &[ParamInfo], block: bool, span: Span) {
        if self.file == 0 {
            return;
        }
        if let Some(message) = equality_params_rule(&self.world, name, params, block) {
            self.error(message, span);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn add_synthetic(
        &mut self,
        owner: ClassId,
        name: String,
        params: Vec<ParamInfo>,
        ret: Type,
        synth: Synth,
        span: Span,
        visibility: Visibility,
    ) {
        self.check_sealed(self.world.class(owner).file, &name, span);
        self.world.add_method(MethodInfo {
            id: 0,
            name,
            owner,
            singleton: false,
            type_params: Vec::new(),
            params,
            block: None,
            block_optional: false,
            block_usings: Vec::new(),
            ret,
            body: None,
            is_abstract: false,
            is_native: true,
            is_static: false,
            visibility,
            span,
            extension: None,
            frame_size: 0,
            checked: true,
            synth,
            alias_of: None,
            generated: None,
            file: self.file,
        });
    }

    /// The methods a data type generates: defaults, each left out when
    /// the body defines a method of its name (docs/01 §4), or for an enum
    /// variant, when the enum's body does (§5).
    fn declare_data_methods(&mut self, id: ClassId, class_self: Type, span: Span) {
        let fields = self.world.class(id).fields.clone();
        let enum_id = self.world.class(id).variant_of;
        // (A variant keeps its own `initialize`: the enum's cannot assign
        // the variant's fields.)
        let own = |s: &Self, name: &str| {
            s.world.class(id).methods.contains_key(name)
                || name != "initialize"
                    && enum_id.is_some_and(|e| s.world.class(e).methods.contains_key(name))
        };
        // Readers.
        for f in &fields {
            if own(self, &f.name) {
                continue;
            }
            self.add_synthetic(
                id,
                f.name.clone(),
                vec![],
                f.ty.clone(),
                Synth::FieldGet(f.name.clone()),
                f.span,
                Visibility::Public,
            );
        }
        let own_init = own(self, "initialize");
        if !own_init {
            self.declare_data_init(id, &fields, span);
        }
        // `with` builds its value through `initialize`: the generated one,
        // or the body's when it takes the fields, in order. With another
        // `initialize` there is none (the body may define its own).
        let init_takes_fields = |s: &Self| {
            s.world
                .class(id)
                .methods
                .get("initialize")
                .is_some_and(|ms| {
                    ms.iter().any(|m| {
                        let ps = &s.world.method(*m).params;
                        ps.len() == fields.len()
                            && ps.iter().zip(&fields).all(|(p, f)| {
                                p.kind == ParamKind::Positional
                                    && p.name == f.name
                                    && s.world.same_type(&p.ty, &f.ty)
                            })
                    })
                })
        };
        if !own(self, "with") && (!own_init || init_takes_fields(self)) {
            self.declare_data_with(id, &fields, class_self, span);
        }
        if !own(self, "to_h") {
            let to_h = self.world.hash_of(self.world.symbol(), self.world.object());
            self.add_synthetic(
                id,
                "to_h".to_string(),
                vec![],
                to_h,
                Synth::DataToH,
                span,
                Visibility::Public,
            );
        }
    }

    /// initialize(field..., positional or keyword)
    fn declare_data_init(&mut self, id: ClassId, fields: &[FieldInfo], span: Span) {
        let params: Vec<ParamInfo> = fields
            .iter()
            .map(|f| ParamInfo {
                name: f.name.clone(),
                kind: ParamKind::Positional,
                ty: f.ty.clone(),
                default: f.default.clone(),
                assigns_ivar: true,
                span: f.span,
            })
            .collect();
        self.add_synthetic(
            id,
            "initialize".to_string(),
            params,
            Type::Void,
            Synth::DataInit,
            span,
            Visibility::Public,
        );
    }

    /// with(field: value = current, ...)
    fn declare_data_with(
        &mut self,
        id: ClassId,
        fields: &[FieldInfo],
        class_self: Type,
        span: Span,
    ) {
        let with_params: Vec<ParamInfo> = fields
            .iter()
            .map(|f| ParamInfo {
                name: f.name.clone(),
                kind: ParamKind::KeywordOnly,
                ty: f.ty.clone(),
                default: Some(Rc::new(Expr {
                    id: u32::MAX,
                    span: f.span,
                    kind: ExprKind::Nil,
                })),
                assigns_ivar: false,
                span: f.span,
            })
            .collect();
        self.add_synthetic(
            id,
            "with".to_string(),
            with_params,
            class_self,
            Synth::DataWith,
            span,
            Visibility::Public,
        );
    }

    fn declare_method(
        &mut self,
        owner: ClassId,
        extension: Option<ExtensionId>,
        def: &MethodDef,
        visibility: Visibility,
        class_scope: &TypeScope,
        class_self: &Type,
    ) {
        self.check_sealed(self.file, &def.name, def.span);
        // An extension's `initialize` would make objects its target's
        // `new` in an inherited class method does not (docs/01 §7).
        if def.name == "initialize" && !def.singleton && extension.is_some() {
            self.error(
                "an extension cannot define `initialize`: objects are made by their class's own",
                def.span,
            );
        }
        // An enum has no fields, and its variants their own `initialize`
        // (docs/01 §5).
        if def.name == "initialize"
            && !def.singleton
            && extension.is_none()
            && self.world.class(owner).kind == ClassKind::Enum
        {
            self.error(
                "an enum cannot define `initialize`: its variants make their own values",
                def.span,
            );
        }
        let type_params: Vec<TypeParamInfo> = self.new_type_params(&def.type_params);
        let mut scope = class_scope.with_params(&type_params);
        scope.self_type = None;
        let _ = class_self;
        let mut type_params = type_params;
        for (i, tp) in def.type_params.iter().enumerate() {
            type_params[i].bounds = tp
                .bounds
                .iter()
                .filter_map(|b| self.resolve_type(b, &scope))
                .collect();
            type_params[i].lower = tp.lower.as_ref().and_then(|l| self.resolve_type(l, &scope));
            if let Some(l) = &type_params[i].lower {
                self.world.lower_bounds.insert(type_params[i].id, l.clone());
            }
        }
        let mut params = Vec::new();
        let mut block = None;
        let mut block_optional = false;
        let mut block_usings: Vec<ExtensionId> = Vec::new();
        for p in &def.params.list {
            if let Some(span) = p.ty.as_ref().and_then(|t| self_against_variance(t, false)) {
                self.error(
                    "`Self` cannot be the type of a value the caller passes in (a parameter, or a block's result): a subclass would receive values of its parent; use a type parameter instead (`module M[T]` with `other: T`)",
                    span,
                );
            }
            if p.kind == ParamKind::Block {
                for path in &p.usings {
                    if let Some(found) = self.resolve_using(scope.namespace, path, p.span) {
                        block_usings.extend(found);
                    }
                }
                match &p.ty {
                    Some(t) => {
                        if let Some(mut ty) = self.resolve_type(t, &scope) {
                            let nil = self.world.builtin.nil;
                            if let Type::Union(ms) = &ty {
                                if let [Type::Proc(..), Type::Class(c, _)]
                                | [Type::Class(c, _), Type::Proc(..)] = ms.as_slice()
                                {
                                    if *c == nil {
                                        block_optional = true;
                                        ty = ty.without_nil(nil);
                                    }
                                }
                            }
                            // `Quoted[P]`: the block as a tree (docs/14 §6).
                            let quoted = matches!(&ty, Type::Class(c, args)
                                if *c == self.world.builtin.quoted
                                    && matches!(args.as_slice(), [Type::Proc(..)]));
                            if !matches!(ty, Type::Proc(..)) && !quoted {
                                self.error(
                                    "a block parameter must have a procedure type `(A) -> R` (or `Quoted[(A) -> R]`)",
                                    t.span,
                                );
                            }
                            block = Some((p.name.clone(), ty));
                        }
                    }
                    None => self.error(
                        "a block parameter needs a type, e.g. `&block: (Int) -> Void`",
                        p.span,
                    ),
                }
                continue;
            }
            let ty = match &p.ty {
                Some(t) => self.resolve_type(t, &scope).unwrap_or(Type::Nothing),
                None => match &p.default {
                    Some(d) => match self.literal_type(d) {
                        Some(t) => t,
                        None => {
                            self.error(
                                format!("parameter `{}` needs a type annotation", p.name),
                                p.span,
                            );
                            Type::Nothing
                        }
                    },
                    None => {
                        self.error(
                            format!("parameter `{}` needs a type annotation", p.name),
                            p.span,
                        );
                        Type::Nothing
                    }
                },
            };
            let ty = match p.kind {
                ParamKind::Rest => self.world.array_of(ty),
                ParamKind::KeywordRest => self.world.hash_of(self.world.symbol(), ty),
                _ => ty,
            };
            if p.assigns_ivar && self.world.find_field(owner, &p.name).is_none() {
                self.error(format!("no field `@{}` to assign", p.name), p.span);
            }
            params.push(ParamInfo {
                name: p.name.clone(),
                kind: p.kind,
                ty,
                default: p.default.as_ref().map(|d| Rc::new(d.clone())),
                assigns_ivar: p.assigns_ivar,
                span: p.span,
            });
        }
        let ret = match &def.ret {
            Some(t) => self.resolve_result_type(t, &scope).unwrap_or(Type::Nothing),
            None if def.name == "initialize" || def.name == "deinitialize" => Type::Void,
            None if def.is_abstract || def.is_native => {
                self.error("abstract and native methods need a return type", def.span);
                Type::Void
            }
            // Return types are declared, not inferred: without one, a
            // method is `-> Void` (its body's value is discarded and it
            // returns nil).
            None => Type::Void,
        };
        if def.is_abstract
            && !self.world.class(owner).is_abstract
            && self.world.class(owner).kind != ClassKind::Module
        {
            self.error(
                "abstract methods are only allowed in abstract classes and modules",
                def.span,
            );
        }
        if let Some(message) = logical_operator_rule(
            &self.world,
            &def.name,
            def.singleton,
            def.params.list.len(),
            block.as_ref().map(|(_, t)| t),
            owner,
        ) {
            self.error(message, def.span);
        }
        if !def.singleton {
            self.check_equality_params(&def.name, &params, block.is_some(), def.span);
        }
        if def.name == "deinitialize" && !def.singleton {
            // Run by the runtime when an instance's last reference goes.
            if !def.params.list.is_empty() || block.is_some() {
                self.error("`deinitialize` takes no parameters", def.span);
            }
            let kind = self.world.class(owner).kind;
            if extension.is_some()
                || self.world.is_value_class(owner)
                || !matches!(kind, ClassKind::Class | ClassKind::Module)
            {
                self.error(
                    "`deinitialize` can only be defined in a class or module (not a built-in value class, `data` type, enum or extension)",
                    def.span,
                );
            }
        }
        self.world.add_method(MethodInfo {
            id: 0,
            name: def.name.clone(),
            owner,
            singleton: def.singleton,
            type_params,
            params,
            block,
            block_optional,
            block_usings,
            ret,
            body: def.body.as_ref().map(|_| Rc::new(def.clone())),
            is_abstract: def.is_abstract,
            is_native: def.is_native,
            is_static: def.is_static,
            visibility,
            span: def.span,
            extension,
            frame_size: 0,
            checked: def.is_native || def.is_abstract,
            synth: Synth::None,
            alias_of: None,
            generated: None,
            file: self.file,
        });
    }

    fn literal_type(&self, expr: &Expr) -> Option<Type> {
        Some(match &expr.kind {
            ExprKind::Int(lit) if lit.value.is_none() => self.world.integer(),
            ExprKind::Int(_) => self.world.int(),
            ExprKind::Float(_) => self.world.float(),
            ExprKind::Str(_) => self.world.string(),
            ExprKind::Bytes(_) => Type::class(self.world.builtin.bytes),
            ExprKind::Symbol(_) => self.world.symbol(),
            ExprKind::True | ExprKind::False => self.world.bool_(),
            _ => return None,
        })
    }

    fn resolve_usings(&mut self) {
        #[allow(clippy::type_complexity)]
        let unit_usings: Vec<(u32, ClassId, Vec<(&'ast ConstPath, u32)>)> = self
            .units
            .iter_mut()
            .map(|u| (u.file, u.main, std::mem::take(&mut u.usings)))
            .collect();
        for (file, main, paths) in unit_usings {
            self.file = file;
            let mut ids = Vec::new();
            for (path, pos) in paths {
                if let Some(found) = self.resolve_using(None, path, Span::empty(0)) {
                    ids.extend(found.into_iter().map(|e| (pos, e)));
                }
            }
            self.world.class_mut(main).usings.extend(ids);
        }
        let per_class = std::mem::take(&mut self.class_usings);
        for (cid, paths) in per_class {
            let mut ids = Vec::new();
            for (path, pos) in paths {
                if let Some(found) = self.resolve_using(Some(cid), path, Span::empty(0)) {
                    ids.extend(found.into_iter().map(|e| (pos, e)));
                }
            }
            self.world.class_mut(cid).usings = ids;
        }
    }

    fn resolve_using(
        &mut self,
        namespace: Option<ClassId>,
        path: &ConstPath,
        span: Span,
    ) -> Option<Vec<ExtensionId>> {
        match self.resolve_path(namespace, path, span) {
            Some(Member::Class(id)) if self.world.class(id).kind == ClassKind::Module => {
                Some(self.world.class(id).extensions.clone())
            }
            _ => {
                self.error(format!("`using {path}`: not a module"), span);
                None
            }
        }
    }

    // ----- type expressions ----------------------------------------------------

    pub fn resolve_path(
        &mut self,
        namespace: Option<ClassId>,
        path: &ConstPath,
        span: Span,
    ) -> Option<Member> {
        let mut member = if path.cog {
            match self.world.resolve_cog_path_start(namespace, path) {
                Ok(m) => Some(m),
                Err(message) => {
                    self.error(message, span);
                    return None;
                }
            }
        } else if path.absolute {
            self.world.top.get(&path.names[0]).copied()
        } else {
            self.world.resolve_member(namespace, &path.names[0])
        };
        if member.is_none() {
            self.error(format!("unknown constant `{}`", path.names[0]), span);
            return None;
        }
        for name in path.names.get(1..).unwrap_or_default() {
            let Some(Member::Class(cid)) = member.map(|m| self.world.through_alias(m)) else {
                self.error(format!("`{}` is not a namespace", path), span);
                return None;
            };
            member = self.world.member_in(Some(cid), name);
            if member.is_none() {
                // Inherited members (e.g. constants of a superclass).
                for (anc, _) in self.world.ancestors(cid, &[]) {
                    if let Some(m) = self.world.class(anc).members.get(name) {
                        member = Some(*m);
                        break;
                    }
                }
            }
            if member.is_none() {
                self.error(
                    format!(
                        "unknown constant `{name}` in `{}`",
                        self.world.class(cid).name
                    ),
                    span,
                );
                return None;
            }
        }
        member
    }

    /// A result type: a method's or a procedure type's, the only places
    /// `Void` may be written.
    pub fn resolve_result_type(&mut self, expr: &TypeExpr, scope: &TypeScope) -> Option<Type> {
        match expr.kind {
            TypeExprKind::Void => Some(Type::Void),
            _ => self.resolve_type(expr, scope),
        }
    }

    /// The type parameters `tps` declare (`Self`, `Void` and `Nothing`
    /// cannot name one).
    fn new_type_params(&mut self, tps: &[TypeParam]) -> Vec<TypeParamInfo> {
        tps.iter()
            .map(|tp| {
                if let Some(msg) = quarz_syntax::reserved_type_name(&tp.name) {
                    self.error(msg, tp.span);
                }
                self.world.new_type_param(&tp.name, tp.variance)
            })
            .collect()
    }

    pub fn resolve_type(&mut self, expr: &TypeExpr, scope: &TypeScope) -> Option<Type> {
        match &expr.kind {
            TypeExprKind::Nothing => Some(Type::Nothing),
            TypeExprKind::Void => {
                self.error(
                    "`Void` is only a result type (`-> Void`, `(A) -> Void`): a value's type is `Nil`",
                    expr.span,
                );
                Some(self.world.nil())
            }
            TypeExprKind::SelfType => {
                Some(scope.self_type.clone().unwrap_or(Type::Param(SELF_PARAM)))
            }
            TypeExprKind::Nilable(inner) => {
                let t = self.resolve_type(inner, scope)?;
                Some(self.world.nilable(t))
            }
            TypeExprKind::Union(members) => {
                let mut out = Vec::new();
                for m in members {
                    out.push(self.resolve_type(m, scope)?);
                }
                Some(self.world.simplify_union(Type::union_of(out)))
            }
            TypeExprKind::Tuple(items) => {
                let mut out = Vec::new();
                for i in items {
                    out.push(self.resolve_type(i, scope)?);
                }
                Some(Type::Tuple(out))
            }
            TypeExprKind::Proc {
                recv,
                params,
                ret,
                shareable,
            } => {
                let rc = match recv {
                    Some(t) => Some(Box::new(self.resolve_type(t, scope)?)),
                    None => None,
                };
                let mut ps = Vec::new();
                for p in params {
                    ps.push(self.resolve_type(p, scope)?);
                }
                let r = self.resolve_result_type(ret, scope)?;
                Some(Type::Proc(rc, ps, Box::new(r), *shareable))
            }
            TypeExprKind::Named { path, args } => {
                // A type parameter in scope?
                if path.names.len() == 1 && !path.absolute && !path.cog {
                    if let Some((_, id)) =
                        scope.params.iter().rev().find(|(n, _)| *n == path.names[0])
                    {
                        if !args.is_empty() {
                            self.error("type parameters cannot take arguments", expr.span);
                        }
                        return Some(Type::Param(*id));
                    }
                }
                let member = self.resolve_path(scope.namespace, path, expr.span)?;
                let member = self.world.through_alias(member);
                let mut resolved_args = Vec::new();
                for a in args {
                    resolved_args.push(self.resolve_type(a, scope)?);
                }
                match member {
                    // `Type[X]`: the class object of `X`, which must be a
                    // class (`Type[Point]`) or a type parameter (`Type[T]`).
                    Member::Class(id) if id == self.world.builtin.class_ => {
                        if resolved_args.len() > 1 {
                            self.error("`Type` takes at most 1 type argument", expr.span);
                            return None;
                        }
                        // `Type` alone is `Type[Object]`, any class.
                        let inner = resolved_args
                            .pop()
                            .unwrap_or_else(|| Type::class(self.world.builtin.object));
                        match inner {
                            Type::Class(..) | Type::Param(_) | Type::Var(_) => {
                                Some(Type::type_of(inner))
                            }
                            _ => {
                                self.error(
                                    format!(
                                        "`Type[{}]`: the argument must be a class or a type parameter",
                                        self.world.type_name(&inner)
                                    ),
                                    expr.span,
                                );
                                None
                            }
                        }
                    }
                    Member::Class(id) => {
                        let class = self.world.class(id);
                        if class.type_params.len() != resolved_args.len() {
                            self.error(
                                format!(
                                    "`{}` takes {} type argument(s), {} given",
                                    class.name,
                                    class.type_params.len(),
                                    resolved_args.len()
                                ),
                                expr.span,
                            );
                            return None;
                        }
                        Some(Type::Class(id, resolved_args))
                    }
                    Member::Alias(aid) => {
                        let alias = self.world.aliases[aid as usize].clone();
                        if alias.type_params.len() != resolved_args.len() {
                            self.error(
                                format!(
                                    "type alias `{}` takes {} argument(s)",
                                    alias.name,
                                    alias.type_params.len()
                                ),
                                expr.span,
                            );
                            return None;
                        }
                        let inner_scope = TypeScope {
                            namespace: alias.owner,
                            params: alias
                                .type_params
                                .iter()
                                .map(|p| (p.name.clone(), p.id))
                                .collect(),
                            self_type: scope.self_type.clone(),
                        };
                        let body = self.resolve_type(&alias.expr, &inner_scope)?;
                        let map: HashMap<TypeParamId, Type> = alias
                            .type_params
                            .iter()
                            .map(|p| p.id)
                            .zip(resolved_args)
                            .collect();
                        Some(body.subst(&map))
                    }
                    Member::Const(_) => {
                        self.error(format!("`{path}` is a constant, not a type"), expr.span);
                        None
                    }
                }
            }
        }
    }
}

/// Where `Self` appears in a contravariant position of `t`,
/// `t` itself being in a covariant position when `covariant`: a method
/// parameter is contravariant, the parameters of a procedure type flip
/// the position and its result keeps it. `&: (Self) -> Void` (the method
/// hands `self` to the block) is fine; `other: Self` and `&: () -> Self`
/// (the caller hands one in) are not.
fn self_against_variance(t: &TypeExpr, covariant: bool) -> Option<Span> {
    match &t.kind {
        TypeExprKind::SelfType => (!covariant).then_some(t.span),
        TypeExprKind::Named { args, .. } => args
            .iter()
            .find_map(|a| self_against_variance(a, covariant)),
        TypeExprKind::Nilable(inner) => self_against_variance(inner, covariant),
        TypeExprKind::Union(ts) | TypeExprKind::Tuple(ts) => {
            ts.iter().find_map(|a| self_against_variance(a, covariant))
        }
        TypeExprKind::Proc {
            recv, params, ret, ..
        } => recv
            .iter()
            .map(|r| &**r)
            .chain(params.iter())
            .find_map(|a| self_against_variance(a, !covariant))
            .or_else(|| self_against_variance(ret, covariant)),
        TypeExprKind::Nothing | TypeExprKind::Void => None,
    }
}

/// `nil?`, `is_a?` and `equal?` cannot be redefined by a program: why,
/// when `name` is one.
fn sealed_name(name: &str) -> Option<String> {
    let why = match name {
        "nil?" | "is_a?" => "types are narrowed by it",
        "equal?" => "it is identity",
        _ => return None,
    };
    Some(format!("`{name}` cannot be redefined: {why}"))
}

/// `==` and `!=` take one parameter, an `Object`: the runtime calls a
/// class's own by name with any value (`x == y` with an operand typed
/// `Object`, `Array#==`, `case`/`when`), so one taking less would
/// receive a value not of its type. A method of another signature is not an override
/// of `Object#==` but an overload, which the check for an `Object`
/// parameter rules out as well.
fn equality_params_rule(
    world: &World,
    name: &str,
    params: &[ParamInfo],
    block: bool,
) -> Option<String> {
    if !matches!(name, "==" | "!=") {
        return None;
    }
    let one_object = match params {
        [p] => p.kind == ParamKind::Positional && p.default.is_none() && world.is_object(&p.ty),
        _ => false,
    };
    (!one_object || block).then(|| {
    format!(
        "`{name}` takes one parameter of type `Object`: it is called with any value (`x == y` with an operand typed `Object`, `Array#==`, `case`/`when`); test the class in the body (`other.is_a?(Foo) && ...`)"
    )
})
}

/// `&&` and `||` are called as `a && b` with `b` as the block: the
/// method decides whether `b` is evaluated. So they take only a block
/// without parameters, and not on Bool or Nil, whose own are the
/// language's.
fn logical_operator_rule(
    world: &World,
    name: &str,
    singleton: bool,
    nparams: usize,
    block: Option<&Type>,
    owner: ClassId,
) -> Option<String> {
    if name != "&&" && name != "||" {
        return None;
    }
    let only_block =
        nparams == 1 && matches!(block, Some(Type::Proc(_, ps, _, _)) if ps.is_empty());
    if !only_block || singleton {
        return Some(format!(
        "`{name}` takes only a block with no parameters, the right operand (`def {name}(&: () -> T) -> R`)"
    ));
    }
    let b = &world.builtin;
    (owner == b.bool_ || owner == b.nil)
        .then(|| format!("`{name}` cannot be defined on Bool or Nil"))
}

/// What a method's name demands of it, for one declared by a program or
/// generated at compile time (docs/14 §5): the rules above, and that the
/// constructor and destructor names are written (their bodies are held
/// to rules of their own, docs/03 §4).
pub fn method_name_rule(
    world: &World,
    name: &str,
    singleton: bool,
    params: &[ParamInfo],
    block: Option<&Type>,
    owner: ClassId,
) -> Option<String> {
    let special = if singleton {
        matches!(name, "new" | "allocate")
    } else {
        matches!(name, "initialize" | "deinitialize")
    };
    if special {
        return Some(format!("`{name}` cannot be generated"));
    }
    if !singleton {
        if let Some(m) = sealed_name(name) {
            return Some(m);
        }
        if let Some(m) = equality_params_rule(world, name, params, block.is_some()) {
            return Some(m);
        }
    }
    // A generated method's block parameter would be a `&block` of the
    // block: refused before, so `nparams` is the parameters' count.
    logical_operator_rule(
        world,
        name,
        singleton,
        params.len() + usize::from(block.is_some()),
        block,
        owner,
    )
}
