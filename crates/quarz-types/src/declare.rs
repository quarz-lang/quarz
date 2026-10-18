//! Declaration collection (phase 1) and header resolution (phase 2).
//!
//! Phase 1 walks the programs and registers every class, module, data,
//! enum, extension, constant and type alias by name, so that phase 2 can
//! resolve superclasses, includes, field types and method signatures in any
//! order.

use std::collections::HashMap;
use std::rc::Rc;

use quarz_syntax::ast::*;
use quarz_syntax::{Diagnostic, Span};

use crate::types::*;
use crate::world::*;

/// Reserved type parameter id standing for the receiver's type in method
/// signatures (`-> self`).
pub const SELF_PARAM: TypeParamId = u32::MAX;

/// A type-expression resolution scope.
#[derive(Clone, Debug, Default)]
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
    class_usings: HashMap<ClassId, Vec<&'ast ConstPath>>,
    builtins_resolved: bool,
}

/// A file's top-level: its pseudo-class for top-level methods, its
/// statements and its `using`s.
pub struct UnitDecl<'ast> {
    pub file: u32,
    pub main: ClassId,
    pub body: Vec<&'ast Expr>,
    pub usings: Vec<&'ast ConstPath>,
}

impl<'ast> Declarer<'ast> {
    pub fn new() -> Declarer<'ast> {
        Declarer {
            world: World::new(),
            diagnostics: Vec::new(),
            file: 0,
            pending: Vec::new(),
            pending_ext: Vec::new(),
            units: Vec::new(),
            class_usings: HashMap::new(),
            builtins_resolved: false,
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
        for expr in &program.body {
            self.collect_item(expr, None, true);
        }
    }

    /// Register the declarations of a user file (file index `file`, 1 or
    /// more); its other statements become the unit's body.
    pub fn collect_unit(&mut self, program: &'ast Program, file: u32) {
        self.file = file;
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

    /// Returns whether the expression was a declaration.
    fn collect_item(
        &mut self,
        expr: &'ast Expr,
        namespace: Option<ClassId>,
        prelude: bool,
    ) -> bool {
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
                for variant in &def.variants {
                    let vpath = ConstPath::simple(variant.name.clone());
                    if let Some(vid) =
                        self.declare_named(&vpath, ClassKind::Variant, Some(id), variant.span)
                    {
                        self.world.class_mut(vid).variant_of = Some(id);
                        self.world.class_mut(vid).auto_initialize = true;
                        self.world.class_mut(id).variants.push(vid);
                        self.pending.push(PendingClass {
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
                    methods: HashMap::new(),
                    span: expr.span,
                    always_active: prelude || namespace.is_none(),
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
                let params = type_params
                    .iter()
                    .map(|p| self.world.new_type_param(&p.name, p.variance))
                    .collect();
                let id = self.world.aliases.len() as u32;
                self.world.aliases.push(TypeAliasInfo {
                    name: name.clone(),
                    owner: namespace,
                    type_params: params,
                    expr: ty.clone(),
                    resolved: None,
                });
                self.register_member(namespace, name, Member::Alias(id), expr.span);
            }
            ExprKind::Using(path) => match namespace {
                Some(ns) => self.class_usings.entry(ns).or_default().push(path),
                None => {
                    if let Some(unit) = self.units.last_mut() {
                        unit.usings.push(path);
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

    fn collect_body(&mut self, id: ClassId, body: &'ast [Expr], prelude: bool) {
        for expr in body {
            if !self.collect_item(expr, Some(id), prelude) {
                self.error("only declarations are allowed in a class body", expr.span);
            }
        }
    }

    fn declare_named(
        &mut self,
        path: &ConstPath,
        kind: ClassKind,
        namespace: Option<ClassId>,
        span: Span,
    ) -> Option<ClassId> {
        // `class A::B` nests B in A (A must exist).
        let mut ns = namespace;
        for prefix in &path.names[..path.names.len() - 1] {
            match self.world.resolve_member(ns, prefix) {
                Some(Member::Class(id)) => ns = Some(id),
                _ => {
                    self.error(format!("unknown namespace `{prefix}`"), span);
                    return None;
                }
            }
        }
        let short = path.last().to_string();
        if let Some(existing) = self.world.member_in(ns, &short) {
            match existing {
                Member::Class(id) => {
                    self.error(
                        format!(
                            "`{}` is already defined; classes cannot be reopened (use `extension`)",
                            self.world.class(id).name
                        ),
                        span,
                    );
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

    fn register_member(
        &mut self,
        namespace: Option<ClassId>,
        name: &str,
        member: Member,
        span: Span,
    ) {
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
                PendingDef::Variant(_) | PendingDef::Main => continue,
            };
            let infos: Vec<TypeParamInfo> = params
                .iter()
                .map(|tp| self.world.new_type_param(&tp.name, tp.variance))
                .collect();
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
            let infos: Vec<TypeParamInfo> = e
                .def
                .type_params
                .iter()
                .map(|tp| self.world.new_type_param(&tp.name, tp.variance))
                .collect();
            self.world.extensions[e.id as usize].type_params = infos;
        }

        // Bounds, superclasses, includes, fields and methods.
        for p in &pending {
            self.file = self.world.class(p.id).file;
            self.resolve_class_header(p);
        }
        for e in &pending_ext {
            self.file = e.file;
            self.resolve_extension(e);
        }
        for p in &pending {
            self.file = self.world.class(p.id).file;
            self.resolve_class_members(p);
        }
        for e in &pending_ext {
            self.file = e.file;
            self.resolve_extension_members(e);
        }
        self.resolve_usings();
    }

    fn find_builtins(&mut self) {
        let get = |world: &World, name: &str| -> ClassId {
            match world.top.get(name) {
                Some(Member::Class(id)) => *id,
                _ => panic!("prelude does not define `{name}`"),
            }
        };
        let w = &self.world;
        let builtin = Builtin {
            object: get(w, "Object"),
            nil: get(w, "Nil"),
            bool_: get(w, "Bool"),
            int: get(w, "Int"),
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
            class_: get(w, "Class"),
            shareable: get(w, "Shareable"),
            task: get(w, "Task"),
            channel: get(w, "Channel"),
            atom: get(w, "Atom"),
            scope: get(w, "Scope"),
            duration: get(w, "Duration"),
            array_builder: 0,
            hash_builder: 0,
            string_builder: 0,
            set_builder: 0,
            match_data: get(w, "MatchData"),
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
                self.world.class_mut(id).type_params[i].bounds = bounds;
            }
        }
        match p.def {
            PendingDef::Class(d) => {
                if let Some(sup) = &d.superclass {
                    if let Some(t) = self.resolve_type(sup, &scope) {
                        match &t {
                            Type::Class(sid, _)
                                if matches!(self.world.class(*sid).kind, ClassKind::Class) =>
                            {
                                self.world.class_mut(id).superclass = Some(t);
                            }
                            Type::Class(sid, _) => {
                                let kind = self.world.class(*sid).kind;
                                self.error(format!("cannot inherit from a {kind:?}"), sup.span);
                            }
                            _ => self.error("superclass must be a class", sup.span),
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
        for expr in p.body {
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
        self.world.add_method(MethodInfo {
            id: 0,
            name,
            owner,
            singleton: false,
            type_params: Vec::new(),
            params,
            block: None,
            ret: RetType::Known(ret),
            body: None,
            is_abstract: false,
            is_native: true,
            is_override: false,
            visibility,
            span,
            extension: None,
            frame_size: 0,
            checked: true,
            synth,
            alias_of: None,
            file: self.file,
        });
    }

    fn declare_data_methods(&mut self, id: ClassId, class_self: Type, span: Span) {
        let fields = self.world.class(id).fields.clone();
        // Readers.
        for f in &fields {
            if self.world.class(id).methods.contains_key(&f.name) {
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
        // initialize(field..., positional or keyword)
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
            self.world.nil(),
            Synth::DataInit,
            span,
            Visibility::Public,
        );
        // with(field: value = current, ...)
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
            class_self.clone(),
            Synth::DataWith,
            span,
            Visibility::Public,
        );
        // to_h
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

    fn declare_method(
        &mut self,
        owner: ClassId,
        extension: Option<ExtensionId>,
        def: &MethodDef,
        visibility: Visibility,
        class_scope: &TypeScope,
        class_self: &Type,
    ) {
        let type_params: Vec<TypeParamInfo> = def
            .type_params
            .iter()
            .map(|tp| self.world.new_type_param(&tp.name, tp.variance))
            .collect();
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
        }
        let mut params = Vec::new();
        let mut block = None;
        for p in &def.params.list {
            if p.kind == ParamKind::Block {
                match &p.ty {
                    Some(t) => {
                        if let Some(ty) = self.resolve_type(t, &scope) {
                            if !matches!(ty, Type::Proc(_, _)) {
                                self.error(
                                    "a block parameter must have a procedure type `(A) -> R`",
                                    t.span,
                                );
                            }
                            block = Some((p.name.clone(), ty));
                        }
                    }
                    None => self.error(
                        "a block parameter needs a type, e.g. `&block: (Int) -> Nil`",
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
            Some(t) => RetType::Known(self.resolve_type(t, &scope).unwrap_or(Type::Nothing)),
            None if def.name == "initialize" => RetType::Known(self.world.nil()),
            None if def.is_abstract || def.is_native => {
                self.error("abstract and native methods need a return type", def.span);
                RetType::Known(self.world.nil())
            }
            None => RetType::Infer,
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
        self.world.add_method(MethodInfo {
            id: 0,
            name: def.name.clone(),
            owner,
            singleton: def.singleton,
            type_params,
            params,
            block,
            ret,
            body: def.body.as_ref().map(|_| Rc::new(def.clone())),
            is_abstract: def.is_abstract,
            is_native: def.is_native,
            is_override: def.is_override,
            visibility,
            span: def.span,
            extension,
            frame_size: 0,
            checked: def.is_native || def.is_abstract,
            synth: Synth::None,
            alias_of: None,
            file: self.file,
        });
    }

    fn literal_type(&self, expr: &Expr) -> Option<Type> {
        Some(match &expr.kind {
            ExprKind::Int(_) => self.world.int(),
            ExprKind::Float(_) => self.world.float(),
            ExprKind::Str(_) => self.world.string(),
            ExprKind::Symbol(_) => self.world.symbol(),
            ExprKind::True | ExprKind::False => self.world.bool_(),
            _ => return None,
        })
    }

    fn resolve_usings(&mut self) {
        let unit_usings: Vec<(u32, ClassId, Vec<&'ast ConstPath>)> = self
            .units
            .iter_mut()
            .map(|u| (u.file, u.main, std::mem::take(&mut u.usings)))
            .collect();
        for (file, main, paths) in unit_usings {
            self.file = file;
            let mut ids = Vec::new();
            for path in paths {
                if let Some(found) = self.resolve_using(None, path) {
                    ids.extend(found);
                }
            }
            self.world.class_mut(main).usings = ids;
        }
        let per_class = std::mem::take(&mut self.class_usings);
        for (cid, paths) in per_class {
            let mut ids = Vec::new();
            for path in paths {
                if let Some(found) = self.resolve_using(Some(cid), path) {
                    ids.extend(found);
                }
            }
            self.world.class_mut(cid).usings = ids;
        }
    }

    fn resolve_using(
        &mut self,
        namespace: Option<ClassId>,
        path: &ConstPath,
    ) -> Option<Vec<ExtensionId>> {
        let span = Span::empty(0);
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
        let mut member = if path.absolute {
            self.world.top.get(&path.names[0]).copied()
        } else {
            self.world.resolve_member(namespace, &path.names[0])
        };
        if member.is_none() {
            self.error(format!("unknown constant `{}`", path.names[0]), span);
            return None;
        }
        for name in &path.names[1..] {
            let Some(Member::Class(cid)) = member else {
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

    pub fn resolve_type(&mut self, expr: &TypeExpr, scope: &TypeScope) -> Option<Type> {
        match &expr.kind {
            TypeExprKind::Nothing => Some(Type::Nothing),
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
            TypeExprKind::Proc { params, ret } => {
                let mut ps = Vec::new();
                for p in params {
                    ps.push(self.resolve_type(p, scope)?);
                }
                let r = self.resolve_type(ret, scope)?;
                Some(Type::Proc(ps, Box::new(r)))
            }
            TypeExprKind::Named { path, args } => {
                // A type parameter in scope?
                if path.names.len() == 1 && !path.absolute {
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
                let mut resolved_args = Vec::new();
                for a in args {
                    resolved_args.push(self.resolve_type(a, scope)?);
                }
                match member {
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
