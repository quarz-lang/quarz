//! Type checking of method bodies, constant initializers and the main
//! program (phase 3).

use std::collections::{HashMap, HashSet};

use rustc_hash::FxHashMap;

use quarz_syntax::ast::*;
use quarz_syntax::token::OpAssign;
use quarz_syntax::{Diagnostic, Span};

use crate::declare::{TypeScope, SELF_PARAM};
use crate::types::*;
use crate::world::*;

/// Where a local variable lives at run time: `depth` frames up from the
/// current one (0 = the current frame), at `slot`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VarRef {
    pub depth: u32,
    pub slot: u32,
}

/// What a call expression was resolved to.
#[derive(Clone, Debug)]
pub enum CallTarget {
    /// An ordinary method call. The runtime dispatches on the receiver's
    /// class by name when it differs from the method's owner.
    Method { method: MethodId },
    /// `Class.new(...)`: allocate and run `initialize` if any.
    Constructor {
        class: ClassId,
        init: Option<MethodId>,
    },
    /// Calling a procedure value.
    ProcCall,
    /// `x.is_a?(T)`
    IsA(Type),
    /// `x.as(T)` / `x.as?(T)`
    As { ty: Type, optional: bool },
    /// `respond_to?` folded to a constant.
    Constant(bool),
    /// `raise ...`
    Raise,
    /// `super(...)` resolved to the superclass method.
    Super { method: MethodId },
}

/// What a constant expression refers to.
#[derive(Clone, Debug)]
pub enum ConstTarget {
    Class(ClassId),
    /// A field-less enum variant used as a value.
    VariantSingleton(ClassId),
    Const(ConstId),
}

/// The checker's output for the evaluator.
#[derive(Clone, Debug, Default)]
pub struct Output {
    pub node_types: FxHashMap<NodeId, Type>,
    pub calls: FxHashMap<NodeId, CallTarget>,
    pub const_targets: FxHashMap<NodeId, ConstTarget>,
    /// Variable occurrences (uses and definitions) keyed by their span.
    pub var_refs: FxHashMap<Span, VarRef>,
    /// Frame sizes of blocks (keyed by the call node) and lambdas (keyed by
    /// the lambda node).
    pub frame_sizes: FxHashMap<NodeId, u32>,
    /// Frame size of each file's top-level statements, by file index.
    pub unit_frame_sizes: Vec<u32>,
    /// Field index for `@x` reads and writes, keyed by the node.
    pub ivar_fields: FxHashMap<NodeId, usize>,
    /// Classes referred to by constant patterns, keyed by pattern span.
    pub pattern_classes: FxHashMap<Span, ClassId>,
    /// Methods whose `&block` is passed as `&:sym` or `&proc`, by call node.
    pub block_pass: FxHashMap<NodeId, BlockPass>,
    /// For block parameters that destructure a tuple: the arity.
    pub block_destructure: FxHashMap<NodeId, usize>,
    /// Exception classes of each `rescue` clause, keyed by its span.
    pub rescue_classes: FxHashMap<Span, Vec<ClassId>>,
    /// Integer literals typed as `Float` because of their context.
    pub float_literals: rustc_hash::FxHashSet<NodeId>,
}

#[derive(Clone, Debug)]
pub enum BlockPass {
    /// `&:name`: call `name` on the block's argument.
    Symbol(String),
    /// `&expr`: the expression evaluates to a procedure.
    Proc,
}

#[derive(Clone, Debug)]
struct VarInfo {
    name: String,
    declared: Type,
    narrowed: Option<Type>,
}

#[derive(Clone, Debug)]
struct Frame {
    vars: Vec<VarInfo>,
    is_block: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum VarKey {
    Local(String),
    IVar(String),
}

pub(crate) type Facts = Vec<(VarKey, Type)>;

/// Narrowed types of all variables and immutable fields at a point.
type Snapshot = (Vec<Vec<Option<Type>>>, HashMap<String, Type>);

#[derive(Clone, Debug)]
struct Env {
    frames: Vec<Frame>,
    self_type: Type,
    class_id: Option<ClassId>,
    method: Option<MethodId>,
    scope: TypeScope,
    /// `None` while inferring.
    ret_expected: Option<Type>,
    ret_collected: Vec<Type>,
    block_type: Option<Type>,
    in_initialize: bool,
    assigned_fields: HashSet<String>,
    loop_depth: u32,
    /// For each enclosing block (innermost last): the proc's return type
    /// (for `next`) and the collected `break` value types.
    blocks: Vec<BlockCtx>,
    ivar_narrow: HashMap<String, Type>,
    in_rescue: u32,
    file: u32,
    /// While checking a `case/in` arm: the number of variables the current
    /// frame had before the `case`. Pattern variables declared by earlier
    /// arms (at or past this index) are re-declared rather than re-bound.
    pattern_base: Option<usize>,
    /// Index of the innermost frame that runs on another task (`spawn`
    /// block). Variables from frames below it are captured by value and must
    /// be shareable; they cannot be assigned.
    task_frame: Option<usize>,
}

#[derive(Clone, Debug)]
struct BlockCtx {
    ret: Type,
    breaks: Vec<Type>,
    is_lambda: bool,
}

#[derive(Debug, Default)]
struct InferTable {
    bindings: Vec<Option<Type>>,
}

impl InferTable {
    fn fresh(&mut self) -> Type {
        self.bindings.push(None);
        Type::Var(self.bindings.len() as InferVar - 1)
    }

    fn resolve(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => match &self.bindings[*v as usize] {
                Some(b) => self.resolve(b),
                None => t.clone(),
            },
            Type::Nothing | Type::Param(_) => t.clone(),
            Type::Class(id, args) => {
                Type::Class(*id, args.iter().map(|a| self.resolve(a)).collect())
            }
            Type::ClassObject(id, args) => {
                Type::ClassObject(*id, args.iter().map(|a| self.resolve(a)).collect())
            }
            Type::Union(ms) => Type::union_of(ms.iter().map(|m| self.resolve(m)).collect()),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| self.resolve(t)).collect()),
            Type::Proc(ps, r) => Type::Proc(
                ps.iter().map(|p| self.resolve(p)).collect(),
                Box::new(self.resolve(r)),
            ),
        }
    }

    fn bind(&mut self, v: InferVar, t: Type) {
        if t == Type::Var(v) {
            return;
        }
        self.bindings[v as usize] = Some(t);
    }

    fn save(&self) -> Vec<Option<Type>> {
        self.bindings.clone()
    }

    fn restore(&mut self, saved: Vec<Option<Type>>) {
        self.bindings = saved;
    }
}

pub struct Checker {
    pub world: World,
    pub diagnostics: Vec<(u32, Diagnostic)>,
    pub out: Output,
    infer: InferTable,
    env: Env,
    touched: Vec<NodeId>,
    /// The pseudo-class of each file's top-level methods, by file index.
    file_mains: Vec<Option<ClassId>>,
    /// The REPL's top-level environment, kept across inputs.
    repl_env: Option<Env>,
    /// Methods currently being checked (to detect inference cycles).
    in_progress: Vec<MethodId>,
}

/// Arguments after matching to parameters.
struct MatchedArg<'a> {
    param_ty: Type,
    arg: &'a Expr,
    /// Already computed type (for arguments typed before overload
    /// resolution).
    pre_type: Option<Type>,
}

impl Checker {
    pub fn new(world: World, file_mains: Vec<Option<ClassId>>) -> Checker {
        let env = Env {
            frames: vec![Frame {
                vars: Vec::new(),
                is_block: false,
            }],
            self_type: Type::class(file_mains.iter().flatten().next().copied().unwrap_or(0)),
            class_id: None,
            method: None,
            scope: TypeScope::default(),
            ret_expected: None,
            ret_collected: Vec::new(),
            block_type: None,
            in_initialize: false,
            assigned_fields: HashSet::new(),
            loop_depth: 0,
            blocks: Vec::new(),
            ivar_narrow: HashMap::new(),
            in_rescue: 0,
            file: 1,
            pattern_base: None,
            task_frame: None,
        };
        Checker {
            world,
            diagnostics: Vec::new(),
            out: Output::default(),
            infer: InferTable::default(),
            env,
            touched: Vec::new(),
            file_mains,
            repl_env: None,
            in_progress: Vec::new(),
        }
    }

    // ----- diagnostics -----------------------------------------------------

    fn error(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics
            .push((self.env.file, Diagnostic::error(message, span)));
    }

    fn warning(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics
            .push((self.env.file, Diagnostic::warning(message, span)));
    }

    fn name(&self, t: &Type) -> String {
        self.world.type_name(&self.infer.resolve(t))
    }

    // ----- entry points ------------------------------------------------------

    /// The pseudo-class holding the top-level methods of file `file`.
    fn file_main(&self, file: u32) -> Option<ClassId> {
        self.file_mains.get(file as usize).copied().flatten()
    }

    /// Register the pseudo-class of a file loaded after construction (a
    /// `require` in the REPL).
    pub fn add_file_main(&mut self, file: u32, main: ClassId) {
        let index = file as usize;
        if self.file_mains.len() <= index {
            self.file_mains.resize(index + 1, None);
        }
        self.file_mains[index] = Some(main);
    }

    /// Check every method body, constant initializer and each file's
    /// top-level statements.
    pub fn check_all(&mut self, units: &[(u32, Vec<&Expr>)]) {
        let count = self.world.consts.len();
        for cid in 0..count as ConstId {
            self.const_type(cid, Span::empty(0));
        }
        let count = self.world.methods.len();
        for mid in 0..count as MethodId {
            self.ensure_method_checked(mid);
        }
        for (file, body) in units {
            self.check_main(*file, body);
        }
    }

    fn check_main(&mut self, file: u32, body: &[&Expr]) {
        let main = self.file_main(file).unwrap_or(self.world.builtin.object);
        let mut env = self.fresh_env(
            Type::class(main),
            Some(main),
            None,
            TypeScope::default(),
            file,
        );
        env.ret_expected = Some(self.world.nil());
        let saved_infer = std::mem::take(&mut self.infer);
        self.check_top_level(env, file, body);
        self.infer = saved_infer;
    }

    /// Check top-level statements in `env`, returning the environment.
    fn check_top_level(&mut self, env: Env, file: u32, body: &[&Expr]) -> Env {
        let main = self.file_main(file).unwrap_or(self.world.builtin.object);
        let saved_env = std::mem::replace(&mut self.env, env);
        self.world.active_extensions = self.world.class(main).usings.clone();
        for expr in body {
            let t = self.check_expr(expr, None);
            if t.is_nothing() {
                // Statements after `exit` etc. are unreachable; keep going
                // for diagnostics.
            }
        }
        self.finish_frame_types();
        let size = self.env.frames[0].vars.len() as u32;
        if self.out.unit_frame_sizes.len() <= file as usize {
            self.out.unit_frame_sizes.resize(file as usize + 1, 0);
        }
        self.out.unit_frame_sizes[file as usize] = size;
        std::mem::replace(&mut self.env, saved_env)
    }

    /// Check REPL input: unchecked methods and constants, then the
    /// statements in the persistent top-level environment.
    pub fn check_repl(&mut self, file: u32, body: &[&Expr]) {
        let count = self.world.consts.len();
        for cid in 0..count as ConstId {
            self.const_type(cid, Span::empty(0));
        }
        let count = self.world.methods.len();
        for mid in 0..count as MethodId {
            self.ensure_method_checked(mid);
        }
        let main = self.file_main(file).unwrap_or(self.world.builtin.object);
        let env = match self.repl_env.take() {
            Some(env) => env,
            None => {
                let mut env = self.fresh_env(
                    Type::class(main),
                    Some(main),
                    None,
                    TypeScope::default(),
                    file,
                );
                env.ret_expected = Some(self.world.nil());
                env
            }
        };
        // The REPL keeps its inference variables across inputs.
        let env = self.check_top_level(env, file, body);
        self.repl_env = Some(env);
    }

    /// Discard the diagnostics of a failed REPL input and forget the
    /// variables it declared.
    pub fn take_diagnostics(&mut self) -> Vec<(u32, Diagnostic)> {
        std::mem::take(&mut self.diagnostics)
    }

    pub fn file_main_class(&self, file: u32) -> Option<ClassId> {
        self.file_main(file)
    }

    /// Names of the variables of the REPL's top level.
    pub fn repl_locals(&self) -> Vec<String> {
        match &self.repl_env {
            Some(env) => env.frames[0].vars.iter().map(|v| v.name.clone()).collect(),
            None => Vec::new(),
        }
    }

    fn fresh_env(
        &self,
        self_type: Type,
        class_id: Option<ClassId>,
        method: Option<MethodId>,
        scope: TypeScope,
        file: u32,
    ) -> Env {
        Env {
            frames: vec![Frame {
                vars: Vec::new(),
                is_block: false,
            }],
            self_type,
            class_id,
            method,
            scope,
            ret_expected: None,
            ret_collected: Vec::new(),
            block_type: None,
            in_initialize: false,
            assigned_fields: HashSet::new(),
            loop_depth: 0,
            blocks: Vec::new(),
            ivar_narrow: HashMap::new(),
            in_rescue: 0,
            file,
            pattern_base: None,
            task_frame: None,
        }
    }

    /// Resolve the types recorded for the nodes of the frame just checked.
    fn finish_frame_types(&mut self) {
        let touched = std::mem::take(&mut self.touched);
        for id in touched {
            if let Some(t) = self.out.node_types.get(&id) {
                let r = self.infer.resolve(t);
                self.out.node_types.insert(id, r);
            }
        }
        // Call targets with types (is_a?, as) are resolved too.
        let keys: Vec<NodeId> = self.out.calls.keys().copied().collect();
        for k in keys {
            let target = self.out.calls.get(&k).cloned();
            match target {
                Some(CallTarget::IsA(t)) => {
                    let r = self.infer.resolve(&t);
                    self.out.calls.insert(k, CallTarget::IsA(r));
                }
                Some(CallTarget::As { ty, optional }) => {
                    let r = self.infer.resolve(&ty);
                    self.out.calls.insert(k, CallTarget::As { ty: r, optional });
                }
                _ => {}
            }
        }
    }

    fn record(&mut self, id: NodeId, t: &Type) {
        self.out.node_types.insert(id, t.clone());
        self.touched.push(id);
    }

    // ----- methods ---------------------------------------------------------

    /// The return type of a method, inferring it from the body if needed.
    fn method_ret(&mut self, mid: MethodId, span: Span) -> Type {
        match self.world.method(mid).ret.clone() {
            RetType::Known(t) => t,
            RetType::Inferring => {
                let name = self.world.method(mid).name.clone();
                self.error(
                    format!("the recursive method `{name}` needs an explicit return type"),
                    span,
                );
                Type::Nothing
            }
            RetType::Infer => {
                self.ensure_method_checked(mid);
                match self.world.method(mid).ret.clone() {
                    RetType::Known(t) => t,
                    _ => Type::Nothing,
                }
            }
        }
    }

    pub fn ensure_method_checked(&mut self, mid: MethodId) {
        if self.world.method(mid).checked {
            return;
        }
        if self.in_progress.contains(&mid) {
            return;
        }
        let Some(def) = self.world.method(mid).body.clone() else {
            self.world.method_mut(mid).checked = true;
            return;
        };
        self.in_progress.push(mid);
        if matches!(self.world.method(mid).ret, RetType::Infer) {
            self.world.method_mut(mid).ret = RetType::Inferring;
        }

        let info = self.world.method(mid).clone();
        let owner = info.owner;
        let class = self.world.class(owner).clone();
        let self_type = if info.singleton {
            Type::ClassObject(
                owner,
                class
                    .type_params
                    .iter()
                    .map(|p| Type::Param(p.id))
                    .collect(),
            )
        } else if let Some(ext) = info.extension {
            let e = &self.world.extensions[ext as usize];
            Type::Class(e.target, e.target_args.clone())
        } else {
            Type::Class(
                owner,
                class
                    .type_params
                    .iter()
                    .map(|p| Type::Param(p.id))
                    .collect(),
            )
        };
        let mut params: Vec<(String, TypeParamId)> = Vec::new();
        let namespace;
        if let Some(ext) = info.extension {
            let e = &self.world.extensions[ext as usize];
            params.extend(e.type_params.iter().map(|p| (p.name.clone(), p.id)));
            namespace = e.module;
        } else {
            params.extend(class.type_params.iter().map(|p| (p.name.clone(), p.id)));
            namespace = if class.kind == ClassKind::Main {
                None
            } else {
                Some(owner)
            };
        }
        params.extend(info.type_params.iter().map(|p| (p.name.clone(), p.id)));
        let scope = TypeScope {
            namespace,
            params,
            self_type: Some(self_type.clone()),
        };
        let mut env = self.fresh_env(self_type.clone(), Some(owner), Some(mid), scope, info.file);
        let self_subst: HashMap<TypeParamId, Type> =
            [(SELF_PARAM, self_type.clone())].into_iter().collect();
        env.ret_expected = match &info.ret {
            RetType::Known(t) => Some(t.subst(&self_subst)),
            _ => None,
        };
        env.block_type = info.block.as_ref().map(|(_, t)| t.subst(&self_subst));
        env.in_initialize = info.name == "initialize" && !info.singleton;
        env.frames[0].vars = Vec::new();
        for p in &info.params {
            env.frames[0].vars.push(VarInfo {
                name: p.name.clone(),
                declared: p.ty.subst(&self_subst),
                narrowed: None,
            });
        }
        if let Some((name, t)) = &info.block {
            env.frames[0].vars.push(VarInfo {
                name: name.clone(),
                declared: t.subst(&self_subst),
                narrowed: None,
            });
        }
        // Active extensions: the class's `using`s plus those of the file's
        // top level.
        let mut active = class.usings.clone();
        if let Some(fm) = self.file_main(info.file) {
            for e in &self.world.class(fm).usings {
                if !active.contains(e) {
                    active.push(*e);
                }
            }
        }
        // Usings of enclosing namespaces.
        let mut ns = class.parent;
        while let Some(n) = ns {
            for e in &self.world.class(n).usings {
                if !active.contains(e) {
                    active.push(*e);
                }
            }
            ns = self.world.class(n).parent;
        }

        let saved_env = std::mem::replace(&mut self.env, env);
        let saved_infer = std::mem::take(&mut self.infer);
        let saved_touched = std::mem::take(&mut self.touched);
        let saved_active = std::mem::replace(&mut self.world.active_extensions, active);

        // Parameter slots are the first slots of the frame.
        for (i, p) in info.params.iter().enumerate() {
            self.out.var_refs.insert(
                p.span,
                VarRef {
                    depth: 0,
                    slot: i as u32,
                },
            );
            if let Some(d) = &p.default {
                let expected = p.ty.subst(&self_subst);
                let t = self.check_expr(d, Some(&expected));
                if !self.coerce(&t, &expected) {
                    self.error(
                        format!(
                            "default value of type {} for parameter `{}` of type {}",
                            self.name(&t),
                            p.name,
                            self.name(&expected)
                        ),
                        d.span,
                    );
                }
            }
            if p.assigns_ivar {
                self.env.assigned_fields.insert(p.name.clone());
            }
        }

        let body = def.body.as_ref().cloned().unwrap_or_default();
        let expected = self.env.ret_expected.clone();
        let void = expected.as_ref().is_some_and(|t| self.world.is_nil_type(t));
        let body_ty = self.check_body(&body, if void { None } else { expected.as_ref() });
        match expected {
            Some(ret) if !void => {
                if !body_ty.is_nothing() && !self.coerce(&body_ty, &ret) {
                    let span = body.last().map(|e| e.span).unwrap_or(info.span);
                    self.error(
                        format!(
                            "method `{}` returns {} but its body has type {}",
                            info.name,
                            self.name(&ret),
                            self.name(&body_ty)
                        ),
                        span,
                    );
                }
            }
            Some(_) => {}
            None => {
                let mut t = self.infer.resolve(&body_ty);
                for r in self.env.ret_collected.clone() {
                    let r = self.infer.resolve(&r);
                    t = self.join(&t, &r);
                }
                let t = self.infer.resolve(&t);
                if t.has_vars() {
                    self.error(
                        format!(
                            "cannot infer the return type of `{}` ({}); add `-> Type`",
                            info.name,
                            self.name(&t)
                        ),
                        info.span,
                    );
                }
                self.world.method_mut(mid).ret = RetType::Known(t);
            }
        }

        if self.env.in_initialize {
            let fields = self.world.all_fields(owner);
            for (f, _) in fields {
                if f.default.is_none() && !f.mutable && !self.env.assigned_fields.contains(&f.name)
                {
                    self.error(
                        format!("field `@{}` must be assigned in `initialize`", f.name),
                        info.span,
                    );
                }
            }
        }

        let frame_size = self.env.frames[0].vars.len() as u32;
        self.finish_frame_types();
        self.world.method_mut(mid).frame_size = frame_size;
        self.world.method_mut(mid).checked = true;
        if matches!(self.world.method(mid).ret, RetType::Inferring) {
            self.world.method_mut(mid).ret = RetType::Known(Type::Nothing);
        }
        self.env = saved_env;
        self.infer = saved_infer;
        self.touched = saved_touched;
        self.world.active_extensions = saved_active;
        self.in_progress.pop();
    }

    /// The type of a constant, checking its initializer on first use.
    fn const_type(&mut self, cid: ConstId, span: Span) -> Type {
        let info = self.world.consts[cid as usize].clone();
        if let Some(t) = info.ty {
            return t;
        }
        if info.checking {
            self.error(format!("constant `{}` refers to itself", info.name), span);
            return Type::Nothing;
        }
        let Some(value) = info.value else {
            return Type::Nothing;
        };
        self.world.consts[cid as usize].checking = true;
        let scope = TypeScope {
            namespace: info.owner,
            params: Vec::new(),
            self_type: None,
        };
        let self_type = match info.owner {
            Some(o) => Type::ClassObject(o, vec![]),
            None => Type::class(
                self.file_main(info.file)
                    .unwrap_or(self.world.builtin.object),
            ),
        };
        let env = self.fresh_env(self_type, info.owner, None, scope, info.file);
        let saved_env = std::mem::replace(&mut self.env, env);
        let saved_infer = std::mem::take(&mut self.infer);
        let saved_touched = std::mem::take(&mut self.touched);
        let t = self.check_expr(&value, None);
        let t = self.infer.resolve(&t);
        if t.has_vars() {
            self.error(
                format!("cannot infer the type of constant `{}`", info.name),
                value.span,
            );
        }
        if !self.world.is_shareable(&t) {
            self.error(
                format!(
                    "constant `{}` has the non-shareable type {}",
                    info.name,
                    self.world.type_name(&t)
                ),
                value.span,
            );
        }
        self.finish_frame_types();
        self.env = saved_env;
        self.infer = saved_infer;
        self.touched = saved_touched;
        self.world.consts[cid as usize].ty = Some(t.clone());
        self.world.consts[cid as usize].checking = false;
        t
    }

    // ----- inference helpers -------------------------------------------------

    fn resolve(&self, t: &Type) -> Type {
        self.infer.resolve(t)
    }

    /// Whether a value of type `actual` can be used where `expected` is
    /// required, binding inference variables on either side.
    fn coerce(&mut self, actual: &Type, expected: &Type) -> bool {
        let a = self.infer.resolve(actual);
        let e = self.infer.resolve(expected);
        if a == e || a.is_nothing() {
            return true;
        }
        match (&a, &e) {
            (_, Type::Var(v)) => {
                self.infer.bind(*v, a.clone());
                true
            }
            (Type::Var(v), _) => {
                self.infer.bind(*v, e.clone());
                true
            }
            (_, Type::Class(id, _)) if *id == self.world.builtin.object => true,
            (Type::Union(ms), _) => {
                let ms = ms.clone();
                ms.iter().all(|m| self.coerce(m, &e))
            }
            (_, Type::Union(ms)) => {
                let ms = ms.clone();
                // Prefer a member with the same class.
                if let Type::Class(aid, _) = &a {
                    for m in &ms {
                        if matches!(m, Type::Class(mid, _) if mid == aid) {
                            let saved = self.infer.save();
                            if self.coerce(&a, m) {
                                return true;
                            }
                            self.infer.restore(saved);
                        }
                    }
                }
                for m in &ms {
                    let saved = self.infer.save();
                    if self.coerce(&a, m) {
                        return true;
                    }
                    self.infer.restore(saved);
                }
                false
            }
            (Type::Class(aid, aargs), Type::Class(eid, eargs)) => {
                let ancestors = self.world.ancestors(*aid, aargs);
                let Some((_, anc_args)) = ancestors.into_iter().find(|(id, _)| id == eid) else {
                    return false;
                };
                if anc_args.len() != eargs.len() {
                    return anc_args.is_empty() || eargs.is_empty();
                }
                let params = self.world.class(*eid).type_params.clone();
                for (i, (x, y)) in anc_args.iter().zip(eargs.iter()).enumerate() {
                    let ok = match params.get(i).map(|p| p.variance) {
                        Some(Variance::Covariant) => self.coerce(x, y),
                        Some(Variance::Contravariant) => self.coerce(y, x),
                        _ => self.unify(x, y),
                    };
                    if !ok {
                        return false;
                    }
                }
                true
            }
            (Type::ClassObject(aid, _), Type::ClassObject(eid, _)) => {
                self.world.class_is_a(*aid, *eid)
            }
            (Type::ClassObject(_, _), Type::Class(eid, _)) => *eid == self.world.builtin.class_,
            (Type::Tuple(xs), Type::Tuple(ys)) => {
                if xs.len() != ys.len() {
                    return false;
                }
                let (xs, ys) = (xs.clone(), ys.clone());
                xs.iter().zip(ys.iter()).all(|(x, y)| self.coerce(x, y))
            }
            (Type::Tuple(xs), Type::Class(eid, eargs)) => {
                if *eid == self.world.builtin.array && eargs.len() == 1 {
                    let elem = Type::union_of(xs.clone());
                    let target = eargs[0].clone();
                    return self.coerce(&elem, &target);
                }
                self.world.class_is_a(self.world.builtin.array, *eid)
            }
            (Type::Proc(ps, r), Type::Proc(qs, s)) => {
                if ps.len() != qs.len() {
                    return false;
                }
                let (ps, qs, r, s) = (ps.clone(), qs.clone(), (**r).clone(), (**s).clone());
                for (p, q) in ps.iter().zip(qs.iter()) {
                    if !self.coerce(q, p) {
                        return false;
                    }
                }
                self.coerce(&r, &s)
            }
            (Type::Proc(_, _), Type::Class(eid, _)) => *eid == self.world.builtin.proc_,
            (Type::Param(_), _) | (_, Type::Param(_)) => self.world.is_subtype(&a, &e),
            _ => false,
        }
    }

    /// Both directions (for invariant type arguments).
    fn unify(&mut self, x: &Type, y: &Type) -> bool {
        let rx = self.infer.resolve(x);
        let ry = self.infer.resolve(y);
        if rx == ry {
            return true;
        }
        match (&rx, &ry) {
            (Type::Var(v), _) => {
                self.infer.bind(*v, ry.clone());
                true
            }
            (_, Type::Var(v)) => {
                self.infer.bind(*v, rx.clone());
                true
            }
            (Type::Class(a, aa), Type::Class(b, ba)) if a == b && aa.len() == ba.len() => {
                let (aa, ba) = (aa.clone(), ba.clone());
                aa.iter().zip(ba.iter()).all(|(p, q)| self.unify(p, q))
            }
            (Type::Tuple(xs), Type::Tuple(ys)) if xs.len() == ys.len() => {
                let (xs, ys) = (xs.clone(), ys.clone());
                xs.iter().zip(ys.iter()).all(|(p, q)| self.unify(p, q))
            }
            (Type::Union(_), _) | (_, Type::Union(_)) => {
                self.coerce(&rx, &ry) && self.coerce(&ry, &rx)
            }
            _ => self.world.is_subtype(&rx, &ry) && self.world.is_subtype(&ry, &rx),
        }
    }

    fn join(&mut self, a: &Type, b: &Type) -> Type {
        let ra = self.infer.resolve(a);
        let rb = self.infer.resolve(b);
        if ra.is_nothing() {
            return rb;
        }
        if rb.is_nothing() {
            return ra;
        }
        if let Type::Var(v) = ra {
            self.infer.bind(v, rb.clone());
            return rb;
        }
        if let Type::Var(v) = rb {
            self.infer.bind(v, ra.clone());
            return ra;
        }
        self.world.join(&ra, &rb)
    }

    fn is_truthy_type(&self, t: &Type) -> Option<bool> {
        let t = self.resolve(t);
        let has_nil = t.members().iter().any(|m| self.world.is_nil_type(m));
        let has_bool = t
            .members()
            .iter()
            .any(|m| matches!(m, Type::Class(id, _) if *id == self.world.builtin.bool_));
        let all_nil = t.members().iter().all(|m| self.world.is_nil_type(m));
        if matches!(t, Type::Var(_) | Type::Nothing | Type::Param(_)) {
            return None;
        }
        if t.members()
            .iter()
            .any(|m| self.world.is_object(m) || matches!(m, Type::Param(_) | Type::Var(_)))
        {
            return None;
        }
        if all_nil {
            return Some(false);
        }
        if !has_nil && !has_bool {
            return Some(true);
        }
        None
    }

    fn truthy_part(&self, t: &Type) -> Type {
        let t = self.resolve(t);
        t.without_nil(self.world.builtin.nil)
    }

    fn falsy_part(&self, t: &Type) -> Type {
        let t = self.resolve(t);
        let mut out = Vec::new();
        for m in t.members() {
            if self.world.is_nil_type(&m)
                || matches!(&m, Type::Class(id, _) if *id == self.world.builtin.bool_)
            {
                out.push(m);
            } else if self.world.is_object(&m) {
                out.push(self.world.nil());
                out.push(self.world.bool_());
            }
        }
        Type::union_of(out)
    }

    // ----- variables -------------------------------------------------------------

    fn lookup_var(&self, name: &str) -> Option<(usize, usize)> {
        let n = self.env.frames.len();
        for (i, frame) in self.env.frames.iter().enumerate().rev() {
            // The last declaration wins (pattern variables of later arms).
            if let Some(slot) = frame.vars.iter().rposition(|v| v.name == name) {
                return Some((n - 1 - i, slot));
            }
            if !frame.is_block {
                break;
            }
        }
        None
    }

    /// Whether a variable `depth` frames up lives outside the innermost
    /// task block.
    fn captured_across_task(&self, depth: usize) -> bool {
        match self.env.task_frame {
            Some(tf) => self.env.frames.len() - 1 - depth < tf,
            None => false,
        }
    }

    fn check_task_capture(&mut self, name: &str, depth: usize, t: &Type, span: Span) {
        if !self.captured_across_task(depth) {
            return;
        }
        let rt = self.resolve(t);
        if rt.has_vars() {
            return;
        }
        if !self.world.is_shareable(&rt) {
            self.error(
                format!(
                    "`{name}` has the non-shareable type {} and cannot be captured by a `spawn` block",
                    self.world.type_name(&rt)
                ),
                span,
            );
        }
    }

    fn var_type(&self, depth: usize, slot: usize) -> Type {
        let n = self.env.frames.len();
        let v = &self.env.frames[n - 1 - depth].vars[slot];
        v.narrowed.clone().unwrap_or_else(|| v.declared.clone())
    }

    fn declare_var(&mut self, name: &str, ty: Type, span: Span) -> VarRef {
        let frame = self.env.frames.last_mut().unwrap();
        frame.vars.push(VarInfo {
            name: name.to_string(),
            declared: ty,
            narrowed: None,
        });
        let r = VarRef {
            depth: 0,
            slot: frame.vars.len() as u32 - 1,
        };
        self.out.var_refs.insert(span, r);
        r
    }

    fn set_narrowed(&mut self, key: &VarKey, t: Option<Type>) {
        match key {
            VarKey::Local(name) => {
                if let Some((depth, slot)) = self.lookup_var(name) {
                    let n = self.env.frames.len();
                    let v = &mut self.env.frames[n - 1 - depth].vars[slot];
                    v.narrowed = match t {
                        Some(t) if t != v.declared => Some(t),
                        _ => None,
                    };
                }
            }
            VarKey::IVar(name) => match t {
                Some(t) => {
                    self.env.ivar_narrow.insert(name.clone(), t);
                }
                None => {
                    self.env.ivar_narrow.remove(name);
                }
            },
        }
    }

    fn apply_facts(&mut self, facts: &Facts) {
        for (key, t) in facts {
            self.set_narrowed(key, Some(t.clone()));
        }
    }

    /// Snapshot of all narrowings (for branches).
    fn snapshot(&self) -> Snapshot {
        (
            self.env
                .frames
                .iter()
                .map(|f| f.vars.iter().map(|v| v.narrowed.clone()).collect())
                .collect(),
            self.env.ivar_narrow.clone(),
        )
    }

    fn restore(&mut self, snap: &Snapshot) {
        for (f, saved) in self.env.frames.iter_mut().zip(snap.0.iter()) {
            for (v, s) in f.vars.iter_mut().zip(saved.iter()) {
                v.narrowed = s.clone();
            }
        }
        self.env.ivar_narrow = snap.1.clone();
    }

    /// Merge the narrowings of two branches into the current environment
    /// (which holds the second branch's state).
    fn merge_with(&mut self, other: &Snapshot, other_dead: bool, self_dead: bool) {
        if self_dead && !other_dead {
            self.restore(other);
            return;
        }
        if other_dead {
            return;
        }
        for (fi, f) in self.env.frames.iter_mut().enumerate() {
            let Some(saved) = other.0.get(fi) else {
                continue;
            };
            for (vi, v) in f.vars.iter_mut().enumerate() {
                let Some(s) = saved.get(vi) else {
                    v.narrowed = None;
                    continue;
                };
                if v.narrowed != *s {
                    let a = v.narrowed.clone().unwrap_or_else(|| v.declared.clone());
                    let b = s.clone().unwrap_or_else(|| v.declared.clone());
                    let j = self
                        .world
                        .join(&self.infer.resolve(&a), &self.infer.resolve(&b));
                    v.narrowed = if j == v.declared { None } else { Some(j) };
                }
            }
        }
        let keys: Vec<String> = self.env.ivar_narrow.keys().cloned().collect();
        for k in keys {
            match other.1.get(&k) {
                Some(t) if *t == self.env.ivar_narrow[&k] => {}
                Some(t) => {
                    let a = self.env.ivar_narrow[&k].clone();
                    let j = self.world.join(&a, t);
                    self.env.ivar_narrow.insert(k, j);
                }
                None => {
                    self.env.ivar_narrow.remove(&k);
                }
            }
        }
    }

    /// Names assigned anywhere inside the expressions (for widening before
    /// loops and blocks).
    fn assigned_names(exprs: &[Expr], out: &mut HashSet<String>) {
        for e in exprs {
            Self::assigned_names_expr(e, out);
        }
    }

    fn assigned_names_expr(e: &Expr, out: &mut HashSet<String>) {
        use ExprKind::*;
        match &e.kind {
            Assign { target, value } | OpAssign { target, value, .. } => {
                if let LValue::Local { name, .. } = &**target {
                    out.insert(name.clone());
                }
                Self::assigned_names_expr(value, out);
            }
            MultiAssign { targets, value } => {
                fn collect(t: &MultiTarget, out: &mut HashSet<String>) {
                    match t {
                        MultiTarget::Single(LValue::Local { name, .. }) => {
                            out.insert(name.clone());
                        }
                        MultiTarget::Splat(Some(LValue::Local { name, .. })) => {
                            out.insert(name.clone());
                        }
                        MultiTarget::Nested(ts) => ts.iter().for_each(|t| collect(t, out)),
                        _ => {}
                    }
                }
                targets.iter().for_each(|t| collect(t, out));
                Self::assigned_names_expr(value, out);
            }
            TypedDecl { name, value, .. } => {
                out.insert(name.clone());
                Self::assigned_names_expr(value, out);
            }
            Call(call) => {
                if let Some(r) = &call.recv {
                    Self::assigned_names_expr(r, out);
                }
                for a in &call.args {
                    match a {
                        Arg::Positional(x)
                        | Arg::Splat(x)
                        | Arg::DoubleSplat(x)
                        | Arg::BlockPass(x) => Self::assigned_names_expr(x, out),
                        Arg::Keyword { value, .. } => Self::assigned_names_expr(value, out),
                    }
                }
                if let Some(b) = &call.block {
                    Self::assigned_names(&b.body, out);
                }
            }
            If { cond, then, els } => {
                Self::assigned_names_expr(cond, out);
                Self::assigned_names(then, out);
                if let Some(els) = els {
                    Self::assigned_names(els, out);
                }
            }
            While { cond, body, .. } => {
                Self::assigned_names_expr(cond, out);
                Self::assigned_names(body, out);
            }
            And(a, b) | Or(a, b) => {
                Self::assigned_names_expr(a, out);
                Self::assigned_names_expr(b, out);
            }
            Not(a) => Self::assigned_names_expr(a, out),
            Case {
                subject,
                whens,
                els,
            } => {
                if let Some(s) = subject {
                    Self::assigned_names_expr(s, out);
                }
                for w in whens {
                    Self::assigned_names(&w.body, out);
                }
                if let Some(els) = els {
                    Self::assigned_names(els, out);
                }
            }
            CaseIn { subject, arms, els } => {
                Self::assigned_names_expr(subject, out);
                for a in arms {
                    Self::assigned_names(&a.body, out);
                }
                if let Some(els) = els {
                    Self::assigned_names(els, out);
                }
            }
            Begin(b) => {
                Self::assigned_names(&b.body, out);
                for r in &b.rescues {
                    Self::assigned_names(&r.body, out);
                }
                if let Some(x) = &b.else_body {
                    Self::assigned_names(x, out);
                }
                if let Some(x) = &b.ensure {
                    Self::assigned_names(x, out);
                }
            }
            Seq(es) => Self::assigned_names(es, out),
            Return(Some(v)) | Break(Some(v)) | Next(Some(v)) => Self::assigned_names_expr(v, out),
            Lambda(b) => Self::assigned_names(&b.body, out),
            Array(items) => {
                for a in items {
                    match a {
                        Arg::Positional(x)
                        | Arg::Splat(x)
                        | Arg::DoubleSplat(x)
                        | Arg::BlockPass(x) => Self::assigned_names_expr(x, out),
                        Arg::Keyword { value, .. } => Self::assigned_names_expr(value, out),
                    }
                }
            }
            Str(parts) | DSymbol(parts) | Regexp { parts, .. } => {
                for p in parts {
                    if let StrPart::Interp(x) = p {
                        Self::assigned_names_expr(x, out);
                    }
                }
            }
            _ => {}
        }
    }

    /// Reset the narrowing of outer variables assigned inside `body`.
    fn widen_assigned(&mut self, body: &[Expr]) {
        let mut names = HashSet::new();
        Self::assigned_names(body, &mut names);
        for name in names {
            self.set_narrowed(&VarKey::Local(name), None);
        }
    }

    // ----- bodies --------------------------------------------------------------

    fn check_body(&mut self, body: &[Expr], expected: Option<&Type>) -> Type {
        if body.is_empty() {
            return self.world.nil();
        }
        let mut result = self.world.nil();
        let mut dead = false;
        for (i, e) in body.iter().enumerate() {
            let last = i == body.len() - 1;
            if dead {
                self.warning("unreachable code", e.span);
                dead = false; // report once
            }
            let t = self.check_expr(e, if last { expected } else { None });
            if t.is_nothing() {
                dead = true;
                result = Type::Nothing;
            } else if last {
                result = t;
            }
        }
        result
    }

    // ----- expressions --------------------------------------------------------

    pub fn check_expr(&mut self, expr: &Expr, expected: Option<&Type>) -> Type {
        let t = self.check_expr_inner(expr, expected);
        self.record(expr.id, &t);
        t
    }

    fn check_expr_inner(&mut self, expr: &Expr, expected: Option<&Type>) -> Type {
        use ExprKind::*;
        match &expr.kind {
            Nil => self.world.nil(),
            True | False => self.world.bool_(),
            SelfRef => self.env.self_type.clone(),
            Int(_) => {
                if let Some(e) = expected {
                    let e = self.resolve(e);
                    if e == self.world.float() {
                        self.out.float_literals.insert(expr.id);
                        return self.world.float();
                    }
                }
                self.world.int()
            }
            Float(_) => self.world.float(),
            Str(parts) => {
                self.check_str_parts(parts);
                self.world.string()
            }
            Symbol(_) => self.world.symbol(),
            DSymbol(parts) => {
                self.check_str_parts(parts);
                self.world.symbol()
            }
            Regexp { parts, .. } => {
                self.check_str_parts(parts);
                Type::class(self.world.builtin.regexp)
            }
            Bytes(_) => Type::class(self.world.builtin.bytes),
            Magic(m) => match m {
                quarz_syntax::ast::Magic::Line => self.world.int(),
                _ => self.world.string(),
            },
            Array(items) => self.check_array(items, expected, expr.span),
            Hash(entries) => self.check_hash(entries, expected),
            Range {
                lo,
                hi,
                exclusive: _,
            } => {
                let mut t = Type::Nothing;
                let elem_expected = match expected.map(|e| self.resolve(e)) {
                    Some(Type::Class(id, args))
                        if id == self.world.builtin.range && args.len() == 1 =>
                    {
                        Some(args[0].clone())
                    }
                    _ => None,
                };
                for side in [lo, hi].into_iter().flatten() {
                    let st = self.check_expr(side, elem_expected.as_ref());
                    t = self.join(&t, &st);
                }
                if t.is_nothing() {
                    t = self.infer.fresh();
                }
                Type::Class(self.world.builtin.range, vec![t])
            }
            Lambda(block) => self.check_lambda(expr.id, block, expected),
            Local(name) => match self.lookup_var(name) {
                Some((depth, slot)) => {
                    self.out.var_refs.insert(
                        expr.span,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    let t = self.var_type(depth, slot);
                    self.check_task_capture(name, depth, &t, expr.span);
                    t
                }
                None => {
                    self.error(format!("undefined local variable `{name}`"), expr.span);
                    Type::Nothing
                }
            },
            IVar(name) => self.check_ivar_read(expr, name),
            Const(path) => self.check_const(expr, path),
            TypeApp(te) => {
                let scope = self.env.scope.clone();
                match self.resolve_type_expr(te, &scope) {
                    Some(Type::Class(id, args)) => {
                        self.out
                            .const_targets
                            .insert(expr.id, ConstTarget::Class(id));
                        Type::ClassObject(id, args)
                    }
                    Some(_) => {
                        self.error("expected a class type", te.span);
                        Type::Nothing
                    }
                    None => Type::Nothing,
                }
            }
            Call(call) => self.check_call(expr, call, expected),
            MethodRef { recv, name } => {
                let rt = self.check_expr(recv, None);
                let rt = self.resolve(&rt);
                let cands = self.world.lookup_methods(&rt, name);
                let Some((mid, subst)) = cands.first().cloned() else {
                    self.error(
                        format!("undefined method `{name}` for {}", self.name(&rt)),
                        expr.span,
                    );
                    return Type::Nothing;
                };
                let m = self.world.method(mid).clone();
                let mut subst = subst;
                subst.insert(SELF_PARAM, rt.clone());
                let params: Vec<Type> = m
                    .params
                    .iter()
                    .filter(|p| p.kind == ParamKind::Positional)
                    .map(|p| p.ty.subst(&subst))
                    .collect();
                let ret = self.method_ret(mid, expr.span).subst(&subst);
                self.out
                    .calls
                    .insert(expr.id, CallTarget::Method { method: mid });
                Type::Proc(params, Box::new(ret))
            }
            Yield(args) => self.check_yield(expr, args),
            Super { args, block } => self.check_super(expr, args.as_deref(), block.as_deref()),
            Assign { target, value } => self.check_assign(expr, target, value, expected),
            OpAssign { target, op, value } => self.check_op_assign(expr, target, *op, value),
            MultiAssign { targets, value } => self.check_multi_assign(expr, targets, value),
            TypedDecl { name, ty, value } => {
                let scope = self.env.scope.clone();
                let Some(declared) = self.resolve_type_expr(ty, &scope) else {
                    return Type::Nothing;
                };
                let vt = self.check_expr(value, Some(&declared));
                if !self.coerce(&vt, &declared) {
                    self.error(
                        format!(
                            "cannot assign {} to `{name}` of type {}",
                            self.name(&vt),
                            self.name(&declared)
                        ),
                        value.span,
                    );
                }
                if self.lookup_var(name).is_some_and(|(d, _)| d == 0) {
                    self.error(format!("`{name}` is already declared"), expr.span);
                }
                self.declare_var(name, declared.clone(), expr.span);
                let narrowed = self.resolve(&vt);
                self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
                declared
            }
            And(a, b) => {
                let (ta, facts_true, _) = self.check_cond(a);
                let snap = self.snapshot();
                self.apply_facts(&facts_true);
                let tb = self.check_expr(b, None);
                let b_dead = tb.is_nothing();
                self.merge_with(&snap, false, b_dead);
                if self.resolve(&ta) == self.world.bool_()
                    && self.resolve(&tb) == self.world.bool_()
                {
                    return self.world.bool_();
                }
                let fa = self.falsy_part(&ta);
                self.join(&fa, &tb)
            }
            Or(a, b) => {
                let (ta, _, facts_false) = self.check_cond(a);
                let snap = self.snapshot();
                self.apply_facts(&facts_false);
                let tb = self.check_expr(b, expected);
                let b_dead = tb.is_nothing();
                self.merge_with(&snap, false, b_dead);
                if self.resolve(&ta) == self.world.bool_()
                    && self.resolve(&tb) == self.world.bool_()
                {
                    return self.world.bool_();
                }
                let truthy = self.truthy_part(&ta);
                self.join(&truthy, &tb)
            }
            Not(a) => {
                self.check_expr(a, None);
                self.world.bool_()
            }
            If { cond, then, els } => self.check_if(cond, then, els.as_deref(), expected),
            While {
                cond,
                body,
                negate,
                do_while,
            } => {
                self.widen_assigned(body);
                self.widen_assigned(std::slice::from_ref(cond));
                let (ct, facts_true, facts_false) = self.check_cond(cond);
                let (body_facts, exit_facts) = if *negate {
                    (facts_false, facts_true)
                } else {
                    (facts_true, facts_false)
                };
                let snap = self.snapshot();
                if !*do_while {
                    self.apply_facts(&body_facts);
                }
                self.env.loop_depth += 1;
                self.check_body(body, None);
                self.env.loop_depth -= 1;
                self.restore(&snap);
                self.widen_assigned(body);
                self.apply_facts(&exit_facts);
                let infinite = matches!(cond.kind, ExprKind::True) && !*negate
                    || matches!(cond.kind, ExprKind::False) && *negate;
                let _ = ct;
                if infinite && !Self::contains_break(body) {
                    Type::Nothing
                } else {
                    self.world.nil()
                }
            }
            Case {
                subject,
                whens,
                els,
            } => self.check_case_when(subject.as_deref(), whens, els.as_deref(), expected),
            CaseIn { subject, arms, els } => {
                self.check_case_in(subject, arms, els.as_deref(), expected, expr.span)
            }
            MatchPattern {
                value,
                pattern,
                raises,
            } => {
                let vt = self.check_expr(value, None);
                let vt = self.resolve(&vt);
                let facts = self.check_pattern_facts(pattern, &vt, value);
                if *raises {
                    self.apply_facts(&facts);
                    self.world.nil()
                } else {
                    self.world.bool_()
                }
            }
            Begin(block) => self.check_begin(block, expected),
            Return(value) => {
                let in_lambda = self.env.blocks.last().is_some_and(|b| b.is_lambda);
                if in_lambda {
                    let ret = self.env.blocks.last().unwrap().ret.clone();
                    let t = match value {
                        Some(v) => self.check_expr(v, Some(&ret)),
                        None => self.world.nil(),
                    };
                    if !self.coerce(&t, &ret) {
                        self.error(
                            format!(
                                "lambda returns {} but `return` has type {}",
                                self.name(&ret),
                                self.name(&t)
                            ),
                            expr.span,
                        );
                    }
                    return Type::Nothing;
                }
                if self.env.method.is_none()
                    && self
                        .env
                        .class_id
                        .is_some_and(|c| self.world.class(c).kind == ClassKind::Main)
                    && self.env.frames.len() == 1
                {
                    // `return` at the top level ends the program.
                    if let Some(v) = value {
                        self.check_expr(v, None);
                    }
                    return Type::Nothing;
                }
                match self.env.ret_expected.clone() {
                    Some(ret) => {
                        let void = self.world.is_nil_type(&ret);
                        let t = match value {
                            Some(v) => self.check_expr(v, if void { None } else { Some(&ret) }),
                            None => self.world.nil(),
                        };
                        if !void && !self.coerce(&t, &ret) {
                            self.error(
                                format!(
                                    "`return` has type {} but the method returns {}",
                                    self.name(&t),
                                    self.name(&ret)
                                ),
                                expr.span,
                            );
                        }
                    }
                    None => {
                        let t = match value {
                            Some(v) => self.check_expr(v, None),
                            None => self.world.nil(),
                        };
                        self.env.ret_collected.push(t);
                    }
                }
                Type::Nothing
            }
            Break(value) => {
                let in_block = self.env.blocks.last().is_some_and(|b| !b.is_lambda);
                if self.env.loop_depth == 0 && !in_block {
                    self.error("`break` outside of a loop or block", expr.span);
                }
                let t = match value {
                    Some(v) => self.check_expr(v, None),
                    None => self.world.nil(),
                };
                if in_block && self.env.loop_depth == 0 {
                    if let Some(b) = self.env.blocks.last_mut() {
                        b.breaks.push(t);
                    }
                }
                Type::Nothing
            }
            Next(value) => {
                let in_block = !self.env.blocks.is_empty();
                if self.env.loop_depth == 0 && !in_block {
                    self.error("`next` outside of a loop or block", expr.span);
                    return Type::Nothing;
                }
                if in_block && self.env.loop_depth == 0 {
                    let ret = self.env.blocks.last().unwrap().ret.clone();
                    let void = self.world.is_nil_type(&self.resolve(&ret));
                    let t = match value {
                        Some(v) => self.check_expr(v, if void { None } else { Some(&ret) }),
                        None => self.world.nil(),
                    };
                    if !void && !self.coerce(&t, &ret) {
                        self.error(
                            format!(
                                "`next` has type {} but the block returns {}",
                                self.name(&t),
                                self.name(&ret)
                            ),
                            expr.span,
                        );
                    }
                } else if let Some(v) = value {
                    self.check_expr(v, None);
                }
                Type::Nothing
            }
            Retry => {
                if self.env.in_rescue == 0 {
                    self.error("`retry` outside of a rescue clause", expr.span);
                }
                Type::Nothing
            }
            Seq(exprs) => self.check_body(exprs, expected),
            ClassDef(_)
            | ModuleDef(_)
            | DataDef(_)
            | EnumDef(_)
            | ExtensionDef(_)
            | MethodDef(_)
            | FieldDecl(_)
            | AttrDecl { .. }
            | Mixin { .. }
            | Visibility { .. }
            | Alias { .. }
            | TypeAlias { .. }
            | ConstAssign { .. }
            | Extern { .. } => {
                self.error("declarations are not allowed here", expr.span);
                Type::Nothing
            }
            Using(_) | Require { .. } => self.world.nil(),
        }
    }

    fn contains_break(body: &[Expr]) -> bool {
        fn walk(e: &Expr) -> bool {
            match &e.kind {
                ExprKind::Break(_) => true,
                ExprKind::If { cond, then, els } => {
                    walk(cond)
                        || then.iter().any(walk)
                        || els.as_ref().is_some_and(|b| b.iter().any(walk))
                }
                ExprKind::Begin(b) => {
                    b.body.iter().any(walk) || b.rescues.iter().any(|r| r.body.iter().any(walk))
                }
                ExprKind::Case { whens, els, .. } => {
                    whens.iter().any(|w| w.body.iter().any(walk))
                        || els.as_ref().is_some_and(|b| b.iter().any(walk))
                }
                ExprKind::CaseIn { arms, els, .. } => {
                    arms.iter().any(|a| a.body.iter().any(walk))
                        || els.as_ref().is_some_and(|b| b.iter().any(walk))
                }
                ExprKind::Seq(es) => es.iter().any(walk),
                ExprKind::And(a, b) | ExprKind::Or(a, b) => walk(a) || walk(b),
                ExprKind::Not(a) => walk(a),
                ExprKind::Assign { value, .. } | ExprKind::OpAssign { value, .. } => walk(value),
                _ => false,
            }
        }
        body.iter().any(walk)
    }

    fn check_str_parts(&mut self, parts: &[StrPart]) {
        for p in parts {
            if let StrPart::Interp(e) = p {
                self.check_expr(e, None);
            }
        }
    }

    fn check_array(&mut self, items: &[Arg], expected: Option<&Type>, span: Span) -> Type {
        let expected = expected.map(|e| self.resolve(e));
        // Tuple expectation.
        if let Some(Type::Tuple(ts)) = &expected {
            if ts.len() == items.len() && items.iter().all(|a| matches!(a, Arg::Positional(_))) {
                let mut out = Vec::new();
                for (a, et) in items.iter().zip(ts.iter()) {
                    let Arg::Positional(e) = a else {
                        unreachable!()
                    };
                    let t = self.check_expr(e, Some(et));
                    if !self.coerce(&t, et) {
                        self.error(
                            format!("expected {} but found {}", self.name(et), self.name(&t)),
                            e.span,
                        );
                    }
                    out.push(et.clone());
                }
                return Type::Tuple(out);
            }
        }
        let elem_expected = match &expected {
            Some(Type::Class(id, args)) if *id == self.world.builtin.array && args.len() == 1 => {
                Some(args[0].clone())
            }
            _ => None,
        };
        let mut elem = Type::Nothing;
        for a in items {
            match a {
                Arg::Positional(e) => {
                    let t = self.check_expr(e, elem_expected.as_ref());
                    elem = self.join(&elem, &t);
                }
                Arg::Splat(e) => {
                    let t = self.check_expr(e, None);
                    let t = self.resolve(&t);
                    match &t {
                        Type::Class(id, args)
                            if *id == self.world.builtin.array && args.len() == 1 =>
                        {
                            elem = self.join(&elem, &args[0].clone());
                        }
                        Type::Tuple(ts) => {
                            for x in ts.clone() {
                                elem = self.join(&elem, &x);
                            }
                        }
                        _ => self.error(format!("cannot splat {}", self.name(&t)), e.span),
                    }
                }
                _ => self.error("unexpected argument form in an array literal", a.span()),
            }
        }
        if let Some(et) = &elem_expected {
            if elem.is_nothing() || self.coerce(&elem, et) {
                return self.world.array_of(et.clone());
            }
            self.error(
                format!(
                    "array elements have type {} but {} was expected",
                    self.name(&elem),
                    self.name(et)
                ),
                span,
            );
            return self.world.array_of(et.clone());
        }
        if elem.is_nothing() {
            elem = self.infer.fresh();
        }
        self.world.array_of(elem)
    }

    fn check_hash(&mut self, entries: &[HashEntry], expected: Option<&Type>) -> Type {
        let expected = expected.map(|e| self.resolve(e));
        let (ek, ev) = match &expected {
            Some(Type::Class(id, args)) if *id == self.world.builtin.hash && args.len() == 2 => {
                (Some(args[0].clone()), Some(args[1].clone()))
            }
            _ => (None, None),
        };
        let mut kt = Type::Nothing;
        let mut vt = Type::Nothing;
        for e in entries {
            match e {
                HashEntry::Pair { key, value } => {
                    let k = self.check_expr(key, ek.as_ref());
                    let v = self.check_expr(value, ev.as_ref());
                    kt = self.join(&kt, &k);
                    vt = self.join(&vt, &v);
                }
                HashEntry::DoubleSplat(x) => {
                    let t = self.check_expr(x, None);
                    match self.resolve(&t) {
                        Type::Class(id, args)
                            if id == self.world.builtin.hash && args.len() == 2 =>
                        {
                            kt = self.join(&kt, &args[0].clone());
                            vt = self.join(&vt, &args[1].clone());
                        }
                        other => self.error(
                            format!("cannot splat {} into a hash", self.name(&other)),
                            x.span,
                        ),
                    }
                }
            }
        }
        if let (Some(ek), Some(ev)) = (&ek, &ev) {
            let ok = (kt.is_nothing() || self.coerce(&kt, ek))
                && (vt.is_nothing() || self.coerce(&vt, ev));
            if !ok {
                let span = entries.first().map(|e| match e {
                    HashEntry::Pair { key, .. } => key.span,
                    HashEntry::DoubleSplat(x) => x.span,
                });
                self.error(
                    format!(
                        "hash has type Hash[{}, {}] but Hash[{}, {}] was expected",
                        self.name(&kt),
                        self.name(&vt),
                        self.name(ek),
                        self.name(ev)
                    ),
                    span.unwrap_or(Span::empty(0)),
                );
            }
            return self.world.hash_of(ek.clone(), ev.clone());
        }
        if kt.is_nothing() {
            kt = self.infer.fresh();
        }
        if vt.is_nothing() {
            vt = self.infer.fresh();
        }
        self.world.hash_of(kt, vt)
    }

    fn check_ivar_read(&mut self, expr: &Expr, name: &str) -> Type {
        let Some(cid) = self.env.class_id else {
            self.error("instance variables are not available here", expr.span);
            return Type::Nothing;
        };
        if self.world.class(cid).kind == ClassKind::Main {
            self.error(
                "instance variables are not available at the top level",
                expr.span,
            );
            return Type::Nothing;
        }
        let Some((field, subst)) = self.world.find_field(cid, name) else {
            self.error(
                format!(
                    "undeclared field `@{name}` in `{}`",
                    self.world.class(cid).name
                ),
                expr.span,
            );
            return Type::Nothing;
        };
        let index = self.world.field_index(cid, name).unwrap();
        self.out.ivar_fields.insert(expr.id, index);
        if !field.mutable {
            if let Some(t) = self.env.ivar_narrow.get(name) {
                return t.clone();
            }
        }
        field.ty.subst(&subst)
    }

    fn check_const(&mut self, expr: &Expr, path: &ConstPath) -> Type {
        let namespace = self.env.scope.namespace;
        let Some(member) = self.resolve_path(namespace, path, expr.span) else {
            return Type::Nothing;
        };
        match member {
            Member::Class(id) => {
                let class = self.world.class(id);
                if class.kind == ClassKind::Variant && class.fields.is_empty() {
                    self.out
                        .const_targets
                        .insert(expr.id, ConstTarget::VariantSingleton(id));
                    return Type::class(id);
                }
                self.out
                    .const_targets
                    .insert(expr.id, ConstTarget::Class(id));
                Type::ClassObject(id, vec![])
            }
            Member::Const(cid) => {
                self.out
                    .const_targets
                    .insert(expr.id, ConstTarget::Const(cid));
                self.const_type(cid, expr.span)
            }
            Member::Alias(_) => {
                self.error(format!("`{path}` is a type alias, not a value"), expr.span);
                Type::Nothing
            }
        }
    }

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
                self.error(format!("`{path}` is not a namespace"), span);
                return None;
            };
            member = self.world.member_in(Some(cid), name);
            if member.is_none() {
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

    pub fn resolve_type_expr(&mut self, te: &TypeExpr, scope: &TypeScope) -> Option<Type> {
        // Reuse the declarer's resolution logic through a temporary.
        let mut d = crate::declare::Declarer::new();
        std::mem::swap(&mut d.world, &mut self.world);
        let t = d.resolve_type(te, scope);
        std::mem::swap(&mut d.world, &mut self.world);
        for (_, diag) in d.diagnostics {
            self.diagnostics.push((self.env.file, diag));
        }
        t
    }

    // ----- conditions and narrowing ----------------------------------------------

    /// Check a condition and compute the narrowings that hold when it is
    /// true and when it is false.
    fn check_cond(&mut self, cond: &Expr) -> (Type, Facts, Facts) {
        use ExprKind::*;
        match &cond.kind {
            Not(inner) => {
                let (t, ft, ff) = self.check_cond(inner);
                self.record(inner.id, &t);
                let bt = self.world.bool_();
                self.record(cond.id, &bt);
                (bt, ff, ft)
            }
            And(a, b) => {
                let (ta, fat, _) = self.check_cond(a);
                let snap = self.snapshot();
                self.apply_facts(&fat);
                let (tb, fbt, _) = self.check_cond(b);
                self.merge_with(&snap, false, tb.is_nothing());
                let mut facts_true = fat;
                facts_true.extend(fbt);
                let t = if self.resolve(&ta) == self.world.bool_()
                    && self.resolve(&tb) == self.world.bool_()
                {
                    self.world.bool_()
                } else {
                    let fa = self.falsy_part(&ta);
                    self.join(&fa, &tb)
                };
                self.record(cond.id, &t);
                (t, facts_true, Vec::new())
            }
            Or(a, b) => {
                let (ta, _, faf) = self.check_cond(a);
                let snap = self.snapshot();
                self.apply_facts(&faf);
                let (tb, _, fbf) = self.check_cond(b);
                self.merge_with(&snap, false, tb.is_nothing());
                let mut facts_false = faf;
                facts_false.extend(fbf);
                let t = if self.resolve(&ta) == self.world.bool_()
                    && self.resolve(&tb) == self.world.bool_()
                {
                    self.world.bool_()
                } else {
                    let truthy = self.truthy_part(&ta);
                    self.join(&truthy, &tb)
                };
                self.record(cond.id, &t);
                (t, Vec::new(), facts_false)
            }
            Local(name) => {
                let t = self.check_expr(cond, None);
                let key = VarKey::Local(name.clone());
                (
                    t.clone(),
                    vec![(key.clone(), self.truthy_part(&t))],
                    vec![(key, self.falsy_part(&t))],
                )
            }
            IVar(name) => {
                let t = self.check_expr(cond, None);
                let mutable = self
                    .env
                    .class_id
                    .and_then(|c| self.world.find_field(c, name))
                    .is_some_and(|(f, _)| f.mutable);
                if mutable {
                    return (t, Vec::new(), Vec::new());
                }
                let key = VarKey::IVar(name.clone());
                (
                    t.clone(),
                    vec![(key.clone(), self.truthy_part(&t))],
                    vec![(key, self.falsy_part(&t))],
                )
            }
            Assign { target, value } => {
                let t = self.check_expr(cond, None);
                if let LValue::Local { name, .. } = &**target {
                    let key = VarKey::Local(name.clone());
                    let vt = self.resolve(&t);
                    let _ = value;
                    return (
                        t.clone(),
                        vec![(key.clone(), self.truthy_part(&vt))],
                        vec![(key, self.falsy_part(&vt))],
                    );
                }
                (t, Vec::new(), Vec::new())
            }
            MatchPattern {
                value,
                pattern,
                raises: false,
            } => {
                let vt = self.check_expr(value, None);
                let vt = self.resolve(&vt);
                let facts = self.check_pattern_facts(pattern, &vt, value);
                let bt = self.world.bool_();
                self.record(cond.id, &bt);
                (bt, facts, Vec::new())
            }
            Call(call) => {
                let t = self.check_expr(cond, None);
                let key = call.recv.as_ref().and_then(|r| self.var_key(r));
                let Some(key) = key else {
                    return (t, Vec::new(), Vec::new());
                };
                let recv_ty = self.resolve(&self.out.node_types[&call.recv.as_ref().unwrap().id]);
                match (call.name.as_str(), call.args.as_slice()) {
                    ("nil?", []) => {
                        let nil = self.world.nil();
                        let without = recv_ty.without_nil(self.world.builtin.nil);
                        (t, vec![(key.clone(), nil)], vec![(key, without)])
                    }
                    ("is_a?", [_]) => {
                        let Some(CallTarget::IsA(target)) = self.out.calls.get(&cond.id).cloned()
                        else {
                            return (t, Vec::new(), Vec::new());
                        };
                        let (yes, no) = self.split_by_type(&recv_ty, &target);
                        (t, vec![(key.clone(), yes)], vec![(key, no)])
                    }
                    ("==", [Arg::Positional(arg)]) | ("!=", [Arg::Positional(arg)]) => {
                        let is_nil = matches!(arg.kind, ExprKind::Nil);
                        if !is_nil {
                            return (t, Vec::new(), Vec::new());
                        }
                        let nil = self.world.nil();
                        let without = recv_ty.without_nil(self.world.builtin.nil);
                        if call.name == "==" {
                            (t, vec![(key.clone(), nil)], vec![(key, without)])
                        } else {
                            (t, vec![(key.clone(), without)], vec![(key, nil)])
                        }
                    }
                    _ => (t, Vec::new(), Vec::new()),
                }
            }
            _ => {
                let t = self.check_expr(cond, None);
                (t, Vec::new(), Vec::new())
            }
        }
    }

    fn var_key(&self, e: &Expr) -> Option<VarKey> {
        match &e.kind {
            ExprKind::Local(name) => Some(VarKey::Local(name.clone())),
            ExprKind::IVar(name) => {
                let mutable = self
                    .env
                    .class_id
                    .and_then(|c| self.world.find_field(c, name))
                    .is_some_and(|(f, _)| f.mutable);
                if mutable {
                    None
                } else {
                    Some(VarKey::IVar(name.clone()))
                }
            }
            _ => None,
        }
    }

    /// Split a type into the part that is a `target` and the rest.
    pub fn split_by_type(&mut self, t: &Type, target: &Type) -> (Type, Type) {
        let t = self.resolve(t);
        let mut yes = Vec::new();
        let mut no = Vec::new();
        for m in self.expand_members(&t) {
            if self.world.is_subtype(&m, target) {
                yes.push(m);
            } else if self.world.is_subtype(target, &m) {
                // `Object` narrowed to `Int`: the member is a supertype.
                yes.push(target.clone());
                no.push(m);
            } else if let (Type::Class(mid, _), Type::Class(tid, _)) = (&m, target) {
                // Unrelated classes may still overlap via a module.
                if self.world.class(*tid).kind == ClassKind::Module
                    || self.world.class(*mid).kind == ClassKind::Module
                {
                    yes.push(target.clone());
                }
                no.push(m);
            } else {
                no.push(m);
            }
        }
        (Type::union_of(yes), Type::union_of(no))
    }

    /// Union members, with enums expanded to their variants.
    pub fn expand_members(&self, t: &Type) -> Vec<Type> {
        let mut out = Vec::new();
        for m in t.members() {
            match &m {
                Type::Class(id, args) if self.world.class(*id).kind == ClassKind::Enum => {
                    for v in &self.world.class(*id).variants {
                        out.push(Type::Class(*v, args.clone()));
                    }
                }
                _ => out.push(m),
            }
        }
        out
    }

    fn check_if(
        &mut self,
        cond: &Expr,
        then: &[Expr],
        els: Option<&[Expr]>,
        expected: Option<&Type>,
    ) -> Type {
        let (ct, facts_true, facts_false) = self.check_cond(cond);
        match self.is_truthy_type(&ct) {
            Some(true) => self.warning("condition is always true", cond.span),
            Some(false) => self.warning("condition is always false", cond.span),
            None => {}
        }
        let before = self.snapshot();
        self.apply_facts(&facts_true);
        let tt = self.check_body(then, expected);
        let then_snap = self.snapshot();
        let then_dead = tt.is_nothing();
        self.restore(&before);
        self.apply_facts(&facts_false);
        let et = match els {
            Some(els) => self.check_body(els, expected),
            None => self.world.nil(),
        };
        let else_dead = et.is_nothing();
        self.merge_with(&then_snap, then_dead, else_dead);
        self.join(&tt, &et)
    }

    fn check_case_when(
        &mut self,
        subject: Option<&Expr>,
        whens: &[When],
        els: Option<&[Expr]>,
        expected: Option<&Type>,
    ) -> Type {
        let subject_ty = subject.map(|s| self.check_expr(s, None));
        let key = subject.and_then(|s| self.var_key(s));
        let mut result = Type::Nothing;
        let before = self.snapshot();
        let mut branch_snaps: Vec<(Snapshot, bool)> = Vec::new();
        let mut remaining = subject_ty.clone().map(|t| self.resolve(&t));
        for w in whens {
            self.restore(&before);
            if let Some(rem) = &remaining {
                if let Some(k) = &key {
                    self.set_narrowed(k, Some(rem.clone()));
                }
            }
            let mut narrowed_to = Vec::new();
            for c in &w.conds {
                let Arg::Positional(ce) = c else {
                    self.error("unsupported `when` condition", c.span());
                    continue;
                };
                let ct = self.check_expr(ce, None);
                let ct = self.resolve(&ct);
                if let (Some(st), Type::ClassObject(cid, _)) = (&subject_ty, &ct) {
                    let target = Type::class(*cid);
                    let (yes, no) = self.split_by_type(st, &target);
                    narrowed_to.push(yes);
                    if let Some(rem) = &remaining {
                        let (_, rest) = self.split_by_type(rem, &target);
                        remaining = Some(rest);
                    }
                    let _ = no;
                } else if let Some(st) = &subject_ty {
                    // Value comparison with `===`.
                    narrowed_to.push(self.resolve(st));
                }
            }
            if let (Some(k), false) = (&key, narrowed_to.is_empty()) {
                let t = Type::union_of(narrowed_to);
                self.set_narrowed(k, Some(t));
            }
            let bt = self.check_body(&w.body, expected);
            branch_snaps.push((self.snapshot(), bt.is_nothing()));
            result = self.join(&result, &bt);
        }
        self.restore(&before);
        let et = match els {
            Some(els) => {
                if let (Some(k), Some(rem)) = (&key, &remaining) {
                    self.set_narrowed(k, Some(rem.clone()));
                }
                self.check_body(els, expected)
            }
            // Type tests that cover the whole subject make the `case`
            // exhaustive.
            None if remaining.as_ref().is_some_and(|r| r.is_nothing()) => Type::Nothing,
            None => self.world.nil(),
        };
        let mut dead = et.is_nothing();
        result = self.join(&result, &et);
        for (snap, d) in branch_snaps.iter().rev() {
            self.merge_with(snap, *d, dead);
            dead = dead && *d;
        }
        result
    }

    fn check_begin(&mut self, block: &BeginBlock, expected: Option<&Type>) -> Type {
        let before = self.snapshot();
        let bt = self.check_body(&block.body, expected);
        let body_dead = bt.is_nothing();
        let after_body = self.snapshot();
        let mut result = bt;
        let mut snaps = Vec::new();
        for r in &block.rescues {
            self.restore(&before);
            // Variables assigned in the body may or may not have been.
            self.widen_assigned(&block.body);
            let mut exc_ty = Type::Nothing;
            let mut class_ids = Vec::new();
            if r.classes.is_empty() {
                exc_ty = Type::class(self.world.builtin.standard_error);
                class_ids.push(self.world.builtin.standard_error);
            }
            for c in &r.classes {
                let scope = self.env.scope.clone();
                match self.resolve_type_expr(c, &scope) {
                    Some(t @ Type::Class(id, _)) if self.world.is_exception_class(id) => {
                        exc_ty = self.join(&exc_ty, &t);
                        class_ids.push(id);
                    }
                    Some(_) => self.error("`rescue` needs exception classes", c.span),
                    None => {}
                }
            }
            self.out.rescue_classes.insert(r.span, class_ids);
            if let Some(var) = &r.var {
                if self.lookup_var(var).is_none_or(|(d, _)| d != 0) {
                    self.declare_var(var, exc_ty.clone(), r.span);
                } else {
                    let (depth, slot) = self.lookup_var(var).unwrap();
                    self.out.var_refs.insert(
                        r.span,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    self.set_narrowed(&VarKey::Local(var.clone()), Some(exc_ty.clone()));
                }
            }
            self.env.in_rescue += 1;
            let rt = self.check_body(&r.body, expected);
            self.env.in_rescue -= 1;
            snaps.push((self.snapshot(), rt.is_nothing()));
            result = self.join(&result, &rt);
        }
        self.restore(&after_body);
        if let Some(else_body) = &block.else_body {
            if !body_dead {
                let et = self.check_body(else_body, expected);
                result = self.join(&result, &et);
            }
        }
        let mut dead = result.is_nothing();
        for (snap, d) in snaps.iter().rev() {
            self.merge_with(snap, *d, dead);
            dead = dead && *d;
        }
        if let Some(ensure) = &block.ensure {
            let saved = self.snapshot();
            self.check_body(ensure, None);
            self.restore(&saved);
        }
        result
    }

    // ----- assignment ---------------------------------------------------------------

    fn check_assign(
        &mut self,
        expr: &Expr,
        target: &LValue,
        value: &Expr,
        _expected: Option<&Type>,
    ) -> Type {
        match target {
            LValue::Local { name, span } => {
                if let Some((depth, slot)) = self.lookup_var(name) {
                    if self.captured_across_task(depth) {
                        self.error(
                            format!("cannot assign to `{name}` from a `spawn` block; it is captured by value"),
                            *span,
                        );
                    }
                    let declared = {
                        let n = self.env.frames.len();
                        self.env.frames[n - 1 - depth].vars[slot].declared.clone()
                    };
                    let vt = self.check_expr(value, Some(&declared));
                    if !self.coerce(&vt, &declared) {
                        self.error(
                            format!(
                                "cannot assign {} to `{name}` of type {}",
                                self.name(&vt),
                                self.name(&declared)
                            ),
                            value.span,
                        );
                    }
                    self.out.var_refs.insert(
                        *span,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    let narrowed = self.resolve(&vt);
                    self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
                    vt
                } else {
                    let vt = self.check_expr(value, None);
                    let declared = self.resolve(&vt);
                    let declared = if declared.is_nothing() {
                        self.world.nil()
                    } else {
                        declared
                    };
                    self.declare_var(name, declared, *span);
                    vt
                }
            }
            LValue::IVar(name) => {
                let Some(cid) = self.env.class_id else {
                    self.error("instance variables are not available here", expr.span);
                    return self.check_expr(value, None);
                };
                let Some((field, subst)) = self.world.find_field(cid, name) else {
                    self.error(format!("undeclared field `@{name}`"), expr.span);
                    return self.check_expr(value, None);
                };
                if !field.mutable && !self.env.in_initialize {
                    self.error(
                        format!("field `@{name}` is immutable; declare it with `var` or assign it in `initialize`"),
                        expr.span,
                    );
                }
                let fty = field.ty.subst(&subst);
                let vt = self.check_expr(value, Some(&fty));
                if !self.coerce(&vt, &fty) {
                    self.error(
                        format!(
                            "cannot assign {} to `@{name}` of type {}",
                            self.name(&vt),
                            self.name(&fty)
                        ),
                        value.span,
                    );
                }
                let index = self.world.field_index(cid, name).unwrap();
                self.out.ivar_fields.insert(expr.id, index);
                self.env.assigned_fields.insert(name.clone());
                if !field.mutable {
                    let narrowed = self.resolve(&vt);
                    self.env.ivar_narrow.insert(name.clone(), narrowed);
                }
                vt
            }
            LValue::Const(name) => {
                self.error(format!("cannot reassign constant `{name}`"), expr.span);
                self.check_expr(value, None)
            }
            LValue::Attr {
                recv,
                name,
                safe_nav,
            } => {
                let call = Call {
                    recv: Some(recv.clone()),
                    name: format!("{name}="),
                    args: vec![Arg::Positional(value.clone())],
                    block: None,
                    safe_nav: *safe_nav,
                    has_parens: true,
                    type_args: vec![],
                };
                self.check_call(expr, &call, None);
                self.out
                    .node_types
                    .get(&value.id)
                    .cloned()
                    .unwrap_or(Type::Nothing)
            }
            LValue::Index { recv, args } => {
                let mut all = args.clone();
                all.push(Arg::Positional(value.clone()));
                let call = Call {
                    recv: Some(recv.clone()),
                    name: "[]=".to_string(),
                    args: all,
                    block: None,
                    safe_nav: false,
                    has_parens: true,
                    type_args: vec![],
                };
                self.check_call(expr, &call, None);
                self.out
                    .node_types
                    .get(&value.id)
                    .cloned()
                    .unwrap_or(Type::Nothing)
            }
        }
    }

    fn check_op_assign(
        &mut self,
        expr: &Expr,
        target: &LValue,
        op: OpAssign,
        value: &Expr,
    ) -> Type {
        // Type the current value of the target.
        let current = match target {
            LValue::Local { name, span } => match self.lookup_var(name) {
                Some((depth, slot)) => {
                    if self.captured_across_task(depth) {
                        self.error(
                            format!("cannot assign to `{name}` from a `spawn` block; it is captured by value"),
                            *span,
                        );
                    }
                    self.out.var_refs.insert(
                        *span,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    self.var_type(depth, slot)
                }
                None => {
                    self.error(format!("undefined local variable `{name}`"), expr.span);
                    return Type::Nothing;
                }
            },
            LValue::IVar(name) => {
                let read = Expr {
                    id: expr.id,
                    span: expr.span,
                    kind: ExprKind::IVar(name.clone()),
                };
                let t = self.check_ivar_read(&read, name);
                if let Some(cid) = self.env.class_id {
                    if let Some((f, _)) = self.world.find_field(cid, name) {
                        if !f.mutable && !self.env.in_initialize {
                            self.error(format!("field `@{name}` is immutable"), expr.span);
                        }
                    }
                }
                t
            }
            LValue::Attr { recv, name, .. } => {
                let rt = self.check_expr(recv, None);
                let getter = Call {
                    recv: Some(recv.clone()),
                    name: name.clone(),
                    args: vec![],
                    block: None,
                    safe_nav: false,
                    has_parens: false,
                    type_args: vec![],
                };
                let _ = rt;
                self.check_call_with_types(expr, &getter, None, true)
            }
            LValue::Index { recv, args } => {
                let getter = Call {
                    recv: Some(recv.clone()),
                    name: "[]".to_string(),
                    args: args.clone(),
                    block: None,
                    safe_nav: false,
                    has_parens: true,
                    type_args: vec![],
                };
                self.check_call_with_types(expr, &getter, None, true)
            }
            LValue::Const(name) => {
                self.error(format!("cannot reassign constant `{name}`"), expr.span);
                return Type::Nothing;
            }
        };
        let current = self.resolve(&current);
        let result = match op {
            OpAssign::OrOr => {
                // `x ||= v`: v is evaluated only when x is falsy.
                let vt = self.check_expr(value, Some(&current));
                let truthy = self.truthy_part(&current);
                self.join(&truthy, &vt)
            }
            OpAssign::AndAnd => {
                let vt = self.check_expr(value, Some(&current));
                let falsy = self.falsy_part(&current);
                self.join(&falsy, &vt)
            }
            _ => {
                let name = op.as_str().trim_end_matches('=').to_string();
                let vt = self.check_expr(value, None);
                self.check_operator_call(expr, &current, &name, &vt, value)
            }
        };
        // Assign back.
        match target {
            LValue::Local { name, .. } => {
                let (depth, slot) = self.lookup_var(name).unwrap();
                let declared = {
                    let n = self.env.frames.len();
                    self.env.frames[n - 1 - depth].vars[slot].declared.clone()
                };
                if !self.coerce(&result, &declared) {
                    self.error(
                        format!(
                            "cannot assign {} to `{name}` of type {}",
                            self.name(&result),
                            self.name(&declared)
                        ),
                        expr.span,
                    );
                }
                let narrowed = self.resolve(&result);
                self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
            }
            LValue::IVar(name) => {
                if let Some(cid) = self.env.class_id {
                    if let Some((f, subst)) = self.world.find_field(cid, name) {
                        let fty = f.ty.subst(&subst);
                        if !self.coerce(&result, &fty) {
                            self.error(
                                format!(
                                    "cannot assign {} to `@{name}` of type {}",
                                    self.name(&result),
                                    self.name(&fty)
                                ),
                                expr.span,
                            );
                        }
                        self.env.assigned_fields.insert(name.clone());
                    }
                }
            }
            LValue::Attr { recv, name, .. } => {
                // Check that the setter accepts the result type.
                let rt = self.resolve(&self.out.node_types[&recv.id]);
                let setter = format!("{name}=");
                let cands = self.world.lookup_methods(&rt, &setter);
                if cands.is_empty() {
                    self.error(
                        format!("undefined method `{setter}` for {}", self.name(&rt)),
                        expr.span,
                    );
                } else {
                    self.out
                        .calls
                        .insert(expr.id, CallTarget::Method { method: cands[0].0 });
                }
            }
            LValue::Index { recv, .. } => {
                let rt = self.resolve(&self.out.node_types[&recv.id]);
                let cands = self.world.lookup_methods(&rt, "[]=");
                if cands.is_empty() {
                    self.error(
                        format!("undefined method `[]=` for {}", self.name(&rt)),
                        expr.span,
                    );
                } else {
                    self.out
                        .calls
                        .insert(expr.id, CallTarget::Method { method: cands[0].0 });
                }
            }
            LValue::Const(_) => {}
        }
        result
    }

    /// Type of `lhs <op> rhs` given the operand types (for compound
    /// assignment).
    fn check_operator_call(
        &mut self,
        expr: &Expr,
        lhs: &Type,
        name: &str,
        rhs: &Type,
        rhs_expr: &Expr,
    ) -> Type {
        let lhs = self.resolve(lhs);
        let cands = self.world.lookup_methods(&lhs, name);
        for (mid, subst) in cands {
            let m = self.world.method(mid).clone();
            let positional: Vec<&ParamInfo> = m
                .params
                .iter()
                .filter(|p| p.kind == ParamKind::Positional)
                .collect();
            if positional.len() != 1 || m.block.is_some() {
                continue;
            }
            let mut subst = subst;
            subst.insert(SELF_PARAM, lhs.clone());
            let pt = positional[0].ty.subst(&subst);
            let saved = self.infer.save();
            if self.coerce(rhs, &pt) {
                self.out
                    .calls
                    .insert(expr.id, CallTarget::Method { method: mid });
                return self.method_ret(mid, expr.span).subst(&subst);
            }
            self.infer.restore(saved);
        }
        self.error(
            format!(
                "no method `{name}` on {} accepting {}",
                self.name(&lhs),
                self.name(rhs)
            ),
            rhs_expr.span,
        );
        Type::Nothing
    }

    fn check_multi_assign(&mut self, expr: &Expr, targets: &[MultiTarget], value: &Expr) -> Type {
        let vt = self.check_expr(value, None);
        let vt = self.resolve(&vt);
        self.assign_multi(targets, &vt, expr.span);
        vt
    }

    fn assign_multi(&mut self, targets: &[MultiTarget], vt: &Type, span: Span) {
        let splat_index = targets
            .iter()
            .position(|t| matches!(t, MultiTarget::Splat(_)));
        let elem_types: Vec<Type> = match vt {
            Type::Tuple(ts) => ts.clone(),
            Type::Class(id, args) if *id == self.world.builtin.array && args.len() == 1 => {
                vec![args[0].clone(); targets.len()]
            }
            _ => {
                self.error(
                    format!(
                        "cannot destructure {} (expected a tuple or array)",
                        self.name(vt)
                    ),
                    span,
                );
                vec![Type::Nothing; targets.len()]
            }
        };
        let array_elem = match vt {
            Type::Tuple(ts) => Type::union_of(ts.clone()),
            Type::Class(_, args) if !args.is_empty() => args[0].clone(),
            _ => Type::Nothing,
        };
        let n_before = splat_index.unwrap_or(targets.len());
        let n_after = splat_index.map(|i| targets.len() - i - 1).unwrap_or(0);
        for (i, t) in targets.iter().enumerate() {
            let ty = if let Some(si) = splat_index {
                if i < si {
                    elem_types
                        .get(i)
                        .cloned()
                        .unwrap_or_else(|| self.world.nil())
                } else if i == si {
                    self.world.array_of(array_elem.clone())
                } else {
                    let from_end = targets.len() - i;
                    if elem_types.len() >= from_end + n_before {
                        elem_types[elem_types.len() - from_end].clone()
                    } else {
                        array_elem.clone()
                    }
                }
            } else {
                match vt {
                    Type::Tuple(ts) if i >= ts.len() => self.world.nil(),
                    _ => elem_types
                        .get(i)
                        .cloned()
                        .unwrap_or_else(|| self.world.nil()),
                }
            };
            let _ = n_after;
            match t {
                MultiTarget::Single(lv) | MultiTarget::Splat(Some(lv)) => {
                    self.assign_lvalue(lv, &ty, span)
                }
                MultiTarget::Splat(None) => {}
                MultiTarget::Nested(ts) => {
                    let rty = self.resolve(&ty);
                    self.assign_multi(ts, &rty, span);
                }
            }
        }
    }

    fn assign_lvalue(&mut self, lv: &LValue, ty: &Type, span: Span) {
        match lv {
            LValue::Local { name, span: vspan } => {
                if let Some((depth, slot)) = self.lookup_var(name) {
                    let declared = {
                        let n = self.env.frames.len();
                        self.env.frames[n - 1 - depth].vars[slot].declared.clone()
                    };
                    if !self.coerce(ty, &declared) {
                        self.error(
                            format!(
                                "cannot assign {} to `{name}` of type {}",
                                self.name(ty),
                                self.name(&declared)
                            ),
                            *vspan,
                        );
                    }
                    self.out.var_refs.insert(
                        *vspan,
                        VarRef {
                            depth: depth as u32,
                            slot: slot as u32,
                        },
                    );
                    let narrowed = self.resolve(ty);
                    self.set_narrowed(&VarKey::Local(name.clone()), Some(narrowed));
                } else {
                    let declared = self.resolve(ty);
                    self.declare_var(name, declared, *vspan);
                }
            }
            LValue::IVar(name) => {
                let Some(cid) = self.env.class_id else {
                    self.error("instance variables are not available here", span);
                    return;
                };
                match self.world.find_field(cid, name) {
                    Some((f, subst)) => {
                        let fty = f.ty.subst(&subst);
                        if !f.mutable && !self.env.in_initialize {
                            self.error(format!("field `@{name}` is immutable"), span);
                        }
                        if !self.coerce(ty, &fty) {
                            self.error(
                                format!(
                                    "cannot assign {} to `@{name}` of type {}",
                                    self.name(ty),
                                    self.name(&fty)
                                ),
                                span,
                            );
                        }
                        self.env.assigned_fields.insert(name.clone());
                    }
                    None => self.error(format!("undeclared field `@{name}`"), span),
                }
            }
            _ => self.error("unsupported target in multiple assignment", span),
        }
    }

    // ----- calls -------------------------------------------------------------------

    fn check_call(&mut self, expr: &Expr, call: &Call, expected: Option<&Type>) -> Type {
        self.check_call_with_types(expr, call, expected, false)
    }

    /// `quiet`: used when re-typing a getter for compound assignment (the
    /// receiver was already checked).
    fn check_call_with_types(
        &mut self,
        expr: &Expr,
        call: &Call,
        expected: Option<&Type>,
        _quiet: bool,
    ) -> Type {
        // Special forms.
        if call.recv.is_none() && call.name == "raise" {
            return self.check_raise(expr, call);
        }
        if let Some(recv) = &call.recv {
            match call.name.as_str() {
                "is_a?" | "as" | "as?" if call.args.len() == 1 && call.block.is_none() => {
                    return self.check_type_test(expr, call, recv);
                }
                "respond_to?" if call.args.len() == 1 => {
                    let rt = self.check_expr(recv, None);
                    let rt = self.resolve(&rt);
                    let Arg::Positional(a) = &call.args[0] else {
                        self.error("respond_to? takes a symbol", expr.span);
                        return self.world.bool_();
                    };
                    let answer = match &a.kind {
                        ExprKind::Symbol(name) => !self.world.lookup_methods(&rt, name).is_empty(),
                        _ => {
                            self.error("respond_to? takes a symbol literal", a.span);
                            false
                        }
                    };
                    self.check_expr(a, None);
                    self.out.calls.insert(expr.id, CallTarget::Constant(answer));
                    return self.world.bool_();
                }
                _ => {}
            }
        }

        // `[a, b] <=> [c, d]` / `[a, b] == [c, d]`: compare element-wise as
        // tuples, so that each element only needs to be comparable with its
        // counterpart.
        if let (Some(recv), "<=>" | "==" | "!=", [Arg::Positional(arg)]) =
            (&call.recv, call.name.as_str(), call.args.as_slice())
        {
            if let (ExprKind::Array(xs), ExprKind::Array(ys)) = (&recv.kind, &arg.kind) {
                if xs.len() == ys.len() && call.block.is_none() {
                    return self.check_tuple_compare(expr, call, recv, xs, arg, ys);
                }
            }
        }

        // Receiver.
        let (recv_ty, implicit_self) = match &call.recv {
            Some(r) => {
                let t = self.check_expr(r, None);
                (self.resolve(&t), matches!(r.kind, ExprKind::SelfRef))
            }
            None => (self.env.self_type.clone(), true),
        };
        // `Array.build { }`: a generic class used without arguments gets
        // fresh inference variables for its parameters.
        let recv_ty = match recv_ty {
            Type::ClassObject(cid, args)
                if args.is_empty() && !self.world.class(cid).type_params.is_empty() =>
            {
                let n = self.world.class(cid).type_params.len();
                let fresh: Vec<Type> = (0..n).map(|_| self.infer.fresh()).collect();
                Type::ClassObject(cid, fresh)
            }
            t => t,
        };
        if recv_ty.is_nothing() {
            // Error already reported, or unreachable code.
            self.check_args_blindly(call);
            return Type::Nothing;
        }

        // Safe navigation: `nil` passes through.
        let (recv_ty, nil_passthrough) = if call.safe_nav {
            let without = recv_ty.without_nil(self.world.builtin.nil);
            let had_nil = without != recv_ty;
            if !had_nil {
                self.warning("`&.` on a receiver that is never nil", expr.span);
            }
            if without.is_nothing() {
                // Always nil: the call never happens.
                self.check_args_blindly(call);
                return self.world.nil();
            }
            (without, had_nil)
        } else {
            (recv_ty, false)
        };

        let result = self.check_call_on(expr, call, &recv_ty, implicit_self, expected);
        if nil_passthrough {
            let nil = self.world.nil();
            self.join(&result, &nil)
        } else {
            result
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_tuple_compare(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv: &Expr,
        xs: &[Arg],
        arg: &Expr,
        ys: &[Arg],
    ) -> Type {
        let mut lhs = Vec::new();
        for x in xs {
            let Arg::Positional(e) = x else {
                self.error("unexpected argument form", x.span());
                return Type::Nothing;
            };
            let t = self.check_expr(e, None);
            lhs.push(self.resolve(&t));
        }
        let mut rhs = Vec::new();
        for (y, lt) in ys.iter().zip(lhs.iter()) {
            let Arg::Positional(e) = y else {
                self.error("unexpected argument form", y.span());
                return Type::Nothing;
            };
            let t = self.check_expr(e, Some(lt));
            rhs.push(self.resolve(&t));
        }
        self.record(recv.id, &Type::Tuple(lhs.clone()));
        self.record(arg.id, &Type::Tuple(rhs.clone()));
        let op = if call.name == "<=>" { "<=>" } else { "==" };
        for ((lt, rt), x) in lhs.iter().zip(rhs.iter()).zip(xs.iter()) {
            let Arg::Positional(xe) = x else {
                unreachable!()
            };
            let cands = self.world.lookup_methods(lt, op);
            let mut ok = false;
            for (mid, subst) in cands {
                let m = self.world.method(mid).clone();
                let positional: Vec<&ParamInfo> = m
                    .params
                    .iter()
                    .filter(|p| p.kind == ParamKind::Positional)
                    .collect();
                if positional.len() != 1 {
                    continue;
                }
                let mut subst = subst;
                subst.insert(SELF_PARAM, lt.clone());
                let pt = positional[0].ty.subst(&subst);
                let saved = self.infer.save();
                if self.coerce(rt, &pt) {
                    ok = true;
                    break;
                }
                self.infer.restore(saved);
            }
            if !ok {
                self.error(
                    format!(
                        "cannot compare {} with {} using `{op}`",
                        self.name(lt),
                        self.name(rt)
                    ),
                    xe.span,
                );
            }
        }
        // The runtime compares arrays element-wise.
        let arr = self.world.array_of(self.world.object());
        if let Some((mid, _)) = self.world.lookup_methods(&arr, &call.name).first() {
            self.out
                .calls
                .insert(expr.id, CallTarget::Method { method: *mid });
        }
        if op == "<=>" {
            self.world.int()
        } else {
            self.world.bool_()
        }
    }

    fn check_args_blindly(&mut self, call: &Call) {
        for a in &call.args {
            match a {
                Arg::Positional(e) | Arg::Splat(e) | Arg::DoubleSplat(e) | Arg::BlockPass(e) => {
                    self.check_expr(e, None);
                }
                Arg::Keyword { value, .. } => {
                    self.check_expr(value, None);
                }
            }
        }
    }

    fn check_call_on(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        implicit_self: bool,
        expected: Option<&Type>,
    ) -> Type {
        let name = call.name.as_str();
        match recv_ty {
            Type::Union(members) => {
                // Each member must accept the call; the result is the join.
                let members = members.clone();
                let mut result = Type::Nothing;
                let mut first = true;
                for m in &members {
                    let t = if first {
                        self.check_call_on(expr, call, m, implicit_self, expected)
                    } else {
                        // Re-resolve without re-reporting argument errors for
                        // already typed arguments.
                        self.check_call_on(expr, call, m, implicit_self, expected)
                    };
                    first = false;
                    result = self.join(&result, &t);
                }
                result
            }
            Type::Var(_) => {
                self.error(
                    format!("cannot call `{name}` on a value whose type is not yet known; add a type annotation"),
                    expr.span,
                );
                self.check_args_blindly(call);
                Type::Nothing
            }
            // `f.call(x)`, `f.(x)` and `f[x]` all call the procedure.
            Type::Proc(params, ret) if name == "call" || name == "[]" => {
                let params = params.clone();
                let ret = (**ret).clone();
                let positional: Vec<&Expr> = call
                    .args
                    .iter()
                    .filter_map(|a| match a {
                        Arg::Positional(e) => Some(e),
                        _ => None,
                    })
                    .collect();
                if positional.len() != params.len() || positional.len() != call.args.len() {
                    self.error(
                        format!(
                            "procedure takes {} argument(s), {} given",
                            params.len(),
                            call.args.len()
                        ),
                        expr.span,
                    );
                    self.check_args_blindly(call);
                    return ret;
                }
                for (e, p) in positional.iter().zip(params.iter()) {
                    let t = self.check_expr(e, Some(p));
                    if !self.coerce(&t, p) {
                        self.error(
                            format!("expected {} but found {}", self.name(p), self.name(&t)),
                            e.span,
                        );
                    }
                }
                if call.block.is_some() {
                    self.error("a procedure call does not take a block", expr.span);
                }
                self.out.calls.insert(expr.id, CallTarget::ProcCall);
                ret
            }
            Type::Tuple(ts) if name == "[]" && call.args.len() == 1 && call.block.is_none() => {
                let ts = ts.clone();
                if let Arg::Positional(Expr {
                    kind: ExprKind::Int(lit),
                    ..
                }) = &call.args[0]
                {
                    if let Ok(i) = lit.digits.parse::<usize>() {
                        if let Some(t) = ts.get(i) {
                            self.check_args_blindly(call);
                            let elem = Type::union_of(ts.clone());
                            let arr = self.world.array_of(elem);
                            let cands = self.world.lookup_methods(&arr, "[]");
                            if let Some((mid, _)) = cands.first() {
                                self.out
                                    .calls
                                    .insert(expr.id, CallTarget::Method { method: *mid });
                            }
                            return t.clone();
                        }
                        self.error(
                            format!("tuple index {i} out of range for {}", self.name(recv_ty)),
                            expr.span,
                        );
                        return Type::Nothing;
                    }
                }
                let elem = Type::union_of(ts);
                let arr = self.world.array_of(elem);
                self.check_call_on(expr, call, &arr, implicit_self, expected)
            }
            Type::ClassObject(cid, args) if name == "new" => {
                let cid = *cid;
                let args = args.clone();
                // Prelude singletons named `new` take precedence.
                let cands = self.world.lookup_methods(recv_ty, "new");
                let own: Vec<_> = cands
                    .into_iter()
                    .filter(|(m, _)| self.world.method(*m).singleton)
                    .collect();
                if !own.is_empty() {
                    let t =
                        self.resolve_overloads(expr, call, recv_ty, own, implicit_self, expected);
                    self.check_class_bounds(&t, expr.span);
                    return t;
                }
                self.check_constructor(expr, call, cid, &args, expected)
            }
            _ => {
                let mut cands = self.world.lookup_methods(recv_ty, name);
                if cands.is_empty() && call.recv.is_none() {
                    // Top-level functions of the file.
                    if let Some(fm) = self.file_main(self.env.file) {
                        let main = Type::class(fm);
                        cands = self.world.lookup_methods(&main, name);
                    }
                }
                if cands.is_empty() {
                    let msg = if call.recv.is_none() && call.args.is_empty() && !call.has_parens {
                        format!(
                            "undefined local variable or method `{name}` for {}",
                            self.name(recv_ty)
                        )
                    } else {
                        format!("undefined method `{name}` for {}", self.name(recv_ty))
                    };
                    self.error(msg, expr.span);
                    self.check_args_blindly(call);
                    return Type::Nothing;
                }
                self.resolve_overloads(expr, call, recv_ty, cands, implicit_self, expected)
            }
        }
    }

    fn check_constructor(
        &mut self,
        expr: &Expr,
        call: &Call,
        cid: ClassId,
        args: &[Type],
        expected: Option<&Type>,
    ) -> Type {
        let class = self.world.class(cid).clone();
        if class.is_abstract || matches!(class.kind, ClassKind::Module | ClassKind::Enum) {
            self.error(format!("cannot instantiate `{}`", class.name), expr.span);
            self.check_args_blindly(call);
            return Type::Nothing;
        }
        // Instantiate class parameters: explicit args, the expected type, or
        // fresh inference variables.
        let targs: Vec<Type> = if !args.is_empty() {
            args.to_vec()
        } else if let Some(Type::Class(eid, eargs)) = expected.map(|e| self.resolve(e)) {
            if eid == cid && eargs.len() == class.type_params.len() {
                eargs
            } else {
                class
                    .type_params
                    .iter()
                    .map(|_| self.infer.fresh())
                    .collect()
            }
        } else {
            class
                .type_params
                .iter()
                .map(|_| self.infer.fresh())
                .collect()
        };
        let instance = Type::Class(cid, targs.clone());
        let cands = self.world.lookup_methods(&instance, "initialize");
        // Only the class's own (or inherited) initialize, not Object's.
        let cands: Vec<_> = cands
            .into_iter()
            .filter(|(m, _)| !self.world.method(*m).singleton)
            .collect();
        if cands.is_empty() {
            if !call.args.is_empty() || call.block.is_some() {
                self.error(
                    format!("`{}` takes no constructor arguments", class.name),
                    expr.span,
                );
                self.check_args_blindly(call);
            }
            self.out.calls.insert(
                expr.id,
                CallTarget::Constructor {
                    class: cid,
                    init: None,
                },
            );
            return instance;
        }
        // Resolve against initialize's overloads but return the instance.
        let saved_len = self.out.calls.len();
        let _ = saved_len;
        let _ = self.resolve_overloads_as(expr, call, &instance, cands, true, None, true);
        let init = match self.out.calls.get(&expr.id) {
            Some(CallTarget::Method { method }) => Some(*method),
            _ => None,
        };
        self.out
            .calls
            .insert(expr.id, CallTarget::Constructor { class: cid, init });
        self.check_class_bounds(&instance, expr.span);
        instance
    }

    /// Check the bounds of a class's type parameters against the arguments
    /// of an instance type (`Channel[T: Shareable]`).
    fn check_class_bounds(&mut self, instance: &Type, span: Span) {
        let Type::Class(cid, args) = self.resolve(instance) else {
            return;
        };
        let params = self.world.class(cid).type_params.clone();
        for (p, a) in params.iter().zip(args.iter()) {
            if a.has_vars() {
                continue;
            }
            for b in &p.bounds {
                let ok = if matches!(b, Type::Class(bid, _) if *bid == self.world.builtin.shareable)
                {
                    self.world.is_shareable(a)
                } else {
                    self.world.is_subtype(a, b)
                };
                if !ok {
                    self.error(
                        format!(
                            "type argument {} for `{}` of `{}` must be {}",
                            self.world.type_name(a),
                            p.name,
                            self.world.class(cid).name,
                            self.world.type_name(b)
                        ),
                        span,
                    );
                }
            }
        }
    }

    fn resolve_overloads(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        cands: Vec<(MethodId, HashMap<TypeParamId, Type>)>,
        implicit_self: bool,
        expected: Option<&Type>,
    ) -> Type {
        self.resolve_overloads_as(expr, call, recv_ty, cands, implicit_self, expected, false)
    }

    #[allow(clippy::too_many_arguments)]
    fn resolve_overloads_as(
        &mut self,
        expr: &Expr,
        call: &Call,
        recv_ty: &Type,
        cands: Vec<(MethodId, HashMap<TypeParamId, Type>)>,
        implicit_self: bool,
        expected: Option<&Type>,
        is_init: bool,
    ) -> Type {
        // Pre-type arguments that do not benefit from an expected type.
        let mut pre: HashMap<NodeId, Type> = HashMap::new();
        let block_given =
            call.block.is_some() || call.args.iter().any(|a| matches!(a, Arg::BlockPass(_)));
        for a in &call.args {
            let e = match a {
                Arg::Positional(e) | Arg::Splat(e) | Arg::DoubleSplat(e) => e,
                Arg::Keyword { value, .. } => value,
                Arg::BlockPass(_) => continue,
            };
            if !Self::needs_expectation(e) {
                let t = self.check_expr(e, None);
                pre.insert(e.id, t);
            }
        }

        let single = cands.len() == 1;
        let mut failures: Vec<String> = Vec::new();
        for (mid, class_subst) in &cands {
            let m = self.world.method(*mid).clone();
            // Visibility.
            if m.visibility == Visibility::Private && !implicit_self && !is_init {
                failures.push(format!("`{}` is private", m.name));
                continue;
            }
            if (m.block.is_some()) != block_given {
                failures.push(if m.block.is_some() {
                    format!("{} requires a block", self.signature(&m))
                } else {
                    format!("{} does not take a block", self.signature(&m))
                });
                continue;
            }
            let saved_infer = self.infer.save();
            let saved_diags = self.diagnostics.len();
            // Instantiate.
            let mut subst = class_subst.clone();
            subst.insert(SELF_PARAM, recv_ty.clone());
            let mut method_vars = Vec::new();
            if !call.type_args.is_empty() && call.type_args.len() != m.type_params.len() {
                failures.push(format!(
                    "{} takes {} type argument(s)",
                    self.signature(&m),
                    m.type_params.len()
                ));
                continue;
            }
            for (i, tp) in m.type_params.iter().enumerate() {
                let t = if let Some(te) = call.type_args.get(i) {
                    let scope = self.env.scope.clone();
                    self.resolve_type_expr(te, &scope).unwrap_or(Type::Nothing)
                } else {
                    self.infer.fresh()
                };
                method_vars.push((tp.clone(), t.clone()));
                subst.insert(tp.id, t);
            }
            match self.try_candidate(expr, call, &m, &subst, &pre, expected, single) {
                Ok(ret) => {
                    // Bounds of method type parameters.
                    let mut ok = true;
                    for (tp, t) in &method_vars {
                        let rt = self.infer.resolve(t);
                        for b in &tp.bounds {
                            let b = b.subst(&subst);
                            if !self.coerce(&rt, &b) {
                                ok = false;
                                self.error(
                                    format!(
                                        "type argument {} for `{}` does not satisfy the bound {}",
                                        self.name(&rt),
                                        tp.name,
                                        self.name(&b)
                                    ),
                                    expr.span,
                                );
                            }
                        }
                    }
                    // Bounds of the extension's parameters.
                    if let Some(ext) = m.extension {
                        let ext = self.world.extensions[ext as usize].clone();
                        for tp in &ext.type_params {
                            let Some(t) = subst.get(&tp.id).cloned() else {
                                continue;
                            };
                            let rt = self.infer.resolve(&t);
                            for b in &tp.bounds {
                                let b = b.subst(&subst);
                                if !self.coerce(&rt, &b) {
                                    ok = false;
                                    if single {
                                        self.error(
                                            format!(
                                                "`{}` requires {} to be {} (found {})",
                                                m.name,
                                                tp.name,
                                                self.name(&b),
                                                self.name(&rt)
                                            ),
                                            expr.span,
                                        );
                                    }
                                }
                            }
                        }
                    }
                    if !ok && !single {
                        self.infer.restore(saved_infer);
                        self.diagnostics.truncate(saved_diags);
                        failures.push(format!("{}: type bounds not satisfied", self.signature(&m)));
                        continue;
                    }
                    self.out
                        .calls
                        .insert(expr.id, CallTarget::Method { method: *mid });
                    // `loop { }` without `break` never returns.
                    if m.name == "loop" && m.owner == self.world.builtin.kernel {
                        if let Some(b) = &call.block {
                            if !Self::contains_break(&b.body) {
                                return Type::Nothing;
                            }
                        }
                    }
                    return ret;
                }
                Err(reason) => {
                    if !single {
                        self.infer.restore(saved_infer);
                        self.diagnostics.truncate(saved_diags);
                    }
                    failures.push(reason);
                }
            }
        }
        if !single || cands.is_empty() {
            let recv_name = self.name(recv_ty);
            let arg_desc = self.describe_args(call, &pre);
            self.error(
                format!(
                    "no overload of `{}` on {recv_name} matches ({arg_desc}):\n    {}",
                    call.name,
                    failures.join("\n    ")
                ),
                expr.span,
            );
        } else if self.diagnostics.is_empty() {
            self.error(failures.join("; "), expr.span);
        }
        // Still type the block for its own diagnostics.
        if let Some(b) = &call.block {
            let fresh = self.infer.fresh();
            let params: Vec<Type> = b.params.list.iter().map(|_| self.infer.fresh()).collect();
            self.check_block(expr.id, b, &Type::Proc(params, Box::new(fresh)));
        }
        Type::Nothing
    }

    fn describe_args(&self, call: &Call, pre: &HashMap<NodeId, Type>) -> String {
        let mut parts = Vec::new();
        for a in &call.args {
            match a {
                Arg::Positional(e) => parts.push(
                    pre.get(&e.id)
                        .or_else(|| self.out.node_types.get(&e.id))
                        .map(|t| self.name(t))
                        .unwrap_or_else(|| "?".to_string()),
                ),
                Arg::Splat(e) => parts.push(format!(
                    "*{}",
                    pre.get(&e.id)
                        .map(|t| self.name(t))
                        .unwrap_or_else(|| "?".to_string())
                )),
                Arg::DoubleSplat(_) => parts.push("**".to_string()),
                Arg::Keyword { name, value, .. } => parts.push(format!(
                    "{name}: {}",
                    pre.get(&value.id)
                        .map(|t| self.name(t))
                        .unwrap_or_else(|| "?".to_string())
                )),
                Arg::BlockPass(_) => parts.push("&block".to_string()),
            }
        }
        if call.block.is_some() {
            parts.push("{ block }".to_string());
        }
        parts.join(", ")
    }

    pub fn signature(&self, m: &MethodInfo) -> String {
        let mut parts: Vec<String> = m
            .params
            .iter()
            .map(|p| {
                let prefix = match p.kind {
                    ParamKind::Rest => "*",
                    ParamKind::KeywordRest => "**",
                    _ => "",
                };
                let default = if p.default.is_some() { " = ..." } else { "" };
                format!(
                    "{prefix}{}: {}{default}",
                    p.name,
                    self.world.type_name(&p.ty)
                )
            })
            .collect();
        if let Some((name, t)) = &m.block {
            let name = if name == "&" { "" } else { name.as_str() };
            parts.push(format!("&{name}: {}", self.world.type_name(t)));
        }
        let ret = match &m.ret {
            RetType::Known(t) => self.world.type_name(t),
            _ => "?".to_string(),
        };
        format!("{}({}) -> {}", m.name, parts.join(", "), ret)
    }

    /// Expressions whose type depends on the expected type.
    fn needs_expectation(e: &Expr) -> bool {
        matches!(
            e.kind,
            ExprKind::Array(_)
                | ExprKind::Hash(_)
                | ExprKind::Lambda(_)
                | ExprKind::Nil
                | ExprKind::Int(_)
                | ExprKind::Range { .. }
        )
    }

    /// Try to apply a method to the call's arguments. Returns the return type
    /// (with the substitution applied) or a reason for failure.
    #[allow(clippy::too_many_arguments)]
    fn try_candidate(
        &mut self,
        expr: &Expr,
        call: &Call,
        m: &MethodInfo,
        subst: &HashMap<TypeParamId, Type>,
        pre: &HashMap<NodeId, Type>,
        expected: Option<&Type>,
        report: bool,
    ) -> Result<Type, String> {
        // Match arguments to parameters.
        let positional: Vec<usize> = m
            .params
            .iter()
            .enumerate()
            .filter(|(_, p)| p.kind == ParamKind::Positional)
            .map(|(i, _)| i)
            .collect();
        let rest = m.params.iter().position(|p| p.kind == ParamKind::Rest);
        let kwrest = m
            .params
            .iter()
            .position(|p| p.kind == ParamKind::KeywordRest);
        let mut bound: HashMap<usize, Vec<MatchedArg>> = HashMap::new();
        let mut next_pos = 0;
        let mut has_splat = false;
        for a in &call.args {
            match a {
                Arg::Positional(e) => {
                    if let Some(&pi) = positional.get(next_pos) {
                        next_pos += 1;
                        bound.entry(pi).or_default().push(MatchedArg {
                            param_ty: m.params[pi].ty.subst(subst),
                            arg: e,
                            pre_type: pre.get(&e.id).cloned(),
                        });
                    } else if let Some(ri) = rest {
                        let elem = match m.params[ri].ty.subst(subst) {
                            Type::Class(_, args) if args.len() == 1 => args[0].clone(),
                            t => t,
                        };
                        bound.entry(ri).or_default().push(MatchedArg {
                            param_ty: elem,
                            arg: e,
                            pre_type: pre.get(&e.id).cloned(),
                        });
                    } else {
                        return Err(format!(
                            "{} takes {} positional argument(s)",
                            self.signature(m),
                            positional.len()
                        ));
                    }
                }
                Arg::Splat(e) => {
                    has_splat = true;
                    let Some(ri) = rest else {
                        return Err(format!(
                            "{} does not take a variable number of arguments",
                            self.signature(m)
                        ));
                    };
                    bound.entry(ri).or_default().push(MatchedArg {
                        param_ty: m.params[ri].ty.subst(subst),
                        arg: e,
                        pre_type: pre.get(&e.id).cloned(),
                    });
                }
                Arg::Keyword { name, value, .. } => {
                    let found = m.params.iter().position(|p| {
                        &p.name == name
                            && matches!(p.kind, ParamKind::Positional | ParamKind::KeywordOnly)
                    });
                    match found {
                        Some(pi) if !bound.contains_key(&pi) => {
                            bound.entry(pi).or_default().push(MatchedArg {
                                param_ty: m.params[pi].ty.subst(subst),
                                arg: value,
                                pre_type: pre.get(&value.id).cloned(),
                            });
                        }
                        Some(_) => return Err(format!("argument `{name}` given twice")),
                        None => match kwrest {
                            Some(ki) => {
                                let elem = match m.params[ki].ty.subst(subst) {
                                    Type::Class(_, args) if args.len() == 2 => args[1].clone(),
                                    t => t,
                                };
                                bound.entry(ki).or_default().push(MatchedArg {
                                    param_ty: elem,
                                    arg: value,
                                    pre_type: pre.get(&value.id).cloned(),
                                });
                            }
                            None => {
                                return Err(format!(
                                    "{} has no parameter `{name}`",
                                    self.signature(m)
                                ))
                            }
                        },
                    }
                }
                Arg::DoubleSplat(e) => {
                    let Some(ki) = kwrest else {
                        return Err(format!("{} does not take `**`", self.signature(m)));
                    };
                    bound.entry(ki).or_default().push(MatchedArg {
                        param_ty: m.params[ki].ty.subst(subst),
                        arg: e,
                        pre_type: pre.get(&e.id).cloned(),
                    });
                }
                Arg::BlockPass(_) => {}
            }
        }
        // Missing required parameters.
        for (i, p) in m.params.iter().enumerate() {
            if bound.contains_key(&i) || p.default.is_some() {
                continue;
            }
            match p.kind {
                ParamKind::Rest | ParamKind::KeywordRest | ParamKind::Block => continue,
                ParamKind::Positional if has_splat => continue,
                _ => {
                    return Err(format!(
                        "{} is missing the argument `{}`",
                        self.signature(m),
                        p.name
                    ))
                }
            }
        }
        // Type the arguments.
        for (pi, matched) in &bound {
            for ma in matched {
                let expected_ty = ma.param_ty.clone();
                let actual = match &ma.pre_type {
                    Some(t) => t.clone(),
                    None => self.check_expr(ma.arg, Some(&expected_ty)),
                };
                let p = &m.params[*pi];
                let ok = self.coerce(&actual, &expected_ty);
                if !ok {
                    let msg = format!(
                        "argument `{}` of {} expects {} but found {}",
                        p.name,
                        self.signature(m),
                        self.name(&expected_ty),
                        self.name(&actual)
                    );
                    if report {
                        self.error(msg.clone(), ma.arg.span);
                    }
                    return Err(msg);
                }
            }
        }
        // The return type, unified with the expected type first so that it
        // can drive inference inside the block (`Array.build { |out| ... }`
        // where the result type is known).
        let ret = self.method_ret(m.id, expr.span).subst(subst);
        if let Some(e) = expected {
            let r = self.infer.resolve(&ret);
            if r.has_vars() {
                let saved = self.infer.save();
                if !self.coerce(&r, e) {
                    self.infer.restore(saved);
                }
            }
        }
        // Block.
        if let Some((_, block_ty)) = &m.block {
            let block_ty = block_ty.subst(subst);
            if let Some(b) = &call.block {
                let resolved = self.infer.resolve(&block_ty);
                let is_task = m.name == "spawn"
                    && (m.owner == self.world.builtin.kernel
                        || m.owner == self.world.builtin.scope);
                self.check_block_as(expr.id, b, &resolved, is_task);
            } else if let Some(Arg::BlockPass(e)) =
                call.args.iter().find(|a| matches!(a, Arg::BlockPass(_)))
            {
                match &e.kind {
                    ExprKind::Symbol(name) => {
                        // `&:name`: the block calls `name` on its argument.
                        let Type::Proc(params, ret) = self.infer.resolve(&block_ty) else {
                            return Err("invalid block type".to_string());
                        };
                        if params.len() != 1 {
                            return Err(format!("`&:{name}` needs a block with one parameter"));
                        }
                        let recv = self.infer.resolve(&params[0]);
                        let cands = self.world.lookup_methods(&recv, name);
                        let Some((mid, msubst)) = cands.first().cloned() else {
                            let msg = format!(
                                "undefined method `{name}` for {} (in `&:{name}`)",
                                self.name(&recv)
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        };
                        let mut msubst = msubst;
                        msubst.insert(SELF_PARAM, recv.clone());
                        let r = self.method_ret(mid, e.span).subst(&msubst);
                        if !self.coerce(&r, &ret) {
                            let msg = format!(
                                "`&:{name}` returns {} but {} was expected",
                                self.name(&r),
                                self.name(&ret)
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        self.out
                            .block_pass
                            .insert(expr.id, BlockPass::Symbol(name.clone()));
                        self.record(e.id, &self.world.symbol());
                    }
                    _ => {
                        let t = self.check_expr(e, Some(&block_ty));
                        if !self.coerce(&t, &block_ty) {
                            let msg = format!(
                                "block argument has type {} but {} was expected",
                                self.name(&t),
                                self.name(&block_ty)
                            );
                            if report {
                                self.error(msg.clone(), e.span);
                            }
                            return Err(msg);
                        }
                        self.out.block_pass.insert(expr.id, BlockPass::Proc);
                    }
                }
            }
        }
        Ok(ret)
    }

    /// Check a block against the procedure type it is passed as.
    fn check_block(&mut self, call_id: NodeId, block: &Block, proc_ty: &Type) {
        self.check_block_as(call_id, block, proc_ty, false)
    }

    fn check_block_as(&mut self, call_id: NodeId, block: &Block, proc_ty: &Type, is_task: bool) {
        let Type::Proc(params, ret) = proc_ty else {
            self.error("internal: block type is not a procedure", block.span);
            return;
        };
        let params = params.clone();
        let ret = (**ret).clone();
        self.widen_assigned(&block.body);
        self.env.frames.push(Frame {
            vars: Vec::new(),
            is_block: true,
        });
        let saved_task_frame = self.env.task_frame;
        if is_task {
            self.env.task_frame = Some(self.env.frames.len() - 1);
        }
        self.env.blocks.push(BlockCtx {
            ret: ret.clone(),
            breaks: Vec::new(),
            is_lambda: false,
        });
        // Parameters: destructure a single tuple parameter over several
        // block parameters.
        let declared: Vec<&Param> = block
            .params
            .list
            .iter()
            .filter(|p| p.kind != ParamKind::Block)
            .collect();
        let mut param_types: Vec<Type> = params.clone();
        if declared.len() > 1 && params.len() == 1 {
            match self.infer.resolve(&params[0]) {
                Type::Tuple(ts) => {
                    param_types = ts;
                    self.out.block_destructure.insert(call_id, declared.len());
                }
                // An array is spread over the parameters, as in Ruby.
                Type::Class(id, args) if id == self.world.builtin.array && args.len() == 1 => {
                    param_types = vec![args[0].clone(); declared.len()];
                    self.out.block_destructure.insert(call_id, declared.len());
                }
                _ => {}
            }
        }
        if declared.len() > param_types.len() {
            self.error(
                format!(
                    "block takes {} parameter(s) but {} are declared",
                    param_types.len(),
                    declared.len()
                ),
                block.span,
            );
        }
        for (i, p) in declared.iter().enumerate() {
            let mut t = param_types
                .get(i)
                .cloned()
                .unwrap_or_else(|| self.world.nil());
            if let Some(te) = &p.ty {
                let scope = self.env.scope.clone();
                if let Some(annotated) = self.resolve_type_expr(te, &scope) {
                    if !self.coerce(&t, &annotated) {
                        self.error(
                            format!(
                                "block parameter `{}` is annotated {} but receives {}",
                                p.name,
                                self.name(&annotated),
                                self.name(&t)
                            ),
                            te.span,
                        );
                    }
                    t = annotated;
                }
            }
            if p.kind == ParamKind::Rest {
                t = self.world.array_of(t);
            }
            self.declare_var(&p.name, t, p.span);
        }
        let void = self.world.is_nil_type(&self.infer.resolve(&ret));
        let bt = self.check_body(&block.body, if void { None } else { Some(&ret) });
        if !void && !bt.is_nothing() && !self.coerce(&bt, &ret) {
            let span = block.body.last().map(|e| e.span).unwrap_or(block.span);
            self.error(
                format!(
                    "block returns {} but {} was expected",
                    self.name(&bt),
                    self.name(&ret)
                ),
                span,
            );
        }
        let frame = self.env.frames.pop().unwrap();
        self.env.blocks.pop();
        self.env.task_frame = saved_task_frame;
        self.out
            .frame_sizes
            .insert(call_id, frame.vars.len() as u32);
        self.widen_assigned(&block.body);
    }

    fn check_lambda(&mut self, id: NodeId, block: &Block, expected: Option<&Type>) -> Type {
        let expected_proc = match expected.map(|e| self.resolve(e)) {
            Some(Type::Proc(ps, r)) => Some((ps, *r)),
            _ => None,
        };
        self.widen_assigned(&block.body);
        let mut param_types = Vec::new();
        self.env.frames.push(Frame {
            vars: Vec::new(),
            is_block: true,
        });
        let ret_var = match &expected_proc {
            Some((_, r)) => r.clone(),
            None => self.infer.fresh(),
        };
        self.env.blocks.push(BlockCtx {
            ret: ret_var.clone(),
            breaks: Vec::new(),
            is_lambda: true,
        });
        for (i, p) in block.params.list.iter().enumerate() {
            let t = match &p.ty {
                Some(te) => {
                    let scope = self.env.scope.clone();
                    self.resolve_type_expr(te, &scope).unwrap_or(Type::Nothing)
                }
                None => match expected_proc.as_ref().and_then(|(ps, _)| ps.get(i)) {
                    Some(t) => t.clone(),
                    None => {
                        self.error(
                            format!("lambda parameter `{}` needs a type", p.name),
                            p.span,
                        );
                        Type::Nothing
                    }
                },
            };
            param_types.push(t.clone());
            self.declare_var(&p.name, t, p.span);
        }
        let bt = self.check_body(&block.body, None);
        if !bt.is_nothing() && !self.coerce(&bt, &ret_var) {
            self.error(
                format!(
                    "lambda returns {} but {} was expected",
                    self.name(&bt),
                    self.name(&ret_var)
                ),
                block.span,
            );
        }
        let frame = self.env.frames.pop().unwrap();
        self.env.blocks.pop();
        self.out.frame_sizes.insert(id, frame.vars.len() as u32);
        let ret = self.infer.resolve(&ret_var);
        Type::Proc(param_types, Box::new(ret))
    }

    fn check_yield(&mut self, expr: &Expr, args: &[Arg]) -> Type {
        let Some(bt) = self.env.block_type.clone() else {
            self.error("`yield` in a method without a block parameter", expr.span);
            self.check_args_blindly(&Call {
                recv: None,
                name: String::new(),
                args: args.to_vec(),
                block: None,
                safe_nav: false,
                has_parens: true,
                type_args: vec![],
            });
            return Type::Nothing;
        };
        let Type::Proc(params, ret) = bt else {
            return Type::Nothing;
        };
        let positional: Vec<&Expr> = args
            .iter()
            .filter_map(|a| match a {
                Arg::Positional(e) => Some(e),
                _ => None,
            })
            .collect();
        if positional.len() != params.len() {
            self.error(
                format!(
                    "the block takes {} argument(s), `yield` passes {}",
                    params.len(),
                    positional.len()
                ),
                expr.span,
            );
            for e in positional {
                self.check_expr(e, None);
            }
            return *ret;
        }
        for (e, p) in positional.iter().zip(params.iter()) {
            let t = self.check_expr(e, Some(p));
            if !self.coerce(&t, p) {
                self.error(
                    format!(
                        "`yield` passes {} where the block expects {}",
                        self.name(&t),
                        self.name(p)
                    ),
                    e.span,
                );
            }
        }
        *ret
    }

    fn check_super(&mut self, expr: &Expr, args: Option<&[Arg]>, block: Option<&Block>) -> Type {
        let Some(mid) = self.env.method else {
            self.error("`super` outside of a method", expr.span);
            return Type::Nothing;
        };
        let m = self.world.method(mid).clone();
        let owner = m.owner;
        // Find the next definition in the ancestor chain after the owner.
        let self_ty = self.env.self_type.clone();
        let cands = self.world.lookup_methods(&self_ty, &m.name);
        let mut after_owner = false;
        let mut target = None;
        for (c, subst) in cands {
            let cm = self.world.method(c);
            if cm.owner == owner && cm.extension.is_none() {
                after_owner = true;
                continue;
            }
            if after_owner && cm.singleton == m.singleton {
                target = Some((c, subst));
                break;
            }
        }
        let Some((sid, subst)) = target else {
            self.error(format!("no superclass method `{}`", m.name), expr.span);
            return Type::Nothing;
        };
        let call = Call {
            recv: None,
            name: m.name.clone(),
            args: match args {
                Some(a) => a.to_vec(),
                None => {
                    // zsuper: forward the parameters.
                    m.params
                        .iter()
                        .map(|p| {
                            let e = Expr {
                                id: u32::MAX - 1,
                                span: expr.span,
                                kind: ExprKind::Local(p.name.clone()),
                            };
                            match p.kind {
                                ParamKind::KeywordOnly => Arg::Keyword {
                                    name: p.name.clone(),
                                    value: e,
                                    span: expr.span,
                                },
                                _ => Arg::Positional(e),
                            }
                        })
                        .collect()
                }
            },
            block: block.cloned(),
            safe_nav: false,
            has_parens: true,
            type_args: vec![],
        };
        let t = self.resolve_overloads_as(
            expr,
            &call,
            &self_ty,
            vec![(sid, subst)],
            true,
            None,
            m.name == "initialize",
        );
        if let Some(CallTarget::Method { method }) = self.out.calls.get(&expr.id).cloned() {
            self.out.calls.insert(expr.id, CallTarget::Super { method });
        }
        if m.name == "initialize" {
            // The superclass initialize assigned its fields.
            let fields = self.world.all_fields(owner);
            for (f, _) in fields {
                if self
                    .world
                    .class(owner)
                    .fields
                    .iter()
                    .all(|own| own.name != f.name)
                {
                    self.env.assigned_fields.insert(f.name);
                }
            }
        }
        t
    }

    fn check_raise(&mut self, expr: &Expr, call: &Call) -> Type {
        let args: Vec<&Expr> = call
            .args
            .iter()
            .filter_map(|a| match a {
                Arg::Positional(e) => Some(e),
                _ => None,
            })
            .collect();
        if args.len() != call.args.len() || args.is_empty() || args.len() > 2 {
            self.error(
                "`raise` takes an exception class, an exception, or a message",
                expr.span,
            );
            self.check_args_blindly(call);
            return Type::Nothing;
        }
        let first = self.check_expr(args[0], None);
        let first = self.resolve(&first);
        match &first {
            Type::ClassObject(cid, _) => {
                if !self.world.is_exception_class(*cid) {
                    self.error(
                        format!(
                            "`{}` is not an exception class",
                            self.world.class(*cid).name
                        ),
                        args[0].span,
                    );
                }
                if let Some(msg) = args.get(1) {
                    let t = self.check_expr(msg, None);
                    let s = self.world.string();
                    if !self.coerce(&t, &s) {
                        self.error("the exception message must be a String", msg.span);
                    }
                }
            }
            Type::Class(cid, _) if *cid == self.world.builtin.string => {
                if args.len() > 1 {
                    self.error("`raise` with a message takes no second argument", expr.span);
                }
            }
            Type::Class(cid, _) if self.world.is_exception_class(*cid) => {
                if args.len() > 1 {
                    self.error(
                        "`raise` with an exception object takes no second argument",
                        expr.span,
                    );
                }
            }
            _ => self.error(format!("cannot raise {}", self.name(&first)), args[0].span),
        }
        self.out.calls.insert(expr.id, CallTarget::Raise);
        Type::Nothing
    }

    fn check_type_test(&mut self, expr: &Expr, call: &Call, recv: &Expr) -> Type {
        let rt = self.check_expr(recv, None);
        let Arg::Positional(arg) = &call.args[0] else {
            self.error("expected a type", call.args[0].span());
            return Type::Nothing;
        };
        let scope = self.env.scope.clone();
        let target = match &arg.kind {
            ExprKind::Const(path) => {
                let te = TypeExpr {
                    span: arg.span,
                    kind: TypeExprKind::Named {
                        path: path.clone(),
                        args: vec![],
                    },
                };
                self.resolve_type_expr(&te, &scope)
            }
            ExprKind::TypeApp(te) => self.resolve_type_expr(te, &scope),
            _ => {
                self.error("expected a type", arg.span);
                None
            }
        };
        let Some(target) = target else {
            return Type::Nothing;
        };
        self.record(
            arg.id,
            &Type::ClassObject(
                target.class_id().unwrap_or(self.world.builtin.object),
                vec![],
            ),
        );
        let rt = self.resolve(&rt);
        match call.name.as_str() {
            "is_a?" => {
                self.out.calls.insert(expr.id, CallTarget::IsA(target));
                self.world.bool_()
            }
            "as" => {
                let (yes, _) = self.split_by_type(&rt, &target);
                if yes.is_nothing() {
                    self.warning(
                        format!(
                            "{} is never {}; `as` will always raise",
                            self.name(&rt),
                            self.name(&target)
                        ),
                        expr.span,
                    );
                }
                self.out.calls.insert(
                    expr.id,
                    CallTarget::As {
                        ty: target.clone(),
                        optional: false,
                    },
                );
                target
            }
            _ => {
                self.out.calls.insert(
                    expr.id,
                    CallTarget::As {
                        ty: target.clone(),
                        optional: true,
                    },
                );
                self.world.nilable(target)
            }
        }
    }
}

impl Checker {
    /// Narrowings established when `value` matches `pattern`, with pattern
    /// variables declared. Used by `in` conditions and `=>`.
    fn check_pattern_facts(&mut self, pattern: &Pattern, value_ty: &Type, value: &Expr) -> Facts {
        let narrowed = self.check_pattern(pattern, value_ty);
        match self.var_key(value) {
            Some(key) => vec![(key, narrowed)],
            None => Vec::new(),
        }
    }
}

// Re-export for the pattern module.
pub(crate) use VarKey as PatternVarKey;

impl Checker {
    pub(crate) fn declare_pattern_var(&mut self, name: &str, ty: Type, span: Span) {
        let existing = self.lookup_var(name).filter(|(depth, slot)| {
            !(*depth == 0 && self.env.pattern_base.is_some_and(|base| *slot >= base))
        });
        if let Some((depth, slot)) = existing {
            // Re-binding an existing variable: it must accept the type.
            let declared = {
                let n = self.env.frames.len();
                self.env.frames[n - 1 - depth].vars[slot].declared.clone()
            };
            if !self.coerce(&ty, &declared) {
                self.error(
                    format!(
                        "pattern binds `{name}` to {} but it has type {}",
                        self.name(&ty),
                        self.name(&declared)
                    ),
                    span,
                );
            }
            self.out.var_refs.insert(
                span,
                VarRef {
                    depth: depth as u32,
                    slot: slot as u32,
                },
            );
            let narrowed = self.resolve(&ty);
            self.set_narrowed(&PatternVarKey::Local(name.to_string()), Some(narrowed));
        } else {
            let declared = self.resolve(&ty);
            self.declare_var(name, declared, span);
        }
    }

    pub(crate) fn report(&mut self, message: impl Into<String>, span: Span) {
        self.error(message, span);
    }

    pub(crate) fn warn(&mut self, message: impl Into<String>, span: Span) {
        self.warning(message, span);
    }

    pub(crate) fn type_name(&self, t: &Type) -> String {
        self.name(t)
    }

    pub(crate) fn resolve_ty(&self, t: &Type) -> Type {
        self.resolve(t)
    }

    pub(crate) fn join_types(&mut self, a: &Type, b: &Type) -> Type {
        self.join(a, b)
    }

    pub(crate) fn check_expr_pub(&mut self, e: &Expr, expected: Option<&Type>) -> Type {
        self.check_expr(e, expected)
    }

    pub(crate) fn check_case_in(
        &mut self,
        subject: &Expr,
        arms: &[InArm],
        els: Option<&[Expr]>,
        expected: Option<&Type>,
        span: Span,
    ) -> Type {
        let st = self.check_expr(subject, None);
        let st = self.resolve(&st);
        let key = self.var_key(subject);
        let before = self.snapshot();
        let mut remaining: Vec<Type> = self.expand_members(&st);
        let mut result = Type::Nothing;
        let mut snaps = Vec::new();
        let saved_base = self.env.pattern_base;
        self.env.pattern_base = Some(self.env.frames.last().unwrap().vars.len());
        for arm in arms {
            self.restore(&before);
            let narrowed = self.check_pattern(&arm.pattern, &st);
            if let Some(k) = &key {
                self.set_narrowed(k, Some(narrowed));
            }
            if let Some(g) = &arm.guard {
                let (_, ft, ff) = self.check_cond(&g.cond);
                self.apply_facts(if g.negate { &ff } else { &ft });
            } else {
                remaining.retain(|m| !self.pattern_covers(&arm.pattern, m));
            }
            let bt = self.check_body(&arm.body, expected);
            snaps.push((self.snapshot(), bt.is_nothing()));
            result = self.join(&result, &bt);
        }
        self.env.pattern_base = saved_base;
        self.restore(&before);
        let et = match els {
            Some(els) => {
                if let Some(k) = &key {
                    let rem = Type::union_of(remaining.clone());
                    self.set_narrowed(k, Some(rem));
                }
                self.check_body(els, expected)
            }
            None => {
                if !remaining.is_empty() {
                    let names: Vec<String> = remaining.iter().map(|t| self.name(t)).collect();
                    // A union lists its alternatives explicitly, so a
                    // missing one is an error; for a single open type
                    // (numbers, strings, open classes) it is a warning.
                    let closed = remaining.iter().all(|t| self.is_closed_type(t))
                        || self.expand_members(&st).len() > 1;
                    let msg = format!("`case` does not cover: {}", names.join(", "));
                    if closed {
                        self.error(format!("{msg} (add an `in` arm or `else`)"), span);
                    } else {
                        self.warning(
                            format!("{msg}; a NoMatchingPatternError is raised at run time"),
                            span,
                        );
                    }
                }
                Type::Nothing
            }
        };
        let mut dead = et.is_nothing();
        result = self.join(&result, &et);
        for (snap, d) in snaps.iter().rev() {
            self.merge_with(snap, *d, dead);
            dead = dead && *d;
        }
        result
    }

    /// Types whose set of values is fully known to the checker, so that an
    /// uncovered one is an error rather than a warning.
    fn is_closed_type(&self, t: &Type) -> bool {
        match t {
            Type::Class(id, _) => {
                let class = self.world.class(*id);
                // Values of these types can be enumerated by patterns;
                // numbers and strings cannot, so a missing case there is a
                // run-time error (warning only).
                matches!(
                    class.kind,
                    ClassKind::Data | ClassKind::Variant | ClassKind::Enum
                ) || [self.world.builtin.nil, self.world.builtin.bool_].contains(id)
            }
            Type::Tuple(_) => true,
            _ => false,
        }
    }
}

impl Checker {
    pub fn into_output(self) -> (World, Output, Vec<(u32, Diagnostic)>) {
        (self.world, self.out, self.diagnostics)
    }

    pub fn frame_var_count(&self) -> usize {
        self.env.frames[0].vars.len()
    }

    pub fn method_ret_pub(&mut self, mid: MethodId, span: Span) -> Type {
        self.method_ret(mid, span)
    }

    pub fn fresh_var(&mut self) -> Type {
        self.infer.fresh()
    }

    pub(crate) fn resolve_path_pub(
        &mut self,
        namespace: Option<ClassId>,
        path: &ConstPath,
        span: Span,
    ) -> Option<Member> {
        self.resolve_path(namespace, path, span)
    }

    pub(crate) fn current_namespace(&self) -> Option<ClassId> {
        self.env.scope.namespace
    }
}
