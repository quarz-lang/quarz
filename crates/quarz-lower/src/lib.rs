//! Lowering of a checked program to QIR.
//!
//! The lowerer is incremental: the REPL calls it once per input, and only
//! the methods, constants and field defaults that have not been lowered
//! yet get functions. Function ids are stable and append-only.

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use quarz_ir::*;
use quarz_syntax::ast::Expr;
use quarz_syntax::SourceFile;
use quarz_types::{Checked, Output, World};

mod borrow;
mod capture;
mod cha;
mod copyprop;
mod devirt;
mod func;
mod inline;
mod iter;
pub mod layout;
pub mod lift;
mod regshare;
mod release;

mod rtworld;
mod sroa;
pub mod verify;

use func::FnBuilder;

/// A unit body to lower: a file's top-level statements, or one REPL
/// input.
pub struct UnitInput<'a> {
    pub file: u32,
    pub name: String,
    pub main_class: ClassId,
    pub body: &'a [Expr],
    /// Runs in the persistent REPL frame (every variable lives in it).
    pub repl: bool,
}

/// The result of one lowering round: the complete metadata plus the
/// functions added in this round (ids starting at `base`).
pub struct Delta {
    pub world: RtWorld,
    pub base: FuncId,
    pub functions: Vec<Function>,
    pub units: Vec<Unit>,
}

/// One round of `Lowerer::lower_static`: the functions it added, the
/// statement's own function, and the methods and constants it reached
/// whose checks are not done yet (the caller checks them and asks for
/// another round, which continues where this one stopped).
pub struct StaticRound {
    pub delta: Delta,
    pub stmt_func: FuncId,
    pub unchecked: Vec<MethodId>,
    pub unchecked_consts: Vec<ConstId>,
}

#[derive(Default)]
pub struct Lowerer {
    /// Lowering for a compile-time run (docs/14): every method is lazy,
    /// reached from the statement, and one whose body is not checked yet
    /// is reported instead of lowered.
    static_mode: bool,
    unchecked: Vec<MethodId>,
    unchecked_consts: Vec<ConstId>,
    /// What the previous static round left unchecked: reached again in
    /// the next one, once checked.
    static_retry: Vec<MethodId>,
    static_retry_consts: Vec<ConstId>,
    /// In a static round: the classes whose `static` statements have not
    /// all run (and their descendants). A reach by one of the names the
    /// runtime calls everywhere (`shake::RUNTIME_NAMES`: `to_s`,
    /// `initialize`, `hash`...) leaves their methods out: their bodies
    /// may use members not generated yet. A call that resolves to one,
    /// or a reach by another name, still gets it.
    pub static_skip: HashSet<ClassId>,
    /// The statement function of the previous static round, reused when
    /// the next round is for the same statement.
    static_stmt_func: Option<(quarz_syntax::ast::NodeId, FuncId)>,
    /// The functions of the rounds before this one, by id (the runner
    /// of `static` statements hands each round's back): what a lifted
    /// block's function is copied from.
    pub done: Vec<Function>,
    /// The call each block function was written at, and the block's
    /// span, for the generation of methods from blocks (docs/14 §5).
    pub block_calls: HashMap<FuncId, (quarz_syntax::ast::NodeId, quarz_syntax::Span)>,
    pub(crate) method_funcs: Vec<Option<FuncId>>,
    pub(crate) const_funcs: Vec<Option<FuncId>>,
    /// Whether a quoted block's tree is built once, by a constant of its
    /// own (docs/14 §6): in the final lowering, whose world no longer
    /// grows, so that the constants can follow the checker's. The REPL
    /// and compile-time runs build it at each call.
    pub(crate) quoted_once: bool,
    /// Those constants, after the world's: each builds a tree.
    pub(crate) quoted_consts: Vec<RtConst>,
    pub(crate) field_default_funcs: HashMap<(ClassId, usize), FuncId>,
    /// Whether an instance of the class (one of a subclass included) may
    /// have a `deinitialize`: its `initialize` marks where the object
    /// becomes usable (`Inst::MarkUsable`).
    pub(crate) may_deinitialize: HashMap<ClassId, bool>,
    next_func: FuncId,
    /// Functions of the current round, by id minus `round_base`.
    pending: Vec<Option<Function>>,
    round_base: FuncId,
    /// Source files by index, for line numbers.
    pub(crate) files: Vec<SourceFile>,
    /// `(class, name)` pairs for which some descendant of the class (or
    /// an extension on one) declares a method `name`: a call resolved to
    /// the class's method may dispatch elsewhere.
    pub(crate) overridden: HashSet<(ClassId, String)>,
    /// Where each class's declared fields live (see `layout`).
    pub(crate) layouts: Vec<layout::Layout>,
    /// The prelude's methods are lowered only once something lowered may
    /// call them (most programs use a small part of it): the methods and
    /// names reached so far, kept across REPL inputs. Reachability is
    /// `quarz_ir::shake`'s, by name.
    reached: Vec<bool>,
    reached_names: HashSet<String>,
    /// Lowered functions of this round whose references were followed.
    scanned: usize,
}

impl Lowerer {
    /// A constant whose initializer `init` builds a quoted block's tree
    /// (docs/14 §6), after the world's constants: its id.
    pub(crate) fn add_quoted_const(
        &mut self,
        world: &World,
        file: u32,
        line: u32,
        init: FuncId,
    ) -> ConstId {
        let id = (world.consts.len() + self.quoted_consts.len()) as ConstId;
        self.quoted_consts.push(RtConst {
            name: format!("<tree of the block at line {line}>"),
            owner: None,
            init: Some(init),
            file,
        });
        id
    }

    pub fn new() -> Lowerer {
        Lowerer::default()
    }

    pub(crate) fn alloc_func(&mut self) -> FuncId {
        let id = self.next_func;
        self.next_func += 1;
        self.pending.push(None);
        id
    }

    pub(crate) fn set_func(&mut self, id: FuncId, f: Function) {
        self.pending[(id - self.round_base) as usize] = Some(f);
    }

    /// Lower everything new in `world` plus the given unit bodies.
    pub fn lower(
        &mut self,
        world: &World,
        out: &Output,
        units: &[UnitInput],
        files: Vec<SourceFile>,
    ) -> Delta {
        self.static_mode = false;
        self.round_base = self.next_func;
        self.pending.clear();
        self.files = files;
        self.overridden = overridden_methods(world);
        self.layouts = layout::compute(world);

        // Methods.
        if self.method_funcs.len() < world.methods.len() {
            self.method_funcs.resize(world.methods.len(), None);
        }
        let known = self.reached.len();
        if self.reached.len() < world.methods.len() {
            self.reached.resize(world.methods.len(), false);
        }
        for mid in 0..world.methods.len() {
            if !self.lazy(world, world.methods[mid].file) || self.reached[mid] {
                self.lower_method(world, out, mid as MethodId);
            }
        }
        // Constants.
        if self.const_funcs.len() < world.consts.len() {
            self.const_funcs.resize(world.consts.len(), None);
        }
        for cid in 0..world.consts.len() {
            if self.const_funcs[cid].is_some() {
                continue;
            }
            let c = &world.consts[cid];
            let Some(value) = &c.value else { continue };
            let id = self.alloc_func();
            self.const_funcs[cid] = Some(id);
            let name = format!("const {}", c.name);
            let f = FnBuilder::init(self, world, out, name, c.file, c.owner, value);
            self.set_func(id, f);
        }
        // Field defaults: each by the class that declares it, which its
        // subclasses (in later units too) share.
        for class in &world.classes {
            let fields = world.all_fields(class.id);
            let own = fields.len().saturating_sub(class.fields.len());
            for (i, (field, _)) in fields.iter().enumerate().skip(own) {
                if self.field_default_funcs.contains_key(&(class.id, i)) {
                    continue;
                }
                let name = format!("default of {}#@{}", class.name, field.name);
                let f = if let Some(default) = &field.default {
                    let id = self.alloc_func();
                    self.field_default_funcs.insert((class.id, i), id);
                    let f = FnBuilder::init(
                        self,
                        world,
                        out,
                        name,
                        class.file,
                        Some(class.id),
                        default,
                    );
                    (id, f)
                } else if let Some(baked) = &field.baked_default {
                    let id = self.alloc_func();
                    self.field_default_funcs.insert((class.id, i), id);
                    (id, self.baked_init(name, class.file, baked))
                } else {
                    continue;
                };
                self.set_func(f.0, f.1);
            }
        }
        // Unit bodies.
        let mut lowered_units = Vec::new();
        for u in units {
            let id = self.alloc_func();
            let f = FnBuilder::top_level(self, world, out, u);
            self.set_func(id, f);
            lowered_units.push(Unit {
                file: u.file,
                name: u.name.clone(),
                main_class: u.main_class,
                body: id,
            });
        }
        // The prelude methods what was lowered may call, and theirs.
        self.scanned = 0;
        let by_name = methods_by_name(world);
        let mut work: Vec<MethodId> = Vec::new();
        for n in quarz_ir::shake::RUNTIME_NAMES {
            self.reach_name(world, n, &by_name, &mut work);
        }
        // Methods new this round (a REPL input requiring a library) whose
        // name an earlier round reached: callable already.
        for mid in known..world.methods.len() {
            if self
                .reached_names
                .contains(world.methods[mid].name.as_str())
            {
                self.reach_method(world, mid as MethodId, &by_name, &mut work);
            }
        }
        self.reach_all(world, out, &by_name, &mut work);
        let functions: Vec<Function> = self
            .pending
            .drain(..)
            .map(|f| f.expect("function lowered"))
            .collect();
        let file_names = self.files.iter().map(|f| f.name.clone()).collect();
        let world = rtworld::build(world, self, file_names);
        Delta {
            world,
            base: self.round_base,
            functions,
            units: lowered_units,
        }
    }
}

impl Lowerer {
    /// An initializer (a field default) that is a baked value (docs/14
    /// §5): the instructions that make it, returned.
    fn baked_init(&mut self, name: String, file: u32, baked: &quarz_types::Baked) -> Function {
        let mut baker = lift::Baker::new(&self.layouts, 1);
        let mut insts = Vec::new();
        baker.bake(&mut insts, 0, baked);
        let (nregs, consts) = baker.finish();
        let lines = vec![0; insts.len()];
        Function {
            name,
            kind: FuncKind::Init,
            file,
            nregs,
            frame_size: 0,
            param_kinds: Vec::new(),
            arity: 0,
            consts,
            blocks: vec![Block {
                insts,
                lines,
                term: Term::Return(0),
                term_line: 0,
                handler: None,
            }],
            inlined: Vec::new(),
        }
    }

    /// A field was added to `classes` (a class and its descendants, by
    /// `def_field` at compile time): what was lowered before assumed
    /// their layouts without it. Those functions are lowered again when
    /// next reached: the methods whose functions read or write a field
    /// of one of them or construct one (and those making a block that
    /// does), the constant initializers likewise, and the field defaults
    /// of the classes themselves (kept by field index).
    pub fn invalidate_layout(&mut self, classes: &[ClassId]) {
        let touches = |f: &Function| {
            f.blocks.iter().flat_map(|b| &b.insts).any(|i| match i {
                Inst::FieldGet { class, .. } | Inst::FieldSet { class, .. } => {
                    classes.contains(class)
                }
                Inst::Call {
                    kind: CallKind::Construct { class, .. } | CallKind::ConstructRecv { class, .. },
                    ..
                } => classes.contains(class),
                _ => false,
            })
        };
        let mut stale: Vec<bool> = self.done.iter().map(touches).collect();
        // A block's function is lowered with its method's.
        loop {
            let mut changed = false;
            for (i, f) in self.done.iter().enumerate() {
                if stale[i] {
                    continue;
                }
                let makes_stale = f.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
                    matches!(inst, Inst::MakeBlock { func, .. }
                        if stale.get(*func as usize).copied().unwrap_or(false))
                });
                if makes_stale {
                    stale[i] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let is_stale = |id: FuncId| stale.get(id as usize).copied().unwrap_or(false);
        // Lowered again in the next static round (`static_retry`: the
        // names they were reached by are not walked again).
        for (mid, m) in self.method_funcs.iter_mut().enumerate() {
            if m.is_some_and(is_stale) {
                *m = None;
                if let Some(r) = self.reached.get_mut(mid) {
                    *r = false;
                }
                self.static_retry.push(mid as MethodId);
            }
        }
        for (cid, c) in self.const_funcs.iter_mut().enumerate() {
            if c.is_some_and(is_stale) {
                *c = None;
                self.static_retry_consts.push(cid as ConstId);
            }
        }
        // A field default is kept by (class, index): the indices of the
        // classes' own fields may have moved.
        self.field_default_funcs
            .retain(|(class, _), id| !is_stale(*id) && !classes.contains(class));
    }

    /// The function of the default of field `index` of class `cid`
    /// (counting inherited fields first): the declaring class's.
    pub(crate) fn field_default(
        &self,
        world: &World,
        cid: ClassId,
        index: usize,
    ) -> Option<FuncId> {
        let mut c = Some(cid);
        while let Some(k) = c {
            if let Some(f) = self.field_default_funcs.get(&(k, index)) {
                return Some(*f);
            }
            c = match &world.class(k).superclass {
                Some(quarz_types::Type::Class(s, _)) => Some(*s),
                _ => None,
            };
        }
        None
    }
}

/// The file index of the prelude.
const PRELUDE_FILE: u32 = 0;

fn methods_by_name(world: &World) -> HashMap<&str, Vec<MethodId>> {
    let mut by_name: HashMap<&str, Vec<MethodId>> = HashMap::default();
    for (i, m) in world.methods.iter().enumerate() {
        by_name
            .entry(m.name.as_str())
            .or_default()
            .push(i as MethodId);
    }
    by_name
}

impl Lowerer {
    /// Whether the methods of `file` are lowered only once something may
    /// call them: the prelude's and the standard library's.
    fn lazy(&self, world: &World, file: u32) -> bool {
        self.static_mode || file == PRELUDE_FILE || world.std_files.contains(&file)
    }

    /// Lower method `mid` if it has a body and has not been lowered.
    fn lower_method(&mut self, world: &World, out: &Output, mid: MethodId) {
        let m = &world.methods[mid as usize];
        if self.method_funcs[mid as usize].is_some() {
            return;
        }
        if let Some(g) = &m.generated {
            // A block lifted to a method (docs/14 §5).
            let name = format!(
                "{}{}{}",
                world.class(m.owner).name,
                if m.singleton { "." } else { "#" },
                m.name
            );
            let id = self.lift(mid, name, g);
            self.method_funcs[mid as usize] = Some(id);
            return;
        }
        let Some(def) = &m.body else { return };
        let Some(body) = &def.body else { return };
        if self.static_mode && !m.checked {
            // Not lowerable yet: the caller checks it and comes back.
            self.unchecked.push(mid);
            self.reached[mid as usize] = false;
            return;
        }
        let id = self.alloc_func();
        self.method_funcs[mid as usize] = Some(id);
        let f = FnBuilder::method(self, world, out, mid, body);
        self.set_func(id, f);
    }

    /// Lower what the functions lowered so far reach, until nothing new
    /// is reached: methods by id and by name, and, in static mode,
    /// constants (which `lower` lowered up front).
    fn reach_all(
        &mut self,
        world: &World,
        out: &Output,
        by_name: &HashMap<&str, Vec<MethodId>>,
        work: &mut Vec<MethodId>,
    ) {
        loop {
            while self.scanned < self.pending.len() {
                let i = self.scanned;
                self.scanned += 1;
                let Some(f) = self.pending[i].take() else {
                    continue;
                };
                let mut methods = Vec::new();
                let mut names = Vec::new();
                let mut consts = Vec::new();
                quarz_ir::shake::refs(&f, &mut |r| match r {
                    quarz_ir::shake::Ref::Method(m) => methods.push(m),
                    quarz_ir::shake::Ref::Name(n) => names.push(n.to_string()),
                    quarz_ir::shake::Ref::Const(c) => consts.push(c),
                    _ => {}
                });
                // In a static round, a construction whose class the
                // receiver decides (`new` in an inherited class method)
                // reaches the `initialize` of every class it may make by
                // id: the name is one left out for the classes whose
                // statements are still to run.
                if self.static_mode {
                    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
                        let Inst::Call {
                            kind: CallKind::ConstructRecv { class, .. },
                            ..
                        } = inst
                        else {
                            continue;
                        };
                        for c in &world.classes {
                            if world.class_is_a(c.id, *class) {
                                if let Some(ids) = c.methods.get("initialize") {
                                    methods.extend(ids.iter().copied());
                                }
                            }
                        }
                    }
                }
                self.pending[i] = Some(f);
                for m in methods {
                    self.reach_method(world, m, by_name, work);
                }
                for n in names {
                    self.reach_name(world, &n, by_name, work);
                }
                if self.static_mode {
                    for c in consts {
                        self.lower_const_static(world, out, c);
                    }
                }
            }
            let Some(mid) = work.pop() else {
                break;
            };
            self.lower_method(world, out, mid);
        }
    }

    /// In static mode, a constant's initializer when it is reached: only
    /// once its type is checked (`const_type`), else reported.
    fn lower_const_static(&mut self, world: &World, out: &Output, cid: ConstId) {
        if self.const_funcs.len() < world.consts.len() {
            self.const_funcs.resize(world.consts.len(), None);
        }
        if self.const_funcs[cid as usize].is_some() {
            return;
        }
        let c = &world.consts[cid as usize];
        let Some(value) = &c.value else { return };
        if c.ty.is_none() {
            if !self.unchecked_consts.contains(&cid) {
                self.unchecked_consts.push(cid);
            }
            return;
        }
        let id = self.alloc_func();
        self.const_funcs[cid as usize] = Some(id);
        let name = format!("const {}", c.name);
        let f = FnBuilder::init(self, world, out, name, c.file, c.owner, value);
        self.set_func(id, f);
    }

    /// Lower a class body's `static` statement (docs/14) with what it
    /// reaches, for a compile-time run: the statement as an init function
    /// (its `self` the class), the `static def` it calls, and every method
    /// and constant those reach. A method whose body is not checked yet is
    /// returned in `unchecked` rather than lowered: the caller checks it
    /// and calls again, which continues from the functions already made.
    #[allow(clippy::too_many_arguments)]
    pub fn lower_static(
        &mut self,
        world: &World,
        out: &Output,
        stmt: &Expr,
        class: ClassId,
        file: u32,
        callee: MethodId,
        files: Vec<SourceFile>,
    ) -> StaticRound {
        self.static_mode = true;
        self.unchecked.clear();
        self.unchecked_consts.clear();
        self.round_base = self.next_func;
        self.pending.clear();
        self.files = files;
        self.overridden = overridden_methods(world);
        self.layouts = layout::compute(world);
        if self.method_funcs.len() < world.methods.len() {
            self.method_funcs.resize(world.methods.len(), None);
        }
        let known = self.reached.len();
        if self.reached.len() < world.methods.len() {
            self.reached.resize(world.methods.len(), false);
        }
        // Field defaults whose expressions are checked (a construction
        // at compile time needs them).
        for class_info in &world.classes {
            let fields = world.all_fields(class_info.id);
            let own = fields.len().saturating_sub(class_info.fields.len());
            for (i, (field, _)) in fields.iter().enumerate().skip(own) {
                if self.field_default_funcs.contains_key(&(class_info.id, i)) {
                    continue;
                }
                let name = format!("default of {}#@{}", class_info.name, field.name);
                if let Some(baked) = &field.baked_default {
                    let id = self.alloc_func();
                    self.field_default_funcs.insert((class_info.id, i), id);
                    let f = self.baked_init(name, class_info.file, baked);
                    self.set_func(id, f);
                    continue;
                }
                let Some(default) = &field.default else {
                    continue;
                };
                if !out.node_types.contains_key(&default.id) {
                    continue;
                }
                let id = self.alloc_func();
                self.field_default_funcs.insert((class_info.id, i), id);
                let f = FnBuilder::init(
                    self,
                    world,
                    out,
                    name,
                    class_info.file,
                    Some(class_info.id),
                    default,
                );
                self.set_func(id, f);
            }
        }
        let stmt_func = match self.static_stmt_func {
            Some((id, f)) if id == stmt.id => f,
            _ => {
                let fid = self.alloc_func();
                let f = FnBuilder::init(
                    self,
                    world,
                    out,
                    "static statement".to_string(),
                    file,
                    Some(class),
                    stmt,
                );
                self.set_func(fid, f);
                self.static_stmt_func = Some((stmt.id, fid));
                fid
            }
        };
        self.scanned = 0;
        let by_name = methods_by_name(world);
        let mut work: Vec<MethodId> = Vec::new();
        for n in quarz_ir::shake::RUNTIME_NAMES {
            self.reach_name(world, n, &by_name, &mut work);
        }
        // Methods new since the previous round (generated by a statement)
        // whose name an earlier round reached: callable already, unless
        // the name is one left out for their class, walked again later.
        for mid in known..world.methods.len() {
            let m = &world.methods[mid];
            if !self.reached_names.contains(m.name.as_str()) {
                continue;
            }
            if quarz_ir::shake::RUNTIME_NAMES.contains(&m.name.as_str())
                && self.static_skip.contains(&m.owner)
            {
                self.reached_names.remove(m.name.as_str());
            } else {
                self.reach_method(world, mid as MethodId, &by_name, &mut work);
            }
        }
        self.reach_method(world, callee, &by_name, &mut work);
        // What the previous round could not lower, checked since.
        for m in std::mem::take(&mut self.static_retry) {
            self.reached[m as usize] = false;
            self.reach_method(world, m, &by_name, &mut work);
        }
        for c in std::mem::take(&mut self.static_retry_consts) {
            self.lower_const_static(world, out, c);
        }
        self.reach_all(world, out, &by_name, &mut work);
        let functions: Vec<Function> = self
            .pending
            .drain(..)
            .map(|f| f.expect("function lowered"))
            .collect();
        let file_names = self.files.iter().map(|f| f.name.clone()).collect();
        let rt = rtworld::build(world, self, file_names);
        self.static_mode = false;
        self.static_retry = self.unchecked.clone();
        self.static_retry_consts = self.unchecked_consts.clone();
        StaticRound {
            delta: Delta {
                world: rt,
                base: self.round_base,
                functions,
                units: Vec::new(),
            },
            stmt_func,
            unchecked: std::mem::take(&mut self.unchecked),
            unchecked_consts: std::mem::take(&mut self.unchecked_consts),
        }
    }

    /// Method `mid` may be called: so may every method of its name (and
    /// the one it is an alias of); a prelude one goes to `work`.
    fn reach_method(
        &mut self,
        world: &World,
        mid: MethodId,
        by_name: &HashMap<&str, Vec<MethodId>>,
        work: &mut Vec<MethodId>,
    ) {
        let Some(seen) = self.reached.get_mut(mid as usize) else {
            return;
        };
        if *seen {
            return;
        }
        *seen = true;
        let m = &world.methods[mid as usize];
        if self.lazy(world, m.file) && self.method_funcs[mid as usize].is_none() {
            work.push(mid);
        }
        if let Some(orig) = m.alias_of {
            self.reach_method(world, orig, by_name, work);
        }
        // A field reader nothing overrides is a field read once linked
        // (`cha::rewrite`): it calls no method of its name.
        let plain_reader = matches!(m.synth, quarz_types::Synth::FieldGet(_))
            && !self.overridden.contains(&(m.owner, m.name.clone()));
        if !plain_reader {
            self.reach_name(world, &m.name, by_name, work);
        }
    }

    /// A method called `name` may be called.
    fn reach_name(
        &mut self,
        world: &World,
        name: &str,
        by_name: &HashMap<&str, Vec<MethodId>>,
        work: &mut Vec<MethodId>,
    ) {
        if self.reached_names.contains(name) {
            return;
        }
        // In a static round, a runtime name leaves out the classes whose
        // statements are still to run (`static_skip`); the name is walked
        // again next round.
        let runtime_name = self.static_mode
            && !self.static_skip.is_empty()
            && quarz_ir::shake::RUNTIME_NAMES.contains(&name);
        let mut skipped = false;
        for &m in by_name.get(name).map(|v| v.as_slice()).unwrap_or(&[]) {
            if runtime_name && self.static_skip.contains(&world.methods[m as usize].owner) {
                skipped = true;
                continue;
            }
            self.reach_method(world, m, by_name, work);
        }
        if !skipped {
            self.reached_names.insert(name.to_string());
        }
    }
}

/// Class hierarchy analysis: for every class, the names its descendants
/// (and extensions on them) declare, as `(ancestor, name)` pairs; a class
/// method's name is spelled `self.name`.
fn overridden_methods(world: &World) -> HashSet<(ClassId, String)> {
    let mut declared: HashMap<ClassId, Vec<String>> = HashMap::default();
    for c in &world.classes {
        let names = declared.entry(c.id).or_default();
        names.extend(c.methods.keys().cloned());
        names.extend(c.singleton_methods.keys().map(|n| format!("self.{n}")));
    }
    for e in &world.extensions {
        declared
            .entry(e.target)
            .or_default()
            .extend(e.methods.keys().cloned());
    }
    let ancestors: Vec<Vec<ClassId>> = world
        .classes
        .iter()
        .map(|c| {
            world
                .ancestors(c.id, &[])
                .into_iter()
                .map(|(a, _)| a)
                .collect()
        })
        .collect();
    let mut out = HashSet::default();
    // (`anc`, module) pairs done: many classes include one module.
    let mut done: HashSet<(ClassId, ClassId)> = HashSet::default();
    for c in &world.classes {
        let own: Vec<&String> = declared.get(&c.id).into_iter().flatten().collect();
        let mine = &ancestors[c.id as usize];
        // Modules the class includes (not a module itself, whose methods
        // only reach a class through it).
        let modules: Vec<ClassId> = if c.kind == quarz_types::ClassKind::Module {
            Vec::new()
        } else {
            mine.iter()
                .copied()
                .filter(|m| *m != c.id && world.class(*m).kind == quarz_types::ClassKind::Module)
                .collect()
        };
        for anc in mine {
            if *anc == c.id {
                continue;
            }
            for name in &own {
                out.insert((*anc, (*name).clone()));
            }
            // A module the class includes overrides `anc`'s methods unless
            // `anc` includes it too (it then comes after `anc`).
            for m in &modules {
                if m == anc || ancestors[*anc as usize].contains(m) || !done.insert((*anc, *m)) {
                    continue;
                }
                for name in declared.get(m).into_iter().flatten() {
                    out.insert((*anc, name.clone()));
                }
            }
        }
    }
    out
}

/// Lower a whole checked program into a module. `files` are the source
/// files by index (0 = the prelude), used for line numbers.
pub fn lower_checked(checked: &Checked, files: &[SourceFile]) -> Module {
    lower_checked_with(Lowerer::new(), checked, files)
}

/// `lower_checked` continuing `lw`, the lowerer the `static` statements
/// ran with (docs/14 §5): its functions so far (`Lowerer::done`) are the
/// program's first, and the bodies of the methods they generated are
/// copied from them.
pub fn lower_checked_with(mut lw: Lowerer, checked: &Checked, files: &[SourceFile]) -> Module {
    let max_file = checked.units.iter().map(|u| u.file).max().unwrap_or(0);
    let mut all: Vec<SourceFile> = files.to_vec();
    while all.len() <= max_file as usize {
        let name = checked
            .units
            .iter()
            .find(|u| u.file as usize == all.len())
            .map(|u| u.name.clone())
            .unwrap_or_default();
        all.push(SourceFile::new(name, ""));
    }
    let inputs: Vec<UnitInput> = checked
        .units
        .iter()
        .map(|u| UnitInput {
            file: u.file,
            name: u.name.clone(),
            main_class: u.main_class,
            body: &u.body,
            repl: false,
        })
        .collect();
    lw.quoted_once = true;
    let delta = lw.lower(&checked.world, &checked.output, &inputs, all);
    let mut functions = std::mem::take(&mut lw.done);
    assert_eq!(functions.len(), delta.base as usize);
    functions.extend(delta.functions);
    // After each pass, what it must leave (`verify`).
    let check = |functions: &[Function], stage| verify::check(functions, &delta.world, stage);
    check(&functions, verify::Stage::Lowered);
    cha::rewrite(&mut functions, &delta.world);
    check(&functions, verify::Stage::Cha);
    devirt::devirtualize(&mut functions, &delta.world);
    check(&functions, verify::Stage::Devirt);
    inline::inline_calls(&mut functions, &delta.world.methods, 2);
    check(&functions, verify::Stage::Inline);
    sroa::scalar_replace(&mut functions, &delta.world.methods, &delta.world.classes);
    check(&functions, verify::Stage::Sroa);
    let before = verify::enabled().then(|| functions.clone());
    copyprop::propagate_copies(&mut functions);
    if let Some(before) = before {
        verify::check_copyprop(&before, &functions);
    }
    check(&functions, verify::Stage::Copyprop);
    release::drop_unobserved(&mut functions, &delta.world.methods, &delta.world.builtin);
    check(&functions, verify::Stage::Release);
    borrow::mark_borrows(&mut functions);
    check(&functions, verify::Stage::Borrow);
    let before = verify::enabled().then(|| functions.clone());
    let maps = regshare::share_registers(&mut functions, &delta.world.methods);
    if let Some(before) = before {
        verify::check_regshare(&before, &functions, &maps, &delta.world);
    }
    check(&functions, verify::Stage::Regshare);
    // Last: where values move rather than copy, for every way the
    // functions run.
    let in_place: Vec<bool> = delta
        .world
        .methods
        .iter()
        .map(|m| {
            m.native_key
                .as_deref()
                .is_some_and(|k| quarz_ir::live::IN_PLACE_NATIVES.contains(&k))
        })
        .collect();
    for f in functions.iter_mut() {
        let heap = quarz_ir::live::heap_possible(f, &delta.world.methods);
        quarz_ir::live::mark_moves(f, &heap);
        quarz_ir::live::own_dying_receivers(f, &in_place);
    }
    check(&functions, verify::Stage::Moves);
    Module {
        world: delta.world,
        functions,
        units: delta.units,
    }
}
