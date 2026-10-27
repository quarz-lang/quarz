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
pub(crate) mod layout;
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

#[derive(Default)]
pub struct Lowerer {
    pub(crate) method_funcs: Vec<Option<FuncId>>,
    pub(crate) const_funcs: Vec<Option<FuncId>>,
    pub(crate) field_default_funcs: HashMap<(ClassId, usize), FuncId>,
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
                let Some(default) = &field.default else {
                    continue;
                };
                if self.field_default_funcs.contains_key(&(class.id, i)) {
                    continue;
                }
                let id = self.alloc_func();
                self.field_default_funcs.insert((class.id, i), id);
                let name = format!("default of {}#@{}", class.name, field.name);
                let f =
                    FnBuilder::init(self, world, out, name, class.file, Some(class.id), default);
                self.set_func(id, f);
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
        loop {
            while self.scanned < self.pending.len() {
                let i = self.scanned;
                self.scanned += 1;
                let Some(f) = self.pending[i].take() else {
                    continue;
                };
                let mut methods = Vec::new();
                let mut names = Vec::new();
                quarz_ir::shake::refs(&f, &mut |r| match r {
                    quarz_ir::shake::Ref::Method(m) => methods.push(m),
                    quarz_ir::shake::Ref::Name(n) => names.push(n.to_string()),
                    _ => {}
                });
                self.pending[i] = Some(f);
                for m in methods {
                    self.reach_method(world, m, &by_name, &mut work);
                }
                for n in names {
                    self.reach_name(world, &n, &by_name, &mut work);
                }
            }
            let Some(mid) = work.pop() else {
                break;
            };
            self.lower_method(world, out, mid);
        }
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
        file == PRELUDE_FILE || world.std_files.contains(&file)
    }

    /// Lower method `mid` if it has a body and has not been lowered.
    fn lower_method(&mut self, world: &World, out: &Output, mid: MethodId) {
        let m = &world.methods[mid as usize];
        if self.method_funcs[mid as usize].is_some() {
            return;
        }
        let Some(def) = &m.body else { return };
        let Some(body) = &def.body else { return };
        let id = self.alloc_func();
        self.method_funcs[mid as usize] = Some(id);
        let f = FnBuilder::method(self, world, out, mid, body);
        self.set_func(id, f);
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
        self.reached_names.insert(name.to_string());
        for &m in by_name.get(name).map(|v| v.as_slice()).unwrap_or(&[]) {
            self.reach_method(world, m, by_name, work);
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
    let mut lw = Lowerer::new();
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
    let delta = lw.lower(&checked.world, &checked.output, &inputs, all);
    let mut functions = delta.functions;
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
    copyprop::propagate_copies(&mut functions);
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
