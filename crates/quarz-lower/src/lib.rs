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

mod capture;
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
        for mid in 0..world.methods.len() {
            if self.method_funcs[mid].is_some() {
                continue;
            }
            let m = &world.methods[mid];
            let Some(def) = &m.body else { continue };
            let Some(body) = &def.body else { continue };
            let id = self.alloc_func();
            self.method_funcs[mid] = Some(id);
            let f = FnBuilder::method(self, world, out, mid as MethodId, body);
            self.set_func(id, f);
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
        // Field defaults.
        for class in &world.classes {
            let fields = world.all_fields(class.id);
            for (i, (field, _)) in fields.iter().enumerate() {
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
    let mut out = HashSet::default();
    for c in &world.classes {
        let Some(names) = declared.get(&c.id) else {
            continue;
        };
        for (anc, _) in world.ancestors(c.id, &[]) {
            if anc == c.id {
                continue;
            }
            for name in names {
                out.insert((anc, name.clone()));
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
    devirt::devirtualize(&mut functions, &delta.world);
    inline::inline_calls(&mut functions, &delta.world.methods, 2);
    sroa::scalar_replace(&mut functions, &delta.world.methods, &delta.world.classes);
    copyprop::propagate_copies(&mut functions);
    release::drop_unobserved(&mut functions, &delta.world.methods, &delta.world.builtin);
    regshare::share_registers(&mut functions, &delta.world.methods);
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
        quarz_ir::live::mark_moves(f);
        quarz_ir::live::own_dying_receivers(f, &in_place);
    }
    Module {
        world: delta.world,
        functions,
        units: delta.units,
    }
}
