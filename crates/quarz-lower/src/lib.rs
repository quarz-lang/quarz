//! Lowering of a checked program to QIR.
//!
//! The lowerer is incremental: the REPL calls it once per input, and only
//! the methods, constants and field defaults that have not been lowered
//! yet get functions. Function ids are stable and append-only.

use std::collections::HashMap;

use quarz_ir::*;
use quarz_syntax::ast::Expr;
use quarz_types::{Checked, Output, World};

mod capture;
mod func;
mod rtworld;

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
    pub(crate) file_names: Vec<String>,
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
        file_names: Vec<String>,
    ) -> Delta {
        self.round_base = self.next_func;
        self.pending.clear();
        self.file_names = file_names;

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
        let world = rtworld::build(world, self, self.file_names.clone());
        Delta {
            world,
            base: self.round_base,
            functions,
            units: lowered_units,
        }
    }
}

/// Lower a whole checked program into a module.
pub fn lower_checked(checked: &Checked) -> Module {
    let mut lw = Lowerer::new();
    let max_file = checked.units.iter().map(|u| u.file).max().unwrap_or(0);
    let mut file_names = vec!["<prelude>".to_string(); max_file as usize + 1];
    for u in &checked.units {
        file_names[u.file as usize] = u.name.clone();
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
    let delta = lw.lower(&checked.world, &checked.output, &inputs, file_names);
    Module {
        world: delta.world,
        functions: delta.functions,
        units: delta.units,
    }
}
