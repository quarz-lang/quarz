//! Name resolution and type checking for Quarz.
//!
//! [`check_units`] takes the parsed prelude and the user's compilation
//! units (files, dependencies first) and produces a [`Checked`] program:
//! the world of classes and methods, plus side tables keyed by AST node
//! that the evaluator uses (types, call targets, variable slots).

pub mod check;
pub mod declare;
pub mod load;
pub mod patterns;
pub mod types;
pub mod world;

use quarz_syntax::ast::{Expr, Program};
use quarz_syntax::Diagnostic;

pub use check::{BlockPass, CallTarget, ConstTarget, Output, VarRef};
pub use load::{load, LoadedUnit, STD_MODULES};
pub use types::*;
pub use world::*;

/// The source of the standard prelude, embedded at build time.
pub const PRELUDE_SOURCE: &str = include_str!("../../../std/prelude.qz");

/// A compilation unit to check: a parsed file and the name used for
/// `__FILE__`.
pub struct Unit {
    pub name: String,
    pub program: Program,
}

/// A checked compilation unit: its top-level statements and the
/// pseudo-class holding its top-level methods.
pub struct CheckedUnit {
    pub file: u32,
    pub name: String,
    pub main_class: ClassId,
    pub body: Vec<Expr>,
}

/// A fully checked program.
pub struct Checked {
    pub world: World,
    pub output: Output,
    /// Units in execution order (dependencies first, the main file last).
    pub units: Vec<CheckedUnit>,
}

/// Diagnostics tagged with the index of the file they refer to (0 = prelude,
/// 1.. = units in order).
pub type FileDiagnostic = (u32, Diagnostic);

/// Check a single-file program.
pub fn check(prelude: &Program, program: &Program) -> (Option<Checked>, Vec<FileDiagnostic>) {
    let unit = Unit {
        name: "main".to_string(),
        program: program.clone(),
    };
    check_units(prelude, &[unit])
}

pub fn check_units(prelude: &Program, units: &[Unit]) -> (Option<Checked>, Vec<FileDiagnostic>) {
    let mut declarer = declare::Declarer::new();
    declarer.collect_prelude(prelude);
    for (i, unit) in units.iter().enumerate() {
        declarer.collect_unit(&unit.program, i as u32 + 1);
    }
    declarer.resolve_headers();
    let mut diagnostics = std::mem::take(&mut declarer.diagnostics);
    let mut file_mains: Vec<Option<ClassId>> = vec![None; units.len() + 1];
    let mut bodies: Vec<(u32, Vec<&Expr>)> = Vec::new();
    for u in &declarer.units {
        file_mains[u.file as usize] = Some(u.main);
        bodies.push((u.file, u.body.clone()));
    }
    if diagnostics.iter().any(|(_, d)| d.is_error()) {
        return (None, diagnostics);
    }
    let mut checker = check::Checker::new(declarer.world, file_mains.clone());
    checker.check_all(&bodies);
    let (world, output, mut diags) = checker.into_output();
    diagnostics.append(&mut diags);
    let failed = diagnostics.iter().any(|(_, d)| d.is_error());
    let checked_units = bodies
        .into_iter()
        .map(|(file, body)| CheckedUnit {
            file,
            name: units[file as usize - 1].name.clone(),
            main_class: file_mains[file as usize].unwrap(),
            body: body.into_iter().cloned().collect(),
        })
        .collect();
    let checked = Checked {
        world,
        output,
        units: checked_units,
    };
    if failed {
        (None, diagnostics)
    } else {
        (Some(checked), diagnostics)
    }
}
