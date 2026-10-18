//! Name resolution and type checking for Quarz.
//!
//! [`check`] takes the parsed prelude and user program and produces a
//! [`Checked`] program: the world of classes and methods, plus side tables
//! keyed by AST node that the evaluator uses (types, call targets, variable
//! slots).

pub mod check;
pub mod declare;
pub mod patterns;
pub mod types;
pub mod world;

use quarz_syntax::ast::{Expr, Program};
use quarz_syntax::Diagnostic;

pub use check::{BlockPass, CallTarget, ConstTarget, Output, VarRef};

/// The source of the standard prelude, embedded at build time.
pub const PRELUDE_SOURCE: &str = include_str!("../../../std/prelude.qz");
pub use types::*;
pub use world::*;

/// A fully checked program.
pub struct Checked {
    pub world: World,
    pub output: Output,
    /// The main class (holding top-level methods) and the top-level
    /// statements to run.
    pub main_class: ClassId,
    pub main_body: Vec<Expr>,
    pub main_extensions: Vec<ExtensionId>,
}

/// Diagnostics tagged with the index of the file they refer to (0 = prelude,
/// 1 = user program).
pub type FileDiagnostic = (u32, Diagnostic);

pub fn check(prelude: &Program, program: &Program) -> (Option<Checked>, Vec<FileDiagnostic>) {
    let mut declarer = declare::Declarer::new();
    declarer.collect_prelude(prelude);
    declarer.collect_main(program);
    declarer.resolve_headers();
    let mut diagnostics = std::mem::take(&mut declarer.diagnostics);
    let main_body: Vec<&Expr> = declarer.main_body.clone();
    let main_class = declarer.main_class;
    let main_extensions = declarer.main_extensions.clone();
    if diagnostics.iter().any(|(_, d)| d.is_error()) {
        return (None, diagnostics);
    }
    let mut checker = check::Checker::new(declarer.world, main_class, main_extensions.clone());
    checker.check_all(&main_body);
    let (world, output, mut diags) = checker.into_output();
    diagnostics.append(&mut diags);
    let failed = diagnostics.iter().any(|(_, d)| d.is_error());
    let checked = Checked {
        world,
        output,
        main_class,
        main_body: main_body.into_iter().cloned().collect(),
        main_extensions,
    };
    if failed {
        (None, diagnostics)
    } else {
        (Some(checked), diagnostics)
    }
}
