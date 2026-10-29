//! The driver shared by the `quarz` command and the tests: lowering a
//! checked program and running it on the VM, and the interactive
//! session.

pub mod complete;
pub mod highlight;
pub mod session;
pub mod static_run;
pub mod tree;

use quarz_lower::Lowerer;
use quarz_syntax::SourceFile;
use quarz_types::Checked;

/// Lower and run a checked program; returns the exit code. `files` are
/// the sources by file index (0 = the prelude), for line numbers.
pub fn run(checked: Checked, files: &[SourceFile], argv: Vec<String>) -> i32 {
    let module = quarz_lower::lower_checked(&checked, files);
    quarz_vm::run(module, argv)
}

/// `run` continuing `lowerer`, the one the program's `static` statements
/// ran with (docs/14 §5): what the `quarz` command does.
pub fn run_with(
    checked: Checked,
    files: &[SourceFile],
    lowerer: Lowerer,
    argv: Vec<String>,
) -> i32 {
    let module = quarz_lower::lower_checked_with(lowerer, &checked, files);
    quarz_vm::run(module, argv)
}

/// Run a lowered program (for tests that change its QIR first).
pub fn run_module(module: quarz_ir::Module, argv: Vec<String>) -> i32 {
    quarz_vm::run(module, argv)
}

/// Compile a checked program to the executable `output`.
pub fn build(
    checked: Checked,
    files: &[SourceFile],
    output: &std::path::Path,
) -> Result<(), String> {
    let module = quarz_lower::lower_checked(&checked, files);
    quarz_aot::build(&module, output)
}

/// `build` continuing `lowerer` (see `run_with`).
pub fn build_with(
    checked: Checked,
    files: &[SourceFile],
    lowerer: Lowerer,
    output: &std::path::Path,
) -> Result<(), String> {
    let module = quarz_lower::lower_checked_with(lowerer, &checked, files);
    quarz_aot::build(&module, output)
}

/// Lower and run a checked program capturing its standard output.
pub fn run_capturing(checked: Checked, files: &[SourceFile], argv: Vec<String>) -> (i32, String) {
    let module = quarz_lower::lower_checked(&checked, files);
    quarz_vm::run_capturing(module, argv)
}

/// Lower a checked program (tests of the QIR; a program without `static`
/// statements).
pub fn lower(checked: &Checked, files: &[SourceFile]) -> quarz_ir::Module {
    quarz_lower::lower_checked(checked, files)
}

/// Lower a checked program, continuing the lowerer its `static`
/// statements ran with (for `quarz ir`).
pub fn lower_with(checked: &Checked, files: &[SourceFile], lowerer: Lowerer) -> quarz_ir::Module {
    quarz_lower::lower_checked_with(lowerer, checked, files)
}
