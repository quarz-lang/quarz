//! The driver shared by the `quarz` command and the tests: lowering a
//! checked program and running it on the VM, and the interactive
//! session.

pub mod complete;
pub mod highlight;
pub mod session;
pub mod tree;

use quarz_syntax::SourceFile;
use quarz_types::Checked;

/// Lower and run a checked program; returns the exit code. `files` are
/// the sources by file index (0 = the prelude), for line numbers.
pub fn run(checked: Checked, files: &[SourceFile], argv: Vec<String>) -> i32 {
    let module = quarz_lower::lower_checked(&checked, files);
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

/// Lower and run a checked program capturing its standard output.
pub fn run_capturing(checked: Checked, files: &[SourceFile], argv: Vec<String>) -> (i32, String) {
    let module = quarz_lower::lower_checked(&checked, files);
    quarz_vm::run_capturing(module, argv)
}

/// Lower a checked program (for `quarz ir`).
pub fn lower(checked: &Checked, files: &[SourceFile]) -> quarz_ir::Module {
    quarz_lower::lower_checked(checked, files)
}
