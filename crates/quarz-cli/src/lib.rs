//! The driver shared by the `quarz` command and the tests: lowering a
//! checked program and running it on the VM, and the interactive
//! session.

pub mod session;

use quarz_syntax::SourceFile;
use quarz_types::Checked;

/// Lower and run a checked program; returns the exit code. `files` are
/// the sources by file index (0 = the prelude), for line numbers.
pub fn run(checked: Checked, files: &[SourceFile], argv: Vec<String>) -> i32 {
    let module = quarz_lower::lower_checked(&checked, files);
    quarz_vm::run(module, argv)
}

/// Compile a checked program to the executable `output`.
pub fn build(
    checked: Checked,
    files: &[SourceFile],
    output: &std::path::Path,
    backend: quarz_aot::Backend,
) -> Result<(), String> {
    let sharing = match backend {
        quarz_aot::Backend::Llvm => quarz_lower::Sharing::All,
        quarz_aot::Backend::Cranelift => quarz_lower::Sharing::Numbers,
    };
    let module = quarz_lower::lower_checked_with(&checked, files, sharing);
    quarz_aot::build(&module, output, backend)
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
