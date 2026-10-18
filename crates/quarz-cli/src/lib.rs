//! The driver shared by the `quarz` command and the tests: lowering a
//! checked program and running it on the VM, and the interactive
//! session.

pub mod session;

use quarz_types::Checked;

/// Lower and run a checked program; returns the exit code.
pub fn run(checked: Checked, argv: Vec<String>) -> i32 {
    let module = quarz_lower::lower_checked(&checked);
    quarz_vm::run(module, argv)
}

/// Compile a checked program to the executable `output`.
pub fn build(checked: Checked, output: &std::path::Path) -> Result<(), String> {
    let module = quarz_lower::lower_checked(&checked);
    quarz_aot::build(&module, output)
}

/// Lower and run a checked program capturing its standard output.
pub fn run_capturing(checked: Checked, argv: Vec<String>) -> (i32, String) {
    let module = quarz_lower::lower_checked(&checked);
    quarz_vm::run_capturing(module, argv)
}
