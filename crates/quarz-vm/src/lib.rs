//! The Quarz interpreter.

pub mod eval;
pub mod interp;
pub mod natives;
pub mod sched;
pub mod value;

pub use interp::Interp;

/// Run a checked program with the given arguments; returns the exit code.
pub fn run(checked: quarz_types::Checked, argv: Vec<String>) -> i32 {
    let interp = Interp::new(checked, argv);
    interp.run()
}
