//! The Quarz runtime and VM: values, the QIR interpreter, the scheduler
//! and the native methods. Compiled programs (`quarz build`) link this
//! crate as their runtime.

pub mod ffi;
pub mod interp;
pub mod layout;
pub mod native_bt;
pub mod natives;
pub mod sched;
pub mod transfer;
pub mod value;
pub mod vm;

use std::cell::RefCell;
use std::rc::Rc;

pub use interp::{Interp, SharedState};
pub use quarz_ir::Module;

/// Run a lowered program with the given arguments; returns the exit code.
pub fn run(module: Module, argv: Vec<String>) -> i32 {
    let interp = Interp::new(module, argv);
    interp.run()
}

/// A writer collecting output into a shared buffer (for tests).
pub struct SharedBuffer(pub Rc<RefCell<Vec<u8>>>);

impl std::io::Write for SharedBuffer {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.borrow_mut().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Run a lowered program capturing its standard output. Returns the exit
/// code and the output.
pub fn run_capturing(module: Module, argv: Vec<String>) -> (i32, String) {
    let buffer = Rc::new(RefCell::new(Vec::new()));
    let interp = Interp::with_output(module, argv, Box::new(SharedBuffer(buffer.clone())));
    let code = interp.run();
    drop(interp);
    let out = String::from_utf8_lossy(&buffer.borrow()).into_owned();
    (code, out)
}
