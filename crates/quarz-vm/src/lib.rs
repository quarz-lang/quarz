//! The Quarz interpreter.

pub mod eval;
pub mod interp;
pub mod natives;
pub mod sched;
pub mod value;

use std::cell::RefCell;
use std::rc::Rc;

pub use interp::Interp;

/// Run a checked program with the given arguments; returns the exit code.
pub fn run(checked: quarz_types::Checked, argv: Vec<String>) -> i32 {
    let interp = Interp::new(checked, argv);
    interp.run()
}

/// A writer collecting output into a shared buffer (for tests).
struct SharedBuffer(Rc<RefCell<Vec<u8>>>);

impl std::io::Write for SharedBuffer {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.borrow_mut().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Run a checked program capturing its standard output. Returns the exit
/// code and the output.
pub fn run_capturing(checked: quarz_types::Checked, argv: Vec<String>) -> (i32, String) {
    let buffer = Rc::new(RefCell::new(Vec::new()));
    let interp = Interp::with_output(checked, argv, Box::new(SharedBuffer(buffer.clone())));
    let code = interp.run();
    drop(interp);
    let out = String::from_utf8_lossy(&buffer.borrow()).into_owned();
    (code, out)
}
