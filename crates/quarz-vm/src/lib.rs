//! The Quarz runtime and VM: values, the QIR interpreter, the scheduler
//! and the native methods. Compiled programs (`quarz build`) link this
//! crate as their runtime.

#[cfg(feature = "mimalloc")]
pub mod alloc;
pub mod cycles;
pub mod deinit;
#[cfg(target_os = "linux")]
mod epoll;
pub mod ffi;
pub mod ffi_ops;
pub mod interp;
pub mod layout;
pub mod methods;
pub mod native_bt;
pub mod natives;
pub mod ops;
pub mod rc;
pub mod sched;
pub mod transfer;
pub mod value;
pub mod vm;

pub use interp::{Interp, SharedState};
pub use quarz_ir::Module;

/// Run a lowered program with the given arguments; returns the exit code.
pub fn run(module: Module, argv: Vec<String>) -> i32 {
    let interp = Interp::new(module, argv);
    interp.run()
}

/// A writer collecting output into a shared buffer (for tests).
pub struct SharedBuffer(pub std::sync::Arc<std::sync::Mutex<Vec<u8>>>);

impl std::io::Write for SharedBuffer {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        crate::interp::lock(&self.0).extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Run a lowered program capturing its standard output. Returns the exit
/// code and the output.
pub fn run_capturing(module: Module, argv: Vec<String>) -> (i32, String) {
    let buffer = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let interp = Interp::with_output(module, argv, Box::new(SharedBuffer(buffer.clone())));
    let code = interp.run();
    drop(interp);
    let out = String::from_utf8_lossy(&crate::interp::lock(&buffer)).into_owned();
    (code, out)
}
