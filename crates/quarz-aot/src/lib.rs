//! Ahead-of-time compilation of QIR to native executables.
//!
//! The generator (`gen`) is written against `builder::Builder`; two
//! backends implement it: `llvm` (the production one: machine code
//! through LLVM, typed entries that push no activation, backtraces from
//! the native stack) and `cranelift` (for development: fast to build,
//! no toolchain beyond a C linker).

use std::path::{Path, PathBuf};
use std::process::Command;

use quarz_ir::Module;

mod builder;
mod cranelift;
mod gen;
mod llvm;
mod unbox;

/// Which backend `build` uses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Backend {
    Llvm,
    Cranelift,
}

impl Backend {
    /// From a name (`llvm` or `cranelift`).
    pub fn parse(name: &str) -> Option<Backend> {
        match name {
            "llvm" => Some(Backend::Llvm),
            "cranelift" => Some(Backend::Cranelift),
            _ => None,
        }
    }
}

// ----- building executables ----------------------------------------------------------

/// The runtime static library compiled programs link against: `$QUARZ_RT_LIB`
/// or `libquarz_vm.a` next to the running executable (or one directory
/// up, for `target/debug/deps`).
pub fn find_runtime_lib() -> Result<PathBuf, String> {
    if let Ok(p) = std::env::var("QUARZ_RT_LIB") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Ok(p);
        }
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let mut dir = exe.parent();
    for _ in 0..3 {
        if let Some(d) = dir {
            let candidate = d.join("libquarz_vm.a");
            if candidate.exists() {
                return Ok(candidate);
            }
            dir = d.parent();
        }
    }
    Err("cannot find libquarz_vm.a (build it with `cargo build` or set QUARZ_RT_LIB)".to_string())
}

/// Link an object file with the runtime into the executable `output`.
fn link(object: &Path, output: &Path) -> Result<(), String> {
    let runtime = find_runtime_lib()?;
    let status = Command::new("cc")
        .arg("-o")
        .arg(output)
        .arg(object)
        .arg(&runtime)
        .args(["-lpthread", "-ldl", "-lm", "-lgcc_s", "-lrt", "-lutil"])
        .status()
        .map_err(|e| format!("cannot run cc: {e}"))?;
    if !status.success() {
        return Err(format!("linking failed ({status})"));
    }
    Ok(())
}

/// Compile a module and link it into the executable `output`.
pub fn build(module: &Module, output: &Path, backend: Backend) -> Result<(), String> {
    let obj_path = output.with_extension("o");
    match backend {
        Backend::Cranelift => {
            let object = cranelift::compile(module)?;
            std::fs::write(&obj_path, &object)
                .map_err(|e| format!("{}: {e}", obj_path.display()))?;
        }
        Backend::Llvm => llvm::compile(module, &obj_path)?,
    }
    let linked = link(&obj_path, output);
    let _ = std::fs::remove_file(&obj_path);
    linked
}
