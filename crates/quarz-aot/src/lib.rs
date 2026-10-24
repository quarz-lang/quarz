//! Ahead-of-time compilation of QIR to native executables.
//!
//! The generator (`gen`) is written against `builder::Builder`, which
//! `llvm` implements: LLVM IR compiled by clang, with typed entries that
//! push no activation and backtraces from the native stack.

use std::path::{Path, PathBuf};
use std::process::Command;

use quarz_ir::Module;

mod builder;
mod gen;
mod llvm;
mod unbox;

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

/// Link an object file with the runtime into the executable `output`,
/// dropping the runtime's code the program cannot reach (the runtime is
/// one codegen unit, each function in a section of its own).
fn link(object: &Path, output: &Path) -> Result<(), String> {
    let runtime = find_runtime_lib()?;
    let status = Command::new("cc")
        .arg("-o")
        .arg(output)
        .arg(object)
        .arg(&runtime)
        .arg("-Wl,--gc-sections")
        .args(["-lpthread", "-ldl", "-lm", "-lgcc_s", "-lrt", "-lutil"])
        .status()
        .map_err(|e| format!("cannot run cc: {e}"))?;
    if !status.success() {
        return Err(format!("linking failed ({status})"));
    }
    Ok(())
}

/// Compile a module and link it into the executable `output`.
pub fn build(module: &Module, output: &Path) -> Result<(), String> {
    // What the program cannot run is neither compiled nor decoded at
    // start-up (`QUARZ_NO_SHAKE` keeps everything, for comparison).
    let mut shaken;
    let module = if std::env::var_os("QUARZ_NO_SHAKE").is_some() {
        module
    } else {
        shaken = module.clone();
        quarz_ir::shake::shake(&mut shaken);
        &shaken
    };
    let obj_path = output.with_extension("o");
    llvm::compile(module, &obj_path)?;
    let linked = link(&obj_path, output);
    let _ = std::fs::remove_file(&obj_path);
    linked
}
