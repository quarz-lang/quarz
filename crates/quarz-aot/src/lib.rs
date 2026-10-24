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
        // The unwinder (backtraces walk the native stack with it) linked
        // in: one shared library fewer to load at start-up.
        .arg("-static-libgcc")
        .args(["-lpthread", "-ldl", "-lm", "-lrt", "-lutil"])
        .status()
        .map_err(|e| format!("cannot run cc: {e}"))?;
    if !status.success() {
        return Err(format!("linking failed ({status})"));
    }
    if std::env::var_os("QUARZ_NO_STRIP").is_none() {
        strip(output)?;
    }
    Ok(())
}

/// Strip the executable `output` of its symbols and debug information
/// (most of its size: the standard library's), keeping what backtraces
/// need of them in a section of its own (`quarz_vm::native_bt::table`).
/// Without `objcopy` the executable stays as it is, and its backtraces
/// read the symbols and the DWARF line table.
fn strip(output: &Path) -> Result<(), String> {
    let exe = std::fs::read(output).map_err(|e| format!("{}: {e}", output.display()))?;
    let table = quarz_vm::native_bt::table(&exe)?;
    let table_path = output.with_extension("quarz_bt");
    std::fs::write(&table_path, &table).map_err(|e| format!("{}: {e}", table_path.display()))?;
    let status = Command::new("objcopy")
        .arg("--strip-all")
        .arg("--add-section")
        .arg(format!(
            "{}={}",
            quarz_vm::native_bt::SECTION,
            table_path.display()
        ))
        .arg(output)
        .status();
    let _ = std::fs::remove_file(&table_path);
    match status {
        Ok(s) if s.success() => Ok(()),
        Ok(s) => Err(format!("stripping failed ({s})")),
        // No objcopy: left unstripped.
        Err(_) => Ok(()),
    }
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
