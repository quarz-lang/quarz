//! The driver shared by the `quarz` command and the tests: lowering a
//! checked program and running it on the VM, and the interactive
//! session.

pub mod complete;
pub mod highlight;
pub mod session;
pub mod static_run;
pub mod std_set;
pub mod tree;

use quarz_lower::Lowerer;
use quarz_syntax::SourceFile;
use quarz_types::Checked;

/// Lower and run a checked program; returns the exit code. `files` are
/// the sources by file index (0 = the prelude), for line numbers.
/// Whether a declaration is the program's own for the safety net's errors
/// (`quarz_types::witness_net::errors`): in the application's files (a
/// script's and those it requires), not a dependency's or the standard
/// library's.
pub fn own_in_app(world: &quarz_types::World, d: quarz_types::witness_net::Decl) -> bool {
    let file = match d {
        quarz_types::witness_net::Decl::Class(c) => world.class(c).file,
        quarz_types::witness_net::Decl::Extension(e) => world.extensions[e as usize].file,
    };
    matches!(
        world.file_groups.get(&file),
        Some(quarz_types::UnitGroup::App)
    )
}

pub fn run(checked: Checked, files: &[SourceFile], argv: Vec<String>) -> i32 {
    let module = quarz_lower::lower_checked(&checked, files);
    quarz_vm::run(module, argv)
}

/// `run` continuing `lowerer`, the one the program's `static` statements
/// ran with (docs/14 §5): what the `quarz` command does. A program whose
/// cogs bring native code has their libraries loaded and bound first
/// (`load_natives`); a failure is reported, the program not run.
pub fn run_with(
    checked: Checked,
    files: &[SourceFile],
    lowerer: Lowerer,
    argv: Vec<String>,
) -> i32 {
    let module = quarz_lower::lower_checked_with(lowerer, &checked, files);
    if let Err(e) = load_natives(&module.world) {
        eprintln!("quarz: {e}");
        return 1;
    }
    quarz_vm::run(module, argv)
}

/// The cogs of the movement being run that bring native code (#677):
/// each one's name and the directory of its native package, recorded when
/// the movement is opened (`set_native_cogs`).
static NATIVE_COGS: std::sync::Mutex<Vec<(String, std::path::PathBuf)>> =
    std::sync::Mutex::new(Vec::new());

/// Record the native cogs of the movement opened (`NATIVE_COGS`).
pub fn set_native_cogs(cogs: &[quarz_cog::CogEntry]) {
    *NATIVE_COGS.lock().expect("the native cogs") = cogs
        .iter()
        .filter_map(|c| Some((c.name.clone(), c.native.clone()?)))
        .collect();
}

/// Load the libraries of `world`'s native cogs and bind their entries
/// (`quarz_vm::native_ext`): an error naming the cog when a library is
/// missing (it is built from the cog's native package with `cargo build
/// --release`), cannot be loaded, or does not define what the cog
/// declares.
pub fn load_natives(world: &quarz_ir::RtWorld) -> Result<(), String> {
    if world.native_cogs.is_empty() {
        return Ok(());
    }
    let cogs = NATIVE_COGS.lock().expect("the native cogs").clone();
    for name in &world.native_cogs {
        let Some((_, dir)) = cogs.iter().find(|(n, _)| n == name) else {
            return Err(format!(
                "cog `{name}` brings native code, but its package is not known"
            ));
        };
        let lib = quarz_cog::native::library(dir).map_err(|e| e.to_string())?;
        if !lib.is_file() {
            return Err(format!(
                "cog `{name}` brings native code, but its library is not built: no {} (build its package in {} with `cargo build --release`)",
                lib.display(),
                dir.display()
            ));
        }
        quarz_vm::native_ext::load(name, &lib)?;
    }
    quarz_vm::native_ext::check(world)
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
    let jobs = quarz_aot::build_jobs(None)?;
    quarz_aot::build_with_jobs(
        &module,
        &file_groups(&checked),
        output,
        jobs,
        object_cache().as_deref(),
    )
}

/// The objects' cache of `quarz build` (#1182): `objects/` in the
/// checker's cache directory (`quarz_types::cache::dir`), none when the
/// cache is off (`QUARZ_NO_CACHE`).
fn object_cache() -> Option<std::path::PathBuf> {
    quarz_types::cache::dir().map(|d| d.join("objects"))
}

/// The checked program's files by group, as `quarz build` partitions them
/// (`quarz_aot::FileGroups`): the application first, then the cogs by
/// index, then the standard library as one group (it changes only with
/// the compiler), which the prelude's files, in none, join.
fn file_groups(checked: &Checked) -> quarz_aot::FileGroups {
    checked
        .world
        .file_groups
        .iter()
        .map(|(file, g)| {
            let key = match g {
                quarz_types::UnitGroup::App => 0,
                quarz_types::UnitGroup::Cog(i) => 1 + u64::from(*i),
                quarz_types::UnitGroup::Std(_) => u64::MAX,
            };
            (*file, key)
        })
        .collect()
}

/// `build_with` by `jobs` clang processes at once (`quarz build -j`).
pub fn build_with_jobs(
    checked: Checked,
    files: &[SourceFile],
    lowerer: Lowerer,
    output: &std::path::Path,
    jobs: usize,
) -> Result<(), String> {
    let start = std::time::Instant::now();
    let module = quarz_lower::lower_checked_with(lowerer, &checked, files);
    quarz_aot::report("lower", start, &[]);
    quarz_aot::build_with_jobs(
        &module,
        &file_groups(&checked),
        output,
        jobs,
        object_cache().as_deref(),
    )
}

/// `build` continuing `lowerer` (see `run_with`).
pub fn build_with(
    checked: Checked,
    files: &[SourceFile],
    lowerer: Lowerer,
    output: &std::path::Path,
) -> Result<(), String> {
    let start = std::time::Instant::now();
    let module = quarz_lower::lower_checked_with(lowerer, &checked, files);
    quarz_aot::report("lower", start, &[]);
    let jobs = quarz_aot::build_jobs(None)?;
    quarz_aot::build_with_jobs(
        &module,
        &file_groups(&checked),
        output,
        jobs,
        object_cache().as_deref(),
    )
}

/// Lower and run a checked program capturing its standard output.
pub fn run_capturing(checked: Checked, files: &[SourceFile], argv: Vec<String>) -> (i32, String) {
    let module = quarz_lower::lower_checked(&checked, files);
    quarz_vm::run_capturing(module, argv)
}

/// Lower a checked program (tests of the QIR; a program without `static`
/// statements).
pub fn lower(checked: &Checked, files: &[SourceFile]) -> quarz_ir::Module {
    quarz_lower::lower_checked(checked, files)
}

/// Lower a checked program, continuing the lowerer its `static`
/// statements ran with (for `quarz ir`).
pub fn lower_with(checked: &Checked, files: &[SourceFile], lowerer: Lowerer) -> quarz_ir::Module {
    quarz_lower::lower_checked_with(lowerer, checked, files)
}
