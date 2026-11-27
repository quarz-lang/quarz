//! The driver shared by the `quarz` command and the tests: lowering a
//! checked program and running it on the VM, and the interactive
//! session.

pub mod complete;
pub mod highlight;
pub mod native;
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
/// cogs bring native code (`natives`) has their libraries built or found
/// kept, loaded and bound first (`load_natives`); a failure is reported,
/// the program not run.
pub fn run_with(
    checked: Checked,
    files: &[SourceFile],
    lowerer: Lowerer,
    argv: Vec<String>,
    natives: &Natives,
) -> i32 {
    let module = quarz_lower::lower_checked_with(lowerer, &checked, files);
    if let Err(e) = load_natives(&module.world, natives) {
        eprintln!("quarz: {e}");
        return 1;
    }
    quarz_vm::run(module, argv)
}

/// The cogs of the movement a program comes from that bring native code
/// (#677), and whether cargo runs offline (as the cogs were resolved:
/// `quarz_cog::Options::offline`).
#[derive(Clone, Debug, Default)]
pub struct Natives {
    pub cogs: Vec<native::NativeCog>,
    pub offline: bool,
}

impl Natives {
    /// Those of `cogs`, a movement's (the application first).
    pub fn of(cogs: &[quarz_cog::CogEntry], opts: &quarz_cog::Options) -> Natives {
        Natives {
            cogs: native::of(cogs),
            offline: opts.offline,
        }
    }
}

/// Build (or find kept) the libraries of `world`'s native cogs
/// (`native::build_all`), load them and bind their entries
/// (`quarz_vm::native_ext`): an error naming the cog when its package
/// cannot be built, its library cannot be loaded, or it does not define
/// what the cog declares.
pub fn load_natives(world: &quarz_ir::RtWorld, natives: &Natives) -> Result<(), String> {
    if world.native_cogs.is_empty() {
        return Ok(());
    }
    let mut cogs = Vec::new();
    for name in world.native_cogs.iter().map(|c| &c.name) {
        let Some(c) = natives.cogs.iter().find(|c| &c.name == name) else {
            return Err(format!(
                "internal error: cog `{name}` brings native code, but its package is not known"
            ));
        };
        cogs.push(c.clone());
    }
    for (name, built) in native::build_all(&cogs, natives.offline, native::Use::Load)? {
        let loaded = quarz_vm::native_ext::load(&name, &built.file);
        if built.remove_after {
            if let Some(dir) = built.file.parent() {
                let _ = std::fs::remove_dir_all(dir);
            }
        }
        loaded?;
    }
    quarz_vm::native_ext::check(world)
}

/// The archives to link, by cog, and the directories to remove after.
type Archives = (Vec<(String, std::path::PathBuf)>, Vec<std::path::PathBuf>);

/// The archives `quarz build` links of `world`'s native cogs, by cog
/// (built, or found kept: `native::build_all`), and the directories to
/// remove once linked (copies, with the cache off).
fn archives(world: &quarz_ir::RtWorld, natives: &Natives) -> Result<Archives, String> {
    let mut cogs = Vec::new();
    for name in world.native_cogs.iter().map(|c| &c.name) {
        let Some(c) = natives.cogs.iter().find(|c| &c.name == name) else {
            return Err(format!(
                "internal error: cog `{name}` brings native code, but its package is not known"
            ));
        };
        cogs.push(c.clone());
    }
    let mut out = Vec::new();
    let mut remove = Vec::new();
    for (name, built) in native::build_all(&cogs, natives.offline, native::Use::Link)? {
        if built.remove_after {
            remove.extend(built.file.parent().map(|p| p.to_path_buf()));
        }
        out.push((name, built.file));
    }
    Ok((out, remove))
}

/// `quarz_aot::build_with_jobs` with the archives of the module's native
/// cogs (`archives`).
fn build_linked(
    module: &quarz_ir::Module,
    checked: &Checked,
    output: &std::path::Path,
    jobs: usize,
    natives: &Natives,
) -> Result<(), String> {
    let (archives, remove) = archives(&module.world, natives)?;
    let built = quarz_aot::build_with_jobs(
        module,
        &file_groups(checked),
        output,
        jobs,
        object_cache().as_deref(),
        &archives,
    );
    for dir in remove {
        let _ = std::fs::remove_dir_all(dir);
    }
    built
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
    build_linked(&module, &checked, output, jobs, &Natives::default())
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
    natives: &Natives,
) -> Result<(), String> {
    let start = std::time::Instant::now();
    let module = quarz_lower::lower_checked_with(lowerer, &checked, files);
    quarz_aot::report("lower", start, &[]);
    build_linked(&module, &checked, output, jobs, natives)
}

/// `build` continuing `lowerer` (see `run_with`).
pub fn build_with(
    checked: Checked,
    files: &[SourceFile],
    lowerer: Lowerer,
    output: &std::path::Path,
    natives: &Natives,
) -> Result<(), String> {
    let start = std::time::Instant::now();
    let module = quarz_lower::lower_checked_with(lowerer, &checked, files);
    quarz_aot::report("lower", start, &[]);
    let jobs = quarz_aot::build_jobs(None)?;
    build_linked(&module, &checked, output, jobs, natives)
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
