//! Ahead-of-time compilation of QIR to native executables.
//!
//! The generator (`gen`) is written against `builder::Builder`, which
//! `llvm` implements: LLVM IR compiled by clang, with typed entries that
//! push no activation and backtraces from the native stack.

use std::path::{Path, PathBuf};
use std::process::Command;

use quarz_ir::Module;

/// Each source file's group, for `quarz build`'s partitions (#786): the
/// files of one group (the application, a cog, the standard library)
/// share a key, and the keys order the groups; a file without one is in
/// the standard library's (`u64::MAX`). Empty, every function is in one
/// group.
pub type FileGroups = std::collections::HashMap<u32, u64>;

mod builder;
pub mod clash;
mod gen;
mod llvm;
pub mod objcache;
mod unbox;

// ----- building executables ----------------------------------------------------------

/// The runtime static library compiled programs link against: `$QUARZ_RT_LIB`
/// or `libquarz_vm.a` next to the running executable or in a directory
/// up to four levels above it: Cargo's profile directory (`target/debug`)
/// for a test binary, which Cargo puts in `target/debug/deps` up to Rust
/// 1.99 and in `target/debug/build/<package>/<hash>/out` from 1.100.
pub fn find_runtime_lib() -> Result<PathBuf, String> {
    if let Ok(p) = std::env::var("QUARZ_RT_LIB") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Ok(p);
        }
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let mut dir = exe.parent();
    for _ in 0..5 {
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

/// Whether `QUARZ_BUILD_TIMINGS=1` asks `quarz build` for its stages'
/// times (#785).
pub fn timings() -> bool {
    std::env::var_os("QUARZ_BUILD_TIMINGS").is_some_and(|v| v == "1")
}

/// Under `QUARZ_BUILD_TIMINGS=1`, one line on standard error for a stage
/// of `quarz build` that began at `start`: `quarz-build-timing
/// stage=<name> ms=<wall time> [<key>=<value> ...]`, for scripts to read
/// (docs/05). Nothing otherwise.
pub fn report(stage: &str, start: std::time::Instant, extra: &[(&str, String)]) {
    if !timings() {
        return;
    }
    let mut line = format!(
        "quarz-build-timing stage={stage} ms={:.3}",
        start.elapsed().as_secs_f64() * 1000.0
    );
    for (k, v) in extra {
        line.push_str(&format!(" {k}={v}"));
    }
    eprintln!("{line}");
}

/// Link the object files (the program's partitions, in order) with the
/// runtime into the executable `output`, dropping the runtime's code the
/// program cannot reach (the runtime is one codegen unit, each function in
/// a section of its own). The names partitions call each other's functions
/// by are equated with the functions' own by `--defsym`, in a response
/// file in `dir` (#1182): the one form GNU ld, gold, lld and mold all
/// document (GNU ld and lld are tested; gold and mold are taken from
/// their documentation). The names are `llvm::localize`'s (letters,
/// digits and `_`), so the file needs no quoting.
fn link(
    compiled: &llvm::Compiled,
    dir: &Path,
    output: &Path,
    archives: &[Archive],
) -> Result<(), String> {
    let runtime = find_runtime_lib()?;
    let start = std::time::Instant::now();
    // The cogs' archives under names that carry the cog (`lib<cog>.a`,
    // links in the build's directory), so that what the linker still
    // says of one names it, not a key of the store.
    let named_dir = dir.join("cogs");
    let mut named = Vec::new();
    if !archives.is_empty() {
        std::fs::create_dir_all(&named_dir).map_err(|e| format!("{}: {e}", named_dir.display()))?;
    }
    for a in archives {
        let link = named_dir.join(format!("lib{}.a", a.cog));
        let _ = std::fs::remove_file(&link);
        std::os::unix::fs::symlink(&a.path, &link)
            .map_err(|e| format!("{}: {e}", link.display()))?;
        named.push(link);
    }
    let mut cc = Command::new("cc");
    // The runtime before the cogs' archives: its definitions (std, the
    // allocator, the personality routine) are the ones taken, and a cog's
    // identical members are not pulled.
    cc.arg("-o")
        .arg(output)
        .args(&compiled.objects)
        .arg(&runtime)
        .args(&named);
    if !compiled.map.is_empty() {
        let mut rsp = String::new();
        for (from, to) in &compiled.map {
            rsp.push_str(&format!("-Wl,--defsym={from}={to}\n"));
        }
        let path = dir.join("names.rsp");
        std::fs::write(&path, rsp).map_err(|e| format!("{}: {e}", path.display()))?;
        let mut arg = std::ffi::OsString::from("@");
        arg.push(&path);
        cc.arg(arg);
    }
    let status = cc
        .arg("-Wl,--gc-sections")
        // The unwinder (backtraces walk the native stack with it) linked
        // in: one shared library fewer to load at start-up.
        .arg("-static-libgcc")
        .args(["-lpthread", "-ldl", "-lm", "-lrt", "-lutil"])
        .status()
        .map_err(|e| format!("cannot run cc: {e}"))?;
    if !status.success() {
        if !compiled.map.is_empty() {
            return Err(format!(
                "linking failed ({status})\n\
                 quarz: the partitions call each other through names the linker equates \
                 (`--defsym`, {} of them); a linker that refuses them builds one partition \
                 with QUARZ_BUILD_PARTITION_BYTES=1000000000",
                compiled.map.len()
            ));
        }
        return Err(format!("linking failed ({status})"));
    }
    report("link", start, &[("names", compiled.map.len().to_string())]);
    let start = std::time::Instant::now();
    strip(
        output,
        &compiled.typed_names,
        std::env::var_os("QUARZ_NO_STRIP").is_none(),
    )?;
    report("strip", start, &[]);
    Ok(())
}

/// Give the executable `output` what backtraces need in a section of its
/// own (`quarz_vm::native_bt::table`: the typed entries, by their names in
/// `typed_names`, and the line table), and with `strip` strip it of its
/// symbols and debug information (most of its size: the standard
/// library's), by `objcopy`, else `llvm-objcopy` (which takes the same
/// arguments). With neither, the executable stays as it is and a warning
/// says so: its backtraces show no compiled function, as the symbols'
/// names do not say which function they are (#1182).
fn strip(
    output: &Path,
    typed_names: &[(String, quarz_ir::FuncId)],
    strip: bool,
) -> Result<(), String> {
    let exe = std::fs::read(output).map_err(|e| format!("{}: {e}", output.display()))?;
    let names: std::collections::HashMap<&str, quarz_ir::FuncId> =
        typed_names.iter().map(|(n, f)| (n.as_str(), *f)).collect();
    let table = quarz_vm::native_bt::table(&exe, &|name| names.get(name).copied())?;
    let table_path = output.with_extension("quarz_bt");
    std::fs::write(&table_path, &table).map_err(|e| format!("{}: {e}", table_path.display()))?;
    let mut result = None;
    for tool in OBJCOPY {
        let mut objcopy = Command::new(tool);
        if strip {
            objcopy.arg("--strip-all");
        }
        let status = objcopy
            .arg("--add-section")
            .arg(format!(
                "{}={}",
                quarz_vm::native_bt::SECTION,
                table_path.display()
            ))
            .arg(output)
            .status();
        match status {
            Ok(s) if s.success() => result = Some(Ok(())),
            Ok(s) => result = Some(Err(format!("{tool} failed on {} ({s})", output.display()))),
            // Not there: the next.
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => result = Some(Err(format!("cannot run {tool}: {e}"))),
        }
        break;
    }
    let _ = std::fs::remove_file(&table_path);
    result.unwrap_or_else(|| {
        eprintln!(
            "quarz: warning: neither objcopy nor llvm-objcopy runs here: {} is left unstripped, and its backtraces will show no compiled function; install binutils or LLVM's llvm-objcopy",
            output.display()
        );
        Ok(())
    })
}

/// The tools `strip` tries, in order.
const OBJCOPY: [&str; 2] = ["objcopy", "llvm-objcopy"];

/// The clang processes `quarz build` runs at once (#786): `jobs` when
/// given (`quarz build -j N`), else `QUARZ_BUILD_JOBS`, else the
/// available parallelism. Zero or a value that is not a number is an
/// error. Whatever it is, the executable is the same.
pub fn build_jobs(jobs: Option<&str>) -> Result<usize, String> {
    let (what, text) = match jobs {
        Some(j) => ("-j", j.to_string()),
        None => match std::env::var("QUARZ_BUILD_JOBS") {
            Ok(v) => ("QUARZ_BUILD_JOBS", v),
            Err(_) => {
                return Ok(std::thread::available_parallelism().map_or(1, |n| n.get()));
            }
        },
    };
    match text.trim().parse::<usize>() {
        Ok(n) if n > 0 => Ok(n),
        _ => Err(format!(
            "{what} must be a number of jobs, 1 or more, not {text:?}"
        )),
    }
}

/// Compile a module and link it into the executable `output`, with the
/// jobs `build_jobs(None)` gives, no file groups and no cache of objects.
pub fn build(module: &Module, output: &Path) -> Result<(), String> {
    build_with_jobs(
        module,
        &FileGroups::default(),
        output,
        build_jobs(None)?,
        None,
        &[],
    )
}

/// A cog's archive to link (#677): its name, how errors name it
/// (``cog `zlib` (app → zlib)``) and the file.
pub struct Archive {
    pub cog: String,
    pub who: String,
    pub path: PathBuf,
}

/// `build` by `jobs` clang processes at once, with the objects' cache in
/// `cache` (`objcache`; none: every partition is compiled). The program's
/// partitions are compiled in a directory next to `output`
/// (`<output>.quarz-build`), removed after the link, or when the build
/// fails; `QUARZ_KEEP_IR` keeps it, with each partition's IR, and says
/// where.
pub fn build_with_jobs(
    module: &Module,
    groups: &FileGroups,
    output: &Path,
    jobs: usize,
    cache: Option<&Path>,
    archives: &[Archive],
) -> Result<(), String> {
    // A cog's native code is linked from its archive (`archives`: each
    // native cog's, by name, in the movement's order), once `clash` found
    // no symbol two of them, or one and the runtime, define differently.
    for cog in &module.world.native_cogs {
        if !archives.iter().any(|a| a.cog == cog.name) {
            return Err(format!(
                "internal error: cog `{}` brings native code, but no archive of it was given",
                cog.name
            ));
        }
    }
    // What the program cannot run is neither compiled nor decoded at
    // start-up (`QUARZ_NO_SHAKE` keeps everything, for comparison).
    let start = std::time::Instant::now();
    let no_shake = std::env::var_os("QUARZ_NO_SHAKE").is_some();
    // (The natives' result tests, #1187, only where the program is
    // checked: built by a `quarz` that checks the facts, as the field
    // checks, `verify_field_class`.)
    let strip = !quarz_vm::verify::enabled();
    let mut owned;
    let module = if no_shake && !strip {
        module
    } else {
        owned = module.clone();
        if !no_shake {
            quarz_ir::shake::shake(&mut owned);
            // (The rows a compiled program keeps, to compare with the
            // lowered ones, `QUARZ_WITNESS_NET=rows`.)
            if std::env::var("QUARZ_WITNESS_NET").as_deref() == Ok("rows") {
                for line in owned.world.witness_row_lines("shaken") {
                    eprintln!("{line}");
                }
            }
        }
        if strip {
            owned.world.native_results = false;
            // (A cog's native keeps its test: it runs on every call, #677.)
            for m in owned.world.methods.iter_mut().filter(|m| m.ext.is_none()) {
                m.result_test = None;
                m.result_union = None;
                m.result_self = None;
            }
        }
        &owned
    };
    report("shake", start, &[]);
    let mut dir = output.as_os_str().to_owned();
    dir.push(".quarz-build");
    let dir = PathBuf::from(dir);
    // (Fresh: what an earlier build left is not linked in.)
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    // Before anything is compiled: a cog defining a symbol of the
    // runtime's with other code (`clash`).
    if !archives.is_empty() {
        let start = std::time::Instant::now();
        let runtime = clash::read(&find_runtime_lib()?)?;
        let tables = archives
            .iter()
            .map(|a| clash::read(&a.path))
            .collect::<Result<Vec<_>, _>>()?;
        let cogs: Vec<(&str, &clash::Table)> = archives
            .iter()
            .zip(&tables)
            .map(|(a, t)| (a.who.as_str(), t))
            .collect();
        clash::check(&runtime, &cogs)?;
        let shared: usize = tables.iter().map(|t| clash::shared(&runtime, t)).sum();
        report("clash", start, &[("shared", shared.to_string())]);
    }
    let built = llvm::compile(module, groups, &dir, jobs, cache)
        .and_then(|c| link(&c, &dir, output, archives));
    if std::env::var_os("QUARZ_KEEP_IR").is_some() {
        // (Each partition's directory keeps its `.ll`.)
        for sub in std::fs::read_dir(&dir).into_iter().flatten().flatten() {
            for entry in std::fs::read_dir(sub.path())
                .into_iter()
                .flatten()
                .flatten()
            {
                if entry.path().extension().is_some_and(|e| e == "o") {
                    let _ = std::fs::remove_file(entry.path());
                }
            }
        }
        eprintln!("quarz: the IR is kept in {}", dir.display());
    } else {
        let _ = std::fs::remove_dir_all(&dir);
    }
    built
}
