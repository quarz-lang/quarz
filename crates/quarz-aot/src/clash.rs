//! Symbols a cog's archive defines that quarz's runtime defines too
//! (#677): `quarz build` links a cog's native code after the runtime, and
//! the linker takes the first definition of a symbol, silently. A cog
//! whose archive defines a symbol of the runtime's (its own copy of a C
//! library the runtime holds, a C file defining `stack_init`) would run
//! the runtime's code in its place; two cogs, each other's. So before
//! linking, each cog's definitions are compared with the runtime's and
//! with those of the cogs before it: a symbol two of them define, in
//! members whose bytes differ, is refused, naming the cogs and the
//! symbol.
//! Members that are byte-identical (std's and compiler-builtins' from the
//! same rustc, a shared crate built alike) are one definition, allowed.
//!
//! Which definitions count: strong global ones only. Weak and common
//! symbols, and those in a COMDAT group (a C++ inline function, a
//! template), may be defined several times by design, and the linker's
//! choice among them is meant to be equivalent.
//!
//! The allocator: a cog's archive holds Rust's default allocator shim,
//! a member of its own (it defines `__rust_no_alloc_shim_is_unstable…`),
//! never pulled, since the runtime defines the allocator's symbols first:
//! a cog's allocations go to the runtime's. Such members are left out. A
//! cog whose crates set a `#[global_allocator]` defines `__rust_alloc`
//! elsewhere: refused with its own error. (This follows rustc's layout of
//! the shim, which the one rustc of quarz and its cogs fixes; the tests
//! hold both cases.)

use std::collections::{HashMap, HashSet};
use std::path::Path;

use object::read::archive::ArchiveFile;
use object::{Object, ObjectComdat, ObjectSymbol, SymbolSection};
use sha2::{Digest, Sha256};

/// An archive's strong global definitions: each symbol and the member
/// defining it (its index); the members' bytes, hashed only when a
/// symbol is compared (`check`); and whether a member sets a global
/// allocator.
pub struct Table {
    data: Vec<u8>,
    members: Vec<std::ops::Range<usize>>,
    symbols: HashMap<String, usize>,
    hashes: std::cell::RefCell<HashMap<usize, [u8; 32]>>,
    global_allocator: bool,
}

impl Table {
    /// The SHA-256 of member `i`, computed once.
    fn hash(&self, i: usize) -> [u8; 32] {
        *self
            .hashes
            .borrow_mut()
            .entry(i)
            .or_insert_with(|| Sha256::digest(&self.data[self.members[i].clone()]).into())
    }
}

/// The table of the archive at `path`: an error when it cannot be read
/// (never skipped: this is a guard).
pub fn read(path: &Path) -> Result<Table, String> {
    let data = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut members = Vec::new();
    let mut symbols = HashMap::new();
    let mut global_allocator = false;
    {
        let archive = ArchiveFile::parse(&*data)
            .map_err(|e| format!("{}: not an archive: {e}", path.display()))?;
        for member in archive.members() {
            let member = member.map_err(|e| format!("{}: {e}", path.display()))?;
            let (offset, size) = member.file_range();
            let range = offset as usize..(offset + size) as usize;
            let Some(bytes) = data.get(range.clone()) else {
                return Err(format!("{}: a member past its end", path.display()));
            };
            // (A member that is no object file, such as rustc's metadata,
            // defines nothing to link.)
            let Ok(file) = object::File::parse(bytes) else {
                continue;
            };
            let grouped: HashSet<_> = file.comdats().flat_map(|c| c.sections()).collect();
            let mut defined = Vec::new();
            let mut shim = false;
            let mut allocates = false;
            for sym in file.symbols() {
                if !sym.is_global() || sym.is_weak() || sym.is_undefined() || sym.is_common() {
                    continue;
                }
                let SymbolSection::Section(section) = sym.section() else {
                    continue;
                };
                if grouped.contains(&section) {
                    continue;
                }
                let Ok(name) = sym.name() else {
                    continue;
                };
                if name.contains("__rust_no_alloc_shim_is_unstable") {
                    shim = true;
                }
                if name.ends_with("___rust_alloc") || name == "__rust_alloc" {
                    allocates = true;
                }
                defined.push(name.to_string());
            }
            if shim {
                continue;
            }
            global_allocator |= allocates;
            let index = members.len();
            members.push(range);
            for name in defined {
                symbols.entry(name).or_insert(index);
            }
        }
    }
    Ok(Table {
        data,
        members,
        symbols,
        hashes: Default::default(),
        global_allocator,
    })
}

/// Refuse a link of `cogs` (each one's table, and how errors name it,
/// in the movement's order) beside `runtime`'s archive when a symbol two
/// of them define, or a cog and the runtime, is defined in members whose
/// bytes differ (the linker would take the first, silently), or when a
/// cog sets a global allocator. One merge: each cog's definitions against
/// the runtime's and those of the cogs before it (decided on #677: no
/// hiding, no single cargo build; identical copies are one).
pub fn check(runtime: &Table, cogs: &[(&str, &Table)]) -> Result<(), String> {
    for (who, cog) in cogs {
        if cog.global_allocator {
            return Err(format!(
                "{who} sets a global allocator (`#[global_allocator]` in its crates), which a built program cannot hold: quarz's runtime has its own"
            ));
        }
    }
    for (k, (who, cog)) in cogs.iter().enumerate() {
        let mut names: Vec<&String> = cog.symbols.keys().collect();
        names.sort();
        for name in names {
            let mine = cog.hash(cog.symbols[name]);
            if let Some(&r) = runtime.symbols.get(name) {
                if runtime.hash(r) != mine {
                    return Err(format!(
                        "{who} defines the symbol `{name}`, which quarz's runtime also defines, with other code: an executable holds one, and the cog would run the runtime's (built from other sources, or with debug info that differs)"
                    ));
                }
                continue;
            }
            for (other, table) in &cogs[..k] {
                if let Some(&o) = table.symbols.get(name) {
                    if table.hash(o) != mine {
                        return Err(format!(
                            "{other} and {who} both define the symbol `{name}`, each with its own code: an executable holds one (each brings its own copy of a library: give them one version, built from the same source)"
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}

/// How many of `cog`'s definitions the runtime also defines (all
/// identical once `check` passed).
pub fn shared(runtime: &Table, cog: &Table) -> usize {
    cog.symbols
        .keys()
        .filter(|n| runtime.symbols.contains_key(*n))
        .count()
}
