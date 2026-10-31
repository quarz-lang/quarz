//! Loading a program and the files it requires.
//!
//! `require "name"` refers to a standard library module (embedded in the
//! binary); `require_relative "path"` refers to a file relative to the
//! requiring file. Dependencies are loaded once, in depth-first order, so
//! that a file's top-level statements run after those of its dependencies.
//! A standard library module that a program names (`JSON`, `TCPSocket`)
//! is loaded without a `require`.
//!
//! A movement (an application and the cogs it depends on, see
//! docs/10-cogs.md) is loaded whole: every file under each cog's `src/`,
//! the cogs a cog depends on before it.

use rustc_hash::FxHashSet as HashSet;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use quarz_syntax::ast::{Expr, ExprKind, Program};
use quarz_syntax::parser::{parse_cog_file, CogMeta};
use quarz_syntax::{parse, parse_with_bases, tokenize, Diagnostic, Keyword, SourceFile, TokenKind};

use crate::declare::CogDecl;

/// Standard library modules available to `require`, by name.
pub const STD_MODULES: &[(&str, &str)] = &[
    ("json", include_str!("../../../std/json.qz")),
    ("time", include_str!("../../../std/time.qz")),
    ("socket", include_str!("../../../std/socket.qz")),
    ("http", include_str!("../../../std/http.qz")),
    ("test", include_str!("../../../std/test.qz")),
];

/// The constants each standard library module declares at the top level,
/// by module name: naming one of them loads the module. Read from the
/// lines that start a top-level declaration (`class X`, `module X`,
/// `data X`, `enum X`, `X = ...`), not by parsing the modules, which took
/// a quarter of a short program's start-up; `std_exports_parsed` checks
/// the two agree.
pub fn std_exports() -> &'static [(&'static str, Vec<String>)] {
    static EXPORTS: OnceLock<Vec<(&'static str, Vec<String>)>> = OnceLock::new();
    EXPORTS.get_or_init(|| {
        STD_MODULES
            .iter()
            .map(|(name, text)| {
                let mut names: Vec<String> = Vec::new();
                for line in text.lines() {
                    let word = |rest: &str| -> Option<String> {
                        let n: String = rest
                            .chars()
                            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                            .collect();
                        (!n.is_empty()).then_some(n)
                    };
                    let found = ["class ", "module ", "data ", "enum "]
                        .iter()
                        .find_map(|k| line.strip_prefix(k).and_then(word))
                        .or_else(|| {
                            let n = word(line)?;
                            let rest = line[n.len()..].trim_start();
                            (n.starts_with(|c: char| c.is_ascii_uppercase())
                                && rest.starts_with('=')
                                && !rest.starts_with("=="))
                            .then_some(n)
                        });
                    if let Some(n) = found {
                        if !names.contains(&n) {
                            names.push(n);
                        }
                    }
                }
                (*name, names)
            })
            .collect()
    })
}

/// `std_exports` by parsing the modules (what the line scan must find).
pub fn std_exports_parsed() -> Vec<(&'static str, Vec<String>)> {
    STD_MODULES
        .iter()
        .map(|(name, text)| {
            let mut names: Vec<String> = Vec::new();
            for e in &parse(text).program.body {
                let n = match &e.kind {
                    ExprKind::ClassDef(d) => d.name.names.first().cloned(),
                    ExprKind::ModuleDef(d) => d.name.names.first().cloned(),
                    ExprKind::DataDef(d) => Some(d.name.clone()),
                    ExprKind::EnumDef(d) => Some(d.name.clone()),
                    ExprKind::ConstAssign { name, .. } => Some(name.clone()),
                    _ => None,
                };
                if let Some(n) = n {
                    if !names.contains(&n) {
                        names.push(n);
                    }
                }
            }
            (*name, names)
        })
        .collect()
}

/// A loaded, parsed file.
pub struct LoadedUnit {
    /// Display name (the path as given, or `<std:name>`).
    pub name: String,
    pub source: SourceFile,
    pub program: Program,
    /// The cog the file belongs to (an index into the movement's cogs).
    pub cog: Option<u32>,
    /// Whether the file may hold statements.
    pub statements: bool,
    /// Whether its statements are left out (an application's main file
    /// under `quarz test`).
    pub declarations_only: bool,
    /// The units it `require_relative`s, by index (loaded before it):
    /// a script's top-level `def`s are visible in what requires it
    /// (docs/01 §1).
    pub requires: Vec<usize>,
    /// For a test file of a cog (`quarz test`), the cog it tests: it sees
    /// its own top-level `def`s, those of what it requires and that cog's,
    /// and neither that cog nor the other test files see its.
    pub tests: Option<u32>,
}

/// A cog of a movement to load: where its files are and what it calls its
/// dependencies.
#[derive(Clone, Debug)]
pub struct CogSpec {
    /// `[cog] name`, and what `cog.name` reads.
    pub name: String,
    /// What `cog.version` reads.
    pub version: String,
    /// The module its declarations live in; `None` for the application.
    pub module: Option<String>,
    /// What `cog.module_name` reads: `module`, or for the application the
    /// one its manifest names (or the CamelCase of its name).
    pub module_name: String,
    /// Its `src/` directory: every `.qz` file under it is part of the cog.
    pub src: PathBuf,
    /// The dependency keys of its manifest and the cogs they name (indices
    /// into the movement's cogs).
    pub imports: Vec<(String, u32)>,
}

/// Diagnostics attached to the file they were found in.
pub type LoadDiagnostic = (SourceFile, Diagnostic);

/// Load `path` and everything it requires. The units come back in
/// execution order (dependencies first, the given file last).
pub fn load(path: &Path) -> (Vec<LoadedUnit>, Vec<LoadDiagnostic>) {
    let mut loader = Loader {
        units: Vec::new(),
        diagnostics: Vec::new(),
        visited: HashSet::default(),
        in_progress: Vec::new(),
        next_unit: 0,
        index_of: Default::default(),
        meta: script_meta(path),
    };
    let key = canonical(path);
    loader.load_file(path, &key, None);
    loader.load_implicit_std();
    std_first(&mut loader.units);
    (loader.units, loader.diagnostics)
}

/// Load each of `paths` and what it requires, in order (a file required
/// by an earlier one is loaded once), and the standard library modules
/// `std` names: `quarz test`'s test files.
pub fn load_files(paths: &[PathBuf], std: &[&str]) -> (Vec<LoadedUnit>, Vec<LoadDiagnostic>) {
    let mut loader = Loader {
        units: Vec::new(),
        diagnostics: Vec::new(),
        visited: HashSet::default(),
        in_progress: Vec::new(),
        next_unit: 0,
        index_of: Default::default(),
        meta: None,
    };
    for name in std {
        let key = format!("<std:{name}>");
        if !loader.visited.contains(&key) {
            let text = STD_MODULES.iter().find(|(n, _)| n == name).unwrap().1;
            loader.load_text(&key, text.to_string(), Path::new("."), key.clone(), None);
        }
    }
    loader.meta = paths.first().and_then(|p| script_meta(p));
    for path in paths {
        let key = canonical(path);
        if !loader.visited.contains(&key) {
            loader.load_file(path, &key, None);
        }
    }
    loader.load_implicit_std();
    std_first(&mut loader.units);
    (loader.units, loader.diagnostics)
}

/// Load a movement: `cogs[0]` is the application, whose `src/main.qz` is
/// the one file allowed statements. The units come back dependencies
/// first, with the cog declarations the checker needs.
pub fn load_movement(cogs: &[CogSpec]) -> (Vec<LoadedUnit>, Vec<CogDecl>, Vec<LoadDiagnostic>) {
    load_cogs(cogs, None)
}

/// Load a movement to test (`quarz test`): `tests` are loaded as a
/// script's files are (`require_relative` between them) and belong to
/// `cogs[0]`, which is the application, its `src/main.qz` declarations
/// only, or a root of their own (its `src` absent) importing the library
/// under test. The standard library's `test` comes first.
pub fn load_movement_tests(
    cogs: &[CogSpec],
    tests: &[PathBuf],
) -> (Vec<LoadedUnit>, Vec<CogDecl>, Vec<LoadDiagnostic>) {
    load_cogs(cogs, Some(tests))
}

fn load_cogs(
    cogs: &[CogSpec],
    tests: Option<&[PathBuf]>,
) -> (Vec<LoadedUnit>, Vec<CogDecl>, Vec<LoadDiagnostic>) {
    let mut loader = Loader {
        units: Vec::new(),
        diagnostics: Vec::new(),
        visited: HashSet::default(),
        in_progress: Vec::new(),
        next_unit: 0,
        index_of: Default::default(),
        meta: None,
    };
    // Dependencies before the cogs that need them.
    let mut order = Vec::new();
    let mut seen = vec![false; cogs.len()];
    fn visit(i: usize, cogs: &[CogSpec], seen: &mut [bool], order: &mut Vec<usize>) {
        if seen[i] {
            return;
        }
        seen[i] = true;
        for (_, dep) in &cogs[i].imports {
            visit(*dep as usize, cogs, seen, order);
        }
        order.push(i);
    }
    if !cogs.is_empty() {
        visit(0, cogs, &mut seen, &mut order);
    }
    for i in order {
        let cog = &cogs[i];
        let meta = CogMeta {
            name: cog.name.clone(),
            version: cog.version.clone(),
            module: cog.module_name.clone(),
        };
        let mut files = Vec::new();
        if i == 0 && tests.is_some() && !cog.src.is_dir() {
            continue;
        }
        if let Err(e) = qz_files(&cog.src, &mut files) {
            loader.diagnostics.push((
                SourceFile::new(cog.src.display().to_string(), ""),
                Diagnostic::error(
                    format!("cannot read the files of cog `{}`: {e}", cog.name),
                    quarz_syntax::Span::empty(0),
                ),
            ));
            continue;
        }
        files.sort();
        // The application's main file last: its statements run last.
        let main = cog.src.join("main.qz");
        if i == 0 && tests.is_some() {
            // Tested: the main file's statements do not run.
            for file in files {
                loader.load_cog_file(&file, 0, &meta, file == main);
                if file == main {
                    loader.units.last_mut().unwrap().declarations_only = true;
                }
            }
            continue;
        }
        if i == 0 {
            files.retain(|f| *f != main);
            if !main.is_file() {
                loader.diagnostics.push((
                    SourceFile::new(main.display().to_string(), ""),
                    Diagnostic::error(
                        format!("the application `{}` has no src/main.qz to run", cog.name),
                        quarz_syntax::Span::empty(0),
                    ),
                ));
            } else {
                files.push(main.clone());
            }
        }
        for file in files {
            let statements = i == 0 && file == main;
            loader.load_cog_file(&file, i as u32, &meta, statements);
        }
    }
    if let Some(tests) = tests {
        // The test files read the root cog's `cog.name` (the
        // application's, or the tests' own root for a library).
        loader.meta = cogs.first().map(|c| CogMeta {
            name: c.name.clone(),
            version: c.version.clone(),
            module: c.module_name.clone(),
        });
        // The application, or a library under the tests' own root, which
        // has no `src/` and imports it first.
        let tested = match cogs.first() {
            Some(root) if !root.src.is_dir() => root.imports.first().map_or(0, |(_, j)| *j),
            _ => 0,
        };
        let first = loader.units.len();
        let key = "<std:test>".to_string();
        if !loader.visited.contains(&key) {
            let text = STD_MODULES.iter().find(|(n, _)| *n == "test").unwrap().1;
            loader.load_text(&key, text.to_string(), Path::new("."), key.clone(), None);
        }
        for path in tests {
            let key = canonical(path);
            if !loader.visited.contains(&key) {
                loader.load_file(path, &key, None);
            }
        }
        for u in &mut loader.units[first..] {
            if !u.name.starts_with("<std:") {
                u.cog = Some(0);
                u.tests = Some(tested);
            }
        }
    }
    loader.load_implicit_std();
    let decls = cogs
        .iter()
        .map(|c| CogDecl {
            name: c.name.clone(),
            version: c.version.clone(),
            module: c.module.clone(),
            imports: c.imports.clone(),
        })
        .collect();
    std_first(&mut loader.units);
    (loader.units, decls, loader.diagnostics)
}

/// The `.qz` files under `dir`, recursively. A symbolic link to a
/// directory is not followed (a link back up would never end); one to a
/// file counts as that file (a fetched cog holds no links at all).
fn qz_files(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let ft = entry.file_type()?;
        if ft.is_dir() {
            qz_files(&path, out)?;
        } else if (ft.is_file() || (ft.is_symlink() && path.is_file()))
            && path.extension().is_some_and(|e| e == "qz")
        {
            out.push(path);
        }
    }
    Ok(())
}

/// The standard library modules a program names without requiring them:
/// those declaring a constant that some file mentions and that no file of
/// the program declares itself (`declared`). `texts` are the files'
/// sources.
pub fn implicit_std<'a>(
    texts: impl Iterator<Item = &'a str>,
    loaded: &dyn Fn(&str) -> bool,
) -> Vec<&'static str> {
    let mut mentioned = HashSet::default();
    let mut declared = HashSet::default();
    for text in texts {
        let lexed = tokenize(text);
        let mut prev_declares = false;
        for (i, tok) in lexed.tokens.iter().enumerate() {
            if let TokenKind::Const(name) = &tok.kind {
                // `class JSON::Mine` declares `Mine` in `JSON`, which it
                // names.
                let qualified = matches!(
                    lexed.tokens.get(i + 1).map(|t| &t.kind),
                    Some(TokenKind::ColonColon)
                );
                if prev_declares && !qualified {
                    declared.insert(name.clone());
                } else {
                    mentioned.insert(name.clone());
                }
            }
            prev_declares = match &tok.kind {
                TokenKind::Keyword(Keyword::Class | Keyword::Module) => true,
                TokenKind::Ident(word) => word == "data" || word == "enum",
                _ => false,
            };
        }
    }
    std_exports()
        .iter()
        .filter(|(module, names)| {
            !loaded(module)
                && names.iter().any(|n| mentioned.contains(n))
                && !names.iter().any(|n| declared.contains(n))
        })
        .map(|(module, _)| *module)
        .collect()
}

struct Loader {
    units: Vec<LoadedUnit>,
    diagnostics: Vec<LoadDiagnostic>,
    visited: HashSet<String>,
    in_progress: Vec<String>,
    next_unit: u32,
    /// The index in `units` of each file loaded, by key.
    index_of: rustc_hash::FxHashMap<String, usize>,
    /// What `cog.name`, `cog.version` and `cog.module_name` read in the
    /// files loaded outside a cog's `src/` (a script and the files it
    /// requires, an application's test files); the defaults when `None`.
    meta: Option<CogMeta>,
}

/// Span/node-id base of the n-th loaded unit (4M ids each, `UNIT_BITS`; the
/// prelude uses the range starting at 0).
pub fn unit_base(n: u32) -> u32 {
    (n + 1) << UNIT_BITS
}

/// A unit's spans and node ids fit in `1 << UNIT_BITS` (4 MiB of source);
/// unit numbers go up to `MAX_UNITS`, the standard library's after the
/// program's.
pub const UNIT_BITS: u32 = 22;
pub const MAX_UNITS: u32 = 1000;

/// The unit number a standard library module's spans and node ids come
/// from, whatever loads it: the same in every program, so that its
/// checked state can be kept (`std_state`). Above the program's files.
pub fn std_unit(module: &str) -> u32 {
    let i = STD_MODULES
        .iter()
        .position(|(n, _)| *n == module)
        .unwrap_or(0);
    MAX_UNITS + i as u32
}

/// Put the standard library's modules first, in `STD_MODULES` order (each
/// after the modules it requires): they depend on nothing else, and so
/// they take the same file numbers in every program that loads the same
/// ones.
fn std_first(units: &mut [LoadedUnit]) {
    let rank = |u: &LoadedUnit| -> usize {
        match u
            .name
            .strip_prefix("<std:")
            .and_then(|n| n.strip_suffix('>'))
        {
            Some(m) => STD_MODULES.iter().position(|(n, _)| *n == m).unwrap_or(0),
            None => STD_MODULES.len(),
        }
    };
    // (`requires` are positions: they move with the units.)
    let mut order: Vec<usize> = (0..units.len()).collect();
    order.sort_by_key(|i| rank(&units[*i]));
    let mut new_of = vec![0; units.len()];
    for (new, old) in order.iter().enumerate() {
        new_of[*old] = new;
    }
    for u in units.iter_mut() {
        for r in u.requires.iter_mut() {
            *r = new_of[*r];
        }
    }
    units.sort_by_key(|u| rank(u));
}

pub(crate) fn canonical(path: &Path) -> String {
    std::fs::canonicalize(path)
        .map(|p| p.display().to_string())
        .unwrap_or_else(|_| path.display().to_string())
}

impl Loader {
    /// Load the standard library modules the loaded files name without a
    /// `require`, before them (they depend on nothing but each other).
    fn load_implicit_std(&mut self) {
        let wanted = implicit_std(
            self.units.iter().map(|u| u.source.text.as_str()),
            &|module| self.visited.contains(&format!("<std:{module}>")),
        );
        if wanted.is_empty() {
            return;
        }
        let rest = std::mem::take(&mut self.units);
        for module in wanted {
            let key = format!("<std:{module}>");
            if self.visited.contains(&key) {
                continue;
            }
            let text = STD_MODULES.iter().find(|(n, _)| *n == module).unwrap().1;
            self.load_text(&key, text.to_string(), Path::new("."), key.clone(), None);
        }
        // (The units loaded before move after these: their `requires`
        // positions with them.)
        let added = self.units.len();
        self.units.extend(rest.into_iter().map(|mut u| {
            for r in u.requires.iter_mut() {
                *r += added;
            }
            u
        }));
    }

    /// Load one file of cog `cog`: its `require`s of the standard library
    /// are loaded first, a `require_relative` is an error (the cog's files
    /// are all loaded).
    fn load_cog_file(&mut self, path: &Path, cog: u32, meta: &CogMeta, statements: bool) {
        let key = canonical(path);
        if !self.visited.insert(key) {
            return;
        }
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) => {
                self.diagnostics.push((
                    SourceFile::new(path.display().to_string(), ""),
                    Diagnostic::error(
                        format!("cannot read `{}`: {e}", path.display()),
                        quarz_syntax::Span::empty(0),
                    ),
                ));
                return;
            }
        };
        let base = unit_base(self.next_unit);
        self.next_unit += 1;
        let name = path.display().to_string();
        if self.next_unit > MAX_UNITS || text.len() >= 1 << UNIT_BITS {
            self.diagnostics.push((
                SourceFile::new(name, ""),
                Diagnostic::error(
                    "cannot load more than 1000 files, or a file of 4 MiB or more",
                    quarz_syntax::Span::empty(0),
                ),
            ));
            return;
        }
        let source = SourceFile::with_base(name.clone(), text, base);
        let parsed = parse_cog_file(&source.text, base, base, meta);
        let mut failed = false;
        for d in parsed.diagnostics {
            failed |= d.is_error();
            self.diagnostics.push((source.clone(), d));
        }
        if !failed {
            for expr in &parsed.program.body {
                if let ExprKind::Require { path, relative } = &expr.kind {
                    if *relative {
                        self.diagnostics.push((
                            source.clone(),
                            Diagnostic::error(
                                "`require_relative` is not needed in a cog: every file under its src/ is loaded",
                                expr.span,
                            ),
                        ));
                    } else {
                        self.load_std(path, &source, expr);
                    }
                }
            }
        }
        self.units.push(LoadedUnit {
            name,
            source,
            program: parsed.program,
            cog: Some(cog),
            statements,
            declarations_only: false,
            requires: Vec::new(),
            tests: None,
        });
    }

    fn load_file(&mut self, path: &Path, key: &str, from: Option<(&SourceFile, &Expr)>) {
        if self.visited.contains(key) {
            if self.in_progress.iter().any(|k| k == key) {
                if let Some((file, expr)) = from {
                    self.diagnostics.push((
                        file.clone(),
                        Diagnostic::error(
                            format!("circular require of `{}`", path.display()),
                            expr.span,
                        ),
                    ));
                }
            }
            return;
        }
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) => {
                let msg = format!("cannot read `{}`: {e}", path.display());
                match from {
                    Some((file, expr)) => self
                        .diagnostics
                        .push((file.clone(), Diagnostic::error(msg, expr.span))),
                    None => self.diagnostics.push((
                        SourceFile::new(path.display().to_string(), ""),
                        Diagnostic::error(msg, quarz_syntax::Span::empty(0)),
                    )),
                }
                return;
            }
        };
        let dir = path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from("."));
        self.load_text(
            &path.display().to_string(),
            text,
            &dir,
            key.to_string(),
            from.map(|(f, _)| f.name.clone()),
        );
    }

    fn load_text(
        &mut self,
        name: &str,
        text: String,
        dir: &Path,
        key: String,
        _from: Option<String>,
    ) {
        self.visited.insert(key.clone());
        self.in_progress.push(key.clone());
        // Each unit gets its own range of spans and node ids (a standard
        // library module always the same one).
        let base = match key.strip_prefix("<std:").and_then(|n| n.strip_suffix('>')) {
            Some(module) => unit_base(std_unit(module)),
            None => {
                self.next_unit += 1;
                unit_base(self.next_unit - 1)
            }
        };
        if self.next_unit > MAX_UNITS || text.len() >= 1 << UNIT_BITS {
            let what = if text.len() >= 1 << UNIT_BITS {
                "a file of 4 MiB or more"
            } else {
                "more than 1000 files"
            };
            self.diagnostics.push((
                SourceFile::new(name, ""),
                Diagnostic::error(format!("cannot load {what}"), quarz_syntax::Span::empty(0)),
            ));
            self.in_progress.pop();
            return;
        }
        let source = SourceFile::with_base(name, text, base);
        let parsed = match &self.meta {
            Some(meta) if !key.starts_with("<std:") => {
                parse_cog_file(&source.text, base, base, meta)
            }
            _ => parse_with_bases(&source.text, base, base),
        };
        let mut failed = false;
        for d in parsed.diagnostics {
            failed |= d.is_error();
            self.diagnostics.push((source.clone(), d));
        }
        let mut requires = Vec::new();
        if !failed {
            // Dependencies first.
            for expr in &parsed.program.body {
                if let ExprKind::Require { path, relative } = &expr.kind {
                    if *relative {
                        let mut target = dir.join(path);
                        if target.extension().is_none() {
                            target.set_extension("qz");
                        }
                        let tkey = canonical(&target);
                        self.load_file(&target, &tkey, Some((&source, expr)));
                        if let Some(i) = self.index_of.get(&tkey) {
                            requires.push(*i);
                        }
                    } else {
                        self.load_std(path, &source, expr);
                    }
                }
            }
        }
        self.in_progress.pop();
        self.index_of.insert(key, self.units.len());
        self.units.push(LoadedUnit {
            name: name.to_string(),
            source,
            program: parsed.program,
            cog: None,
            statements: true,
            declarations_only: false,
            requires,
            tests: None,
        });
    }

    fn load_std(&mut self, name: &str, from: &SourceFile, expr: &Expr) {
        let key = format!("<std:{name}>");
        if self.visited.contains(&key) {
            return;
        }
        let Some((_, text)) = STD_MODULES.iter().find(|(n, _)| *n == name) else {
            self.diagnostics.push((
                from.clone(),
                Diagnostic::error(format!("unknown library `{name}`"), expr.span),
            ));
            return;
        };
        self.load_text(
            &key,
            text.to_string(),
            Path::new("."),
            key.clone(),
            Some(from.name.clone()),
        );
    }
}

/// A script's `cog.name` is its file's name without the extension
/// (docs/10 §6), for the files it requires too.
fn script_meta(path: &Path) -> Option<CogMeta> {
    path.file_stem().map(|stem| {
        let name = stem.to_string_lossy().into_owned();
        CogMeta {
            module: camel_case(&name),
            name,
            version: "0.0.0".to_string(),
        }
    })
}

/// `my-tool_x` as a module name: `MyToolX` (as `quarz_cog`'s
/// `Manifest::module` makes one).
fn camel_case(name: &str) -> String {
    name.split(['-', '_'])
        .filter(|p| !p.is_empty())
        .map(|p| {
            let mut cs = p.chars();
            match cs.next() {
                Some(c) => c.to_ascii_uppercase().to_string() + cs.as_str(),
                None => String::new(),
            }
        })
        .collect()
}
