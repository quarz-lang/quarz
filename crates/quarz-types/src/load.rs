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
];

/// The constants each standard library module declares at the top level,
/// by module name: naming one of them loads the module.
pub fn std_exports() -> &'static [(&'static str, Vec<String>)] {
    static EXPORTS: OnceLock<Vec<(&'static str, Vec<String>)>> = OnceLock::new();
    EXPORTS.get_or_init(|| {
        STD_MODULES
            .iter()
            .map(|(name, text)| {
                let names = parse(text)
                    .program
                    .body
                    .iter()
                    .filter_map(|e| match &e.kind {
                        ExprKind::ClassDef(d) => d.name.names.first().cloned(),
                        ExprKind::ModuleDef(d) => d.name.names.first().cloned(),
                        ExprKind::DataDef(d) => Some(d.name.clone()),
                        ExprKind::EnumDef(d) => Some(d.name.clone()),
                        ExprKind::ConstAssign { name, .. } => Some(name.clone()),
                        _ => None,
                    })
                    .collect();
                (*name, names)
            })
            .collect()
    })
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
    };
    let key = canonical(path);
    loader.load_file(path, &key, None);
    loader.load_implicit_std();
    (loader.units, loader.diagnostics)
}

/// Load a movement: `cogs[0]` is the application, whose `src/main.qz` is
/// the one file allowed statements. The units come back dependencies
/// first, with the cog declarations the checker needs.
pub fn load_movement(cogs: &[CogSpec]) -> (Vec<LoadedUnit>, Vec<CogDecl>, Vec<LoadDiagnostic>) {
    let mut loader = Loader {
        units: Vec::new(),
        diagnostics: Vec::new(),
        visited: HashSet::default(),
        in_progress: Vec::new(),
        next_unit: 0,
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
        };
        let mut files = Vec::new();
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
    loader.load_implicit_std();
    let decls = cogs
        .iter()
        .map(|c| CogDecl {
            name: c.name.clone(),
            module: c.module.clone(),
            imports: c.imports.clone(),
        })
        .collect();
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

/// Load a program given as text (for the REPL and tests); requires resolve
/// relative to `dir`.
pub fn load_source(name: &str, text: &str, dir: &Path) -> (Vec<LoadedUnit>, Vec<LoadDiagnostic>) {
    let mut loader = Loader {
        units: Vec::new(),
        diagnostics: Vec::new(),
        visited: HashSet::default(),
        in_progress: Vec::new(),
        next_unit: 0,
    };
    loader.load_text(name, text.to_string(), dir, format!("<{name}>"), None);
    loader.load_implicit_std();
    (loader.units, loader.diagnostics)
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
}

/// Span/node-id base of the n-th loaded unit (64 MiB of ids each; the
/// prelude uses the range starting at 0).
pub fn unit_base(n: u32) -> u32 {
    (n + 1) << 26
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
        self.units.extend(rest);
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
        // Each unit gets its own range of spans and node ids.
        let base = unit_base(self.next_unit);
        self.next_unit += 1;
        let source = SourceFile::with_base(name, text, base);
        let parsed = parse_with_bases(&source.text, base, base);
        let mut failed = false;
        for d in parsed.diagnostics {
            failed |= d.is_error();
            self.diagnostics.push((source.clone(), d));
        }
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
                    } else {
                        self.load_std(path, &source, expr);
                    }
                }
            }
        }
        self.in_progress.pop();
        self.units.push(LoadedUnit {
            name: name.to_string(),
            source,
            program: parsed.program,
            cog: None,
            statements: true,
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
