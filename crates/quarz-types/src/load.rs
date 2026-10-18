//! Loading a program and the files it requires.
//!
//! `require "name"` refers to a standard library module (embedded in the
//! binary); `require_relative "path"` refers to a file relative to the
//! requiring file. Dependencies are loaded once, in depth-first order, so
//! that a file's top-level statements run after those of its dependencies.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use quarz_syntax::ast::{Expr, ExprKind, Program};
use quarz_syntax::{parse_with_bases, Diagnostic, SourceFile};

/// Standard library modules available to `require`, by name.
pub const STD_MODULES: &[(&str, &str)] = &[
    ("json", include_str!("../../../std/json.qz")),
    ("time", include_str!("../../../std/time.qz")),
];

/// A loaded, parsed file.
pub struct LoadedUnit {
    /// Display name (the path as given, or `<std:name>`).
    pub name: String,
    pub source: SourceFile,
    pub program: Program,
}

/// Diagnostics attached to the file they were found in.
pub type LoadDiagnostic = (SourceFile, Diagnostic);

/// Load `path` and everything it requires. The units come back in
/// execution order (dependencies first, the given file last).
pub fn load(path: &Path) -> (Vec<LoadedUnit>, Vec<LoadDiagnostic>) {
    let mut loader = Loader {
        units: Vec::new(),
        diagnostics: Vec::new(),
        visited: HashSet::new(),
        in_progress: Vec::new(),
        next_unit: 0,
    };
    let key = canonical(path);
    loader.load_file(path, &key, None);
    (loader.units, loader.diagnostics)
}

/// Load a program given as text (for the REPL and tests); requires resolve
/// relative to `dir`.
pub fn load_source(name: &str, text: &str, dir: &Path) -> (Vec<LoadedUnit>, Vec<LoadDiagnostic>) {
    let mut loader = Loader {
        units: Vec::new(),
        diagnostics: Vec::new(),
        visited: HashSet::new(),
        in_progress: Vec::new(),
        next_unit: 0,
    };
    loader.load_text(name, text.to_string(), dir, format!("<{name}>"), None);
    (loader.units, loader.diagnostics)
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
