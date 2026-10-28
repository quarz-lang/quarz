//! `quarz doc` (docs/13-doc-comments.md): the documentation of a cog, a
//! script or the standard library, from the comments above declarations,
//! as text, HTML or JSON; `--check` and `--missing` for CI.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::ExitCode;

use pulldown_cmark::{CodeBlockKind, Event, Options, Parser, Tag, TagEnd};
use quarz_syntax::ast::{ParamKind, Variance, Visibility};
use quarz_syntax::doc::Doc;
use quarz_syntax::{SourceFile, Span};
use quarz_types::{ClassId, ClassKind, Member, MethodId, Synth, Type, World};

pub(crate) mod examples;
mod html;

struct Opts {
    name: Option<String>,
    file: Option<PathBuf>,
    html: bool,
    out: Option<PathBuf>,
    check: bool,
    missing: bool,
    json: bool,
    private: bool,
    std: bool,
    cog: quarz_cog::Options,
}

pub fn command(args: &[String]) -> ExitCode {
    quarz_types::want_docs();
    let mut opts = Opts {
        name: None,
        file: None,
        html: false,
        out: None,
        check: false,
        missing: false,
        json: false,
        private: false,
        std: false,
        cog: quarz_cog::Options {
            verbose: true,
            ..Default::default()
        },
    };
    let mut i = 0;
    while let Some(a) = args.get(i) {
        match a.as_str() {
            "--html" => opts.html = true,
            "-o" => {
                i += 1;
                match args.get(i) {
                    Some(d) => opts.out = Some(PathBuf::from(d)),
                    None => return usage(),
                }
            }
            "--check" => opts.check = true,
            "--missing" => {
                opts.check = true;
                opts.missing = true
            }
            "--json" => opts.json = true,
            "--private" => opts.private = true,
            "--std" => opts.std = true,
            "--locked" => opts.cog.locked = true,
            "--offline" => opts.cog.offline = true,
            _ if a.starts_with('-') => return usage(),
            _ if a.ends_with(".qz") && opts.file.is_none() && opts.name.is_none() => {
                opts.file = Some(PathBuf::from(a))
            }
            _ if opts.name.is_none() => opts.name = Some(a.clone()),
            _ => return usage(),
        }
        i += 1;
    }
    let Some(loaded) = load(&opts) else {
        return ExitCode::FAILURE;
    };
    let api = Api::build(&loaded, opts.private);
    if opts.check {
        let problems = check(&loaded, &api, opts.missing);
        for p in &problems {
            eprint!("{p}");
        }
        return if problems.is_empty() {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        };
    }
    if opts.json {
        print!("{}", json(&loaded, &api));
        return ExitCode::SUCCESS;
    }
    if opts.html {
        let out = opts.out.clone().unwrap_or_else(|| PathBuf::from("doc"));
        return match html::write(&loaded, &api, &out) {
            Ok(n) => {
                eprintln!("quarz doc: {n} pages in {}", out.display());
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("quarz doc: {}: {e}", out.display());
                ExitCode::FAILURE
            }
        };
    }
    match opts.name.clone() {
        None => {
            print!("{}", listing(&loaded, &api));
            ExitCode::SUCCESS
        }
        Some(name) => {
            let mut found = lookup(&loaded, &api, &name);
            // A name of the standard library that the cog does not load.
            if found.is_none() && !opts.std {
                opts.std = true;
                opts.file = None;
                if let Some(std) = load(&opts) {
                    let std_api = Api::build(&std, opts.private);
                    found = lookup(&std, &std_api, &name);
                }
            }
            match found {
                Some(text) => {
                    print!("{text}");
                    ExitCode::SUCCESS
                }
                None => {
                    eprintln!("quarz doc: no documentation for `{name}`");
                    ExitCode::FAILURE
                }
            }
        }
    }
}

fn usage() -> ExitCode {
    eprintln!(
        "usage: quarz doc [FILE] [NAME] [--html [-o DIR]] [--check] [--missing] [--json] [--private] [--std]"
    );
    ExitCode::from(2)
}

// ----- loading -----------------------------------------------------------------------

/// A checked program and which of its files are the ones documented.
pub(crate) struct Loaded {
    pub world: World,
    pub files: Vec<SourceFile>,
    /// The files whose declarations are documented, by index.
    pub own: Vec<u32>,
    pub title: String,
    pub readme: Option<String>,
}

impl Loaded {
    /// The source file a span is in.
    pub fn file_of(&self, offset: u32) -> Option<&SourceFile> {
        self.files
            .iter()
            .filter(|f| f.base <= offset && offset <= f.base + f.text.len() as u32)
            .max_by_key(|f| f.base)
    }

    /// `file:line` of an offset; empty for none (a library's root
    /// module, which has no declaration).
    pub fn location(&self, offset: u32) -> String {
        if offset == 0 {
            return String::new();
        }
        match self.file_of(offset) {
            Some(f) => format!("{}:{}", f.name, f.line_col(offset).line),
            None => "?".to_string(),
        }
    }
}

fn load(opts: &Opts) -> Option<Loaded> {
    let prelude_file = SourceFile::new("<prelude>", quarz_types::PRELUDE_SOURCE);
    let prelude = quarz_types::parse_prelude();
    let all_std: Vec<&str> = quarz_types::STD_MODULES.iter().map(|(n, _)| *n).collect();
    let here = std::env::current_dir().unwrap_or_default();
    let cog = if opts.std || opts.file.is_some() {
        None
    } else {
        quarz_cog::find_root(&here)
    };
    let (units, decls, diagnostics, own_cog, title, readme) = if let Some(root) = &cog {
        let specs = match crate::test::test_specs(root, &opts.cog) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("quarz: {e}");
                return None;
            }
        };
        let app = root.join("src").join("main.qz").is_file();
        let (units, decls, diags) = quarz_types::load_movement_tests(&specs, &[]);
        let name = specs[if app { 0 } else { 1 }].name.clone();
        let readme = std::fs::read_to_string(root.join("README.md")).ok();
        (
            units,
            decls,
            diags,
            Some(if app { 0 } else { 1 }),
            name,
            readme,
        )
    } else if let Some(file) = &opts.file {
        let (units, diags) = quarz_types::load(file);
        let title = file.display().to_string();
        (units, Vec::new(), diags, None, title, None)
    } else {
        let (units, diags) = quarz_types::load::load_files(&[], &all_std);
        (
            units,
            Vec::new(),
            diags,
            None,
            "The Quarz standard library".to_string(),
            None,
        )
    };
    let mut failed = false;
    for (file, diag) in &diagnostics {
        eprint!("{}", diag.render(file));
        failed |= diag.is_error();
    }
    if failed {
        return None;
    }
    let sources: Vec<SourceFile> = units.iter().map(|u| u.source.clone()).collect();
    let mut own: Vec<u32> = Vec::new();
    for (i, u) in units.iter().enumerate() {
        let file = i as u32 + 1;
        let is_std = u.name.starts_with("<std:");
        let mine = match (&cog, own_cog) {
            (Some(_), Some(c)) => u.cog == Some(c),
            _ if opts.file.is_some() => !is_std,
            _ => true,
        };
        if mine {
            own.push(file);
        }
    }
    if cog.is_none() && opts.file.is_none() {
        own.push(0);
    }
    let to_check: Vec<quarz_types::Unit> = units.into_iter().map(quarz_types::Unit::from).collect();
    let (checked, diagnostics) = quarz_types::check_movement(&prelude.program, &to_check, &decls);
    for (file_index, diag) in &diagnostics {
        if !diag.is_error() {
            continue;
        }
        let f = if *file_index == 0 {
            &prelude_file
        } else {
            &sources[*file_index as usize - 1]
        };
        eprint!("{}", diag.render(f));
    }
    let checked = checked?;
    let mut files = vec![prelude_file];
    files.extend(sources);
    Some(Loaded {
        world: checked.world,
        files,
        own,
        title,
        readme,
    })
}

// ----- the API -----------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Class,
    Module,
    Data,
    Enum,
    Variant,
    Method,
    ClassMethod,
    Const,
}

impl Kind {
    pub fn word(self) -> &'static str {
        match self {
            Kind::Class => "class",
            Kind::Module => "module",
            Kind::Data => "data",
            Kind::Enum => "enum",
            Kind::Variant => "variant",
            Kind::Method => "method",
            Kind::ClassMethod => "class method",
            Kind::Const => "constant",
        }
    }
}

/// A documented member of a page: a method (its overloads apart), a
/// constant, a variant.
#[derive(Clone, Debug)]
pub(crate) struct Item {
    pub kind: Kind,
    /// `Stack#pop`, `Stack.new`, `Stack::LIMIT`.
    pub path: String,
    /// The name alone: `pop`, `new`, `LIMIT`.
    pub name: String,
    pub signature: String,
    pub doc: Option<Doc>,
    /// Where the doc comes from, when not from the item itself: `Base` for
    /// an inherited one.
    pub from: Option<String>,
    pub span: Span,
    /// The extension the method is in (`extension String`), if any.
    pub extension: Option<String>,
}

/// A class, module, data or enum, with its members.
#[derive(Clone, Debug)]
pub(crate) struct Page {
    pub id: ClassId,
    pub kind: Kind,
    pub name: String,
    pub signature: String,
    pub doc: Option<Doc>,
    pub span: Span,
    pub members: Vec<Item>,
    /// The modules it includes, and its superclass, by name.
    pub includes: Vec<String>,
}

pub(crate) struct Api {
    pub pages: Vec<Page>,
    /// The top-level constants (of the cog's root, a script, the
    /// prelude).
    pub constants: Vec<Item>,
}

fn nodoc(doc: &Option<Doc>) -> bool {
    doc.as_ref()
        .is_some_and(|d| d.text.lines().next().is_some_and(|l| l.trim() == ":nodoc:"))
}

fn ditto(doc: &Option<Doc>) -> bool {
    doc.as_ref().is_some_and(|d| d.text.trim() == ":ditto:")
}

impl Api {
    fn build(loaded: &Loaded, private: bool) -> Api {
        Api::of(&loaded.world, &loaded.own, private)
    }

    /// The API of the declarations of the files `own`.
    pub(crate) fn of(world: &World, own: &[u32], private: bool) -> Api {
        let mut pages = Vec::new();
        for class in &world.classes {
            let kind = match class.kind {
                ClassKind::Class => Kind::Class,
                ClassKind::Module => Kind::Module,
                ClassKind::Data => Kind::Data,
                ClassKind::Enum => Kind::Enum,
                ClassKind::Variant | ClassKind::Main => continue,
            };
            // A library's root module has no declaration (and no file):
            // it is documented when its cog's files are, by its README.
            let root = class.cog.is_some_and(|cog| {
                own.iter()
                    .any(|f| world.file_groups.get(f) == Some(&quarz_types::UnitGroup::Cog(cog)))
            });
            if !(own.contains(&class.file) || root) || class.name.starts_with('<') {
                continue;
            }
            let doc = if root {
                None
            } else {
                world.doc_at(class.span).cloned()
            };
            if nodoc(&doc) && !private {
                continue;
            }
            pages.push(page(world, class.id, kind, doc, private));
        }
        pages.sort_by(|a, b| a.name.cmp(&b.name));
        let mut constants = Vec::new();
        for k in &world.consts {
            if k.owner.is_none() && own.contains(&k.file) {
                let doc = world.doc_at(k.span).cloned();
                if nodoc(&doc) && !private {
                    continue;
                }
                let ty =
                    k.ty.as_ref()
                        .map(|t| format!(": {}", world.type_name(t)))
                        .unwrap_or_default();
                constants.push(Item {
                    kind: Kind::Const,
                    path: k.name.clone(),
                    name: k.name.clone(),
                    signature: format!("{}{ty}", k.name),
                    doc,
                    from: None,
                    span: k.span,
                    extension: None,
                });
            }
        }
        constants.sort_by(|a, b| a.name.cmp(&b.name));
        Api { pages, constants }
    }

    pub fn page(&self, name: &str) -> Option<&Page> {
        self.pages.iter().find(|p| p.name == name)
    }
}

fn type_params(world: &World, params: &[quarz_types::TypeParamInfo]) -> String {
    if params.is_empty() {
        return String::new();
    }
    let ps: Vec<String> = params
        .iter()
        .map(|p| {
            let mut s = match p.variance {
                Variance::Covariant => format!("out {}", p.name),
                Variance::Contravariant => format!("in {}", p.name),
                Variance::Invariant => p.name.clone(),
            };
            if !p.bounds.is_empty() {
                let b: Vec<String> = p.bounds.iter().map(|t| world.type_name(t)).collect();
                s.push_str(&format!(" <: {}", b.join(" & ")));
            }
            if let Some(l) = &p.lower {
                s.push_str(&format!(" >: {}", world.type_name(l)));
            }
            s
        })
        .collect();
    format!("[{}]", ps.join(", "))
}

/// The `i`-th type argument of a rest parameter's collection (`*xs: Int`
/// is an `Array[Int]`, `**opts: Int` a `Hash[Symbol, Int]`).
fn element(world: &World, t: &Type, i: usize) -> String {
    match t {
        Type::Class(_, args) if args.len() > i => world.type_name(&args[i]),
        _ => world.type_name(t),
    }
}

/// A class's name with its type parameters: `Stack[T]`.
fn class_type(world: &World, id: ClassId) -> String {
    let c = world.class(id);
    if c.type_params.is_empty() {
        c.name.clone()
    } else {
        let ps: Vec<&str> = c.type_params.iter().map(|p| p.name.as_str()).collect();
        format!("{}[{}]", c.name, ps.join(", "))
    }
}

/// `def pop -> [Stack[T], T]`, `def self.new(items: Array[T] = …)`.
pub(crate) fn method_signature(world: &World, mid: MethodId, as_new: Option<&str>) -> String {
    let m = world.method(mid);
    let mut params: Vec<String> = Vec::new();
    for p in &m.params {
        let default = if p.default.is_some() { " = …" } else { "" };
        let ty = world.type_name(&p.ty);
        params.push(match p.kind {
            ParamKind::Positional | ParamKind::KeywordOnly => format!("{}: {ty}{default}", p.name),
            ParamKind::Rest => format!("*{}: {}", p.name, element(world, &p.ty, 0)),
            ParamKind::KeywordRest => format!("**{}: {}", p.name, element(world, &p.ty, 1)),
            ParamKind::Block => format!("&{}: {ty}", p.name.trim_start_matches('&')),
        });
    }
    if let Some((name, ty)) = &m.block {
        let ty = world.type_name(ty);
        let ty = if m.block_optional {
            format!("({ty})?")
        } else {
            ty
        };
        // An anonymous block parameter's name is `&` itself.
        params.push(format!("&{}: {ty}", name.trim_start_matches('&')));
    }
    let params = if params.is_empty() {
        String::new()
    } else {
        format!("({})", params.join(", "))
    };
    let tps = type_params(world, &m.type_params);
    match as_new {
        Some(class) => format!("def self.new{tps}{params} -> {class}"),
        None => {
            let ret = format!(" -> {}", world.type_name(&m.ret));
            let recv = if m.singleton { "self." } else { "" };
            format!("def {recv}{}{tps}{params}{ret}", m.name)
        }
    }
}

fn fields_signature(world: &World, id: ClassId) -> String {
    let c = world.class(id);
    if c.fields.is_empty() {
        return String::new();
    }
    let fs: Vec<String> = c
        .fields
        .iter()
        .map(|f| format!("{}: {}", f.name, world.type_name(&f.ty)))
        .collect();
    format!("({})", fs.join(", "))
}

fn class_signature(world: &World, id: ClassId, kind: Kind) -> String {
    let c = world.class(id);
    let tps = type_params(world, &c.type_params);
    let mut s = String::new();
    if c.is_abstract && kind == Kind::Class {
        s.push_str("abstract ");
    }
    s.push_str(kind.word());
    s.push(' ');
    s.push_str(&c.name);
    s.push_str(&tps);
    match kind {
        Kind::Data | Kind::Variant => s.push_str(&fields_signature(world, id)),
        Kind::Class => {
            if let Some(sup) = &c.superclass {
                let name = world.type_name(sup);
                if name != "Object" {
                    s.push_str(&format!(" < {name}"));
                }
            }
        }
        _ => {}
    }
    s
}

/// The doc of a method: its own; else, for `:ditto:`, the previous
/// declaration's; for an accessor, its field's; else the doc of the
/// method it overrides, with that class's name.
fn method_doc(
    world: &World,
    mid: MethodId,
    previous: Option<&Doc>,
) -> (Option<Doc>, Option<String>) {
    let m = world.method(mid);
    // A doc of the line the owner is declared on is the owner's (a
    // one-line `data`'s fields and generated methods).
    let owner_doc = world.doc_at(world.class(m.owner).span).map(|d| d.span);
    let own = world
        .doc_at(m.span)
        .filter(|d| Some(d.span) != owner_doc)
        .cloned();
    match m.synth {
        Synth::DataWith => {
            return (
                Some(generated("A copy with the fields given replaced.")),
                None,
            )
        }
        Synth::DataToH => return (Some(generated("The fields as a `Hash`, by name.")), None),
        _ => {}
    }
    if ditto(&own) {
        return (previous.cloned(), None);
    }
    if own.is_some() {
        return (own, None);
    }
    if let Synth::FieldGet(f) | Synth::FieldSet(f) = &m.synth {
        let owner = world.class(m.owner);
        if let Some(field) = owner.fields.iter().find(|x| &x.name == f) {
            if let Some(d) = world
                .doc_at(field.span)
                .filter(|d| Some(d.span) != owner_doc)
            {
                return (Some(d.clone()), None);
            }
        }
    }
    if let Some(orig) = m.alias_of {
        if let Some(d) = world.doc_at(world.method(orig).span) {
            return (Some(d.clone()), None);
        }
    }
    for a in world.ancestor_ids(m.owner).into_iter().skip(1) {
        let class = world.class(a);
        let table = if m.singleton {
            &class.singleton_methods
        } else {
            &class.methods
        };
        if let Some(ids) = table.get(&m.name) {
            for id in ids {
                if let Some(d) = world.doc_at(world.method(*id).span) {
                    if !ditto(&Some(d.clone())) {
                        return (Some(d.clone()), Some(class.name.clone()));
                    }
                }
            }
        }
    }
    (None, None)
}

/// A doc the generator writes (for a `data`'s generated methods).
fn generated(text: &str) -> Doc {
    Doc {
        text: text.to_string(),
        span: Span::empty(0),
        line: Span::empty(0),
    }
}

fn page(world: &World, id: ClassId, kind: Kind, doc: Option<Doc>, private: bool) -> Page {
    let c = world.class(id);
    let kernel = c.name == "Kernel";
    let mut methods: Vec<MethodId> = c
        .methods
        .values()
        .chain(c.singleton_methods.values())
        .flatten()
        .copied()
        .filter(|m| world.method(*m).owner == id)
        .collect();
    // An extension's methods, on its module's page.
    let mut ext_methods: Vec<(MethodId, String)> = Vec::new();
    for ext in &world.extensions {
        if ext.module == Some(id) {
            let target = world.class(ext.target).name.clone();
            for ids in ext.methods.values() {
                for m in ids {
                    ext_methods.push((*m, format!("extension {target}")));
                }
            }
        }
    }
    methods.retain(|m| world.method(*m).extension.is_none());
    // An always-active extension's (the prelude's) are the class's own,
    // to every program.
    for ext in &world.extensions {
        if ext.always_active && ext.target == id {
            methods.extend(ext.methods.values().flatten().copied());
        }
    }
    methods.sort_by_key(|m| world.method(*m).span.start);
    ext_methods.sort_by_key(|(m, _)| world.method(*m).span.start);
    let mut members = Vec::new();
    let mut previous: Option<Doc> = None;
    let all = methods
        .into_iter()
        .map(|m| (m, None))
        .chain(ext_methods.into_iter().map(|(m, e)| (m, Some(e))));
    for (mid, extension) in all {
        let m = world.method(mid);
        let public = m.visibility == Visibility::Public || kernel;
        if !public && !private {
            continue;
        }
        if m.name.starts_with("__") && !private {
            continue;
        }
        let (mdoc, from) = method_doc(world, mid, previous.as_ref());
        if mdoc.is_some() && from.is_none() {
            previous = mdoc.clone();
        }
        if nodoc(&mdoc) && !private {
            continue;
        }
        let is_new = m.name == "initialize" && !m.singleton;
        if m.name == "initialize" && !is_new {
            continue;
        }
        let (kind, name, signature) = if is_new {
            (
                Kind::ClassMethod,
                "new".to_string(),
                method_signature(world, mid, Some(&class_type(world, id))),
            )
        } else if m.singleton {
            (
                Kind::ClassMethod,
                m.name.clone(),
                method_signature(world, mid, None),
            )
        } else {
            (
                Kind::Method,
                m.name.clone(),
                method_signature(world, mid, None),
            )
        };
        if matches!(m.synth, Synth::DataInit) {
            continue;
        }
        let sep = if kind == Kind::Method { "#" } else { "." };
        // An extension's method is named after the class it extends.
        let on = match &extension {
            Some(e) => e.trim_start_matches("extension ").to_string(),
            None => c.name.clone(),
        };
        members.push(Item {
            kind,
            path: format!("{on}{sep}{name}"),
            name,
            signature,
            doc: mdoc,
            from,
            span: m.span,
            extension,
        });
    }
    // Variants of an enum.
    if kind == Kind::Enum {
        for v in &c.variants {
            let vc = world.class(*v);
            let vdoc = world
                .doc_at(vc.span)
                .filter(|d| Some(d.span) != doc.as_ref().map(|x| x.span))
                .cloned();
            if nodoc(&vdoc) && !private {
                continue;
            }
            let short = vc.name.rsplit("::").next().unwrap_or(&vc.name).to_string();
            members.push(Item {
                kind: Kind::Variant,
                path: vc.name.clone(),
                name: short,
                signature: class_signature(world, *v, Kind::Variant),
                doc: vdoc,
                from: None,
                span: vc.span,
                extension: None,
            });
        }
    }
    // Constants.
    for k in &world.consts {
        if k.owner == Some(id) {
            let kdoc = world.doc_at(k.span).cloned();
            if nodoc(&kdoc) && !private {
                continue;
            }
            let ty =
                k.ty.as_ref()
                    .map(|t| format!(": {}", world.type_name(t)))
                    .unwrap_or_default();
            members.push(Item {
                kind: Kind::Const,
                path: format!("{}::{}", c.name, k.name),
                name: k.name.clone(),
                signature: format!("{}{ty}", k.name),
                doc: kdoc,
                from: None,
                span: k.span,
                extension: None,
            });
        }
    }
    let mut includes: Vec<String> = c.includes.iter().map(|t| world.type_name(t)).collect();
    includes.retain(|n| n != "Shareable" && n != "Unshareable");
    Page {
        id,
        kind,
        name: c.name.clone(),
        signature: class_signature(world, id, kind),
        doc,
        span: c.span,
        members,
        includes,
    }
}

// ----- names and links ---------------------------------------------------------------

/// What a name in a code span or on the command line refers to.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Target {
    /// A page, and a member of it (`Stack#pop`: the page `Stack`, the
    /// member `Stack#pop`).
    Page(String, Option<String>),
    /// Something that exists but has no page (a private method, a
    /// constant of the program, a class of another cog).
    Elsewhere { private: bool },
}

/// Whether `s` has the shape of a declaration's name: `Foo`, `Foo::Bar`,
/// `Foo#bar`, `Foo.bar`, `#bar`, `.bar` (not a bare `bar`).
pub(crate) fn name_shaped(s: &str) -> bool {
    let (class, method) = split_name(s);
    let class_ok = class.is_empty()
        || class.split("::").all(|seg| {
            let mut cs = seg.chars();
            cs.next().is_some_and(|c| c.is_ascii_uppercase())
                && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
        });
    let method_ok = match method {
        None => !class.is_empty(),
        Some((_, m)) => method_name(m),
    };
    class_ok && method_ok && !(class.is_empty() && method.is_none())
}

fn method_name(m: &str) -> bool {
    let mut cs = m.chars();
    match cs.next() {
        Some(c) if c.is_ascii_lowercase() || c == '_' => {
            let rest: String = cs.collect();
            let body = rest.trim_end_matches(['?', '!', '=']);
            body.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                && rest.len() - body.len() <= 1
        }
        Some(_) => m.chars().all(|c| "[]+-*/%<>=!~^&|".contains(c)),
        None => false,
    }
}

/// `Foo::Bar#baz` → (`Foo::Bar`, Some(('#', `baz`))).
fn split_name(s: &str) -> (&str, Option<(char, &str)>) {
    if let Some(i) = s.find('#') {
        return (&s[..i], Some(('#', &s[i + 1..])));
    }
    // A `.` after the class path (not inside `::`).
    if let Some(i) = s.rfind('.') {
        if !s[i + 1..].contains("::") {
            return (&s[..i], Some(('.', &s[i + 1..])));
        }
    }
    (s, None)
}

/// The class a path names, looked up from `scope` outward.
fn resolve_class(world: &World, scope: Option<ClassId>, path: &str) -> Option<Member> {
    let mut segs = path.trim_start_matches("::").split("::");
    let first = segs.next()?;
    let mut cur = world
        .resolve_member(scope, first)
        .or_else(|| world.top.get(first).copied())?;
    for seg in segs {
        let Member::Class(c) = cur else { return None };
        cur = world.member_in(Some(c), seg)?;
    }
    Some(cur)
}

/// The method `name` of `class` or its ancestors, instance or singleton.
fn find_method(world: &World, class: ClassId, name: &str, singleton: bool) -> Option<MethodId> {
    let name = if singleton && name == "new" {
        // `.new` is `initialize`.
        return find_method(world, class, "initialize", false)
            .or_else(|| find_singleton(world, class, "new"));
    } else {
        name
    };
    if singleton {
        return find_singleton(world, class, name);
    }
    for a in world.ancestor_ids(class) {
        if let Some(ids) = world.class(a).methods.get(name) {
            return ids.first().copied();
        }
        // The prelude's extensions are always active.
        for ext in &world.extensions {
            if ext.always_active && ext.target == a {
                if let Some(ids) = ext.methods.get(name) {
                    return ids.first().copied();
                }
            }
        }
    }
    None
}

fn find_singleton(world: &World, class: ClassId, name: &str) -> Option<MethodId> {
    for a in world.superclass_chain(class) {
        if let Some(ids) = world.class(a).singleton_methods.get(name) {
            return ids.first().copied();
        }
    }
    None
}

impl Api {
    /// Resolve a code span (or a command-line name) in the scope of
    /// `scope` (the class being documented, if any).
    pub(crate) fn resolve(
        &self,
        world: &World,
        scope: Option<ClassId>,
        name: &str,
    ) -> Option<Target> {
        let (class_path, method) = split_name(name);
        let class = if class_path.is_empty() {
            scope?
        } else {
            match resolve_class(world, scope, class_path)? {
                Member::Class(c) => c,
                Member::Const(_) | Member::Alias(_) => {
                    return method
                        .is_none()
                        .then_some(Target::Elsewhere { private: false })
                }
            }
        };
        let page_of = |id: ClassId| {
            let n = &world.class(id).name;
            self.page(n).map(|p| p.name.clone())
        };
        match method {
            None => Some(match page_of(class) {
                Some(p) => Target::Page(p, None),
                None => Target::Elsewhere { private: false },
            }),
            Some((sep, m)) => {
                let mid = find_method(world, class, m, sep == '.')?;
                let info = world.method(mid);
                let owner = if info.name == "initialize" {
                    class
                } else {
                    info.owner
                };
                let kernel = world.class(info.owner).name == "Kernel";
                let private = info.visibility != Visibility::Public && !kernel;
                let member_sep = if sep == '.' || info.name == "initialize" {
                    "."
                } else {
                    "#"
                };
                let shown = if info.name == "initialize" {
                    "new"
                } else {
                    &info.name
                };
                match page_of(owner) {
                    Some(p) if !private => {
                        let member = format!("{p}{member_sep}{shown}");
                        Some(Target::Page(p, Some(member)))
                    }
                    _ => Some(Target::Elsewhere { private }),
                }
            }
        }
    }

    /// A bare `bar` in a span: a public method of `scope`.
    pub(crate) fn resolve_bare(&self, world: &World, scope: ClassId, name: &str) -> Option<Target> {
        if !method_name(name) {
            return None;
        }
        let mid = find_method(world, scope, name, false)?;
        if world.method(mid).visibility != Visibility::Public {
            return None;
        }
        self.resolve(world, Some(scope), &format!("#{name}"))
    }
}

// ----- Markdown as text --------------------------------------------------------------

/// The doc's Markdown as plain text, indented by `indent`.
pub(crate) fn markdown_text(md: &str, indent: &str) -> String {
    let mut out = String::new();
    let mut line = String::new();
    let mut list_depth = 0usize;
    let mut in_code = false;
    // In a list, a bullet's later lines hang under its text.
    let flush = |out: &mut String, line: &mut String, extra: usize, hang: bool| {
        for (i, l) in line.split('\n').enumerate() {
            if l.is_empty() {
                out.push('\n');
            } else {
                out.push_str(indent);
                out.push_str(&"  ".repeat(extra));
                if hang && i > 0 {
                    out.push_str("  ");
                }
                out.push_str(l);
                out.push('\n');
            }
        }
        line.clear();
    };
    for event in Parser::new_ext(md, Options::ENABLE_TABLES) {
        match event {
            Event::Start(Tag::Heading { .. }) => {}
            Event::End(TagEnd::Heading(_)) => {
                flush(&mut out, &mut line, list_depth, false);
                out.push('\n');
            }
            Event::Start(Tag::Paragraph) => {}
            Event::End(TagEnd::Paragraph) => {
                flush(
                    &mut out,
                    &mut line,
                    list_depth.saturating_sub(1),
                    list_depth > 0,
                );
                if list_depth == 0 {
                    out.push('\n');
                }
            }
            Event::Start(Tag::CodeBlock(_)) => in_code = true,
            Event::End(TagEnd::CodeBlock) => {
                in_code = false;
                out.push('\n');
            }
            Event::Start(Tag::List(_)) => list_depth += 1,
            Event::End(TagEnd::List(_)) => {
                list_depth -= 1;
                if list_depth == 0 {
                    out.push('\n');
                }
            }
            Event::Start(Tag::Item) => line.push_str("- "),
            Event::End(TagEnd::Item) => {
                if !line.is_empty() {
                    flush(&mut out, &mut line, list_depth.saturating_sub(1), true);
                }
            }
            Event::Text(t) if in_code => {
                for l in t.lines() {
                    out.push_str(indent);
                    out.push_str("    ");
                    out.push_str(l);
                    out.push('\n');
                }
            }
            Event::Text(t) | Event::Code(t) | Event::Html(t) | Event::InlineHtml(t) => {
                line.push_str(&t)
            }
            Event::SoftBreak | Event::HardBreak => line.push('\n'),
            Event::End(TagEnd::Link) => {}
            Event::Rule => {
                flush(&mut out, &mut line, 0, false);
                out.push_str(indent);
                out.push_str("----\n\n");
            }
            _ => {}
        }
    }
    if !line.is_empty() {
        flush(&mut out, &mut line, 0, false);
    }
    while out.ends_with("\n\n") {
        out.pop();
    }
    out
}

// ----- the commands ------------------------------------------------------------------

fn listing(loaded: &Loaded, api: &Api) -> String {
    let mut out = String::new();
    for k in &api.constants {
        let summary = k
            .doc
            .as_ref()
            .map(|d| first_line(d.summary()))
            .unwrap_or_default();
        out.push_str(&format!(
            "{}  {}
",
            k.signature, summary
        ));
    }
    for p in &api.pages {
        let summary = p
            .doc
            .as_ref()
            .map(|d| first_line(d.summary()))
            .unwrap_or_default();
        out.push_str(&format!("{}  {}\n", p.signature, summary));
        for m in &p.members {
            let summary = m
                .doc
                .as_ref()
                .map(|d| first_line(d.summary()))
                .unwrap_or_default();
            out.push_str(&format!("  {}  {}\n", m.path, summary));
        }
    }
    let _ = loaded;
    out
}

/// A summary on one line, as plain text.
pub(crate) fn first_line(s: &str) -> String {
    let text = markdown_text(s, "");
    let joined: Vec<&str> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    joined.join(" ")
}

fn lookup(loaded: &Loaded, api: &Api, name: &str) -> Option<String> {
    let world = &loaded.world;
    // An extension's method, by the name of the class it extends.
    let ext: Vec<&Item> = api
        .pages
        .iter()
        .flat_map(|p| &p.members)
        .filter(|i| i.extension.is_some() && i.path == name)
        .collect();
    if !ext.is_empty() {
        let mut out = String::new();
        for item in ext {
            out.push_str(&format!(
                "{}  {}\n  ({})\n\n",
                item.path,
                item.signature,
                item.extension.as_deref().unwrap_or_default()
            ));
            if let Some(d) = &item.doc {
                out.push_str(&markdown_text(&d.text, "  "));
                out.push_str("\n\n");
            }
        }
        while out.ends_with("\n\n") {
            out.pop();
        }
        return Some(out);
    }
    // A bare function: a method of Kernel or Object.
    let target = if !name.contains(['#', '.', ':'])
        && name.chars().next().is_some_and(|c| !c.is_ascii_uppercase())
    {
        let kernel = world.top_class("Kernel");
        let object = world.top_class("Object");
        [kernel, object]
            .into_iter()
            .flatten()
            .find_map(|c| find_method(world, c, name, false).map(|_| c))
            .map(|c| format!("{}#{name}", world.class(c).name))
    } else {
        Some(name.to_string())
    }?;
    let (class_path, method) = split_name(&target);
    let class = match resolve_class(world, None, class_path)? {
        Member::Class(c) => c,
        Member::Const(k) if method.is_none() => {
            let k = &world.consts[k as usize];
            let ty =
                k.ty.as_ref()
                    .map(|t| format!(": {}", world.type_name(t)))
                    .unwrap_or_default();
            let mut out = format!("{class_path}{ty}\n");
            if let Some(d) = world.doc_at(k.span) {
                out.push('\n');
                out.push_str(&markdown_text(&d.text, "  "));
            }
            return Some(out);
        }
        _ => return None,
    };
    let mut out = String::new();
    match method {
        None => {
            let kind = match world.class(class).kind {
                ClassKind::Module => Kind::Module,
                ClassKind::Data => Kind::Data,
                ClassKind::Enum => Kind::Enum,
                ClassKind::Variant => Kind::Variant,
                _ => Kind::Class,
            };
            let p = match api.page(&world.class(class).name) {
                Some(p) => p.clone(),
                None => page(
                    world,
                    class,
                    kind,
                    world.doc_at(world.class(class).span).cloned(),
                    false,
                ),
            };
            out.push_str(&p.signature);
            out.push('\n');
            if !p.includes.is_empty() {
                out.push_str(&format!("  include {}\n", p.includes.join(", ")));
            }
            out.push('\n');
            if let Some(d) = &p.doc {
                out.push_str(&markdown_text(&d.text, "  "));
                out.push_str("\n\n");
            }
            for m in &p.members {
                let summary = m
                    .doc
                    .as_ref()
                    .map(|d| first_line(d.summary()))
                    .unwrap_or_default();
                out.push_str(&format!("  {}\n", m.signature));
                if !summary.is_empty() {
                    out.push_str(&format!("      {summary}\n"));
                }
            }
        }
        Some((sep, m)) => {
            // The method's items on its owner's page, which carry
            // `:ditto:`, inherited docs and the accessors'.
            let mid = find_method(world, class, m, sep == '.')?;
            let owner = if world.method(mid).name == "initialize" {
                class
            } else {
                world.method(mid).owner
            };
            let kind = match world.class(owner).kind {
                ClassKind::Module => Kind::Module,
                ClassKind::Data => Kind::Data,
                ClassKind::Enum => Kind::Enum,
                ClassKind::Variant => Kind::Variant,
                _ => Kind::Class,
            };
            let owner_page = page(world, owner, kind, None, true);
            let want = if sep == '.' {
                Kind::ClassMethod
            } else {
                Kind::Method
            };
            for item in owner_page
                .members
                .iter()
                .filter(|i| i.name == m && i.kind == want && i.extension.is_none())
            {
                out.push_str(&format!("{}  {}\n\n", item.path, item.signature));
                if let Some(d) = &item.doc {
                    out.push_str(&markdown_text(&d.text, "  "));
                    out.push('\n');
                    if let Some(f) = &item.from {
                        out.push_str(&format!("  (from {f})\n"));
                    }
                    out.push('\n');
                }
            }
            if out.is_empty() {
                return None;
            }
        }
    }
    while out.ends_with("\n\n") {
        out.pop();
    }
    Some(out)
}

/// The code spans and fences of a doc, for `--check` and HTML.
pub(crate) fn code_spans(md: &str) -> Vec<String> {
    Parser::new(md)
        .filter_map(|e| match e {
            Event::Code(c) => Some(c.to_string()),
            _ => None,
        })
        .collect()
}

/// The fenced code blocks of a doc: info string and code, with the
/// offset of the code in the text.
pub(crate) fn fences(md: &str) -> Vec<(String, String, usize)> {
    let mut out = Vec::new();
    let mut current: Option<(String, String, usize)> = None;
    for (event, range) in Parser::new(md).into_offset_iter() {
        match event {
            Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(info))) => {
                current = Some((info.to_string(), String::new(), range.start))
            }
            Event::Text(t) => {
                if let Some(c) = &mut current {
                    c.1.push_str(&t);
                }
            }
            Event::End(TagEnd::CodeBlock) => {
                if let Some(c) = current.take() {
                    out.push(c);
                }
            }
            _ => {}
        }
    }
    out
}

/// Whether a fence holds Quarz to run (`quarz`, or no language) or to
/// compile only (`quarz no_run`).
pub(crate) fn fence_kind(info: &str) -> Option<bool> {
    let mut words = info.split_whitespace();
    match words.next() {
        None => Some(true),
        Some("quarz") => Some(!words.any(|w| w == "no_run")),
        Some(_) => None,
    }
}

/// Every documented declaration of the API with its doc, in order, and
/// the class whose scope its links resolve in.
fn documented<'a>(world: &World, api: &'a Api) -> Vec<(ClassId, String, Option<&'a Doc>, Span)> {
    let mut out = Vec::new();
    if let Some(object) = world.top_class("Object") {
        for k in &api.constants {
            out.push((object, k.path.clone(), k.doc.as_ref(), k.span));
        }
    }
    for p in &api.pages {
        out.push((p.id, p.name.clone(), p.doc.as_ref(), p.span));
        for m in &p.members {
            if m.from.is_none() {
                out.push((p.id, m.path.clone(), m.doc.as_ref(), m.span));
            }
        }
    }
    out
}

fn check(loaded: &Loaded, api: &Api, missing: bool) -> Vec<String> {
    let world = &loaded.world;
    let mut problems = Vec::new();
    let mut seen: Vec<u32> = Vec::new();
    for (scope, path, doc, span) in documented(world, api) {
        let Some(doc) = doc else {
            // A library's root module is documented by its README.
            if missing && span != Span::empty(0) {
                problems.push(format!(
                    "{}: warning: `{path}` has no documentation comment\n",
                    loaded.location(span.start)
                ));
            }
            continue;
        };
        // An overload's or ditto's doc is checked once.
        if seen.contains(&doc.span.start) {
            continue;
        }
        seen.push(doc.span.start);
        let at = loaded.location(doc.span.start);
        let type_params: Vec<String> = world
            .class(scope)
            .type_params
            .iter()
            .map(|p| p.name.clone())
            .collect();
        for span in code_spans(&doc.text) {
            if !name_shaped(&span) || type_params.contains(&span) || is_type_expr(&span) {
                continue;
            }
            match api.resolve(world, Some(scope), &span) {
                None => problems.push(format!("{at}: warning: `{span}` (in the doc of `{path}`) names nothing\n")),
                Some(Target::Elsewhere { private: true }) => problems.push(format!(
                    "{at}: warning: `{span}` (in the doc of `{path}`) is private, so it is not documented\n"
                )),
                _ => {}
            }
        }
        let fence_lines = doc
            .text
            .lines()
            .filter(|l| l.trim_start().starts_with("```"))
            .count();
        if fence_lines % 2 == 1 {
            problems.push(format!(
                "{at}: warning: a code fence in the doc of `{path}` is not closed\n"
            ));
        }
        for (info, code, _) in fences(&doc.text) {
            if fence_kind(&info).is_none() {
                continue;
            }
            for line in code.lines() {
                let t = line.trim_start();
                if (t.starts_with("puts ") || t.starts_with("print ")) && t.contains("# =>") {
                    problems.push(format!(
                        "{at}: warning: `# =>` after `puts` or `print` (in an example of `{path}`) compares their value, nil\n"
                    ));
                }
            }
        }
    }
    problems
}

/// A one-letter type parameter (`T`, `K`) or a generic type
/// (`Array[Int]`) is a type, not a name to link.
fn is_type_expr(s: &str) -> bool {
    (s.len() == 1 && s.chars().all(|c| c.is_ascii_uppercase())) || s.contains('[')
}

pub(crate) fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json(loaded: &Loaded, api: &Api) -> String {
    let item = |kind: Kind,
                path: &str,
                sig: &str,
                doc: Option<&Doc>,
                span: Span,
                from: Option<&String>| {
        let mut fields: BTreeMap<&str, String> = BTreeMap::new();
        fields.insert("kind", json_string(kind.word()));
        fields.insert("name", json_string(path));
        fields.insert("signature", json_string(sig));
        if let Some(d) = doc {
            fields.insert("summary", json_string(d.summary()));
            fields.insert("doc", json_string(&d.text));
        }
        if let Some(f) = from {
            fields.insert("from", json_string(f));
        }
        let at = loaded.location(span.start);
        if !at.is_empty() {
            fields.insert("location", json_string(&at));
        }
        let body: Vec<String> = fields
            .into_iter()
            .map(|(k, v)| format!("\"{k}\": {v}"))
            .collect();
        format!("{{{}}}", body.join(", "))
    };
    let mut entries: Vec<String> = Vec::new();
    for k in &api.constants {
        entries.push(format!(
            "  {}",
            item(k.kind, &k.path, &k.signature, k.doc.as_ref(), k.span, None)
        ));
    }
    for p in &api.pages {
        let members: Vec<String> = p
            .members
            .iter()
            .map(|m| {
                format!(
                    "    {}",
                    item(
                        m.kind,
                        &m.path,
                        &m.signature,
                        m.doc.as_ref(),
                        m.span,
                        m.from.as_ref()
                    )
                )
            })
            .collect();
        let head = item(p.kind, &p.name, &p.signature, p.doc.as_ref(), p.span, None);
        let head = head.trim_end_matches('}').to_string();
        entries.push(format!(
            "  {head}, \"members\": [\n{}\n  ]}}",
            members.join(",\n")
        ));
    }
    format!("[\n{}\n]\n", entries.join(",\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names() {
        assert!(name_shaped("Array#push"));
        assert!(name_shaped("Stack::Empty"));
        assert!(name_shaped("#pop"));
        assert!(name_shaped(".new"));
        assert!(name_shaped("Array.new"));
        assert!(name_shaped("Array#[]"));
        assert!(name_shaped("Int#+"));
        assert!(!name_shaped("pop"));
        assert!(!name_shaped("x + 1"));
        assert!(!name_shaped("a.b"));
        assert!(!name_shaped("foo#bar"));
    }

    #[test]
    fn markdown_as_text() {
        let text = markdown_text(
            "The `x`.\n\n## Raises\n\nOne\ntwo.\n\n```\na = 1\n```\n\n- a\n- b\n",
            "  ",
        );
        assert_eq!(
            text,
            "  The x.\n\n  Raises\n\n  One\n  two.\n\n      a = 1\n\n  - a\n  - b\n"
        );
    }
}
