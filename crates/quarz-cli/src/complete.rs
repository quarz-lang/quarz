//! Completion for the REPL: the names that may follow what has been
//! typed, from what the session knows (its local variables and their
//! types, the classes and their methods, the constants), taken as a
//! table after each input so that completing needs no access to the
//! session.

use std::collections::{BTreeSet, HashMap};

use quarz_syntax::token::Keyword;
use quarz_types::{ClassId, ClassKind, Type, World};

/// Words that start declarations or calls without being keywords.
const DECLARATION_WORDS: &[&str] = &[
    "abstract",
    "attr_reader",
    "data",
    "enum",
    "extension",
    "include",
    "extend",
    "require",
    "require_relative",
    "using",
    "var",
    "variant",
];

pub struct Completions {
    /// The local variables, with the classes their values may be of.
    locals: Vec<(String, Vec<ClassId>)>,
    /// The methods callable at the top level without a receiver.
    functions: Vec<String>,
    /// The top-level constants: classes, modules and constants.
    constants: Vec<String>,
    /// Classes and modules by qualified name (`Foo::Bar`).
    classes: HashMap<String, ClassId>,
    /// By class: the methods its instances answer, the methods the class
    /// itself answers, and the constants it holds.
    instance_methods: Vec<Vec<String>>,
    singleton_methods: Vec<Vec<String>>,
    members: Vec<Vec<String>>,
    /// Every public method name (for a receiver of unknown type).
    all_methods: Vec<String>,
    literals: Literals,
}

/// The classes of literal receivers (`"a".`, `[1].`, `1.`).
struct Literals {
    string: ClassId,
    symbol: ClassId,
    int: ClassId,
    float: ClassId,
    array: ClassId,
    hash: ClassId,
}

/// A name a completion can offer (not an operator such as `+` or `[]`).
fn is_name(s: &str) -> bool {
    let mut chars = s.chars();
    let first_ok = chars.next().is_some_and(|c| c == '_' || c.is_alphabetic());
    first_ok
        && s.trim_end_matches(['?', '!', '='])
            .chars()
            .all(|c| c == '_' || c.is_alphanumeric())
}

fn sorted(names: impl IntoIterator<Item = String>) -> Vec<String> {
    names
        .into_iter()
        .filter(|n| is_name(n))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

/// The classes a value of type `t` may be of.
fn classes_of(t: &Type, out: &mut Vec<ClassId>) {
    match t {
        Type::Class(id, _) => out.push(*id),
        Type::Union(ms) => ms.iter().for_each(|m| classes_of(m, out)),
        _ => {}
    }
}

impl Completions {
    /// The table for a session: its world, the class of its top level,
    /// and its local variables with their types.
    pub fn new(world: &World, main: ClassId, locals: &[(String, Type)]) -> Completions {
        use quarz_syntax::ast::Visibility;
        let n = world.classes.len();
        let mut instance_methods = Vec::with_capacity(n);
        let mut singleton_methods = Vec::with_capacity(n);
        let mut members = Vec::with_capacity(n);
        let mut all = BTreeSet::new();
        let public = |ids: &[u32]| {
            ids.iter()
                .any(|m| world.method(*m).visibility == Visibility::Public)
        };
        for id in 0..n as ClassId {
            let ancestors = world.ancestor_ids(id);
            let names: Vec<String> = ancestors
                .iter()
                .flat_map(|a| world.class(*a).methods.iter())
                .filter(|(_, ids)| public(ids))
                .map(|(name, _)| name.clone())
                .collect();
            all.extend(names.iter().cloned());
            instance_methods.push(sorted(names));
            let class = world.class(id);
            let mut singles: Vec<String> = ancestors
                .iter()
                .flat_map(|a| {
                    let c = world.class(*a);
                    let extended = c.extends.iter().filter_map(|t| match t {
                        Type::Class(m, _) => Some(*m),
                        _ => None,
                    });
                    std::iter::once(*a)
                        .map(|a| {
                            world
                                .class(a)
                                .singleton_methods
                                .keys()
                                .cloned()
                                .collect::<Vec<_>>()
                        })
                        .chain(extended.map(|m| world.class(m).methods.keys().cloned().collect()))
                        .flatten()
                        .collect::<Vec<_>>()
                })
                .collect();
            if matches!(class.kind, ClassKind::Class | ClassKind::Data) && !class.is_abstract {
                singles.push("new".to_string());
            }
            // A library cog's root module: its public functions
            // (docs/10 §6).
            if let Some(cog) = class.cog {
                for (f, g) in &world.file_groups {
                    if *g != quarz_types::UnitGroup::Cog(cog) {
                        continue;
                    }
                    for k in &world.classes {
                        if k.kind == ClassKind::Main && k.file == *f {
                            singles.extend(
                                k.methods
                                    .iter()
                                    .filter(|(_, ids)| public(ids))
                                    .map(|(n, _)| n.clone()),
                            );
                        }
                    }
                }
            }
            singleton_methods.push(sorted(singles));
            members.push(sorted(class.members.keys().cloned()));
        }
        let mut classes = HashMap::new();
        for c in &world.classes {
            classes.insert(c.name.clone(), c.id);
        }
        let functions = sorted(
            world
                .ancestor_ids(main)
                .iter()
                .chain([&world.builtin.kernel])
                .flat_map(|a| world.class(*a).methods.keys().cloned()),
        );
        let constants = sorted(world.top.keys().cloned());
        let b = &world.builtin;
        Completions {
            locals: locals
                .iter()
                .map(|(name, t)| {
                    let mut cs = Vec::new();
                    classes_of(t, &mut cs);
                    (name.clone(), cs)
                })
                .collect(),
            functions,
            constants,
            classes,
            instance_methods,
            singleton_methods,
            members,
            all_methods: sorted(all),
            literals: Literals {
                string: b.string,
                symbol: b.symbol,
                int: b.int,
                float: b.float,
                array: b.array,
                hash: b.hash,
            },
        }
    }

    /// What may complete the word before byte `pos` of `line`: where the
    /// word starts, and the candidates for it.
    pub fn complete(&self, line: &str, pos: usize) -> (usize, Vec<String>) {
        let before = &line[..pos];
        let start = before
            .char_indices()
            .rev()
            .take_while(|(_, c)| *c == '_' || c.is_alphanumeric() || *c == '?' || *c == '!')
            .last()
            .map_or(pos, |(i, _)| i);
        let word = &before[start..];
        let head = &before[..start];
        let names: Vec<&String> = if let Some(recv) = head.strip_suffix("::") {
            match self.classes.get(constant_path(recv)) {
                Some(id) => self.members[*id as usize].iter().collect(),
                None => Vec::new(),
            }
        } else if let Some(recv) = head.strip_suffix("&.").or_else(|| head.strip_suffix('.')) {
            self.methods_of(recv)
        } else {
            let mut names: Vec<&String> = Vec::new();
            if word.starts_with(|c: char| c.is_uppercase()) {
                names.extend(&self.constants);
            } else {
                names.extend(self.locals.iter().map(|(n, _)| n));
                names.extend(&self.functions);
            }
            names
        };
        let mut found: BTreeSet<String> = names
            .into_iter()
            .filter(|n| n.starts_with(word))
            .cloned()
            .collect();
        if !head.ends_with('.') && !head.ends_with("::") {
            let words = Keyword::ALL
                .iter()
                .map(|k| k.as_str())
                .chain(DECLARATION_WORDS.iter().copied());
            found.extend(words.filter(|w| w.starts_with(word)).map(str::to_string));
        }
        found.remove(word);
        (start, found.into_iter().collect())
    }

    /// The methods a receiver written as `recv` (the text before the dot)
    /// answers: those of a local variable's type, of a class, of a
    /// literal; any method when its type is not known.
    fn methods_of(&self, recv: &str) -> Vec<&String> {
        let recv = recv.trim_end();
        let of = |ids: &[ClassId]| -> Vec<&String> {
            let mut names: Vec<&String> = ids
                .iter()
                .flat_map(|id| &self.instance_methods[*id as usize])
                .collect();
            names.sort();
            names.dedup();
            names
        };
        let l = &self.literals;
        if recv.ends_with('"') || recv.ends_with('\'') {
            return of(&[l.string]);
        }
        if recv.ends_with(']') {
            return of(&[l.array]);
        }
        if recv.ends_with('}') {
            return of(&[l.hash]);
        }
        let ident_start = recv
            .char_indices()
            .rev()
            .take_while(|(_, c)| *c == '_' || *c == ':' || c.is_alphanumeric())
            .last()
            .map_or(recv.len(), |(i, _)| i);
        let ident = &recv[ident_start..];
        if ident.starts_with(':') && !ident.starts_with("::") {
            return of(&[l.symbol]);
        }
        if ident.starts_with(|c: char| c.is_ascii_digit()) {
            let float =
                ident.contains('.') || recv[..ident_start].ends_with(|c: char| c.is_ascii_digit());
            return of(&[if float { l.float } else { l.int }]);
        }
        if ident.starts_with(|c: char| c.is_uppercase()) {
            return match self.classes.get(constant_path(ident)) {
                Some(id) => self.singleton_methods[*id as usize].iter().collect(),
                None => self.all_methods.iter().collect(),
            };
        }
        match self.locals.iter().find(|(n, _)| n == ident) {
            Some((_, ids)) if !ids.is_empty() => of(ids),
            _ => self.all_methods.iter().collect(),
        }
    }
}

/// The constant path that ends `text` (`Foo::Bar` in `x = Foo::Bar`).
fn constant_path(text: &str) -> &str {
    let start = text
        .char_indices()
        .rev()
        .take_while(|(_, c)| *c == '_' || *c == ':' || c.is_alphanumeric())
        .last()
        .map_or(text.len(), |(i, _)| i);
    text[start..].trim_start_matches(':')
}
