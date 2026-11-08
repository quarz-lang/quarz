//! Where `quarz doc`'s pages link beyond themselves: a name of another
//! cog's, or of the standard library's, to that API's published pages
//! (#448), and a declaration's location to its source on GitHub at the
//! commit the pages are made from (#449). See docs/10 §8 and docs/13.

use std::path::{Path, PathBuf};
use std::process::Command;

use quarz_syntax::SourceFile;

/// The standard library's published API, unless `--std-url` says
/// otherwise.
pub(crate) const STD_URL: &str = "https://api.quarz.dev";

/// The standard library's repository.
const STD_REPOSITORY: &str = "https://github.com/quarz-lang/quarz";

/// The links of a loaded program's files and cogs.
#[derive(Default)]
pub(crate) struct Links {
    /// Per file (`Loaded::files`' index): where its source is on GitHub,
    /// at its commit (`https://github.com/o/r/blob/<rev>/src/x.qz`).
    pub source: Vec<Option<String>>,
    /// Per file: the published API its declarations are on, when they
    /// are another site's (a dependency cog's, the standard library's).
    pub docs: Vec<Option<String>>,
    /// Per cog (`World::cogs`' index): the same for its root module,
    /// which has no file.
    pub cog_docs: Vec<Option<String>>,
}

/// What `quarz doc` was asked for, for the links.
pub(crate) struct Asked<'a> {
    /// Documenting the standard library itself (`--std`).
    pub std: bool,
    /// `--std-url`.
    pub std_url: Option<&'a str>,
    /// `--source-rev`: the commit of the documented files' links.
    pub source_rev: Option<&'a str>,
}

/// One cog's links.
struct CogLinks {
    /// Its directory, canonical: its files' paths are relative to it.
    dir: PathBuf,
    /// Its published API, when not this site.
    documentation: Option<String>,
    /// `https://github.com/o/r/blob/<rev>/<its directory in the
    /// repository>/`, when known.
    source: Option<String>,
}

fn git(dir: &Path, args: &[&str]) -> Option<String> {
    let out = Command::new("git")
        .args(args)
        .current_dir(dir)
        .stderr(std::process::Stdio::null())
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8(out.stdout).ok()?.trim().to_string();
    (!s.is_empty()).then_some(s)
}

/// The source base of a checkout's directory `dir`: its repository from
/// `repository` or else `origin`'s URL, at `rev` or else `HEAD` (a dirty
/// tree links to HEAD), with `dir`'s place in the repository.
fn checkout_source(dir: &Path, repository: Option<&str>, rev: Option<&str>) -> Option<String> {
    let page = match repository {
        Some(r) => quarz_cog::github_page(r)?,
        None => quarz_cog::github_page(&git(dir, &["remote", "get-url", "origin"])?)?,
    };
    let rev = match rev {
        Some(r) => r.to_string(),
        None => git(dir, &["rev-parse", "HEAD"])?,
    };
    let prefix = git(dir, &["rev-parse", "--show-prefix"]).unwrap_or_default();
    Some(format!("{page}/blob/{rev}/{prefix}"))
}

/// `[cog] documentation` and `repository` of the cog in `dir`.
fn manifest_urls(dir: &Path) -> (Option<String>, Option<String>) {
    let Ok(text) = std::fs::read_to_string(dir.join("Cog.toml")) else {
        return (None, None);
    };
    match quarz_cog::manifest::Manifest::parse(&text) {
        Ok(m) => (
            m.cog
                .documentation
                .map(|d| d.trim_end_matches('/').to_string()),
            m.cog.repository,
        ),
        Err(_) => (None, None),
    }
}

fn canonical(p: &Path) -> PathBuf {
    std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf())
}

/// `path` relative to `dir`, with `/`s.
fn relative(path: &Path, dir: &Path) -> Option<String> {
    let rel = canonical(path).strip_prefix(dir).ok()?.to_path_buf();
    let parts: Vec<String> = rel
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    Some(parts.join("/"))
}

/// A standard library file's name (`<prelude>`, `<std:json>`) as its
/// path under `std/`.
fn std_path(name: &str) -> Option<String> {
    if name == "<prelude>" {
        return Some("prelude.qz".to_string());
    }
    let module = name.strip_prefix("<std:")?.strip_suffix('>')?;
    Some(format!("{module}.qz"))
}

impl Links {
    /// The links of `files` (`Loaded::files`, the prelude first). `cogs`
    /// gives, per cog spec, its movement entry (`None` for a library's
    /// test application) and whether it is the documented one; `cog_of`
    /// gives each file's (after the prelude) cog spec.
    pub(crate) fn new(
        asked: &Asked,
        files: &[SourceFile],
        cog_of: &[Option<u32>],
        cogs: &[(Option<&quarz_cog::CogEntry>, bool)],
    ) -> Links {
        let std_docs = (!asked.std).then(|| {
            asked
                .std_url
                .unwrap_or(STD_URL)
                .trim_end_matches('/')
                .to_string()
        });
        let std_rev = if asked.std {
            asked.source_rev.or(quarz_cog::GIT_SHA)
        } else {
            quarz_cog::GIT_SHA
        };
        let std_source = std_rev.map(|r| format!("{STD_REPOSITORY}/blob/{r}/std/"));
        let sites: Vec<Option<CogLinks>> = cogs
            .iter()
            .map(|(entry, own)| {
                let entry = (*entry)?;
                let dir = canonical(&entry.dir);
                let (documentation, repository) = manifest_urls(&dir);
                let source = match (&entry.source, &entry.rev) {
                    // A dependency from git: its repository at the locked
                    // commit, in its `subdir`.
                    (Some(src), Some(rev)) if !own => {
                        let page = repository
                            .as_deref()
                            .and_then(quarz_cog::github_page)
                            .or_else(|| quarz_cog::github_page(&src.url));
                        page.map(|p| {
                            let sub = src
                                .subdir
                                .as_deref()
                                .map(|s| format!("{}/", s.trim_matches('/')))
                                .unwrap_or_default();
                            format!("{p}/blob/{rev}/{sub}")
                        })
                    }
                    // The documented cog, or one in a local checkout.
                    _ => checkout_source(
                        &dir,
                        repository.as_deref(),
                        if *own { asked.source_rev } else { None },
                    ),
                };
                Some(CogLinks {
                    dir,
                    documentation: if *own { None } else { documentation },
                    source,
                })
            })
            .collect();
        let mut links = Links {
            cog_docs: sites
                .iter()
                .map(|s| s.as_ref().and_then(|s| s.documentation.clone()))
                .collect(),
            ..Links::default()
        };
        // A single file, outside a cog: its checkout's.
        let mut checkouts: Vec<(PathBuf, Option<(PathBuf, String)>)> = Vec::new();
        for (i, f) in files.iter().enumerate() {
            let cog = i
                .checked_sub(1)
                .and_then(|j| cog_of.get(j).copied().flatten());
            let (source, docs) = if let Some(path) = std_path(&f.name) {
                (
                    std_source.as_ref().map(|s| format!("{s}{path}")),
                    std_docs.clone(),
                )
            } else if let Some(site) = cog.and_then(|c| sites.get(c as usize)?.as_ref()) {
                let path = Path::new(&f.name);
                (
                    site.source
                        .as_ref()
                        .and_then(|s| Some(format!("{s}{}", relative(path, &site.dir)?))),
                    site.documentation.clone(),
                )
            } else {
                let path = Path::new(&f.name);
                let dir = canonical(path.parent().unwrap_or(Path::new(".")));
                let found = match checkouts.iter().find(|(d, _)| *d == dir) {
                    Some((_, c)) => c.clone(),
                    None => {
                        let c = git(&dir, &["rev-parse", "--show-toplevel"]).and_then(|top| {
                            let top = canonical(Path::new(&top));
                            let base = checkout_source(&top, None, asked.source_rev)?;
                            Some((top, base))
                        });
                        checkouts.push((dir, c.clone()));
                        c
                    }
                };
                (
                    found.and_then(|(top, base)| Some(format!("{base}{}", relative(path, &top)?))),
                    None,
                )
            };
            links.source.push(source);
            links.docs.push(docs);
        }
        links
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_dependencys_source_is_its_repository_at_the_locked_commit() {
        let dir = std::env::temp_dir().join(format!("quarz-links-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(
            dir.join("Cog.toml"),
            "[cog]\nname = \"dep\"\ndocumentation = \"https://dep.example\"\nrepository = \"https://github.com/o/mono\"\n",
        )
        .unwrap();
        let file = dir.join("src").join("a.qz");
        std::fs::write(&file, "class A\nend\n").unwrap();
        let entry = quarz_cog::CogEntry {
            name: "dep".into(),
            version: "1.0.0".into(),
            module: "Dep".into(),
            dir: dir.clone(),
            imports: Vec::new(),
            dev_imports: Vec::new(),
            source: Some(quarz_cog::manifest::Source {
                url: "file:///elsewhere".into(),
                subdir: Some("libs/dep".into()),
            }),
            local_patch: false,
            locked_version: None,
            rev: Some("0123abc".into()),
        };
        let files = [
            SourceFile::new("<prelude>", ""),
            SourceFile::new(file.display().to_string(), ""),
        ];
        let links = Links::new(
            &Asked {
                std: false,
                std_url: None,
                source_rev: None,
            },
            &files,
            &[Some(1)],
            &[(None, false), (Some(&entry), false)],
        );
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(
            links.source[1].as_deref(),
            Some("https://github.com/o/mono/blob/0123abc/libs/dep/src/a.qz")
        );
        assert_eq!(links.docs[1].as_deref(), Some("https://dep.example"));
        assert_eq!(links.cog_docs[1].as_deref(), Some("https://dep.example"));
        assert_eq!(links.docs[0].as_deref(), Some(STD_URL));
    }
    #[test]
    fn std_paths() {
        assert_eq!(super::std_path("<prelude>").as_deref(), Some("prelude.qz"));
        assert_eq!(super::std_path("<std:json>").as_deref(), Some("json.qz"));
        assert_eq!(super::std_path("src/x.qz"), None);
    }
}
