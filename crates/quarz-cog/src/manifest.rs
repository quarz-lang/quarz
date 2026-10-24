//! `Cog.toml`: what a cog is and what it depends on.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::version::Version;
use crate::Error;

/// The manifest's file name.
pub const MANIFEST: &str = "Cog.toml";

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub cog: CogSection,
    #[serde(default)]
    pub dependencies: BTreeMap<String, Dependency>,
    #[serde(default, rename = "dev-dependencies")]
    pub dev_dependencies: BTreeMap<String, Dependency>,
    #[serde(default)]
    pub patch: BTreeMap<String, Patch>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CogSection {
    pub name: String,
    #[serde(default = "default_version")]
    pub version: String,
    pub module: Option<String>,
    /// The minimum language version.
    pub quarz: Option<String>,
    /// C libraries to link (reserved for FFI).
    #[serde(default)]
    pub link: Vec<String>,
}

fn default_version() -> String {
    "0.0.0".to_string()
}

/// A dependency: a git repository and where to look in it.
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Dependency {
    pub git: String,
    pub tag: Option<String>,
    pub rev: Option<String>,
    pub branch: Option<String>,
    pub subdir: Option<String>,
}

/// A local replacement of a dependency (`[patch]`).
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Patch {
    pub path: PathBuf,
}

/// Where a dependency points.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ref {
    Tag(String),
    Rev(String),
    Branch(String),
    /// The head of the default branch.
    Head,
}

impl Dependency {
    pub fn source(&self) -> Source {
        Source {
            url: self.git.clone(),
            subdir: self.subdir.clone(),
        }
    }

    pub fn reference(&self) -> Ref {
        if let Some(t) = &self.tag {
            Ref::Tag(t.clone())
        } else if let Some(r) = &self.rev {
            Ref::Rev(r.clone())
        } else if let Some(b) = &self.branch {
            Ref::Branch(b.clone())
        } else {
            Ref::Head
        }
    }
}

/// A cog's identity: its repository and the directory in it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Source {
    pub url: String,
    pub subdir: Option<String>,
}

impl Source {
    /// The form written in `Cog.lock`: `git+URL`, with `?subdir=DIR`.
    pub fn to_lock_string(&self) -> String {
        match &self.subdir {
            Some(d) => format!("git+{}?subdir={d}", self.url),
            None => format!("git+{}", self.url),
        }
    }

    pub fn parse_lock_string(s: &str) -> Option<Source> {
        let rest = s.strip_prefix("git+")?;
        Some(match rest.split_once("?subdir=") {
            Some((url, dir)) => Source {
                url: url.to_string(),
                subdir: Some(dir.to_string()),
            },
            None => Source {
                url: rest.to_string(),
                subdir: None,
            },
        })
    }
}

impl std::fmt::Display for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.subdir {
            Some(d) => write!(f, "{} ({d})", self.url),
            None => write!(f, "{}", self.url),
        }
    }
}

impl Manifest {
    /// Read and validate `dir/Cog.toml`.
    pub fn read(dir: &Path) -> Result<Manifest, Error> {
        let path = dir.join(MANIFEST);
        let text = std::fs::read_to_string(&path)
            .map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
        Manifest::parse(&text).map_err(|e| Error::new(format!("{}: {}", path.display(), e.0)))
    }

    pub fn parse(text: &str) -> Result<Manifest, Error> {
        let m: Manifest = toml::from_str(text).map_err(|e| Error::new(e.message().to_string()))?;
        m.validate()?;
        Ok(m)
    }

    fn validate(&self) -> Result<(), Error> {
        let name = &self.cog.name;
        if name.is_empty()
            || !name
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-' || c == '_')
            || !name.starts_with(|c: char| c.is_ascii_lowercase())
        {
            return Err(Error::new(format!(
                "[cog] name `{name}`: use lowercase letters, digits, `-` and `_`, starting with a letter"
            )));
        }
        if Version::parse(&self.cog.version).is_none() {
            return Err(Error::new(format!(
                "[cog] version `{}` is not a semantic version (MAJOR.MINOR.PATCH)",
                self.cog.version
            )));
        }
        if !is_const_name(&self.module()) {
            return Err(Error::new(format!(
                "[cog] module `{}` is not a constant name",
                self.module()
            )));
        }
        for (table, deps) in [
            ("dependencies", &self.dependencies),
            ("dev-dependencies", &self.dev_dependencies),
        ] {
            for (key, dep) in deps {
                if !is_const_name(key) {
                    return Err(Error::new(format!(
                        "[{table}] `{key}`: the key is the module the cog is seen as, so it starts with a capital letter (`{}`)",
                        camel_case(key)
                    )));
                }
                let refs = [&dep.tag, &dep.rev, &dep.branch]
                    .iter()
                    .filter(|r| r.is_some())
                    .count();
                if refs > 1 {
                    return Err(Error::new(format!(
                        "[{table}] `{key}`: give at most one of `tag`, `rev` and `branch`"
                    )));
                }
                if let Some(rev) = &dep.rev {
                    if rev.len() != 40 || !rev.chars().all(|c| c.is_ascii_hexdigit()) {
                        return Err(Error::new(format!(
                            "[{table}] `{key}`: `rev` must be a full commit id (40 hexadecimal digits)"
                        )));
                    }
                }
                if let Some(tag) = &dep.tag {
                    if Version::parse_tag(tag).is_none() {
                        return Err(Error::new(format!(
                            "[{table}] `{key}`: tag `{tag}` is not a version tag (vMAJOR.MINOR.PATCH)"
                        )));
                    }
                }
                if let Some(dir) = &dep.subdir {
                    if dir.starts_with('/') || dir.split('/').any(|p| p == "..") {
                        return Err(Error::new(format!(
                            "[{table}] `{key}`: `subdir` must be a relative path inside the repository"
                        )));
                    }
                }
            }
        }
        for key in self.patch.keys() {
            if !self.dependencies.contains_key(key) && !self.dev_dependencies.contains_key(key) {
                return Err(Error::new(format!(
                    "[patch] `{key}` is not a dependency of this cog"
                )));
            }
        }
        if let Some(req) = &self.cog.quarz {
            if parse_language_version(req).is_none() {
                return Err(Error::new(format!(
                    "[cog] quarz `{req}`: give a language version such as \"0.1\""
                )));
            }
        }
        Ok(())
    }

    /// The module the cog's declarations live in.
    pub fn module(&self) -> String {
        self.cog
            .module
            .clone()
            .unwrap_or_else(|| camel_case(&self.cog.name))
    }

    /// Whether `quarz` (the running language version) is new enough.
    pub fn check_language(&self, quarz: &str) -> Result<(), Error> {
        let Some(req) = &self.cog.quarz else {
            return Ok(());
        };
        let (Some(need), Some(have)) = (parse_language_version(req), parse_language_version(quarz))
        else {
            return Ok(());
        };
        if have < need {
            return Err(Error::new(format!(
                "cog `{}` needs quarz {req}, this is {quarz}",
                self.cog.name
            )));
        }
        Ok(())
    }
}

/// `"0.1"` or `"0.1.2"` as a comparable triple.
fn parse_language_version(s: &str) -> Option<(u64, u64, u64)> {
    let mut parts = s.split('.');
    let major = parts.next()?.parse().ok()?;
    let minor = parts.next().map_or(Some(0), |p| p.parse().ok())?;
    let patch = parts.next().map_or(Some(0), |p| p.parse().ok())?;
    if parts.next().is_some() {
        return None;
    }
    Some((major, minor, patch))
}

pub fn is_const_name(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_uppercase())
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// `http-client` → `HttpClient`.
pub fn camel_case(name: &str) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_validates() {
        let m = Manifest::parse(
            r#"
[cog]
name = "http-client"
version = "1.2.3"

[dependencies]
Tomlz = { git = "https://example.com/tomlz", tag = "v0.8.1" }
Utils = { git = "https://example.com/mono", rev = "3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e", subdir = "libs/utils" }
"#,
        )
        .unwrap();
        assert_eq!(m.module(), "HttpClient");
        assert_eq!(
            m.dependencies["Tomlz"].reference(),
            Ref::Tag("v0.8.1".into())
        );
        assert_eq!(
            m.dependencies["Utils"].source().to_lock_string(),
            "git+https://example.com/mono?subdir=libs/utils"
        );
        let err = |text: &str| Manifest::parse(text).unwrap_err().0;
        assert!(
            err("[cog]\nname = \"x\"\n[dependencies]\ntomlz = { git = \"u\" }\n")
                .contains("capital letter (`Tomlz`)")
        );
        assert!(err("[cog]\nname = \"x\"\n[dependencies]\nT = { git = \"u\", tag = \"v1.0.0\", branch = \"main\" }\n")
            .contains("at most one"));
        assert!(
            err("[cog]\nname = \"x\"\n[dependencies]\nT = { git = \"u\", rev = \"abc\" }\n")
                .contains("full commit id")
        );
        assert!(err("[cog]\nname = \"X\"\n").contains("lowercase"));
        assert!(err("[cog]\nname = \"x\"\nfoo = 1\n").contains("unknown field"));
    }

    #[test]
    fn language_version() {
        let m = Manifest::parse("[cog]\nname = \"x\"\nquarz = \"0.2\"\n").unwrap();
        assert!(m.check_language("0.1.9").is_err());
        assert!(m.check_language("0.2.0").is_ok());
        assert!(m.check_language("1.0.0").is_ok());
    }
}
