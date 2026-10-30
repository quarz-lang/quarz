//! The git operations cogs need, run with the `git` command: a bare
//! mirror per repository in the cache, fetched one commit at a time.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::Error;

/// A repository's mirror in the cache.
pub struct Mirror {
    pub dir: PathBuf,
    pub url: String,
}

fn git() -> Command {
    let mut c = Command::new("git");
    // Never stop to ask for credentials: authentication is git's own
    // (SSH keys, credential helpers), set up beforehand.
    c.env("GIT_TERMINAL_PROMPT", "0");
    c.stdin(Stdio::null());
    c
}

fn run(mut cmd: Command, what: &str) -> Result<String, Error> {
    let out = cmd
        .output()
        .map_err(|e| Error::new(format!("cannot run git ({what}): {e}")))?;
    if !out.status.success() {
        let err = String::from_utf8_lossy(&out.stderr);
        return Err(Error::new(format!("git failed ({what}): {}", err.trim())));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// The repository of `dir`, when it is in a git working tree with an
/// `origin` remote: its URL as configured (not as an `insteadOf` rewrites
/// it) and `dir`'s directory within the tree (`None` at its top).
pub fn origin(dir: &Path) -> Option<(String, Option<String>)> {
    let mut cmd = git();
    cmd.arg("-C")
        .arg(dir)
        .args(["config", "--get", "remote.origin.url"]);
    let url = run(cmd, "reading the origin remote").ok()?;
    let url = url.trim().to_string();
    if url.is_empty() {
        return None;
    }
    let mut cmd = git();
    cmd.arg("-C").arg(dir).args(["rev-parse", "--show-prefix"]);
    let prefix = run(cmd, "reading the directory in the repository").ok()?;
    let prefix = prefix.trim().trim_end_matches('/');
    Some((url, (!prefix.is_empty()).then(|| prefix.to_string())))
}

/// The refs a remote advertises: (name, commit), with annotated tags
/// peeled to their commits.
pub fn ls_remote(url: &str) -> Result<Vec<(String, String)>, Error> {
    let mut cmd = git();
    cmd.args(["ls-remote", "--", url]);
    let out = run(cmd, &format!("listing {url}"))?;
    let mut refs: Vec<(String, String)> = Vec::new();
    for line in out.lines() {
        let Some((commit, name)) = line.split_once('\t') else {
            continue;
        };
        if let Some(tag) = name.strip_suffix("^{}") {
            // The peeled commit of an annotated tag replaces the tag object.
            if let Some(entry) = refs.iter_mut().find(|(n, _)| n == tag) {
                entry.1 = commit.to_string();
            }
            continue;
        }
        refs.push((name.to_string(), commit.to_string()));
    }
    Ok(refs)
}

/// The host of a URL (`https://user@host:443/p`, `git@host:p`), lowercase,
/// or `local` for a `file://` URL or a path. Only the authority is looked
/// at: an `@` or `:` in the path is part of the path.
pub fn url_host(url: &str) -> String {
    if let Some((scheme, rest)) = url.split_once("://") {
        if scheme.eq_ignore_ascii_case("file") {
            return "local".to_string();
        }
        let authority = rest.split('/').next().unwrap_or("");
        let host = authority.rsplit_once('@').map_or(authority, |(_, h)| h);
        return host.to_ascii_lowercase();
    }
    // scp-like `user@host:path`: the part before the first `:`, if it holds
    // no `/` (otherwise it is a path).
    match url.split_once(':') {
        Some((authority, _)) if !authority.contains('/') && !authority.is_empty() => authority
            .rsplit_once('@')
            .map_or(authority, |(_, h)| h)
            .to_ascii_lowercase(),
        _ => "local".to_string(),
    }
}

/// Whether a URL names a repository on this machine (`file://` or a path).
pub fn is_local_url(url: &str) -> bool {
    url_host(url) == "local"
}

/// The directory a repository is mirrored in:
/// `<cache>/git/<host>/<name>-<digest of the URL>.git`. The digest keeps
/// every URL apart (`https://a/p@b/x` is not `https://b/x`); host and name
/// are only there to be read.
pub fn mirror_path(cache: &Path, url: &str) -> PathBuf {
    let clean = |s: &str| -> String {
        let c: String = s
            .chars()
            .map(|c| {
                if c.is_ascii_alphanumeric() || "._-".contains(c) {
                    c
                } else {
                    '_'
                }
            })
            .collect();
        c.trim_start_matches('.').to_string()
    };
    let host = clean(&url_host(url));
    let name = url
        .trim_end_matches('/')
        .rsplit(['/', ':'])
        .next()
        .unwrap_or("")
        .trim_end_matches(".git");
    let name = Some(clean(name))
        .filter(|n| !n.is_empty())
        .unwrap_or_else(|| "repo".into());
    let digest: String = crate::hash::digest(url.as_bytes())
        .chars()
        .skip(3)
        .filter(char::is_ascii_alphanumeric)
        .take(16)
        .collect();
    cache
        .join("git")
        .join(if host.is_empty() {
            "local".into()
        } else {
            host
        })
        .join(format!("{name}-{digest}.git"))
}

/// A full commit id: what every revision handed to git here must be, so
/// that none can be read as an option.
pub fn check_rev(rev: &str) -> Result<(), Error> {
    if rev.len() == 40 && rev.bytes().all(|b| b.is_ascii_hexdigit()) {
        Ok(())
    } else {
        let sha256 = rev.len() == 64 && rev.bytes().all(|b| b.is_ascii_hexdigit());
        Err(Error::new(if sha256 {
            format!("`{rev}` is a SHA-256 object id; repositories that use SHA-256 are not supported yet")
        } else {
            format!("`{rev}` is not a full commit id")
        }))
    }
}

impl Mirror {
    /// The mirror of `url`, created (empty) when it does not exist yet.
    pub fn open(cache: &Path, url: &str) -> Result<Mirror, Error> {
        let mirror = Mirror {
            dir: mirror_path(cache, url),
            url: url.to_string(),
        };
        if !mirror.dir.join("HEAD").exists() {
            let _lock = mirror.lock()?;
            if !mirror.dir.join("HEAD").exists() {
                let mut cmd = git();
                cmd.arg("init").arg("--bare").arg("-q").arg(&mirror.dir);
                run(cmd, "creating a mirror")?;
            }
        }
        Ok(mirror)
    }

    /// Hold the mirror for writing (creating it, fetching into it):
    /// another `quarz` process waits until the returned file is dropped.
    fn lock(&self) -> Result<std::fs::File, Error> {
        let mut path = self.dir.clone().into_os_string();
        path.push(".lock");
        let path = PathBuf::from(path);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .map_err(|e| Error::new(format!("{}: {e}", parent.display())))?;
        }
        let file = std::fs::OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .open(&path)
            .map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
        file.lock()
            .map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
        Ok(file)
    }

    fn cmd(&self) -> Command {
        let mut c = git();
        c.arg("--git-dir").arg(&self.dir);
        c
    }

    /// A fetch into the mirror. Its objects arrive as one pack, which
    /// appears at once: unpacked into loose objects (git's default for a
    /// small fetch), a commit could be seen by another process before its
    /// trees and blobs, which read without the lock.
    fn fetch(&self) -> Command {
        let mut c = self.cmd();
        c.args(["-c", "fetch.unpackLimit=1", "fetch", "-q"]);
        c
    }

    pub fn has_commit(&self, rev: &str) -> bool {
        let mut c = self.cmd();
        c.args(["cat-file", "-e", &format!("{rev}^{{commit}}")]);
        c.stderr(Stdio::null());
        c.status().is_ok_and(|s| s.success())
    }

    /// Fetch one commit (and nothing of its history).
    pub fn fetch_commit(&self, rev: &str) -> Result<(), Error> {
        check_rev(rev)?;
        if self.has_commit(rev) {
            return Ok(());
        }
        let _lock = self.lock()?;
        if self.has_commit(rev) {
            return Ok(());
        }
        let mut c = self.fetch();
        c.args(["--depth", "1", "--", &self.url, rev]);
        run(c, &format!("fetching {rev} from {}", self.url))?;
        Ok(())
    }

    /// Fetch a commit with its history and the repository's tags, to
    /// find the version tags it descends from. The mirror is this URL's
    /// alone, and its tags are made the remote's (moved and deleted ones
    /// included), so no other repository's tags get in.
    pub fn fetch_history(&self, rev: &str) -> Result<(), Error> {
        check_rev(rev)?;
        let _lock = self.lock()?;
        let mut c = self.fetch();
        c.arg("--prune");
        if self.dir.join("shallow").exists() {
            c.arg("--unshallow");
        }
        c.args(["--", &self.url, rev, "+refs/tags/*:refs/tags/*"]);
        run(
            c,
            &format!("fetching the history of {rev} from {}", self.url),
        )?;
        Ok(())
    }

    /// A file at a commit, or `None` when the commit has no such file
    /// (any other failure of git is an error).
    pub fn show(&self, rev: &str, path: &str) -> Result<Option<String>, Error> {
        check_rev(rev)?;
        if !self.has_commit(rev) {
            return Err(Error::new(format!("{} has no commit {rev}", self.url)));
        }
        let mut probe = self.cmd();
        probe.args(["cat-file", "-e", &format!("{rev}:{path}")]);
        probe.stderr(Stdio::null());
        if !probe.status().is_ok_and(|s| s.success()) {
            return Ok(None);
        }
        let mut c = self.cmd();
        c.args(["cat-file", "blob", &format!("{rev}:{path}")]);
        Ok(Some(run(c, &format!("reading {path} at {rev}"))?))
    }

    /// The commit's time, in seconds since the epoch.
    pub fn commit_time(&self, rev: &str) -> Result<u64, Error> {
        check_rev(rev)?;
        let mut c = self.cmd();
        c.args(["show", "-s", "--format=%ct", rev]);
        let out = run(c, "reading a commit time")?;
        out.trim()
            .parse()
            .map_err(|_| Error::new(format!("bad commit time for {rev}")))
    }

    /// The version tags among the commit's ancestors, the commit itself
    /// included (`git tag --merged`), with the commits they name.
    pub fn tags_merged(&self, rev: &str) -> Result<Vec<(String, String)>, Error> {
        check_rev(rev)?;
        let mut c = self.cmd();
        c.args([
            "for-each-ref",
            "--merged",
            rev,
            "--format=%(refname:strip=2) %(*objectname)%(objectname)",
            "refs/tags/v*",
        ]);
        let out = run(c, "listing tags")?;
        Ok(out
            .lines()
            .filter_map(|line| {
                let (name, ids) = line.split_once(' ')?;
                // A peeled annotated tag prints its commit first.
                Some((name.to_string(), ids.get(..40)?.to_string()))
            })
            .collect())
    }

    /// Write the tree of `rev` (or of its directory `subdir`) into `dest`.
    pub fn export(&self, rev: &str, subdir: Option<&str>, dest: &Path) -> Result<(), Error> {
        check_rev(rev)?;
        std::fs::create_dir_all(dest)
            .map_err(|e| Error::new(format!("{}: {e}", dest.display())))?;
        let tree = match subdir {
            Some(d) => format!("{rev}:{d}"),
            None => rev.to_string(),
        };
        let mut archive = self.cmd();
        // Only what is compiled and hashed: the manifest and `src/`.
        archive.args(["archive", "--format=tar", &tree, "--", "Cog.toml", "src"]);
        archive.stdout(Stdio::piped());
        archive.stderr(Stdio::piped());
        let mut child = archive
            .spawn()
            .map_err(|e| Error::new(format!("cannot run git: {e}")))?;
        let stdout = child.stdout.take().unwrap();
        let tar = Command::new("tar")
            .arg("-x")
            .arg("-C")
            .arg(dest)
            .stdin(stdout)
            .output()
            .map_err(|e| Error::new(format!("cannot run tar: {e}")))?;
        let status = child
            .wait_with_output()
            .map_err(|e| Error::new(format!("git archive: {e}")))?;
        if !status.status.success() {
            return Err(Error::new(format!(
                "git failed (exporting {tree}): {}",
                String::from_utf8_lossy(&status.stderr).trim()
            )));
        }
        if !tar.status.success() {
            return Err(Error::new(format!(
                "tar failed: {}",
                String::from_utf8_lossy(&tar.stderr).trim()
            )));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hosts_come_from_the_authority_only() {
        assert_eq!(url_host("https://github.com/foo/httpx"), "github.com");
        assert_eq!(
            url_host("https://user@GitHub.com:443/foo"),
            "github.com:443"
        );
        assert_eq!(
            url_host("https://evil.example/p@github.com/foo/httpx"),
            "evil.example"
        );
        assert_eq!(url_host("git@github.com:foo/httpx.git"), "github.com");
        assert_eq!(url_host("ssh://git@internal/devlib"), "internal");
        assert_eq!(url_host("file:///tmp/repo"), "local");
        assert_eq!(url_host("/tmp/repo"), "local");
        assert_eq!(url_host("../repo:x"), "local");
        assert!(is_local_url("file:///x") && !is_local_url("https://h/x"));
    }

    #[test]
    fn every_url_has_a_mirror_of_its_own() {
        let c = Path::new("/c");
        let real = mirror_path(c, "https://github.com/foo/httpx");
        let fake = mirror_path(c, "https://evil.example/p@github.com/foo/httpx");
        assert_ne!(real, fake);
        assert!(real.starts_with("/c/git/github.com"), "{}", real.display());
        assert!(
            fake.starts_with("/c/git/evil.example"),
            "{}",
            fake.display()
        );
        let name = real.file_name().unwrap().to_string_lossy().into_owned();
        assert!(
            name.starts_with("httpx-") && name.ends_with(".git"),
            "{name}"
        );
        assert_eq!(real, mirror_path(c, "https://github.com/foo/httpx"));
        assert!(mirror_path(c, "file:///tmp/x/../repo").starts_with("/c/git/local"));
    }

    #[test]
    fn revisions_are_commit_ids() {
        assert!(check_rev("3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e").is_ok());
        assert!(check_rev("--output=/tmp/x").is_err());
        assert!(check_rev("HEAD").is_err());
    }
}
