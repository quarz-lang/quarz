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

/// The directory a repository is mirrored in: `<cache>/git/<host>/<path>.git`.
pub fn mirror_path(cache: &Path, url: &str) -> PathBuf {
    let rest = url.split_once("://").map(|(_, r)| r).unwrap_or(url);
    // `git@host:path` (scp-like) and `user@host/path`.
    let rest = rest.rsplit_once('@').map(|(_, r)| r).unwrap_or(rest);
    let rest = rest.replacen(':', "/", 1);
    let mut dir = cache.join("git");
    for part in rest
        .split('/')
        .filter(|p| !p.is_empty() && *p != "." && *p != "..")
    {
        dir.push(part.trim_end_matches(".git"));
    }
    let mut s = dir.into_os_string();
    s.push(".git");
    PathBuf::from(s)
}

impl Mirror {
    /// The mirror of `url`, created (empty) when it does not exist yet.
    pub fn open(cache: &Path, url: &str) -> Result<Mirror, Error> {
        let dir = mirror_path(cache, url);
        if !dir.join("HEAD").exists() {
            std::fs::create_dir_all(&dir)
                .map_err(|e| Error::new(format!("{}: {e}", dir.display())))?;
            let mut cmd = git();
            cmd.arg("init").arg("--bare").arg("-q").arg(&dir);
            run(cmd, "creating a mirror")?;
        }
        Ok(Mirror {
            dir,
            url: url.to_string(),
        })
    }

    fn cmd(&self) -> Command {
        let mut c = git();
        c.arg("--git-dir").arg(&self.dir);
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
        if self.has_commit(rev) {
            return Ok(());
        }
        let mut c = self.cmd();
        c.args(["fetch", "-q", "--depth", "1", "--", &self.url, rev]);
        run(c, &format!("fetching {rev} from {}", self.url))?;
        Ok(())
    }

    /// Fetch a commit with its history and the repository's tags, to
    /// find the version tags it descends from.
    pub fn fetch_history(&self, rev: &str) -> Result<(), Error> {
        let mut c = self.cmd();
        c.args(["fetch", "-q"]);
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

    /// A file at a commit, or `None` when the commit has no such file.
    pub fn show(&self, rev: &str, path: &str) -> Result<Option<String>, Error> {
        let mut c = self.cmd();
        c.args(["show", &format!("{rev}:{path}")]);
        let out = c
            .output()
            .map_err(|e| Error::new(format!("cannot run git: {e}")))?;
        if !out.status.success() {
            return Ok(None);
        }
        Ok(Some(String::from_utf8_lossy(&out.stdout).into_owned()))
    }

    /// The commit's time, in seconds since the epoch.
    pub fn commit_time(&self, rev: &str) -> Result<u64, Error> {
        let mut c = self.cmd();
        c.args(["show", "-s", "--format=%ct", rev]);
        let out = run(c, "reading a commit time")?;
        out.trim()
            .parse()
            .map_err(|_| Error::new(format!("bad commit time for {rev}")))
    }

    /// The version tags naming the commit.
    pub fn tags_at(&self, rev: &str) -> Result<Vec<String>, Error> {
        let mut c = self.cmd();
        c.args(["tag", "--points-at", rev, "--list", "v[0-9]*"]);
        Ok(run(c, "listing tags")?
            .lines()
            .map(str::to_string)
            .collect())
    }

    /// The version tags among the commit's ancestors (itself excluded),
    /// nearest first as `git describe` finds them.
    pub fn nearest_tag(&self, rev: &str) -> Option<String> {
        let mut c = self.cmd();
        c.args([
            "describe",
            "--tags",
            "--abbrev=0",
            "--match",
            "v[0-9]*",
            &format!("{rev}^"),
        ]);
        c.stderr(Stdio::null());
        let out = c.output().ok()?;
        if !out.status.success() {
            return None;
        }
        Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
    }

    /// Write the tree of `rev` (or of its directory `subdir`) into `dest`.
    pub fn export(&self, rev: &str, subdir: Option<&str>, dest: &Path) -> Result<(), Error> {
        std::fs::create_dir_all(dest)
            .map_err(|e| Error::new(format!("{}: {e}", dest.display())))?;
        let tree = match subdir {
            Some(d) => format!("{rev}:{d}"),
            None => rev.to_string(),
        };
        let mut archive = self.cmd();
        archive.args(["archive", "--format=tar", &tree]);
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
    fn mirror_paths() {
        let c = Path::new("/c");
        assert_eq!(
            mirror_path(c, "https://github.com/foo/httpx"),
            Path::new("/c/git/github.com/foo/httpx.git")
        );
        assert_eq!(
            mirror_path(c, "https://github.com/foo/httpx.git"),
            Path::new("/c/git/github.com/foo/httpx.git")
        );
        assert_eq!(
            mirror_path(c, "git@github.com:foo/httpx.git"),
            Path::new("/c/git/github.com/foo/httpx.git")
        );
        assert_eq!(
            mirror_path(c, "ssh://git@internal/devlib"),
            Path::new("/c/git/internal/devlib.git")
        );
        assert_eq!(
            mirror_path(c, "file:///tmp/x/../repo"),
            Path::new("/c/git/tmp/x/repo.git")
        );
    }
}
