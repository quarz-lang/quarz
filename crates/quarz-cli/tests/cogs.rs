//! Cogs (docs/10-cogs.md): applications whose dependencies are git
//! repositories, made here as local repositories in a temporary
//! directory and fetched through `file://` URLs into a private cache.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

struct World {
    dir: PathBuf,
}

impl Drop for World {
    fn drop(&mut self) {
        make_writable(&self.dir);
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn make_writable(dir: &Path) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            make_writable(&path);
        } else if let Ok(meta) = std::fs::metadata(&path) {
            let mut perms = meta.permissions();
            #[allow(clippy::permissions_set_readonly_false)]
            perms.set_readonly(false);
            let _ = std::fs::set_permissions(&path, perms);
        }
    }
}

/// The output of a command: exit status, standard output, standard error.
struct Out {
    ok: bool,
    stdout: String,
    stderr: String,
}

impl World {
    fn new() -> World {
        static N: AtomicU32 = AtomicU32::new(0);
        let dir = std::env::temp_dir().join(format!(
            "quarz-cogs-{}-{}",
            std::process::id(),
            N.fetch_add(1, Ordering::SeqCst)
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        World { dir }
    }

    fn path(&self, rel: &str) -> PathBuf {
        self.dir.join(rel)
    }

    fn url(&self, repo: &str) -> String {
        format!("file://{}", self.path(repo).display())
    }

    fn write(&self, rel: &str, text: &str) {
        let path = self.path(rel);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }

    fn git(&self, repo: &str, args: &[&str]) -> String {
        let out = Command::new("git")
            .args(args)
            .current_dir(self.path(repo))
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@example.com")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@example.com")
            .output()
            .expect("git");
        assert!(
            out.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    }

    /// Commit everything in `repo` (creating it), tag the commit when
    /// `tag` is given, and return the commit id.
    fn commit(&self, repo: &str, tag: Option<&str>) -> String {
        if !self.path(repo).join(".git").exists() {
            self.git(repo, &["init", "-q", "-b", "main"]);
        }
        self.git(repo, &["add", "-A"]);
        self.git(repo, &["commit", "-q", "--allow-empty", "-m", "commit"]);
        if let Some(t) = tag {
            self.git(repo, &["tag", t]);
        }
        self.git(repo, &["rev-parse", "HEAD"])
    }

    fn quarz(&self, cwd: &str, args: &[&str]) -> Out {
        let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
            .args(args)
            .current_dir(self.path(cwd))
            .env("QUARZ_CACHE", self.path("cache"))
            .env("QUARZ_THREADS", "1")
            .output()
            .expect("quarz");
        Out {
            ok: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        }
    }

    fn ok(&self, cwd: &str, args: &[&str]) -> String {
        let out = self.quarz(cwd, args);
        assert!(
            out.ok,
            "quarz {args:?} failed:\n{}{}",
            out.stdout, out.stderr
        );
        out.stdout
    }

    fn fails(&self, cwd: &str, args: &[&str]) -> String {
        let out = self.quarz(cwd, args);
        assert!(!out.ok, "quarz {args:?} succeeded:\n{}", out.stdout);
        out.stderr
    }

    fn locked_version(&self, app: &str, name: &str) -> String {
        let lock = std::fs::read_to_string(self.path(app).join("Cog.lock")).unwrap();
        let at = lock
            .find(&format!("name = \"{name}\""))
            .unwrap_or_else(|| panic!("{name} not in the lock:\n{lock}"));
        let rest = &lock[at..];
        let v = rest.find("version = \"").unwrap() + "version = \"".len();
        rest[v..v + rest[v..].find('"').unwrap()].to_string()
    }

    /// `tomlz` (tags v0.8.1, v0.8.3, v0.9.0 and an untagged commit after)
    /// and `httpx` v1.4.0, which depends on tomlz v0.8.1.
    fn libraries(&self) -> String {
        self.write(
            "tomlz/Cog.toml",
            "[cog]\nname = \"tomlz\"\nversion = \"0.8.1\"\n",
        );
        self.write(
            "tomlz/src/value.qz",
            "class Value\n  @text: String\n  def initialize(@text: String)\n  end\n  def to_s -> String = \"Value(#{@text})\"\nend\n\ndef self.parse(text: String) -> Value = Value.new(text.strip)\n",
        );
        self.commit("tomlz", Some("v0.8.1"));
        self.write(
            "tomlz/Cog.toml",
            "[cog]\nname = \"tomlz\"\nversion = \"0.8.3\"\n",
        );
        self.commit("tomlz", Some("v0.8.3"));
        self.write(
            "tomlz/Cog.toml",
            "[cog]\nname = \"tomlz\"\nversion = \"0.9.0\"\n",
        );
        self.commit("tomlz", Some("v0.9.0"));
        self.write("tomlz/src/more.qz", "LEVEL = 9\n");
        let untagged = self.commit("tomlz", None);
        self.write(
            "httpx/Cog.toml",
            &format!(
                "[cog]\nname = \"httpx\"\nversion = \"1.4.0\"\n\n[dependencies]\nTomlz = {{ git = \"{}\", tag = \"v0.8.1\" }}\n",
                self.url("tomlz")
            ),
        );
        self.write(
            "httpx/src/client.qz",
            "class Client\n  def get(url: String) -> Response = Response.new(url, Tomlz.parse(\" body \"))\nend\n\ndef self.get(url: String) -> Response = Client.new.get(url)\n",
        );
        self.write(
            "httpx/src/response.qz",
            "class Response\n  @url: String\n  @body: Tomlz::Value\n  def initialize(@url: String, @body: Tomlz::Value)\n  end\n  def body -> Tomlz::Value = @body\n  def to_s -> String = \"#{cog.name} #{cog.version} #{@url}\"\nend\n\nmodule Inner\n  def self.root -> String = cog::Response.name + \" \" + cog.get(\"i\").to_s\nend\n",
        );
        self.commit("httpx", Some("v1.4.0"));
        untagged
    }

    fn app(&self, deps: &str, main: &str) {
        self.write(
            "app/Cog.toml",
            &format!("[cog]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies]\n{deps}"),
        );
        self.write("app/src/main.qz", main);
    }
}

#[test]
fn an_application_uses_its_cogs_without_require() {
    let w = World::new();
    w.libraries();
    w.app(
        &format!("Httpx = {{ git = \"{}\", tag = \"v1.4.0\" }}\n", w.url("httpx")),
        "res = Httpx.get(\"u\")\nputs res\nputs res.body\nputs Httpx::Inner.root\nc: Httpx::Client = Httpx::Client.new\nputs c.get(\"x\").class.name\nputs cog.name + \" \" + cog.version\nputs JSON.generate([1])\n",
    );
    let expected = "httpx 1.4.0 u\nValue(body)\nHttpx::Response httpx 1.4.0 i\nHttpx::Response\napp 0.1.0\n[1]\n";
    assert_eq!(w.ok("app", &["run"]), expected);
    // The lock pins both cogs, with their versions and content hashes.
    assert_eq!(w.locked_version("app", "httpx"), "1.4.0");
    assert_eq!(w.locked_version("app", "tomlz"), "0.8.1");
    let lock = std::fs::read_to_string(w.path("app/Cog.lock")).unwrap();
    assert!(lock.contains("hash = \"h1:"), "{lock}");
    // The same from a directory argument and from the main file.
    assert_eq!(w.ok(".", &["run", "app"]), expected);
    assert_eq!(w.ok(".", &["run", "app/src/main.qz"]), expected);
    assert_eq!(
        w.ok("app", &["cog", "tree"]),
        format!(
            "app 0.1.0\n  httpx 1.4.0 ({})\n    tomlz 0.8.1 ({})\n",
            w.url("httpx"),
            w.url("tomlz")
        )
    );
    // Compiled, the application prints the same.
    let exe = w.path("app/app-bin");
    w.ok("app", &["build", "-o", exe.to_str().unwrap()]);
    let out = Command::new(&exe)
        .env("QUARZ_THREADS", "1")
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
}

#[test]
fn keys_name_cogs_and_scopes_are_closed() {
    let w = World::new();
    w.libraries();
    for who in ["a", "b"] {
        w.write(
            &format!("util-{who}/Cog.toml"),
            &format!("[cog]\nname = \"util-{who}\"\nmodule = \"Util\"\n"),
        );
        w.write(
            &format!("util-{who}/src/table.qz"),
            &format!("class Table\n  def who -> String = \"{who}\"\nend\n"),
        );
        w.commit(&format!("util-{who}"), Some("v1.0.0"));
    }
    w.app(
        &format!(
            "AUtil = {{ git = \"{}\", tag = \"v1.0.0\" }}\nBUtil = {{ git = \"{}\", tag = \"v1.0.0\" }}\nHttpx = {{ git = \"{}\", tag = \"v1.4.0\" }}\n",
            w.url("util-a"),
            w.url("util-b"),
            w.url("httpx")
        ),
        "puts AUtil::Table.new.who\nputs BUtil::Table.new.who\nputs AUtil::Table.name\n",
    );
    assert_eq!(w.ok("app", &["run"]), "a\nb\nUtil::Table\n");
    // A dependency's dependency is not the application's.
    w.write("app/src/main.qz", "puts Tomlz.parse(\"x\")\n");
    assert!(w
        .fails("app", &["check"])
        .contains("unknown constant `Tomlz`"));
    // A library does not see the application's names (a patched copy).
    w.write("app/src/main.qz", "puts Httpx.get(\"u\")\n");
    w.write("app/src/user.qz", "class AppUser\nend\n");
    std::fs::create_dir_all(w.path("httpx-dev")).unwrap();
    for f in ["Cog.toml", "src/client.qz", "src/response.qz"] {
        w.write(
            &format!("httpx-dev/{f}"),
            &std::fs::read_to_string(w.path("httpx").join(f)).unwrap(),
        );
    }
    let manifest = std::fs::read_to_string(w.path("app/Cog.toml")).unwrap();
    w.write(
        "app/Cog.toml",
        &format!("{manifest}\n[patch]\nHttpx = {{ path = \"../httpx-dev\" }}\n"),
    );
    w.write(
        "httpx-dev/src/peek.qz",
        "class Peek\n  def peek -> String = AppUser.name\nend\n",
    );
    assert!(w
        .fails("app", &["check"])
        .contains("unknown constant `AppUser`"));
    // The patch is used, and is not locked.
    w.write(
        "httpx-dev/src/peek.qz",
        "def self.patched -> String = \"patched\"\n",
    );
    w.write("app/src/main.qz", "puts Httpx.patched\n");
    assert_eq!(w.ok("app", &["run"]), "patched\n");
    let lock = std::fs::read_to_string(w.path("app/Cog.lock")).unwrap();
    assert!(!lock.contains("httpx"), "{lock}");
    assert!(lock.contains("tomlz"), "{lock}");
    // A key that would hide a standard constant is refused.
    w.write(
        "app/Cog.toml",
        &format!(
            "{manifest}JSON = {{ git = \"{}\", tag = \"v1.0.0\" }}\n",
            w.url("util-a")
        ),
    );
    assert!(w
        .fails("app", &["check"])
        .contains("name of a built-in or standard library constant"));
}

#[test]
fn cog_files_hold_declarations_only() {
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    w.write("lib/src/a.qz", "puts \"loading\"\n");
    w.commit("lib", Some("v0.1.0"));
    w.app(
        &format!("Lib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib")),
        "puts 1\n",
    );
    assert!(w
        .fails("app", &["check"])
        .contains("a cog's files hold declarations only"));
    w.write("lib/src/a.qz", "require_relative \"b\"\n");
    w.commit("lib", Some("v0.1.1"));
    w.app(
        &format!("Lib = {{ git = \"{}\", tag = \"v0.1.1\" }}\n", w.url("lib")),
        "puts 1\n",
    );
    assert!(w
        .fails("app", &["check"])
        .contains("`require_relative` is not needed in a cog"));
    // The application's statements go in src/main.qz.
    w.app("", "puts 1\n");
    w.write("app/src/helper.qz", "puts 2\n");
    assert!(w
        .fails("app", &["check"])
        .contains("statements of the application go in src/main.qz"));
    w.write(
        "app/src/helper.qz",
        "def self_helper -> Int = 2\nclass Helper\n  def self.two -> Int = 2\nend\n",
    );
    w.write("app/src/main.qz", "puts Helper.two\np cog\n");
    assert!(w
        .fails("app", &["check"])
        .contains("`cog` is the top level here"));
    w.write("app/src/main.qz", "puts Helper.two\nputs cog::Helper.two\n");
    assert_eq!(w.ok("app", &["run"]), "2\n2\n");
}

#[test]
fn versions_follow_minimal_version_selection() {
    let w = World::new();
    let untagged = w.libraries();
    let httpx = format!(
        "Httpx = {{ git = \"{}\", tag = \"v1.4.0\" }}\n",
        w.url("httpx")
    );
    let main = "puts Httpx.get(\"u\").body\n";
    // The highest version asked for.
    w.app(
        &format!(
            "{httpx}Tomlz = {{ git = \"{}\", tag = \"v0.8.3\" }}\n",
            w.url("tomlz")
        ),
        main,
    );
    w.ok("app", &["check"]);
    assert_eq!(w.locked_version("app", "tomlz"), "0.8.3");
    // Dropping the requirement lowers it again.
    w.app(&httpx, main);
    assert!(w
        .fails("app", &["check", "--locked"])
        .contains("Cog.lock is out of date"));
    w.ok("app", &["check"]);
    assert_eq!(w.locked_version("app", "tomlz"), "0.8.1");
    // 0.8 and 0.9 are not compatible.
    w.app(
        &format!(
            "{httpx}Tomlz = {{ git = \"{}\", tag = \"v0.9.0\" }}\n",
            w.url("tomlz")
        ),
        main,
    );
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("httpx 1.4.0 needs") && err.contains("not compatible"),
        "{err}"
    );
    // An untagged commit gets a pseudo-version after the nearest tag.
    w.app(
        &format!(
            "Tomlz = {{ git = \"{}\", rev = \"{untagged}\" }}\n",
            w.url("tomlz")
        ),
        "puts Tomlz::LEVEL\n",
    );
    assert_eq!(w.ok("app", &["run"]), "9\n");
    let v = w.locked_version("app", "tomlz");
    assert!(
        v.starts_with("0.9.1-0.") && v.ends_with(&untagged[..12]),
        "{v}"
    );
    // A `rev` in the application's manifest is also a ceiling.
    let v081 = w.git("tomlz", &["rev-parse", "v0.8.1"]);
    let v083 = w.git("tomlz", &["rev-parse", "v0.8.3"]);
    let _ = v083;
    w.write(
        "mid/Cog.toml",
        &format!("[cog]\nname = \"mid\"\n\n[dependencies]\nTomlz = {{ git = \"{}\", tag = \"v0.8.3\" }}\n", w.url("tomlz")),
    );
    w.write("mid/src/m.qz", "X = 1\n");
    w.commit("mid", Some("v0.1.0"));
    w.app(
        &format!(
            "Tomlz = {{ git = \"{}\", rev = \"{v081}\" }}\nMid = {{ git = \"{}\", tag = \"v0.1.0\" }}\n",
            w.url("tomlz"),
            w.url("mid")
        ),
        "puts Mid::X\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("pins") && err.contains("0.8.1") && err.contains("0.8.3"),
        "{err}"
    );
}

#[test]
fn the_lock_is_verified_reused_and_vendored() {
    let w = World::new();
    w.libraries();
    w.app(
        &format!(
            "Httpx = {{ git = \"{}\", tag = \"v1.4.0\" }}\n",
            w.url("httpx")
        ),
        "puts Httpx.get(\"u\").body\n",
    );
    assert_eq!(w.ok("app", &["run"]), "Value(body)\n");
    // With the lock and the cache, nothing needs git.
    assert_eq!(w.ok("app", &["run", "--offline"]), "Value(body)\n");
    assert!(w
        .ok("app", &["cog", "verify"])
        .contains("every cog matches"));
    // A cached tree that changed is refused.
    let cached = std::fs::read_dir(w.path("cache/src"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .find(|p| {
            p.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("httpx-")
        })
        .unwrap();
    let file = cached.join("src/client.qz");
    make_writable(&cached);
    let original = std::fs::read_to_string(&file).unwrap();
    std::fs::write(&file, format!("{original}# changed\n")).unwrap();
    assert!(w.fails("app", &["run"]).contains("do not match Cog.lock"));
    assert!(!w.quarz("app", &["cog", "verify"]).ok);
    std::fs::write(&file, original).unwrap();
    // vendor/ serves the cogs without the cache.
    assert!(w.ok("app", &["cog", "vendor"]).contains("copied 2 cog(s)"));
    make_writable(&w.path("cache"));
    std::fs::remove_dir_all(w.path("cache")).unwrap();
    assert_eq!(w.ok("app", &["run", "--offline"]), "Value(body)\n");
    // A lock that the manifest has outgrown, with --offline, cannot be
    // resolved again.
    std::fs::remove_dir_all(w.path("app/vendor")).unwrap();
    w.app(
        &format!("Httpx = {{ git = \"{}\", tag = \"v1.4.0\" }}\nTomlz = {{ git = \"{}\", tag = \"v0.9.0\" }}\n", w.url("httpx"), w.url("tomlz")),
        "puts 1\n",
    );
    let err = w.fails("app", &["check", "--offline"]);
    assert!(err.contains("--offline"), "{err}");
}

#[test]
fn cog_add_writes_a_tag_or_a_rev() {
    let w = World::new();
    w.libraries();
    std::fs::create_dir_all(w.path("app")).unwrap();
    assert!(w.ok("app", &["cog", "init"]).contains("`app`"));
    assert_eq!(w.ok("app", &["run"]), "Hello from app!\n");
    // A tag, under another key than the module the cog declares.
    let out = w.ok(
        "app",
        &[
            "cog",
            "add",
            &w.url("httpx"),
            "--tag",
            "v1.4.0",
            "--as",
            "Http",
        ],
    );
    assert!(
        out.contains("added `Http`") && out.contains("tag = \"v1.4.0\""),
        "{out}"
    );
    w.write("app/src/main.qz", "puts Http.get(\"u\")\n");
    assert_eq!(w.ok("app", &["run"]), "httpx 1.4.0 u\n");
    // tomlz's default branch is an untagged 0.9 commit: written as a rev,
    // but httpx needs 0.8, so the addition is refused and undone.
    let before = std::fs::read_to_string(w.path("app/Cog.toml")).unwrap();
    assert!(w
        .fails("app", &["cog", "add", &w.url("tomlz")])
        .contains("not compatible"));
    assert_eq!(
        std::fs::read_to_string(w.path("app/Cog.toml")).unwrap(),
        before
    );
    // A tagged head is written as its tag.
    w.write("plain/Cog.toml", "[cog]\nname = \"plain\"\n");
    w.write("plain/src/p.qz", "P = 1\n");
    w.commit("plain", Some("v2.1.0"));
    let out = w.ok("app", &["cog", "add", &w.url("plain")]);
    assert!(
        out.contains("added `Plain`") && out.contains("tag = \"v2.1.0\""),
        "{out}"
    );
    // An untagged head as its commit.
    w.write("plain/src/q.qz", "Q = 2\n");
    let head = w.commit("plain", None);
    let out = w.ok("app", &["cog", "add", &w.url("plain"), "--as", "Plain2"]);
    assert!(out.contains(&format!("rev = \"{head}\"")), "{out}");
}

/// A cog at `version` of repository `repo` (module `module`) whose
/// manifest lists `deps` (key, repo, tag), committed and tagged.
fn publish(w: &World, repo: &str, version: &str, deps: &[(&str, &str, &str)]) {
    let mut manifest =
        format!("[cog]\nname = \"{repo}\"\nversion = \"{version}\"\n\n[dependencies]\n");
    for (key, dep, tag) in deps {
        manifest.push_str(&format!(
            "{key} = {{ git = \"{}\", tag = \"{tag}\" }}\n",
            w.url(dep)
        ));
    }
    w.write(&format!("{repo}/Cog.toml"), &manifest);
    w.write(&format!("{repo}/src/v.qz"), &format!("V = \"{version}\"\n"));
    w.commit(repo, Some(&format!("v{version}")));
}

#[test]
fn a_lock_just_resolved_is_used_as_it_is() {
    // The resolution visits A 1.0.0 (asking for C 1.5.0) before B lifts A
    // to 1.1.0 (asking for C 1.2.0): C stays at 1.5.0, and the next run
    // must take the lock as it is.
    let w = World::new();
    publish(&w, "c", "1.2.0", &[]);
    publish(&w, "c", "1.5.0", &[]);
    publish(&w, "a", "1.0.0", &[("C", "c", "v1.5.0")]);
    publish(&w, "a", "1.1.0", &[("C", "c", "v1.2.0")]);
    publish(&w, "b", "1.0.0", &[("A", "a", "v1.1.0")]);
    w.app(
        &format!(
            "A = {{ git = \"{}\", tag = \"v1.0.0\" }}\nB = {{ git = \"{}\", tag = \"v1.0.0\" }}\n",
            w.url("a"),
            w.url("b")
        ),
        "puts A::V\n",
    );
    assert_eq!(w.ok("app", &["run"]), "1.1.0\n");
    assert_eq!(w.locked_version("app", "c"), "1.5.0");
    assert_eq!(w.ok("app", &["run", "--locked", "--offline"]), "1.1.0\n");
}
