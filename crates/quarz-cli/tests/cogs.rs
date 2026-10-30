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
        let Ok(ft) = entry.file_type() else {
            continue;
        };
        if ft.is_dir() {
            make_writable(&path);
        } else if !ft.is_file() {
            // A symbolic link: its target is not ours to change.
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
        self.quarz_env(cwd, args, &[])
    }

    fn quarz_env(&self, cwd: &str, args: &[&str], env: &[(&str, &str)]) -> Out {
        let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
            .args(args)
            .envs(env.iter().copied())
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
fn static_defs_run_from_dependency_cogs() {
    // A library cog's `static def` runs, at compile time, from a class
    // body of the application; one of the application's own cog does not
    // (docs/14 §2).
    let w = World::new();
    w.write(
        "orm/Cog.toml",
        "[cog]\nname = \"orm\"\nversion = \"0.1.0\"\n",
    );
    w.write(
        "orm/src/model.qz",
        "class Model\n  static def self.table(name: String) -> Void\n    puts \"#{self.name} -> #{name} (#{fields.size} fields)\"\n  end\nend\n",
    );
    w.commit("orm", Some("v0.1.0"));
    w.app(
        &format!("Orm = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("orm")),
        "class Post < Orm::Model\n  @title: String\n  def initialize(@title: String); end\n  table \"posts\"\nend\nputs Post.new(\"t\").class.name\n",
    );
    let out = w.quarz("app", &["run"]);
    assert!(out.ok, "{}", out.stderr);
    assert_eq!(out.stdout, "Post\n");
    // The statement's output, after the fetch's progress lines.
    let said: Vec<&str> = out
        .stderr
        .lines()
        .filter(|l| !l.starts_with("quarz: "))
        .collect();
    assert_eq!(said, ["Post -> posts (1 fields)"]);
    w.write(
        "app/src/main.qz",
        "class Base\n  static def self.own -> Void; end\nend\nclass K < Base\n  own\nend\n",
    );
    let out = w.quarz("app", &["check"]);
    assert!(!out.ok);
    assert!(
        out.stderr
            .contains("`own` is a `static def` of the application"),
        "{}",
        out.stderr
    );
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
    // With a key renamed, the unchanged main file names nothing (what was
    // checked and kept for it before is not used: docs/05 §2).
    let manifest = std::fs::read_to_string(w.path("app/Cog.toml")).unwrap();
    w.write("app/Cog.toml", &manifest.replace("AUtil =", "AaUtil ="));
    assert!(w
        .fails("app", &["check"])
        .contains("unknown constant `AUtil`"));
    w.write("app/Cog.toml", &manifest);
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
fn namespaces_are_added_to_not_reopened() {
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    // `a.qz` loads before the file declaring `Shapes`: the qualified
    // declaration waits for it.
    w.write(
        "lib/src/a.qz",
        "class Shapes::Line\n  def self.k -> Int = Shapes.k + 1\nend\n",
    );
    w.write(
        "lib/src/b.qz",
        "module Shapes\n  def self.k -> Int = 1\nend\n",
    );
    w.commit("lib", Some("v0.1.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib"));
    w.app(&dep, "puts Lib::Shapes::Line.k\n");
    assert_eq!(w.ok("app", &["run"]), "2\n");
    // A dependency's root module is not the application's to add to.
    w.app(&dep, "module Lib\nend\nputs 1\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("`Lib` is already defined; modules cannot be reopened"),
        "{err}"
    );
    assert!(!err.contains("declare `class"), "{err}");
    // Nor to a dependency's modules, nor the standard library's.
    w.app(&dep, "class Lib::Shapes::Q\nend\nputs 1\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("cannot declare in `Lib::Shapes`: it is another cog's"),
        "{err}"
    );
    w.app(&dep, "class Lib::Q\nend\nputs 1\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("cannot declare in `Lib`: it is another cog's"),
        "{err}"
    );
    w.app(&dep, "class JSON::Mine\nend\nputs 1\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("cannot declare in `JSON`: it is in the standard library"),
        "{err}"
    );
    // A cog's files are its root module's body already.
    w.write("lib/src/c.qz", "module Lib\nend\n");
    w.commit("lib", Some("v0.1.1"));
    w.app(
        &format!("Lib = {{ git = \"{}\", tag = \"v0.1.1\" }}\n", w.url("lib")),
        "puts 1\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(err.contains("`Lib` is this cog's root module"), "{err}");
    // Also as `cog::Lib`.
    w.write("lib/src/c.qz", "module cog::Lib\nend\n");
    w.commit("lib", Some("v0.1.4"));
    w.app(
        &format!("Lib = {{ git = \"{}\", tag = \"v0.1.4\" }}\n", w.url("lib")),
        "puts 1\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(err.contains("`Lib` is this cog's root module"), "{err}");
    // Nor may a cog declare a module named like a dependency's key.
    w.write(
        "user/Cog.toml",
        &format!(
            "[cog]\nname = \"user\"\n\n[dependencies]\nLib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n",
            w.url("lib")
        ),
    );
    w.write("user/src/a.qz", "module Lib\nend\n");
    w.commit("user", Some("v0.1.0"));
    w.app(
        &format!(
            "User = {{ git = \"{}\", tag = \"v0.1.0\" }}\n",
            w.url("user")
        ),
        "puts 1\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(err.contains("`Lib` is a dependency of this cog"), "{err}");
    w.write("user/src/a.qz", "Lib = 5\n");
    w.commit("user", Some("v0.1.2"));
    w.app(
        &format!(
            "User = {{ git = \"{}\", tag = \"v0.1.2\" }}\n",
            w.url("user")
        ),
        "puts 1\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(err.contains("`Lib` is a dependency of this cog"), "{err}");
    // A cog declares nothing at the application's top level.
    w.write("user/src/a.qz", "class ::Leak\nend\n");
    w.commit("user", Some("v0.1.3"));
    w.app(
        &format!(
            "User = {{ git = \"{}\", tag = \"v0.1.3\" }}\n",
            w.url("user")
        ),
        "puts 1\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("a cog declares only in its root module"),
        "{err}"
    );
    w.write("user/src/a.qz", "class Lib\nend\n");
    w.commit("user", Some("v0.1.1"));
    w.app(
        &format!(
            "User = {{ git = \"{}\", tag = \"v0.1.1\" }}\n",
            w.url("user")
        ),
        "puts 1\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(err.contains("`Lib` is a dependency of this cog"), "{err}");
    // A class named after the cog is not its root module.
    w.write("lib/src/c.qz", "class Lib\n  def self.k -> Int = 3\nend\n");
    w.commit("lib", Some("v0.1.2"));
    w.app(
        &format!("Lib = {{ git = \"{}\", tag = \"v0.1.2\" }}\n", w.url("lib")),
        "puts Lib::Lib.k\n",
    );
    assert_eq!(w.ok("app", &["run"]), "3\n");
}

#[test]
fn top_level_extensions_stay_in_their_cog() {
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    // A library's top-level extension is active in its files (another
    // file of it uses it), not in the application's.
    w.write(
        "lib/src/a.qz",
        "extension Int\n  def twice -> Int = self * 2\nend\n",
    );
    w.write(
        "lib/src/b.qz",
        "module Calc\n  def self.k -> Int = 21.twice\nend\n",
    );
    w.commit("lib", Some("v0.1.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib"));
    w.app(&dep, "puts Lib::Calc.k\n");
    assert_eq!(w.ok("app", &["run"]), "42\n");
    w.app(&dep, "puts 1.twice\n");
    let err = w.fails("app", &["check"]);
    assert!(err.contains("undefined method `twice`"), "{err}");
    // The application's top-level extension is active in its own files,
    // and changes nothing in the library's.
    w.write(
        "app/src/ext.qz",
        "extension Int\n  def twice -> Int = self * 3\nend\n",
    );
    w.app(&dep, "puts 1.twice, Lib::Calc.k\n");
    assert_eq!(w.ok("app", &["run"]), "3\n42\n");
}

#[test]
fn top_level_defs_are_cog_wide() {
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    // A library's top-level `def` is callable from its other files, with
    // its own file's top-level object as `self`; not from the application.
    w.write(
        "lib/src/a.qz",
        "def helper(x: Int) -> Int = x * 10\ndef where_am_i -> Object = self\n",
    );
    w.write(
        "lib/src/b.qz",
        "module Calc\n  def self.k -> Int = helper(4) + ::helper(0)\n  def self.same -> Bool = where_am_i.equal?(where_am_i)\nend\n",
    );
    w.commit("lib", Some("v0.1.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib"));
    w.app(&dep, "p Lib::Calc.k, Lib::Calc.same\n");
    assert_eq!(w.ok("app", &["run"]), "40\ntrue\n");
    w.app(&dep, "p helper(1)\n");
    let err = w.fails("app", &["check"]);
    assert!(err.contains("undefined method `helper`"), "{err}");
    // The application's files see each other's; a function's `self` is
    // its own file's object, not the caller's.
    w.write(
        "app/src/util.qz",
        "def twice(x: Int) -> Int = x * 2\ndef util_self -> Object = self\n",
    );
    w.app(
        &dep,
        "class C\n  def go -> Int = twice(5)\nend\nu = util_self\np twice(2), C.new.go, u.equal?(util_self), u.equal?(self)\n",
    );
    assert_eq!(w.ok("app", &["run"]), "4\n10\ntrue\nfalse\n");
    // One set per name: the same signature in two files is an error.
    w.write("app/src/again.qz", "def twice(x: Int) -> Int = x\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("`twice` is already defined with the same parameters in"),
        "{err}"
    );
    std::fs::remove_file(w.path("app/src/again.qz")).unwrap();
    // A changed signature in one file checks the others again: with the
    // cache, cold then warm, as without it.
    let cache = w.path("checks").display().to_string();
    let run = |env: &[(&str, &str)]| {
        let out = w.quarz_env("app", &["check"], env);
        (out.ok, out.stderr)
    };
    let cached = [("QUARZ_CACHE_DIR", cache.as_str())];
    assert!(run(&cached).0);
    w.write(
        "app/src/util.qz",
        "def twice(x: String) -> String = x + x\ndef util_self -> Object = self\n",
    );
    let warm = run(&cached);
    let off = run(&[("QUARZ_NO_CACHE", "1")]);
    assert!(!warm.0, "{}", warm.1);
    assert_eq!(warm, off);
}

#[test]
fn a_scripts_functions_reach_what_requires_it() {
    // A script sees the top-level `def`s of the files it requires, not
    // the other way round; each runs with its own file's object.
    let w = World::new();
    w.write(
        "s/lib.qz",
        "def helper(x: Int) -> Int = x * 10\ndef lib_self -> Object = self\ndef puts(s: String) -> Void = print(\"[lib] \", s, \"\\n\")\n",
    );
    w.write(
        "s/main.qz",
        "require_relative \"lib\"\nclass C\n  def go -> Int = helper(4)\nend\na = lib_self\np helper(1), C.new.go, a.equal?(lib_self), a.equal?(self)\nputs \"hi\"\nputs 2\n::puts \"via\"\n::puts 3\nKernel.puts \"built-in\"\n",
    );
    assert_eq!(
        w.ok("s", &["run", "main.qz"]),
        "10\n40\ntrue\nfalse\n[lib] hi\n2\n[lib] via\n3\nbuilt-in\n"
    );
    w.write("s/back.qz", "def back -> Int = only_main\n");
    w.write(
        "s/main2.qz",
        "require_relative \"back\"\ndef only_main -> Int = 3\np back\n",
    );
    let err = w.fails("s", &["check", "main2.qz"]);
    assert!(err.contains("`only_main`"), "{err}");
    // With a standard library module loaded without `require` (loaded
    // first, before the files).
    w.write(
        "s/main3.qz",
        "require_relative \"lib\"\np helper(2)\np JSON.generate([1])\n",
    );
    assert_eq!(w.ok("s", &["run", "main3.qz"]), "20\n\"[1]\"\n");
    // Another file's `require_relative`s decide what a file sees: the
    // cache sees a change of them (warm as without it).
    w.write("s/d.qz", "def dfun -> Int = 7\n");
    w.write("s/c.qz", "require_relative \"d\"\ndef cfun -> Int = 1\n");
    w.write(
        "s/y.qz",
        "require_relative \"c\"\ndef yfun -> Int = dfun + cfun\n",
    );
    w.write(
        "s/x.qz",
        "require_relative \"d\"\nrequire_relative \"y\"\np yfun\n",
    );
    let cache = w.path("checks").display().to_string();
    let run = |env: &[(&str, &str)]| {
        let out = w.quarz_env("s", &["run", "x.qz"], env);
        (out.ok, out.stdout, out.stderr)
    };
    let cached = [("QUARZ_CACHE_DIR", cache.as_str())];
    assert_eq!(run(&cached).1, "8\n");
    w.write("s/c.qz", "def cfun -> Int = 1\n");
    let warm = run(&cached);
    assert!(!warm.0, "{}", warm.1);
    assert_eq!(warm, run(&[("QUARZ_NO_CACHE", "1")]));
}

#[test]
fn test_files_see_the_cogs_functions_one_way() {
    // A cog's test files see its top-level `def`s, their own and what
    // they require; the cog and the other test files do not see theirs.
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    w.write(
        "lib/src/a.qz",
        "def base -> Int = 100\ndef show(x: Object) -> String = \"obj\"\ndef self.which -> String = show(1)\n",
    );
    for (f, n) in [("one", 1), ("two", 2)] {
        w.write(
            &format!("lib/test/{f}_test.qz"),
            &format!("require \"test\"\ndef make -> Int = base + {n}\ndef show(x: Int) -> String = \"int\"\nclass T{n} < Test::Case\n  def test_make -> Void\n    assert_equal(100 + {n}, make)\n    assert_equal(\"int\", show(1))\n    assert_equal(\"obj\", Lib.which)\n  end\nend\n"),
        );
    }
    let out = w.ok("lib", &["test"]);
    assert!(out.contains("2 tests, 6 assertions, 0 failures"), "{out}");
    // Its own `def` of a cog's signature is a duplicate.
    w.write("lib/test/three_test.qz", "def base -> Int = 0\n");
    let err = w.fails("lib", &["test"]);
    assert!(
        err.contains("`base` is already defined with the same parameters"),
        "{err}"
    );
}

#[test]
fn a_def_in_another_file_ties_as_in_its_own() {
    // An equally specific `def` beats `Kernel`'s built-in in every file
    // that sees it, and two files' `def`s that fit equally are ambiguous,
    // as two of one file are.
    let w = World::new();
    w.write(
        "app/src/util.qz",
        "def puts[T](*args: T) -> Void = Kernel.puts(\"mine\")\n",
    );
    w.app(
        "",
        "puts 1\n::puts 2\nclass D\n  def go -> Void = puts(3)\nend\nD.new.go\n",
    );
    assert_eq!(w.ok("app", &["run"]), "mine\nmine\nmine\n");
    w.write("app/src/a.qz", "def f[T](x: T) -> String = \"a\"\n");
    w.write("app/src/b.qz", "def f(x: Object) -> String = \"b\"\n");
    w.app("", "p f(1)\n");
    let err = w.fails("app", &["check"]);
    assert!(err.contains("the call of `f` is ambiguous"), "{err}");
}

#[test]
fn a_cogs_functions_come_after_selfs_methods_and_before_kernels() {
    // docs/01 §1: an implicit call finds a method of `self`, then the
    // cog's top-level `def`s, then `Kernel`'s built-in functions, inside
    // a class as at the top level, one set of overloads.
    let w = World::new();
    w.write(
        "app/src/out.qz",
        "def puts(s: String) -> Void = Kernel.puts(\"[cog] \" + s)\n",
    );
    w.app(
        "",
        "class A\n  def hi -> Void = puts(\"A\")\n  def blk -> Void = [1].each { |_| puts(\"block\") }\n  def exe -> Void = 5.instance_exec { puts(\"exec\") }\n  def int -> Void = puts(3)\nend\nclass B < A\n  def puts(s: String) -> Void = Kernel.puts(\"[B] \" + s)\n  def own -> Void = puts(\"B\")\nend\nclass N\n  def puts(n: Int) -> Void = Kernel.puts(\"[N] #{n}\")\n  def go -> Void\n    puts(1)\n    puts(\"s\")\n    puts(1.5)\n  end\nend\nN.new.go\na = A.new\na.hi\na.blk\na.exe\na.int\nB.new.own\nB.new.hi\nputs(\"top\")\nKernel.puts(\"built-in\")\n",
    );
    assert_eq!(
        w.ok("app", &["run"]),
        "[N] 1\n[cog] s\n1.5\n[cog] A\n[cog] block\n[cog] exec\n3\n[B] B\n[cog] A\n[cog] top\nbuilt-in\n"
    );
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

#[cfg(unix)]
#[test]
fn symbolic_links_are_refused_in_cogs_and_not_followed_in_the_application() {
    use std::os::unix::fs::PermissionsExt;
    let w = World::new();
    w.write("secret.txt", "secret\n");
    let secret = w.path("secret.txt");
    w.write("s/Cog.toml", "[cog]\nname = \"s\"\n");
    w.write("s/src/a.qz", "A = 1\n");
    std::os::unix::fs::symlink(&secret, w.path("s/src/leak.txt")).unwrap();
    w.commit("s", Some("v0.1.0"));
    w.app(
        &format!("S = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("s")),
        "puts S::A\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(err.contains("symbolic link"), "{err}");
    // The link's target was neither changed nor copied, and nothing is
    // left in the cache.
    let mode = std::fs::metadata(&secret).unwrap().permissions().mode();
    assert_eq!(mode & 0o200, 0o200, "the secret was made read-only");
    let left: Vec<_> = std::fs::read_dir(w.path("cache/src"))
        .map(|d| d.flatten().map(|e| e.file_name()).collect())
        .unwrap_or_default();
    assert!(left.is_empty(), "{left:?}");
    // In the application's own src/, a link back up is not walked.
    w.app("", "puts 1\n");
    std::os::unix::fs::symlink("..", w.path("app/src/up")).unwrap();
    assert_eq!(w.ok("app", &["run"]), "1\n");
}

#[test]
fn a_failed_vendor_keeps_the_old_vendor() {
    let w = World::new();
    w.libraries();
    w.app(
        &format!(
            "Httpx = {{ git = \"{}\", tag = \"v1.4.0\" }}\n",
            w.url("httpx")
        ),
        "puts Httpx.get(\"u\").body\n",
    );
    w.ok("app", &["cog", "vendor"]);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = std::fs::metadata(w.path("app/vendor/httpx/src/client.qz"))
            .unwrap()
            .permissions()
            .mode();
        assert_eq!(
            mode & 0o777,
            0o644,
            "vendored files are the owner's to change, no one else's"
        );
    }
    make_writable(&w.path("cache"));
    std::fs::remove_dir_all(w.path("cache")).unwrap();
    assert_eq!(w.ok("app", &["run", "--offline"]), "Value(body)\n");
    // With nothing in the cache, vendoring again cannot work offline; the
    // vendor/ that worked must still be there.
    assert!(w
        .fails("app", &["cog", "vendor", "--offline"])
        .contains("--offline"));
    assert_eq!(w.ok("app", &["run", "--offline"]), "Value(body)\n");
}

#[test]
fn concurrent_fetches_share_the_cache() {
    let w = World::new();
    w.libraries();
    w.app(
        &format!(
            "Httpx = {{ git = \"{}\", tag = \"v1.4.0\" }}\n",
            w.url("httpx")
        ),
        "puts Httpx.get(\"u\").body\n",
    );
    w.ok("app", &["run"]);
    // An empty cache: every process mirrors, fetches and installs.
    make_writable(&w.path("cache"));
    std::fs::remove_dir_all(w.path("cache")).unwrap();
    let w = std::sync::Arc::new(w);
    let runs: Vec<_> = (0..48)
        .map(|_| {
            let w = w.clone();
            std::thread::spawn(move || w.quarz("app", &["cog", "fetch", "--locked"]))
        })
        .collect();
    for r in runs {
        let out = r.join().unwrap();
        assert!(out.ok, "{}", out.stderr);
    }
    let names: Vec<String> = std::fs::read_dir(w.path("cache/src"))
        .unwrap()
        .flatten()
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    assert_eq!(names.len(), 2, "{names:?}");
    assert!(names.iter().all(|n| !n.starts_with('.')), "{names:?}");
}

#[test]
fn a_pseudo_version_follows_the_highest_version_tag_among_its_ancestors() {
    // `v1.5` is not a version tag; the base is v1.4.0, not 0.0.0.
    let w = World::new();
    publish(&w, "p", "1.4.0", &[]);
    w.write("p/src/w.qz", "W = 1\n");
    w.commit("p", Some("v1.5"));
    w.write("p/src/x.qz", "X = 2\n");
    let head = w.commit("p", None);
    w.app(
        &format!("P = {{ git = \"{}\", rev = \"{head}\" }}\n", w.url("p")),
        "puts P::X\n",
    );
    assert_eq!(w.ok("app", &["run"]), "2\n");
    let v = w.locked_version("app", "p");
    assert!(v.starts_with("1.4.1-0."), "{v}");
    // A release branch merged back: the higher tag on the merged side is
    // an ancestor too.
    w.git("p", &["checkout", "-q", "-b", "release", "v1.4.0"]);
    w.write("p/src/r.qz", "R = 3\n");
    w.commit("p", Some("v2.0.0"));
    w.git("p", &["checkout", "-q", "main"]);
    w.git(
        "p",
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@example.com",
            "merge",
            "-q",
            "--no-edit",
            "release",
        ],
    );
    let merged = w.git("p", &["rev-parse", "HEAD"]);
    w.app(
        &format!("P = {{ git = \"{}\", rev = \"{merged}\" }}\n", w.url("p")),
        "puts P::R\n",
    );
    assert_eq!(w.ok("app", &["run"]), "3\n");
    let v = w.locked_version("app", "p");
    assert!(v.starts_with("2.0.1-0."), "{v}");
}

#[test]
fn a_cog_from_elsewhere_may_not_name_a_local_repository() {
    // `https://example.invalid/` is this test's directory to git, so that
    // `r` is a cog from elsewhere; it names `t` by a file:// URL.
    let w = World::new();
    publish(&w, "t", "1.0.0", &[]);
    publish(&w, "r", "1.0.0", &[("T", "t", "v1.0.0")]);
    w.app(
        "R = { git = \"https://example.invalid/r\", tag = \"v1.0.0\" }\n",
        "puts R::V\n",
    );
    let base = format!("{}/", w.url(""));
    let base = base.replace("//", "/").replacen("file:/", "file:///", 1);
    let env = [
        ("GIT_CONFIG_COUNT", "1"),
        ("GIT_CONFIG_KEY_0", &*format!("url.{base}.insteadOf")),
        ("GIT_CONFIG_VALUE_0", "https://example.invalid/"),
    ];
    let out = w.quarz_env("app", &["check"], &env);
    assert!(
        !out.ok && out.stderr.contains("a repository on this machine"),
        "{}",
        out.stderr
    );
    // The application itself may.
    w.app(
        &format!("T = {{ git = \"{}\", tag = \"v1.0.0\" }}\n", w.url("t")),
        "puts T::V\n",
    );
    assert_eq!(w.ok("app", &["run"]), "1.0.0\n");
}

#[test]
fn annotated_tags_give_versions_too() {
    // ls-remote shows an annotated tag's object and its peeled commit;
    // the version comes from the commit on both sides.
    let w = World::new();
    w.write("q/Cog.toml", "[cog]\nname = \"q\"\nversion = \"1.2.0\"\n");
    w.write("q/src/v.qz", "V = 1\n");
    w.commit("q", None);
    w.git(
        "q",
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@example.com",
            "tag",
            "-a",
            "-m",
            "release",
            "v1.2.0",
        ],
    );
    let tagged = w.git("q", &["rev-parse", "HEAD"]);
    w.write("q/src/w.qz", "W = 2\n");
    let later = w.commit("q", None);
    // By tag, by the tagged commit (its exact version), by a later commit
    // (a pseudo-version after the annotated tag).
    w.app(
        &format!("Q = {{ git = \"{}\", tag = \"v1.2.0\" }}\n", w.url("q")),
        "puts Q::V\n",
    );
    assert_eq!(w.ok("app", &["run"]), "1\n");
    assert_eq!(w.locked_version("app", "q"), "1.2.0");
    w.app(
        &format!("Q = {{ git = \"{}\", rev = \"{tagged}\" }}\n", w.url("q")),
        "puts Q::V\n",
    );
    w.ok("app", &["check"]);
    assert_eq!(w.locked_version("app", "q"), "1.2.0");
    w.app(
        &format!("Q = {{ git = \"{}\", rev = \"{later}\" }}\n", w.url("q")),
        "puts Q::W\n",
    );
    assert_eq!(w.ok("app", &["run"]), "2\n");
    let v = w.locked_version("app", "q");
    assert!(v.starts_with("1.2.1-0."), "{v}");
}

/// The path a new user takes first (tmp/instructions-cog-e2e.md): an
/// application depending on a library cog by its https URL (here a
/// repository of this test's, through git's `insteadOf`), with a
/// `static def` macro, its tests and a second library that needs a newer
/// version; then the errors a user meets.
#[test]
fn a_new_users_walk() {
    let w = World::new();
    // (`w.url("")` ends with the directory's `/`.)
    let key = format!("url.{}.insteadOf", w.url(""));
    assert!(!key.contains("//."), "{key}");
    // (No global or system git configuration: an `insteadOf` there could
    // take over the redirection.)
    let env = [
        ("GIT_CONFIG_GLOBAL", "/dev/null"),
        ("GIT_CONFIG_NOSYSTEM", "1"),
        ("GIT_CONFIG_COUNT", "1"),
        ("GIT_CONFIG_KEY_0", key.as_str()),
        ("GIT_CONFIG_VALUE_0", "https://github.com/quarz-lang/"),
    ];
    let run = |cwd: &str, args: &[&str]| w.quarz_env(cwd, args, &env);
    // greet v1.0.0, then v1.1.0 with `bye`.
    let greeter = |bye: &str| {
        format!("class Greeter\n  @name: String\n  def initialize(@name: String); end\n  def hello -> String = \"Hello, #{{@name}}!\"\n{bye}\n  static def self.greets(name: Symbol) -> Void\n    def_method(\"greet_#{{name}}\".to_sym) do -> String\n      Greeter.new(name.to_s).hello\n    end\n  end\nend\n")
    };
    w.write(
        "greet/Cog.toml",
        "[cog]\nname = \"greet\"\nversion = \"1.0.0\"\nmodule = \"Greet\"\n",
    );
    w.write("greet/src/greeter.qz", &greeter(""));
    w.write(
        "greet/test/greeter_test.qz",
        "require \"test\"\nclass GreeterTest < Test::Case\n  def test_hello -> Void = assert_equal(\"Hello, Ann!\", Greet::Greeter.new(\"Ann\").hello)\nend\n",
    );
    w.commit("greet", Some("v1.0.0"));
    w.write(
        "greet/Cog.toml",
        "[cog]\nname = \"greet\"\nversion = \"1.1.0\"\nmodule = \"Greet\"\n",
    );
    w.write(
        "greet/src/greeter.qz",
        &greeter("  def bye -> String = \"Goodbye, #{@name}.\""),
    );
    let v110 = w.commit("greet", Some("v1.1.0"));
    let out = run("greet", &["test"]);
    assert!(
        out.ok && out.stdout.contains("1 tests, 1 assertions, 0 failures"),
        "{}{}",
        out.stdout,
        out.stderr
    );
    // The application: check, run, build, test, the lock.
    let greet = "Greet = { git = \"https://github.com/quarz-lang/greet\", tag = \"v1.0.0\" }\n";
    w.app(
        greet,
        "class Team < Greet::Greeter\n  def initialize; super(\"team\"); end\n  greets :world\nend\nputs Greet::Greeter.new(\"Quarz\").hello\nputs Team.new.greet_world\n",
    );
    w.write(
        "app/test/team_test.qz",
        "require \"test\"\nclass TeamTest < Test::Case\n  def test_world -> Void = assert_equal(\"Hello, world!\", Team.new.greet_world)\nend\n",
    );
    let out = run("app", &["check"]);
    assert!(out.ok, "{}", out.stderr);
    let expected = "Hello, Quarz!\nHello, world!\n";
    assert_eq!(run("app", &["run"]).stdout, expected);
    let out = run("app", &["build", "-o", "hello"]);
    assert!(out.ok, "{}", out.stderr);
    let exe = Command::new(w.path("app/hello")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&exe.stdout), expected);
    let out = run("app", &["test"]);
    assert!(
        out.stdout.contains("1 tests, 1 assertions, 0 failures"),
        "{}{}",
        out.stdout,
        out.stderr
    );
    let lock = std::fs::read_to_string(w.path("app/Cog.lock")).unwrap();
    assert!(
        lock.contains("source = \"git+https://github.com/quarz-lang/greet\""),
        "{lock}"
    );
    assert_eq!(w.locked_version("app", "greet"), "1.0.0");
    // A second run fetches nothing: it works with the repository gone.
    std::fs::rename(w.path("greet"), w.path("greet.away")).unwrap();
    let out = run("app", &["run"]);
    assert_eq!(out.stdout, expected, "{}", out.stderr);
    assert!(!out.stderr.contains("fetching"), "{}", out.stderr);
    std::fs::rename(w.path("greet.away"), w.path("greet")).unwrap();
    // greet-more needs greet v1.1.0: the version chosen (minimal version
    // selection), under the application's key, which may be another.
    w.write(
        "greet-more/Cog.toml",
        "[cog]\nname = \"greet-more\"\nversion = \"1.0.0\"\nmodule = \"GreetMore\"\n\n[dependencies]\nGreet = { git = \"https://github.com/quarz-lang/greet\", tag = \"v1.1.0\" }\n",
    );
    w.write(
        "greet-more/src/farewell.qz",
        "def self.farewell(name: String) -> String = Greet::Greeter.new(name).bye + \" (#{cog.name} #{cog.version})\"\n",
    );
    w.commit("greet-more", Some("v1.0.0"));
    let more =
        "GreetMore = { git = \"https://github.com/quarz-lang/greet-more\", tag = \"v1.0.0\" }\n";
    w.app(
        &format!("{}{more}", greet.replace("Greet = ", "Hi = ")),
        "puts Hi::Greeter.new(\"Quarz\").bye\nputs GreetMore.farewell(\"Quarz\")\n",
    );
    let out = run("app", &["run"]);
    assert_eq!(
        out.stdout, "Goodbye, Quarz.\nGoodbye, Quarz. (greet-more 1.0.0)\n",
        "{}",
        out.stderr
    );
    assert_eq!(w.locked_version("app", "greet"), "1.1.0");
    // A `rev` in the application's manifest pins: greet-more's need is
    // then an error naming both.
    let v100 = w.git("greet", &["rev-parse", "v1.0.0"]);
    assert_ne!(v100, v110);
    w.app(
        &format!(
            "Greet = {{ git = \"https://github.com/quarz-lang/greet\", rev = \"{v100}\" }}\n{more}"
        ),
        "puts GreetMore.farewell(\"Quarz\")\n",
    );
    let err = run("app", &["check"]).stderr;
    assert!(
        err.contains("the application pins https://github.com/quarz-lang/greet to 1.0.0 with `rev`, but greet-more 1.0.0 needs 1.1.0"),
        "{err}"
    );
    // A test's own dependency is a `[dev-dependencies]` entry.
    w.write(
        "app/Cog.toml",
        &format!("[cog]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies]\n{greet}\n[dev-dependencies]\n{more}"),
    );
    w.write(
        "app/src/main.qz",
        "puts Greet::Greeter.new(\"Quarz\").hello\n",
    );
    w.write(
        "app/test/team_test.qz",
        "require \"test\"\nclass FarewellTest < Test::Case\n  def test_farewell -> Void = assert_equal(\"Goodbye, Ann. (greet-more 1.0.0)\", GreetMore.farewell(\"Ann\"))\nend\n",
    );
    let out = run("app", &["test"]);
    assert!(
        out.stdout.contains("1 tests, 1 assertions, 0 failures"),
        "{}{}",
        out.stdout,
        out.stderr
    );
    assert_eq!(run("app", &["run"]).stdout, "Hello, Quarz!\n");
    std::fs::remove_file(w.path("app/test/team_test.qz")).unwrap();
    // Errors a user meets: a missing tag, a mistyped URL, a fetched cog
    // patching with a path.
    w.app(&greet.replace("v1.0.0", "v9.9.9"), "puts 1\n");
    let err = run("app", &["check"]).stderr;
    assert!(
        err.contains(
            "https://github.com/quarz-lang/greet has no tag `v9.9.9` (required by the application)"
        ),
        "{err}"
    );
    w.app(&greet.replace("/greet\"", "/gret\""), "puts 1\n");
    let err = run("app", &["check"]).stderr;
    assert!(
        err.contains("listing https://github.com/quarz-lang/gret")
            && err.contains("(required by the application)"),
        "{err}"
    );
    w.write(
        "pathy/Cog.toml",
        "[cog]\nname = \"pathy\"\nversion = \"1.0.0\"\n\n[dependencies]\nGreet = { git = \"https://github.com/quarz-lang/greet\", tag = \"v1.0.0\" }\n\n[patch]\nGreet = { path = \"../greet\" }\n",
    );
    w.write("pathy/src/z.qz", "Z = 1\n");
    w.commit("pathy", Some("v1.0.0"));
    w.app(greet, "puts 1\n");
    assert!(run("app", &["check"]).ok);
    let lock = std::fs::read_to_string(w.path("app/Cog.lock")).unwrap();
    let out = run(
        "app",
        &[
            "cog",
            "add",
            "https://github.com/quarz-lang/pathy",
            "--tag",
            "v1.0.0",
        ],
    );
    assert!(
        !out.ok
            && out.stderr.contains(
                "pathy 1.0.0 has a [patch] `Greet` naming ../greet, a directory on this machine"
            ),
        "{}",
        out.stderr
    );
    // Refused before anything is written.
    assert_eq!(
        std::fs::read_to_string(w.path("app/Cog.lock")).unwrap(),
        lock
    );
    // The application may patch with a path.
    w.app(
        &format!("{greet}\n[patch]\nGreet = {{ path = \"../greet\" }}\n"),
        "puts Greet::Greeter.new(\"dev\").bye\n",
    );
    let out = run("app", &["run"]);
    assert_eq!(out.stdout, "Goodbye, dev.\n", "{}", out.stderr);
}

#[test]
fn cogs_depend_on_each_other_in_no_cycle() {
    // docs/10 §4: with a cycle, each cog's `static` statements could run
    // the other's `static def`s, neither cog complete before the other.
    let w = World::new();
    publish(&w, "c1", "1.0.0", &[("C2", "c2", "v1.0.0")]);
    publish(&w, "c2", "1.0.0", &[("C1", "c1", "v1.0.0")]);
    w.app(
        &format!("C1 = {{ git = \"{}\", tag = \"v1.0.0\" }}\n", w.url("c1")),
        "puts C1::V\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("the cogs depend on each other in a cycle: c1 -> c2 -> c1")
            || err.contains("the cogs depend on each other in a cycle: c2 -> c1 -> c2"),
        "{err}"
    );
    assert!(!w.path("app/Cog.lock").exists());
    // Also when the cycle spells a repository otherwise (a trailing `/`),
    // and through a patched cog.
    w.write(
        "c2/Cog.toml",
        &format!(
            "[cog]\nname = \"c2\"\nversion = \"1.1.0\"\n\n[dependencies]\nC1 = {{ git = \"{}/\", tag = \"v1.0.0\" }}\n",
            w.url("c1")
        ),
    );
    w.commit("c2", Some("v1.1.0"));
    w.write(
        "c1/Cog.toml",
        &format!(
            "[cog]\nname = \"c1\"\nversion = \"1.1.0\"\n\n[dependencies]\nC2 = {{ git = \"{}\", tag = \"v1.1.0\" }}\n",
            w.url("c2")
        ),
    );
    w.commit("c1", Some("v1.1.0"));
    w.app(
        &format!("C1 = {{ git = \"{}\", tag = \"v1.1.0\" }}\n", w.url("c1")),
        "puts C1::V\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(err.contains("in a cycle: c"), "{err}");
    w.write(
        "app/Cog.toml",
        &format!(
            "[cog]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies]\nC1 = {{ git = \"{}\", tag = \"v1.0.0\" }}\n\n[patch]\nC1 = {{ path = \"../c1\" }}\n",
            w.url("c1")
        ),
    );
    let err = w.fails("app", &["check"]);
    assert!(err.contains("in a cycle: c"), "{err}");
}
