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
            "class Value\n  @text: String\n  def initialize(@text: String)\n  end\n  def to_s -> String = \"Value(#{@text})\"\nend\n\npublic def parse(text: String) -> Value = Value.new(text.strip)\n",
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
            "class Client\n  def get(url: String) -> Response = Response.new(url, Tomlz.parse(\" body \"))\nend\n\npublic def get(url: String) -> Response = Client.new.get(url)\n",
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
fn check_takes_a_library_as_its_users_load_it() {
    // A cog without src/main.qz: `quarz check` checks its files, under its
    // root module and with its dependencies; `run` and `build` have
    // nothing to run.
    let w = World::new();
    w.libraries();
    for (cwd, args) in [("httpx", &["check"][..]), (".", &["check", "httpx"][..])] {
        let out = w.quarz(cwd, args);
        assert!(out.ok, "{}", out.stderr);
        assert_eq!(out.stdout, "");
        assert!(
            out.stderr
                .contains("quarz: checked `httpx` as a library: no src/main.qz\n"),
            "{}",
            out.stderr
        );
    }
    w.write(
        "httpx/src/bad.qz",
        "class Bad\n  def body -> String = Client.new.get(\"u\").body\nend\n",
    );
    let err = w.fails("httpx", &["check"]);
    assert!(
        err.contains("bad.qz:2:")
            && err.contains("returns String but its body has type Tomlz::Value"),
        "{err}"
    );
    w.write("httpx/src/bad.qz", "puts 1\n");
    let err = w.fails("httpx", &["check"]);
    assert!(
        err.contains("a cog's files hold declarations only"),
        "{err}"
    );
    std::fs::remove_file(w.path("httpx/src/bad.qz")).unwrap();
    for cmd in ["run", "build"] {
        let err = w.fails("httpx", &[cmd]);
        assert!(
            err.contains("the application `httpx` has no src/main.qz to run"),
            "{cmd}: {err}"
        );
    }
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
fn statements_run_after_their_ancestors() {
    // docs/14 §2: within a cog, a class's statements run after those of
    // its superclasses, wherever these are written; unrelated classes
    // keep file name order.
    let w = World::new();
    w.write(
        "orm/Cog.toml",
        "[cog]\nname = \"orm\"\nversion = \"0.1.0\"\n",
    );
    w.write(
        "orm/src/model.qz",
        "class Model\n  static def self.gen(n: Symbol) -> Void\n    def_method(n) { 1 }\n  end\n  static def self.gens(n: Symbol) -> Void\n    def_method(n) { \"s\" }\n  end\n  static def self.show -> Void\n    puts \"#{name}: #{methods.map(&:name).select { |m| m.to_s.start_with?(\"g_\") }.inspect}\"\n  end\nend\n",
    );
    w.commit("orm", Some("v0.1.0"));
    w.app(
        &format!("Orm = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("orm")),
        "p Sub.new.g_base\n",
    );
    // `a_sub.qz` sorts before the file declaring `Sub`'s superclass.
    w.write(
        "app/src/a_sub.qz",
        "class Sub < Base\n  show\nend\nclass Lone < Orm::Model\n  gen :g_lone\n  show\nend\n",
    );
    w.write(
        "app/src/b_base.qz",
        "class Base < Orm::Model\n  gen :g_base\nend\nclass Other < Orm::Model\n  show\nend\n",
    );
    let said = |out: &Out| -> Vec<String> {
        out.stderr
            .lines()
            .filter(|l| !l.starts_with("quarz: "))
            .map(str::to_string)
            .collect()
    };
    // `Sub`'s statement waits for `Base`'s, then runs before `Other`'s,
    // whose file sorts after its own.
    let expected = ["Lone: [:g_lone]", "Sub: [:g_base]", "Other: []"];
    // The same with the check cache cold and warm.
    for _ in 0..2 {
        let out = w.quarz("app", &["run"]);
        assert!(out.ok, "{}", out.stderr);
        assert_eq!(out.stdout, "1\n");
        assert_eq!(said(&out), expected);
    }
    // A subclass's statement generating an override of what its
    // superclass's generates is checked against it, though its file
    // sorts first.
    w.write(
        "app/src/a_sub.qz",
        "class Sub < Base\n  gens :g_base\nend\n",
    );
    for _ in 0..2 {
        let out = w.quarz("app", &["check"]);
        assert!(!out.ok);
        assert!(
            out.stderr.contains("a_sub.qz:2:3: error: `g_base` returns String but `Base#g_base`, which it overrides, returns Int"),
            "{}",
            out.stderr
        );
    }
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
        "public def patched -> String = \"patched\"\n",
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

/// An extension's include at the top level of a library cog overrides the
/// class's ancestors' methods as one at the application's top level does;
/// one in a module body does not (docs/01 §7, #536).
#[test]
fn a_librarys_top_level_extension_include_overrides() {
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    w.write(
        "lib/src/a.qz",
        "class EB\n  def initialize; end\n  def m(x: Int) -> String = \"base\"\nend\n\
         module EM\n  def m(x: Int) -> String = \"sub\"\nend\n\
         class EC < EB\n  def initialize; end\nend\n\
         extension EC\n  include EM\nend\n\
         class XC < EB\n  def initialize; end\nend\n\
         module Scope\n  extension XC\n    include EM\n  end\nend\n\
         module Calc\n  def self.via(b: EB) -> String = b.m(1)\nend\n",
    );
    w.commit("lib", Some("v0.1.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib"));
    w.app(
        &dep,
        "puts Lib::Calc.via(Lib::EC.new), Lib::Calc.via(Lib::XC.new)\n",
    );
    assert_eq!(w.ok("app", &["run"]), "sub\nbase\n");
    // Not on a class from outside the cog (std's here): a cog cannot
    // monkey-patch its users (docs/10).
    w.write(
        "lib/src/b.qz",
        "module PM\n  def message -> String = \"patched by lib\"\nend\n\
         extension ArgumentError\n  include PM\nend\n\
         public def touch -> Int = 0\n",
    );
    w.commit("lib", Some("v0.2.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.2.0\" }}\n", w.url("lib"));
    w.app(
        &dep,
        "Lib.touch\nbegin\n  raise ArgumentError.new(\"app's message\")\nrescue ArgumentError => e\n  puts e.message\nend\n\
         e2: Exception = ArgumentError.new(\"x\")\nputs e2.message\n",
    );
    assert_eq!(w.ok("app", &["run"]), "app's message\nx\n");
    // The application's top-level extension overrides on a library's
    // class; one in a module body does not.
    w.app(
        &dep,
        "module EM2\n  def m(x: Int) -> String = \"app sub\"\nend\n\
         class AC < Lib::EB\n  def initialize; end\nend\n\
         class BC < Lib::EB\n  def initialize; end\nend\n\
         extension AC\n  include EM2\nend\n\
         module App\n  extension BC\n    include EM2\n  end\nend\n\
         puts Lib::Calc.via(AC.new), Lib::Calc.via(BC.new)\n",
    );
    assert_eq!(w.ok("app", &["run"]), "app sub\nbase\n");
    // A std class's own method overrides a library extension's module
    // method of its name, checked at the library's extension (#536).
    w.write(
        "lib/src/c.qz",
        "module OM\n  def hash -> String = \"om-hash\"\nend\nextension Object\n  include OM\nend\n",
    );
    w.commit("lib", Some("v0.3.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.3.0\" }}\n", w.url("lib"));
    w.app(&dep, "puts Lib.touch\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("`hash` returns Int but `Lib::OM#hash`, which it overrides as `Object#hash`, returns String")
            && err.contains("src/c.qz"),
        "{err}"
    );
}

#[test]
fn top_level_defs_are_cog_wide() {
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    // A library's top-level `def` is callable from its other files, and
    // has no `self` there either; not from the application.
    w.write(
        "lib/src/a.qz",
        "def helper(x: Int) -> Int = x * 10\ndef same(x: Object) -> Bool = x.equal?(x)\n",
    );
    w.write(
        "lib/src/b.qz",
        "module Calc\n  def self.k -> Int = helper(4) + ::helper(0)\n  def self.same -> Bool = ::same(self)\nend\n",
    );
    w.commit("lib", Some("v0.1.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib"));
    w.app(&dep, "p Lib::Calc.k, Lib::Calc.same\n");
    assert_eq!(w.ok("app", &["run"]), "40\ntrue\n");
    w.app(&dep, "p helper(1)\n");
    let err = w.fails("app", &["check"]);
    assert!(err.contains("undefined method `helper`"), "{err}");
    // The application's files see each other's.
    w.write("app/src/util.qz", "def twice(x: Int) -> Int = x * 2\n");
    w.app(
        &dep,
        "class C\n  def go -> Int = twice(5)\nend\np twice(2), C.new.go\n",
    );
    assert_eq!(w.ok("app", &["run"]), "4\n10\n");
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
        "def twice(x: String) -> String = x + x\n",
    );
    let warm = run(&cached);
    let off = run(&[("QUARZ_NO_CACHE", "1")]);
    assert!(!warm.0, "{}", warm.1);
    assert_eq!(warm, off);
}

#[test]
fn a_scripts_functions_reach_what_requires_it() {
    // A script sees the top-level `def`s of the files it requires, not
    // the other way round.
    let w = World::new();
    w.write(
        "s/lib.qz",
        "def helper(x: Int) -> Int = x * 10\ndef puts(s: String) -> Void = print(\"[lib] \", s, \"\\n\")\n",
    );
    w.write(
        "s/main.qz",
        "require_relative \"lib\"\nclass C\n  def go -> Int = helper(4)\nend\np helper(1), C.new.go\nputs \"hi\"\nputs 2\n::puts \"via\"\n::puts 3\nKernel.puts \"built-in\"\n",
    );
    assert_eq!(
        w.ok("s", &["run", "main.qz"]),
        "10\n40\n[lib] hi\n2\n[lib] via\n3\nbuilt-in\n"
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
        "def base -> Int = 100\ndef show(x: Object) -> String = \"obj\"\npublic def which -> String = show(1)\n",
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

/// docs/10 §2: `Cog.local.toml` holds a `[patch]` table of this machine's,
/// merged over `Cog.toml`'s at the root of the movement (the application,
/// or a library under `quarz test`), not locked, marked by `cog tree`.
#[test]
fn cog_local_toml_patches_at_the_root() {
    let w = World::new();
    w.libraries();
    let dep = format!(
        "Tomlz = {{ git = \"{}\", tag = \"v0.8.1\" }}\n",
        w.url("tomlz")
    );
    w.app(&dep, "puts Tomlz.parse(\" x \")\n");
    assert_eq!(w.ok("app", &["run"]), "Value(x)\n");
    // A local copy, patched by the local file alone.
    std::fs::create_dir_all(w.path("tomlz-dev/src")).unwrap();
    w.write(
        "tomlz-dev/Cog.toml",
        "[cog]\nname = \"tomlz\"\nversion = \"0.8.1\"\n",
    );
    w.write(
        "tomlz-dev/src/value.qz",
        "public def parse(text: String) -> String = \"local #{text.strip}\"\n",
    );
    let lock = std::fs::read_to_string(w.path("app/Cog.lock")).unwrap();
    w.write(
        "app/Cog.local.toml",
        "[patch]\nTomlz = { path = \"../tomlz-dev\" }\n",
    );
    assert_eq!(w.ok("app", &["run"]), "local x\n");
    // The lock is resolved without it: unchanged, and `--locked` holds.
    let read_lock = || std::fs::read_to_string(w.path("app/Cog.lock")).unwrap();
    assert_eq!(read_lock(), lock);
    assert_eq!(w.ok("app", &["run", "--locked"]), "local x\n");
    let tree = w.ok("app", &["cog", "tree"]);
    assert!(
        tree.contains("tomlz 0.8.1 (patched: ") && tree.contains(", Cog.local.toml; locked 0.8.1)"),
        "{tree}"
    );
    // A local copy that needs what the lock does not have: resolved for
    // the build, not written; refused with `--locked`.
    w.write(
        "extra/Cog.toml",
        "[cog]\nname = \"extra\"\nversion = \"1.0.0\"\n",
    );
    w.write("extra/src/e.qz", "E = 1\n");
    w.commit("extra", Some("v1.0.0"));
    w.write(
        "tomlz-dev/Cog.toml",
        &format!(
            "[cog]\nname = \"tomlz\"\nversion = \"0.8.1\"\n\n[dependencies]\nExtra = {{ git = \"{}\", tag = \"v1.0.0\" }}\n",
            w.url("extra")
        ),
    );
    assert_eq!(w.ok("app", &["run"]), "local x\n");
    assert_eq!(read_lock(), lock);
    let err = w.fails("app", &["run", "--locked"]);
    assert!(
        err.contains("a cog Cog.local.toml patches needs what Cog.lock does not have")
            && err.contains("(--locked)"),
        "{err}"
    );
    w.write(
        "tomlz-dev/Cog.toml",
        "[cog]\nname = \"tomlz\"\nversion = \"0.8.1\"\n",
    );
    // Over `Cog.toml`'s own entry for the same key.
    std::fs::create_dir_all(w.path("tomlz-other/src")).unwrap();
    w.write(
        "tomlz-other/Cog.toml",
        "[cog]\nname = \"tomlz\"\nversion = \"0.8.1\"\n",
    );
    w.write(
        "tomlz-other/src/value.qz",
        "public def parse(text: String) -> String = \"other\"\n",
    );
    w.app(
        &format!("{dep}\n[patch]\nTomlz = {{ path = \"../tomlz-other\" }}\n"),
        "puts Tomlz.parse(\" x \")\n",
    );
    assert_eq!(w.ok("app", &["run"]), "local x\n");
    std::fs::remove_file(w.path("app/Cog.local.toml")).unwrap();
    assert_eq!(w.ok("app", &["run"]), "other\n");
    let tree = w.ok("app", &["cog", "tree"]);
    assert!(!tree.contains("Cog.local.toml"), "{tree}");
    // A table other than `[patch]`, and a key that is no dependency.
    w.write(
        "app/Cog.local.toml",
        "[dependencies]\nX = { git = \"x\" }\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("Cog.local.toml holds a [patch] table only"),
        "{err}"
    );
    w.write(
        "app/Cog.local.toml",
        "[patch]\nNope = { path = \"../tomlz-dev\" }\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("[patch] `Nope` is not a dependency of this cog"),
        "{err}"
    );
    std::fs::remove_file(w.path("app/Cog.local.toml")).unwrap();
    // A library under `quarz test`: its own local file applies.
    w.write(
        "lib/Cog.toml",
        &format!("[cog]\nname = \"lib\"\nversion = \"0.1.0\"\n\n[dependencies]\n{dep}"),
    );
    w.write(
        "lib/src/lib.qz",
        "public def shown -> String = Tomlz.parse(\" y \").to_s\n",
    );
    w.write(
        "lib/test/lib_test.qz",
        "require \"test\"\nclass LibTest < Test::Case\n  def test_shown -> Void = assert_equal(\"local y\", Lib.shown)\nend\n",
    );
    w.write(
        "lib/Cog.local.toml",
        "[patch]\nTomlz = { path = \"../tomlz-dev\" }\n",
    );
    let out = w.ok("lib", &["test"]);
    assert!(out.contains("1 tests, 1 assertions, 0 failures"), "{out}");
}

/// A local copy that asks for a later version of a locked cog than the
/// lock holds builds with that version (resolved for the build alone),
/// and `--locked` refuses it.
#[test]
fn a_local_copy_asking_for_more_than_the_lock() {
    let w = World::new();
    w.write(
        "extra/Cog.toml",
        "[cog]\nname = \"extra\"\nversion = \"1.0.0\"\n",
    );
    w.write("extra/src/e.qz", "public def ver -> String = \"e1.0\"\n");
    w.commit("extra", Some("v1.0.0"));
    w.write(
        "extra/Cog.toml",
        "[cog]\nname = \"extra\"\nversion = \"1.1.0\"\n",
    );
    w.write("extra/src/e.qz", "public def ver -> String = \"e1.1\"\n");
    w.commit("extra", Some("v1.1.0"));
    let needs = |tag: &str| {
        format!(
            "[cog]\nname = \"base\"\nversion = \"0.1.0\"\n\n[dependencies]\nExtra = {{ git = \"{}\", tag = \"{tag}\" }}\n",
            w.url("extra")
        )
    };
    w.write("base/Cog.toml", &needs("v1.0.0"));
    w.write(
        "base/src/b.qz",
        "public def show -> String = \"git #{Extra.ver}\"\n",
    );
    w.commit("base", Some("v0.1.0"));
    w.write("base-dev/Cog.toml", &needs("v1.1.0"));
    w.write(
        "base-dev/src/b.qz",
        "public def show -> String = \"local #{Extra.ver}\"\n",
    );
    w.app(
        &format!(
            "Base = {{ git = \"{}\", tag = \"v0.1.0\" }}\n",
            w.url("base")
        ),
        "puts Base.show\n",
    );
    assert_eq!(w.ok("app", &["run"]), "git e1.0\n");
    let lock = std::fs::read_to_string(w.path("app/Cog.lock")).unwrap();
    w.write(
        "app/Cog.local.toml",
        "[patch]\nBase = { path = \"../base-dev\" }\n",
    );
    assert_eq!(w.ok("app", &["run"]), "local e1.1\n");
    assert_eq!(
        std::fs::read_to_string(w.path("app/Cog.lock")).unwrap(),
        lock
    );
    let err = w.fails("app", &["run", "--locked"]);
    assert!(
        err.contains("base asks for") && err.contains("at tag v1.1.0, the lock holds 1.0.0"),
        "{err}"
    );
}

/// docs/10 §6: inside a cog, `::Key` (and `cog::Key`) is its own
/// manifest's key, never the application's: a library reaches a key that
/// a nested declaration hides, `::` a standard class its own declaration
/// hides, and an application and a dependency with the same key for
/// different cogs each reach their own.
#[test]
fn a_cogs_absolute_names_are_its_own() {
    let w = World::new();
    for (repo, module) in [("inner", "Inner"), ("other", "Other")] {
        w.write(
            &format!("{repo}/Cog.toml"),
            &format!("[cog]\nname = \"{repo}\"\nversion = \"1.0.0\"\nmodule = \"{module}\"\n"),
        );
        w.write(
            &format!("{repo}/src/who.qz"),
            &format!("public def who -> String = \"{repo}\"\n"),
        );
        w.commit(repo, Some("v1.0.0"));
    }
    w.write(
        "lib/Cog.toml",
        &format!(
            "[cog]\nname = \"lib\"\nversion = \"1.0.0\"\n\n[dependencies]\nX = {{ git = \"{}\", tag = \"v1.0.0\" }}\n",
            w.url("inner")
        ),
    );
    // `Wrap::X` hides the key `X` inside `Wrap`.
    w.write(
        "lib/src/wrap.qz",
        "class Duration\nend\nmodule Wrap\n  class X\n  end\n  def self.a -> String = ::X.who\n  def self.b -> String = cog::X.who\n  def self.c -> String = X.name\n  def self.e -> String = ::Duration.name + \" \" + cog::Duration.name\nend\npublic def d -> String = ::X.who\n",
    );
    w.commit("lib", Some("v1.0.0"));
    let lib = format!("Lib = {{ git = \"{}\", tag = \"v1.0.0\" }}\n", w.url("lib"));
    // An application that does not list the key.
    // (`::Duration` is the standard class the cog's own hides.)
    w.app(
        &lib,
        "puts Lib::Wrap.a, Lib::Wrap.b, Lib::Wrap.c, Lib.d, Lib::Wrap.e\n",
    );
    assert_eq!(
        w.ok("app", &["run"]),
        "inner\ninner\nLib::Wrap::X\ninner\nDuration Lib::Duration\n"
    );
    // One whose key `X` is another cog: each `::X` is its own.
    w.app(
        &format!(
            "{lib}X = {{ git = \"{}\", tag = \"v1.0.0\" }}\n",
            w.url("other")
        ),
        "puts Lib::Wrap.a, Lib.d, ::X.who, X.who\n",
    );
    assert_eq!(w.ok("app", &["run"]), "inner\ninner\nother\nother\n");
}

/// `quarz cog init` keeps `Cog.local.toml` out of version control, once.
#[test]
fn cog_init_ignores_the_local_file() {
    let w = World::new();
    std::fs::create_dir_all(w.path("a")).unwrap();
    w.ok("a", &["cog", "init"]);
    assert_eq!(
        std::fs::read_to_string(w.path("a/.gitignore")).unwrap(),
        "/Cog.local.toml\n"
    );
    std::fs::create_dir_all(w.path("b")).unwrap();
    w.write("b/.gitignore", "/target");
    w.ok("b", &["cog", "init"]);
    assert_eq!(
        std::fs::read_to_string(w.path("b/.gitignore")).unwrap(),
        "/target\n/Cog.local.toml\n"
    );
    std::fs::create_dir_all(w.path("c")).unwrap();
    w.write("c/.gitignore", "Cog.local.toml\n");
    w.ok("c", &["cog", "init"]);
    assert_eq!(
        std::fs::read_to_string(w.path("c/.gitignore")).unwrap(),
        "Cog.local.toml\n"
    );
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
        "public def farewell(name: String) -> String = Greet::Greeter.new(name).bye + \" (#{cog.name} #{cog.version})\"\n",
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
    // Errors a user meets: a missing tag, a mistyped URL; and a fetched
    // cog's own `[patch]`, which is not read (a warning).
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
        out.ok
            && out.stderr.contains(
                "quarz: warning: pathy 1.0.0: its [patch] is not read; only the application's applies"
            ),
        "{}",
        out.stderr
    );
    w.write("app/src/main.qz", "puts Pathy::Z\n");
    let out = run("app", &["run"]);
    assert_eq!(out.stdout, "1\n", "{}", out.stderr);
    // (Once, when it is resolved: not again from the lock.)
    assert!(!out.stderr.contains("[patch]"), "{}", out.stderr);
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

#[test]
fn a_copy_of_the_application_is_no_dependency() {
    // docs/10 §4: `c1` names the application's own repository (an older
    // tag of it): a copy of the application would be loaded as a cog.
    let w = World::new();
    w.app("", "puts 1\n");
    w.commit("app", Some("v0.1.0"));
    publish(&w, "c1", "1.0.0", &[("App", "app", "v0.1.0")]);
    w.app(
        &format!("C1 = {{ git = \"{}\", tag = \"v1.0.0\" }}\n", w.url("c1")),
        "puts C1::V\n",
    );
    // Without a remote: the same name and module.
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("declares the application's name `app` and module `App`"),
        "{err}"
    );
    // With the application's remote: named as a copy of it.
    w.git("app", &["remote", "add", "origin", &w.url("app")]);
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("at 0.1.0 comes from the application's own repository (its origin)"),
        "{err}"
    );
    // Another cog that only shares the module stays allowed (§2, §6).
    w.write(
        "other/Cog.toml",
        "[cog]\nname = \"other\"\nversion = \"1.0.0\"\nmodule = \"App\"\n",
    );
    w.write("other/src/v.qz", "V = 2\n");
    w.commit("other", Some("v1.0.0"));
    w.app(
        &format!(
            "Other = {{ git = \"{}\", tag = \"v1.0.0\" }}\n",
            w.url("other")
        ),
        "puts Other::V\n",
    );
    assert_eq!(w.ok("app", &["run"]), "2\n");
}

#[test]
fn a_dependencys_functions_at_compile_time() {
    // docs/14 §8: a dependency cog's `public static def` function is a
    // `static(...)` call (`static(Key.f(1))`), and a block in
    // `static(...)` may call the functions of the cogs the file depends
    // on, not the application's own (not yet compiled).
    let w = World::new();
    w.write(
        "lib/Cog.toml",
        "[cog]\nname = \"lib\"\nversion = \"1.0.0\"\nmodule = \"Lib\"\n",
    );
    w.write(
        "lib/src/a.qz",
        "public static def triple(n: Int) -> Int = helper(n) * 3\npublic def plus(n: Int) -> Int = n + 10\ndef helper(n: Int) -> Int = n\nclass Runs\n  static def self.run(&: () -> Int) -> Int = yield\nend\n",
    );
    w.commit("lib", Some("v1.0.0"));
    let dep = format!("L = {{ git = \"{}\", tag = \"v1.0.0\" }}\n", w.url("lib"));
    w.app(
        &dep,
        "p static(L.triple(2)), static(L::Runs.run { L.plus(1) + L.triple(1) })\n",
    );
    let expected = "6\n14\n";
    assert_eq!(w.ok("app", &["run"]), expected);
    w.ok("app", &["build", "-o", "app.bin"]);
    let exe = Command::new(w.path("app/app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&exe.stdout), expected);
    // The application's own functions are not compiled yet.
    w.app(
        &dep,
        "def mine -> Int = 1\nstatic def own(n: Int) -> Int = n\np static(L::Runs.run { mine })\np static(own(1))\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains(
            "`mine` is a function of the application, not yet compiled when `static(...)` runs"
        ),
        "{err}"
    );
    assert!(
        err.contains("`own` is a `static def` of the application"),
        "{err}"
    );
}

#[test]
fn a_cogs_public_functions() {
    // docs/10 §6: `public def f` is called `Key.f` from the cogs that
    // depend on the cog (and `cog.f` inside it); a `def` is private to it.
    let w = World::new();
    w.write(
        "lib/Cog.toml",
        "[cog]\nname = \"lib\"\nversion = \"1.0.0\"\nmodule = \"Lib\"\n",
    );
    w.write(
        "lib/src/a.qz",
        "# Shouts `s`.\npublic def shout(s: String) -> String = helper(s) + \"!\"\npublic def shout(n: Int) -> String = \"#{n}!\"\npublic def tag -> String = \"tag #{TAG}\"\ndef helper(s: String) -> String = s.upcase\nTAG = \"lib\"\nclass Box\n  def go -> String = cog.shout(\"box\") + \" \" + shout(\"in\")\nend\n",
    );
    w.commit("lib", Some("v1.0.0"));
    let dep = format!("L = {{ git = \"{}\", tag = \"v1.0.0\" }}\n", w.url("lib"));
    w.app(
        &dep,
        "p L.shout(\"hi\"), L.shout(3), L.tag, L::Box.new.go\n",
    );
    let expected = "\"HI!\"\n\"3!\"\n\"tag lib\"\n\"BOX! IN!\"\n";
    assert_eq!(w.ok("app", &["run"]), expected);
    let out = w.ok("app", &["build", "-o", "app.bin"]);
    let _ = out;
    let exe = Command::new(w.path("app/app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&exe.stdout), expected);
    // A private function, and none of the name.
    w.app(&dep, "p L.helper(\"x\")\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("`helper` is private to cog `Lib`; declare it `public def helper`"),
        "{err}"
    );
    w.app(&dep, "p L.nope\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("no function `nope` in cog `Lib` (its public functions: shout, tag)"),
        "{err}"
    );
    // `quarz doc` lists them under the module, private ones left out.
    let doc = w.ok("lib", &["doc"]);
    assert!(
        doc.contains("Lib.shout") && doc.contains("Lib.tag") && !doc.contains("helper"),
        "{doc}"
    );
    let doc = w.ok("lib", &["doc", "Lib.shout"]);
    assert!(
        doc.contains("(function)") && doc.contains("Shouts s."),
        "{doc}"
    );
    // Called by name only: `&.` or a value of the module's type is no
    // function call (the call would not evaluate it).
    w.app(&dep, "p L&.shout(\"x\")\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("undefined method `shout` for Type[Lib]"),
        "{err}"
    );
    w.app(&dep, "p (puts(\"side\"); L).shout(\"y\")\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("undefined method `shout` for Type[Lib]"),
        "{err}"
    );
    // `quarz doc --check` resolves a link to one.
    w.write(
        "lib/src/c.qz",
        "# See `Lib.shout`.\npublic def linked -> Int = 1\n",
    );
    let out = w.quarz("lib", &["doc", "--check"]);
    assert!(!out.stderr.contains("names nothing"), "{}", out.stderr);
    // `def self.f` in a cog's file, a visibility line, and `protected def`,
    // are errors.
    // `--tree` shows `L.shout(...)` as the function call it is.
    w.app(&dep, "p L.shout(\"t\")\n");
    let tree = w.ok("app", &["check", "--tree"]);
    assert!(
        tree.contains("\"function\":true") || tree.contains("\"function\": true"),
        "{tree}"
    );
    // A public function cannot take a name of the module's own methods.
    w.write("lib/src/e.qz", "public def inspect -> String = \"x\"\n");
    let err = w.fails("lib", &["test"]);
    assert!(
        err.contains("a public function cannot be named like a method of `Cog`: `Lib.inspect` is `Object#inspect`"),
        "{err}"
    );
    w.write("lib/src/e.qz", "public def version -> String = \"x\"\n");
    let err = w.fails("lib", &["test"]);
    assert!(
        err.contains("a public function cannot be named like a method of `Cog`: `Lib.version` is `Cog#version`"),
        "{err}"
    );
    std::fs::remove_file(w.path("lib/src/e.qz")).unwrap();
    w.write("lib/src/d.qz", "def v -> Int = 1\npublic :v\n");
    let err = w.fails("lib", &["test"]);
    assert!(
        err.contains("a cog's file has no visibility lines"),
        "{err}"
    );
    std::fs::remove_file(w.path("lib/src/d.qz")).unwrap();
    w.write(
        "lib/src/b.qz",
        "def self.old -> Int = 1\nprotected def p -> Int = 2\n",
    );
    let err = w.fails("lib", &["test"]);
    assert!(err.contains("a cog's file declares no `def self.old`: a function other cogs call is written `public def old`"), "{err}");
    assert!(err.contains("`protected` does not apply to `p`"), "{err}");
}

#[test]
fn a_cog_is_a_dependency_or_a_dev_dependency() {
    let w = World::new();
    publish(&w, "t", "1.0.0", &[]);
    w.app(
        &format!("T = {{ git = \"{}\", tag = \"v1.0.0\" }}\n", w.url("t")),
        "puts T::V\n",
    );
    let err = w.fails("app", &["cog", "add", &w.url("t"), "--dev"]);
    assert!(err.contains("is already in [dependencies] as `T`: a cog is a dependency or a dev-dependency, not both"), "{err}");
    // A patch's path shows without `..`.
    w.write("app/Cog.toml", &format!("[cog]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies]\nT = {{ git = \"{}\", tag = \"v1.0.0\" }}\n\n[patch]\nT = {{ path = \"../t\" }}\n", w.url("t")));
    let tree = w.ok("app", &["cog", "tree"]);
    assert!(!tree.contains(".."), "{tree}");
}

#[test]
fn a_cogs_root_module_is_a_cog() {
    // docs/10 §6: a dependency's key (and `cog` inside it) is a `Cog`,
    // which tells the manifest's name and version and the module's name.
    let w = World::new();
    w.write(
        "lib/Cog.toml",
        "[cog]\nname = \"greet-more\"\nversion = \"1.1.0\"\nmodule = \"GreetMore\"\n",
    );
    w.write(
        "lib/src/a.qz",
        "public def info -> String = \"#{cog.name} #{cog.version} #{cog.module_name}\"\npublic def me -> Cog = cog\n",
    );
    w.commit("lib", Some("v1.1.0"));
    w.app(
        &format!("GM = {{ git = \"{}\", tag = \"v1.1.0\" }}\n", w.url("lib")),
        "p GM.info, GM.name, GM.version, GM.module_name\nx: Cog = GM\np x.name, x, GM.me.version\np cog.name, cog.module_name\n",
    );
    let expected = "\"greet-more 1.1.0 GreetMore\"\n\"greet-more\"\n\"1.1.0\"\n\"GreetMore\"\n\"greet-more\"\nGreetMore\n\"1.1.0\"\n\"app\"\n\"App\"\n";
    assert_eq!(w.ok("app", &["run"]), expected);
    let out = w.ok("app", &["build", "-o", "app.bin"]);
    let _ = out;
    let exe = Command::new(w.path("app/app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&exe.stdout), expected);
    // A `Cog` at run time too: through `Type`, in a type test, in a
    // `case` over a union.
    w.app(
        &format!("GM = {{ git = \"{}\", tag = \"v1.1.0\" }}\n", w.url("lib")),
        "def f(t: Type) -> String = t.name\np f(GM), f(Int), GM.is_a?(Cog), Int.is_a?(Cog), GM.class\ndef pick(n: Int) -> Cog | Int = n > 0 ? GM : n\nu = pick(1)\nr = case u\n    in Int then \"int\"\n    in Cog then \"cog \" + u.name\n    end\np r\n",
    );
    let expected = "\"greet-more\"\n\"Int\"\ntrue\nfalse\nCog\n\"cog greet-more\"\n";
    assert_eq!(w.ok("app", &["run"]), expected);
    w.ok("app", &["build", "-o", "app.bin"]);
    let exe = Command::new(w.path("app/app.bin")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&exe.stdout), expected);
    // A script's `cog` is its file's; an application's test files read
    // the application's.
    w.write(
        "s/my-tool_x.qz",
        "p cog.name, cog.version, cog.module_name\n",
    );
    assert_eq!(
        w.ok("s", &["run", "my-tool_x.qz"]),
        "\"my-tool_x\"\n\"0.0.0\"\n\"MyToolX\"\n"
    );
    w.app("", "puts 1\n");
    w.write(
        "app/test/meta_test.qz",
        "require \"test\"\nclass MetaTest < Test::Case\n  def test_meta -> Void = assert_equal(\"app 0.1.0 App\", \"#{cog.name} #{cog.version} #{cog.module_name}\")\nend\n",
    );
    let out = w.ok("app", &["test"]);
    assert!(out.contains("1 tests, 1 assertions, 0 failures"), "{out}");
    std::fs::remove_file(w.path("app/test/meta_test.qz")).unwrap();
    w.app("", "x = Cog.new\nclass MyCog < Cog\nend\n");
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("Cog") && err.contains("cannot inherit from `Cog`"),
        "{err}"
    );
}

#[test]
fn a_tag_and_a_manifest_that_disagree_warn() {
    // The tag decides a cog's version; a manifest writing another one is
    // said so (its author may not know), but nothing fails.
    let w = World::new();
    w.write("t/Cog.toml", "[cog]\nname = \"t\"\nversion = \"1.0.0\"\n");
    w.write("t/src/v.qz", "V = 1\n");
    let tagged = w.commit("t", Some("v1.0.1"));
    let warning =
        "warning: t's Cog.toml says version = \"1.0.0\", but its tag v1.0.1 makes it 1.0.1";
    // By the tag, and by `rev` on the tagged commit.
    for dep in [
        format!("T = {{ git = \"{}\", tag = \"v1.0.1\" }}\n", w.url("t")),
        format!("T = {{ git = \"{}\", rev = \"{tagged}\" }}\n", w.url("t")),
    ] {
        w.app(&dep, "puts T::V\n");
        let _ = std::fs::remove_file(w.path("app/Cog.lock"));
        let out = w.quarz("app", &["run"]);
        assert!(out.ok && out.stderr.contains(warning), "{}", out.stderr);
    }
    // A tag with build metadata decides as well; a tag without `v` is
    // no version tag, and agrees with nothing.
    w.git("t", &["tag", "v1.0.1+b1", &tagged]);
    w.git("t", &["tag", "1.0.0", &tagged]);
    w.app(
        &format!("T = {{ git = \"{}\", tag = \"v1.0.1+b1\" }}\n", w.url("t")),
        "puts T::V\n",
    );
    let _ = std::fs::remove_file(w.path("app/Cog.lock"));
    let out = w.quarz("app", &["run"]);
    assert!(
        out.ok
            && out
                .stderr
                .contains("warning: t's Cog.toml says version = \"1.0.0\", but its tag v1.0.1"),
        "{}",
        out.stderr
    );
    // Another version tag on the commit that agrees silences it.
    w.git("t", &["tag", "v1.0.0", &tagged]);
    w.app(
        &format!("T = {{ git = \"{}\", rev = \"{tagged}\" }}\n", w.url("t")),
        "puts T::V\n",
    );
    let _ = std::fs::remove_file(w.path("app/Cog.lock"));
    let out = w.quarz("app", &["run"]);
    assert!(out.ok && !out.stderr.contains("warning"), "{}", out.stderr);
    // A tag that agrees, a manifest with no `version`, and a commit no
    // tag names, say nothing.
    w.write("t/Cog.toml", "[cog]\nname = \"t\"\nversion = \"1.0.2\"\n");
    w.commit("t", Some("v1.0.2"));
    w.write("t/Cog.toml", "[cog]\nname = \"t\"\n");
    w.commit("t", Some("v1.0.3"));
    w.write("t/Cog.toml", "[cog]\nname = \"t\"\nversion = \"9.0.0\"\n");
    w.write("t/src/w.qz", "W = 2\n");
    let later = w.commit("t", None);
    for dep in [
        format!("T = {{ git = \"{}\", tag = \"v1.0.2\" }}\n", w.url("t")),
        format!("T = {{ git = \"{}\", tag = \"v1.0.3\" }}\n", w.url("t")),
        format!("T = {{ git = \"{}\", rev = \"{later}\" }}\n", w.url("t")),
    ] {
        w.app(&dep, "puts T::V\n");
        let _ = std::fs::remove_file(w.path("app/Cog.lock"));
        let out = w.quarz("app", &["run"]);
        assert!(
            out.ok && !out.stderr.contains("warning"),
            "{dep}: {}",
            out.stderr
        );
    }
}

#[test]
fn the_author_sees_a_tag_that_disagrees_with_the_manifest() {
    // `quarz test` (and `check`) in a cog whose checked-out commit has a
    // version tag that is not its manifest's `version`: a warning for its
    // author, before anyone depends on the tag.
    let w = World::new();
    w.write("t/Cog.toml", "[cog]\nname = \"t\"\nversion = \"1.0.0\"\n");
    w.write("t/src/v.qz", "V = 1\n");
    w.write(
        "t/test/v_test.qz",
        "require \"test\"\nclass VTest < Test::Case\n  def test_v -> Void = assert_equal(1, T::V)\nend\n",
    );
    let warning = "warning: HEAD is tagged v1.0.1 but its Cog.toml says version = \"1.0.0\"";
    // Not tagged yet: nothing.
    w.commit("t", None);
    let out = w.quarz("t", &["test"]);
    assert!(out.ok && !out.stderr.contains("warning"), "{}", out.stderr);
    w.git("t", &["tag", "v1.0.1"]);
    let out = w.quarz("t", &["test"]);
    assert!(out.ok && out.stderr.contains(warning), "{}", out.stderr);
    // The manifest compared is the one committed there, which is what
    // those who depend on the tag get: an edit not committed changes
    // nothing either way.
    w.write("t/Cog.toml", "[cog]\nname = \"t\"\nversion = \"1.0.1\"\n");
    let out = w.quarz("t", &["test"]);
    assert!(out.stderr.contains(warning), "{}", out.stderr);
    w.write("t/Cog.toml", "[cog]\nname = \"t\"\nversion = \"1.0.0\"\n");
    // Another version tag on the commit that agrees, or no `version`
    // written: nothing.
    w.git("t", &["tag", "v1.0.0"]);
    let out = w.quarz("t", &["test"]);
    assert!(!out.stderr.contains("warning"), "{}", out.stderr);
    w.git("t", &["tag", "-d", "v1.0.0"]);
    w.write("t/Cog.toml", "[cog]\nname = \"t\"\n");
    let out = w.quarz("t", &["test"]);
    assert!(!out.stderr.contains("warning"), "{}", out.stderr);
    // A cog not committed in the (tagged) repository it lies in: nothing.
    w.write(
        "t/inner/Cog.toml",
        "[cog]\nname = \"inner\"\nversion = \"0.1.0\"\n",
    );
    w.write("t/inner/src/main.qz", "puts 1\n");
    let out = w.quarz("t/inner", &["check"]);
    assert!(out.ok && !out.stderr.contains("warning"), "{}", out.stderr);
    // An application's `quarz check` says it too.
    w.write("a/Cog.toml", "[cog]\nname = \"a\"\nversion = \"0.1.0\"\n");
    w.write("a/src/main.qz", "puts 1\n");
    w.commit("a", Some("v0.2.0"));
    let out = w.quarz("a", &["check"]);
    assert!(
        out.ok
            && out.stderr.contains(
                "warning: HEAD is tagged v0.2.0 but its Cog.toml says version = \"0.1.0\""
            ),
        "{}",
        out.stderr
    );
}

/// `quarz doc --html` links a dependency's names to its `documentation`
/// (#448), the standard library's to api.quarz.dev or `--std-url`, and
/// the documented cog's locations to its `repository` at `--source-rev`
/// (#449).
#[test]
fn doc_links_other_cogs_the_std_and_the_source() {
    let w = World::new();
    w.write(
        "dep/Cog.toml",
        "[cog]\nname = \"dep\"\nversion = \"1.0.0\"\ndocumentation = \"https://dep.example/api/\"\nrepository = \"https://github.com/o/dep\"\n",
    );
    w.write(
        "dep/src/thing.qz",
        "# A thing.\nclass Thing\n  # Goes.\n  def go -> String = \"go\"\nend\n\n# A base.\nclass Base\nend\n\n# Colors.\nenum Color\n  variant Red\nend\n\n# :nodoc:\nclass Hidden\nend\n\n# A point.\ndata Point = (x: Int)\n",
    );
    w.commit("dep", Some("v1.0.0"));
    w.write(
        "lib/Cog.toml",
        &format!(
            "[cog]\nname = \"mylib\"\nversion = \"0.1.0\"\nrepository = \"https://github.com/me/mylib\"\n\n[dependencies]\nDep = {{ git = \"{}\", tag = \"v1.0.0\" }}\n",
            w.url("dep")
        ),
    );
    w.write(
        "lib/src/user.qz",
        "# Uses `Dep::Thing#go` and `String`; `Dep::Color::Red`, `Dep::Hidden`, `Dep::Point.new`.\nclass User < Dep::Base\n  # Makes one.\n  def make(name: String) -> Dep::Thing = Dep::Thing.new\nend\n",
    );
    w.ok(
        "lib",
        &["doc", "--html", "-o", "site", "--source-rev", "abc123"],
    );
    let page = std::fs::read_to_string(w.path("lib/site/Mylib--User.html")).unwrap();
    for href in [
        "https://dep.example/api/Dep--Thing.html",
        "https://dep.example/api/Dep--Thing.html#method-go",
        "https://dep.example/api/Dep--Base.html",
        "https://api.quarz.dev/String.html",
        "https://github.com/me/mylib/blob/abc123/src/user.qz#L2",
        "https://github.com/me/mylib/blob/abc123/src/user.qz#L4",
        // A variant on its enum's page; a data type's `new` (no member
        // of its page) on the type's page.
        "https://dep.example/api/Dep--Color.html#variant-Red",
        "https://dep.example/api/Dep--Point.html",
    ] {
        assert!(
            page.contains(&format!("href=\"{href}\"")),
            "no {href} in\n{page}"
        );
    }
    // A `:nodoc:` class has no page there.
    assert!(!page.contains("Dep--Hidden"), "{page}");
    w.ok(
        "lib",
        &[
            "doc",
            "--html",
            "-o",
            "site2",
            "--std-url",
            "http://localhost:8000/",
        ],
    );
    let page = std::fs::read_to_string(w.path("lib/site2/Mylib--User.html")).unwrap();
    assert!(
        page.contains("href=\"http://localhost:8000/String.html\""),
        "{page}"
    );
    // Without a repository, origin, nor a documentation: plain text.
    w.write(
        "lib/Cog.toml",
        &format!(
            "[cog]\nname = \"mylib\"\nversion = \"0.1.0\"\n\n[dependencies]\nDep = {{ git = \"{}\", tag = \"v1.0.0\" }}\n",
            w.url("dep")
        ),
    );
    w.ok("lib", &["doc", "--html", "-o", "site3"]);
    let page = std::fs::read_to_string(w.path("lib/site3/Mylib--User.html")).unwrap();
    assert!(!page.contains("github.com"), "{page}");
}

#[test]
fn a_type_value_reaches_a_conformance_from_another_cogs_extension() {
    // #504: a library's extension makes its class conform to its module,
    // class methods included (the extension is active in the library's
    // files only); the application gets the class as a `Type[Parsable]`
    // value and calls the module's class methods through it: the abstract
    // one runs the extension's implementation, the default the module's,
    // interpreted and compiled (dispatch at run time is global).
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    w.write(
        "lib/src/parsable.qz",
        "module Parsable\n  abstract def self.parse(s: String) -> Self\n  def self.describe -> String = \"parsable #{name}\"\n  def parsed? -> Bool = true\nend\n",
    );
    w.write(
        "lib/src/num.qz",
        "class Num\n  @v: Int\n  def initialize(@v: Int); end\n  def to_s -> String = \"Num(#{@v})\"\nend\n",
    );
    w.write(
        "lib/src/ext.qz",
        "extension Num\n  include Parsable\n  def self.parse(s: String) -> Self = new(s.to_i)\nend\n",
    );
    w.write(
        "lib/src/registry.qz",
        "module Registry\n  def self.parser -> Type[Parsable] = Num\n  def self.via(t: Type[Num], s: String) -> String\n    u: Type[Parsable] = t\n    u.parse(s).to_s\n  end\nend\n",
    );
    w.commit("lib", Some("v0.1.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib"));
    w.app(
        &dep,
        "t = Lib::Registry.parser\nputs t.parse(\"5\"), t.describe\nclass Sub < Lib::Num\n  def self.parse(s: String) -> Self = new(99)\nend\nputs Lib::Registry.via(Sub, \"6\"), Sub.parse(\"6\")\n",
    );
    // (A subclass in the application: the library's witness runs for it
    // through `Type[Parsable]`, its own `parse` on itself, #504.)
    let expected = "Num(5)\nparsable Lib::Num\nNum(6)\nNum(99)\n";
    assert_eq!(w.ok("app", &["run"]), expected);
    w.ok("app", &["build", "-o", "app.bin"]);
    let run = std::process::Command::new(w.path("app/app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}

#[test]
fn an_extension_cannot_include_what_a_library_superclass_includes() {
    // #504: `Base` in a library includes `M` itself; an application's
    // extension of a subclass cannot include it again.
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    w.write(
        "lib/src/base.qz",
        "module M\n  def self.describe -> String = \"M\"\nend\nclass Base\n  include M\nend\n",
    );
    w.commit("lib", Some("v0.1.0"));
    let dep = format!("Lib = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib"));
    w.app(
        &dep,
        "class A < Lib::Base\nend\nextension A\n  include Lib::M\nend\n",
    );
    let err = w.fails("app", &["check"]);
    assert!(
        err.contains("`A` already includes `Lib::M` (through `Lib::Base`'s `include`): an extension cannot include it again"),
        "{err}"
    );
}

#[test]
fn witness_matrix_across_cogs() {
    // The cross-cog column of the #504 witness matrix (the other columns:
    // the `witness_matrix_*.qz` fixtures): a library's extensions make its
    // classes conform to `M`, one per witness source; the application's
    // subclasses of them reach the same witnesses through the library's
    // `Type[M]` (the extensions are not active in the application), run
    // and built.
    let w = World::new();
    w.write("lib/Cog.toml", "[cog]\nname = \"lib\"\n");
    w.write(
        "lib/src/m.qz",
        "module M\n  def self.d -> String = \"M\"\nend\nmodule N\n  include M\n  def self.d -> String = \"N\"\nend\nclass B\n  def initialize; end\n  def self.d -> String = \"sup\"\nend\n",
    );
    w.write(
        "lib/src/x.qz",
        "class XExt\n  def initialize; end\nend\nextension XExt\n  include M\n  def self.d -> String = \"ext\"\nend\nclass XOwn\n  def initialize; end\n  def self.d -> String = \"own\"\nend\nextension XOwn\n  include M\nend\nclass XSup < B\nend\nextension XSup\n  include M\nend\nclass XN\n  def initialize; end\nend\nextension XN\n  include N\nend\nclass XDef\n  def initialize; end\nend\nextension XDef\n  include M\nend\n",
    );
    w.write(
        "lib/src/reg.qz",
        "module Reg\n  def self.ext(t: Type[XExt]) -> String\n    u: Type[M] = t\n    u.d\n  end\n  def self.own(t: Type[XOwn]) -> String\n    u: Type[M] = t\n    u.d\n  end\n  def self.sup(t: Type[XSup]) -> String\n    u: Type[M] = t\n    u.d\n  end\n  def self.n(t: Type[XN]) -> String\n    u: Type[M] = t\n    u.d\n  end\n  def self.default(t: Type[XDef]) -> String\n    u: Type[M] = t\n    u.d\n  end\nend\n",
    );
    w.commit("lib", Some("v0.1.0"));
    let dep = format!("L = {{ git = \"{}\", tag = \"v0.1.0\" }}\n", w.url("lib"));
    w.app(
        &dep,
        "class SExt < L::XExt\nend\nclass SOwn < L::XOwn\nend\nclass SSup < L::XSup\nend\nclass SN < L::XN\nend\nclass SDef < L::XDef\nend\nputs L::Reg.ext(L::XExt), L::Reg.ext(SExt)\nputs L::Reg.own(L::XOwn), L::Reg.own(SOwn)\nputs L::Reg.sup(L::XSup), L::Reg.sup(SSup)\nputs L::Reg.n(L::XN), L::Reg.n(SN)\nputs L::Reg.default(L::XDef), L::Reg.default(SDef)\n",
    );
    let expected = "ext\next\nown\nown\nsup\nsup\nN\nN\nM\nM\n";
    assert_eq!(w.ok("app", &["run"]), expected);
    w.ok("app", &["build", "-o", "app.bin"]);
    let run = std::process::Command::new(w.path("app/app.bin"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected);
}
