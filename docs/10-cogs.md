# Cogs: Packages

日本語版: [10-cogs.ja.md](10-cogs.ja.md)

A Quarz package is a **cog**: a git repository with a `Cog.toml` at its root, fetched as source and compiled with the program that uses it. The program being built, with every cog it brings in, is a **movement**. There is no registry and nothing is distributed as a binary: a cog is named by the URL of its repository, and the lock file pins it to one commit. A cog is used without `require`: naming it in the manifest makes its module visible.

This is the design, and it is implemented (crates `quarz-cog` for manifests, locks, resolution and fetching; `quarz-types` for loading and checking a movement) except where a paragraph says *not yet*. Scripts keep `require_relative` ([01-syntax.md](01-syntax.md) §2).

## 1. Vocabulary and Shape

```
httpx/                      a cog
├── Cog.toml                its manifest
├── Cog.lock                its lock file (committed by an application, optional for a library)
├── src/                    every .qz file under here is part of the cog
│   ├── client.qz
│   ├── response.qz
│   └── errors.qz
└── test/
```

- A cog is identified by its git URL (`https://github.com/foo/httpx`, `ssh://git@host/path`); a `subdir` picks a cog inside a larger repository (a monorepo).
- A cog is the whole of `src/`, as a Go package is the whole of its directory: every `.qz` file under it is loaded, and the files refer to one another by name, with no `require_relative` between them. How the files are named and nested is the author's business.
- Versions are git tags named `vMAJOR.MINOR.PATCH` (semantic versioning). A commit that no tag names gets a *pseudo-version* (§4).
- An application is a cog too (the root of its movement), with its statements in `src/main.qz` (§6). A single file run with `quarz run file.qz` and no `Cog.toml` is a *script*: it has no dependencies, and `require_relative` loads its neighbors.

## 2. The Manifest: `Cog.toml`

The manifest is named after what it describes, one cog, as Crystal's `shard.yml` is; `cog.name` and `cog.version` (§6) read from it.

```toml
[cog]
name    = "webkit"
version = "0.3.1"
module  = "Webkit"      # the module the cog's declarations live in; default: `name` in CamelCase
quarz   = "0.1"         # the language version it is written for

[dependencies]
# key = the module the cog is seen as; `git` is required, with at most one of tag/rev/branch
Httpx  = { git = "https://github.com/foo/httpx", tag = "v1.4.0" }
Tomlz  = { git = "https://github.com/bar/tomlz", rev = "3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e" }
Utils  = { git = "https://github.com/baz/mono",  tag = "v2.0.0", subdir = "libs/utils" }
AUtil  = { git = "https://github.com/a/util",    tag = "v2.0.0" }    # both declare `module = "Util"`:
BUtil  = { git = "https://github.com/b/util",    tag = "v1.1.0" }    # the keys tell them apart (§6)
DevLib = { git = "ssh://git@internal/devlib",    branch = "main" }   # development only

[dev-dependencies]          # for `quarz test` and the cog's own development, not for its users
Spec = { git = "https://github.com/quarz-lang/spec", tag = "v0.2.0" }

[patch]                     # local replacements while developing several cogs together; never locked
Httpx = { path = "../httpx" }
```

- The key of a dependency is the constant under which this cog sees it: a module name, so it is capitalized. When it equals the module the dependency declares (`[cog] module`), nothing more is said; when it differs, it is an alias of that module (§6). A key that is the name of a built-in or standard library module (`JSON`, `Socket`, `Array`) is an error.
- `tag`, `rev` and `branch` say where to look; the commit actually used is recorded in the lock file (§3). A `branch` moves with every `quarz cog update`, so it is for development; `quarz cog add` writes a `tag` or `rev`, never a `branch`.
- Dependency keys are local to the cog that declares them: another cog may see the same repository under another name.
- A cog fetched from elsewhere may not name a repository on this machine (a `file://` URL or a path): only the application, a patched cog and a cog that is itself local may.
- `quarz` is the minimum language version the cog needs (as `go 1.21` in a `go.mod` and `minimum_zig_version` in Zig); a program refuses to build with an older `quarz`.
- A cog with `extern "C"` declarations will need to name the C libraries to link; `[cog] link = ["ssl"]` is reserved for that and not designed further here.

## 3. The Lock File: `Cog.lock`

`Cog.lock` is generated, and an application commits it; a library may commit it for its own development, but its users ignore it (as Cargo and Bundler do).

```toml
version = 1
inputs  = "h1:p0Xv…"   # the resolution's inputs (§4)

[[cog]]
name    = "httpx"                                    # the cog's own `[cog] name`
module  = "Httpx"
source  = "git+https://github.com/foo/httpx"
version = "1.4.0"
rev     = "9b1c4e2f0a7d3b6c8e5f1a2b3c4d5e6f7a8b9c0d"
hash    = "h1:Zk3q…"
dependencies = ["git+https://github.com/bar/tomlz"]

[[cog]]
name    = "tomlz"
module  = "Tomlz"
source  = "git+https://github.com/bar/tomlz"
version = "0.8.1-0.20261023141500.3f2a9c1e0b4d"       # a pseudo-version: no tag names the commit
rev     = "3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e"
hash    = "h1:Q8ua…"
dependencies = []
```

- A cog is identified by its `source` (the URL, with the `subdir` when there is one); the keys the manifests use for it are not recorded, since each manifest has its own. Two spellings of one source are one cog: a `subdir` of `a`, `a/` or `./a`, and URLs that differ only in the case of the scheme and host or in a trailing `/` or `.git`.
- `inputs` is a digest of the dependency tables of the manifests that can change: the application's and the patched cogs' (every other manifest is pinned by its commit). The lock is the resolution of those inputs: while the digest matches, it is used as it is; when the manifests list other dependencies, it is resolved again.
- `rev` is the key for fetching, `hash` the key for verification: a hash of the cog's files at that commit (`Cog.toml` and everything under `src/`): one line per file in path order, its SHA-256 in hex, two spaces and its path, and the base64 of the SHA-256 of those lines (as Go's module hashes). The two are kept apart because a git commit id is a SHA-1 of the repository's history, not of the files Quarz compiles: after fetching, a tree whose hash differs from the lock (a rewritten history, a force-pushed tag, a tampered mirror) is refused. The `h1:` prefix names the algorithm so it can change.
- The lock lists only what the resolution chose: one entry per cog, whatever the manifests asked for. `[patch]` entries are not recorded.

## 4. Version Resolution

Resolution follows Go's *minimal version selection*: every manifest in the graph names, for each dependency, the lowest version it accepts (the one its `tag` or `rev` denotes), and the version chosen for a cog is the highest of the lowest versions asked for. There is no search and no solver, the result is a function of the manifests alone, and the lock file records it rather than steering it.

- **One version per cog.** A cog's declarations live in one module (§6) and a class is one class, so the same cog cannot appear twice in a movement. When the chosen version does not share its major with every requirement (its minor, while the major is `0`), the resolution fails and names the two requirements; the application pins one side with `rev` or replaces it with `[patch]`.
- **A `rev` in the application's own manifest pins.** Elsewhere a `rev` is a lower bound like any other, but in the movement's manifest it is also the ceiling: a dependency that asks for a newer version is an error, not a silent upgrade.
- **Pseudo-versions.** A commit that no tag names is ordered as `1.4.1-0.20261023141500.3f2a9c1e0b4d`: the patch after the highest version tag among its ancestors (`0.0.0` when there is none; a tag that is not a semantic version does not count, nor one that the repository's own listing does not show on the same commit), a `0` so that it sorts below any real pre-release of that patch, the commit's time in UTC, and twelve hex digits of its id. Semantic versioning's precedence rules then order it between the tag and the next release, as Go's pseudo-versions do.
- `quarz cog update [Key]` re-resolves and rewrites the lock. Otherwise a locked version moves only when the dependencies a manifest lists change (the application's or a patched cog's): the lock is then resolved again as a whole, and a `branch` dependency elsewhere may move with it. `quarz run`, `quarz build` and `quarz check` use the lock when it is present and was resolved from the current manifests, resolve and write it when it is absent or was not, and fail with `--locked` when it would have to change (as a lock written before `inputs` existed does once).

## 5. Fetching, Cache and Vendoring

- The cache is `$QUARZ_CACHE`, else `$XDG_CACHE_HOME/quarz`, else `~/.cache/quarz`. Repositories are mirrored under `~/.cache/quarz/git/<host>/<name>-<digest of the URL>.git` (a bare clone, one per URL: the host is read from the URL's authority only), and only the commit the lock names is fetched (`git fetch --depth 1 origin <rev>`), so a large history costs nothing. Resolving a branch or a `rev` that no tag names fetches the commit's history and tags once, to find the tags for its pseudo-version; the mirror's tags are made the remote's, deleted ones included. Creating a mirror and fetching into it hold a lock file, so several `quarz` processes can share the cache.
- The cog's `Cog.toml` and `src/` are checked out, read-only, into `~/.cache/quarz/src/<name>-<first 12 hex digits of rev>/` (with a digest of the `subdir` after it for a cog in a subdirectory) and verified against the lock's `hash` before anything is compiled. A tree holding a symbolic link (its target would be outside what the hash covers), anything but files and directories, or a file name that is not UTF-8 or holds a control character, is refused. Each process writes into a directory of its own and renames it into place. The directory never changes once written: a pinned commit is immutable, so the type-check results and the `.qzi` of a cog ([05-execution.md](05-execution.md) §2) can be cached by `(hash, quarz version, back end)` and never invalidated. Loading a whole cog rather than the files a program names costs type checking once per commit, not once per run; `quarz build` drops what the program does not reach.
- `quarz cog vendor` copies every locked cog into `vendor/<name>/` next to the manifest (into a new directory that replaces `vendor/` only once it is complete); when that directory exists, nothing is fetched. `--offline` resolves from the cache and `vendor/` only.
- Private repositories use git's own authentication (SSH keys, credential helpers); Quarz adds no credential handling of its own.

## 6. Namespaces: a Cog Is a Module

The declarations of a cog never reach the top level. Its files are the body of one module, the one `[cog] module` names (by default the cog's name in CamelCase), as if each file were written inside `module Httpx … end`:

```ruby
# httpx/src/client.qz          → everything here is inside `Httpx`
class Client
  def get(url: String) -> Response … end     # `Response` is in response.qz: no require
end

def self.get(url: String) -> Response        # a module function: `Httpx.get`
  Client.new.get(url)
end

def helper(…) … end                          # a top-level `def` stays private to its file, as always
```

The user of the cog names it in `[dependencies]` and sees it under the key:

```ruby
# src/main.qz of the application; `Httpx = { git = … }` in its Cog.toml
res = Httpx.get("https://example.com")
client = Httpx::Client.new
```

- **No `require`.** Declarations are hoisted across every loaded file, so `require` only ever chose which files are loaded and in which order their statements run; the manifest answers the first, and §6's rule on statements the second. `require "json"` is accepted as a no-op, as `require "time"` is today, so Ruby code moves over unchanged: the standard library's modules (`JSON`, `Socket`, …) are visible without it. `require_relative` remains for scripts, which have no manifest.
- **A cog has no statements.** Its files hold declarations and constants only; a statement at the top level of a cog file is an error. Loading a cog therefore has no effect, and there is no order of loading to define. The application's statements are in `src/main.qz`, the one file of a movement that may have them, and they run after every constant is initialized.
- **Constants are initialized in dependency order.** Each constant is initialized at its first use, so the constants an initializer reads come first and a constant used by its own initializer raises `RuntimeError` ([01-syntax.md](01-syntax.md) §8); no load order is needed for that either.
- **The root module is an ordinary module** and follows the ordinary rules: it cannot be reopened (no `module Httpx` anywhere, inside or outside the cog, since classes and modules are never reopened), including or extending it warns as including any namespace module does ([01-syntax.md](01-syntax.md) §6), and `extension`s a cog defines take effect only where a file says `using Httpx::StringExt`. A cog cannot monkey-patch its users.
- **The key is the name, and an alias when it differs.** The key under which a manifest lists a cog is bound, in that cog's scope, to the dependency's root module, as a constant `AUtil = Util` would be. When two dependencies declare the same `module`, their keys tell them apart; a key equal to the declared module is the common case and says nothing. The dependency's own code is unaffected, so its `.qzi` is shared by every user whatever they call it. (Swift PM's `moduleAliases`, .NET's `extern alias` and Cabal's `mixins` solve the same collision the same way.)
- **The dependencies of a cog are resolved by its own manifest.** When `httpx`'s code says `Tomlz::Parser`, the name is `httpx`'s key for that dependency, whatever the application calls it. A class is the same class under every name, so a `Tomlz::Value` built by `httpx` and one built by the application have one type.
- The application is the root cog of its movement, and its declarations are not wrapped: `src/main.qz` and its neighbors are at the top level, as a script is today.

### The `cog` keyword

Inside a cog its own declarations are visible by their bare names, so the root is rarely named. For the cases where it must be, `cog` is a keyword that denotes the current cog's root module (Rust's `crate`):

```ruby
cog::Response        # the root's `Response`, when a nested scope shadows the name
cog.get(url)         # the root's module function, from inside a class
cog.name             # "httpx", from the manifest
cog.version          # "1.4.0", from the manifest: no second copy in the source
```

In the application and in a script, `cog` is the top level; `cog.name` is then the name in the application's manifest, or the file's name without its extension for a script, and `cog.version` is its version or `"0.0.0"`. `cog` is a keyword rather than a predefined constant so that no cog can shadow it, and it is not spelled `::` because Ruby's `::Foo` (the top level) is still needed to reach a standard class that the cog's own declarations hide.

## 7. Commands

| Command | Behavior |
|---|---|
| `quarz cog init` | Write a `Cog.toml` for the current directory |
| `quarz cog add <git-url> [--tag v1.4.0 \| --rev <hash>] [--as Key] [--subdir dir] [--dev]` | Add a dependency and resolve; the key is the module the cog declares unless `--as` says otherwise, and a `--tag` or the default branch's head is recorded as a `tag` or `rev` |
| `quarz cog update [Key]` | Re-resolve (one cog or all) and rewrite the lock |
| `quarz cog fetch` | Fetch and verify everything the lock names, compiling nothing |
| `quarz cog vendor` | Copy the locked cogs into `vendor/` |
| `quarz cog tree` | Print the resolved dependency graph |
| `quarz cog outdated` | Show, for each cog, the newest tag beyond the locked version |
| `quarz cog verify` | Check the cache and `vendor/` against the lock's hashes |
| `quarz run`/`build`/`check`/`ir` [`--locked`] [`--offline`] [TARGET] | TARGET is the application's directory, its `src/main.qz`, or nothing for the application around the current directory (`quarz run -- ARGS`); a `.qz` file elsewhere is a script. Use the lock, or resolve and write it; `--locked` fails instead of writing, `--offline` fetches nothing. `quarz build` writes the executable next to the manifest, named after the cog, unless `-o` says otherwise |

## 8. Design Notes

- **Git, not a registry.** A registry needs a server, an account system and a policy for names; a URL needs none of these and leaves the publisher in control of their repository. Discovery (a searchable index of known cogs) can be added later without changing how a cog is named or fetched, as Go's `pkg.go.dev` was.
- **Source, not binaries.** A cog is compiled on the user's machine with the user's `quarz`; the fetched tree is verified by content, and the cache keyed by content keeps the cost to the first build. Separate compilation ([05-execution.md](05-execution.md) §2) is what makes this cheap.
- **A commit, not a version, is what the lock pins.** Tags move; a commit does not. The version is derived from the tag for ordering, and the content hash is checked for safety.
- **Minimal version selection over a solver.** Cargo's and Bundler's resolvers can pick any version that satisfies the constraints, so the result depends on the resolver and the lock file is the only record of it. With MVS the manifests determine the result, the lock is a cache of it, and a dependency upgrade never lowers a version. The price is that a cog cannot say "below 2.0" except by the major-version rule; Go pays the same price.
- **A directory, not a list of files, and no `require`** (Go). The manifest already names every cog a program may use, and hoisting already makes every loaded declaration visible, so a `require` would repeat the manifest; dropping it also removes the only way a library could run code when loaded. File names stay free: unlike Rails' Zeitwerk, nothing maps a constant to a path, in line with matz's view that namespaces and file names are better kept apart (「モジュールによる名前空間とライブラリのファイル名は分離してた方が自由度が高い」, [ruby-list:7885]).
- **The key is the alias.** Once `require` is gone the dependency's key has no other job, so it is the name the cog is seen under, and renaming is editing the key: no separate `namespace` field, and no rewrap of the cog's source under another module, which would make its type-check results depend on every user's choice of name and break cross-cog references.
- **Declarations are wrapped from the start.** Ruby's `Namespace` (Feature #19744) has to load libraries written for the top level into a namespace after the fact, which matz called hard ("もともとトップレベルに読み込まれるべく作られたモジュールをトップレベル以外に読み込んで来るのは無理がある", [ruby-dev:725]). A Quarz cog is written inside its module from its first line, so there is nothing to retrofit.
- **Rejected: URLs in `require`** (Deno). Two files could then name two versions of one library, which a movement with one global class table cannot hold; and a URL in every file is not Ruby.
- **Rejected: coexisting versions of one cog** (Cargo, Java shading). Technically open, since every cog has its own root, but two `Tomlz::Value` types in one program would confuse more than they help. If needed later it can be allowed per dependency without changing the manifest's shape.

## 9. Open Questions

- The name a class prints: the diagnostic at a use site can show the name visible there (`AUtil::Table`), while `Class#name` at run time gives the declared one (`Util::Table`); Ruby's `Namespace` has the same question open (Bug #21316).
- Whether `branch` should be allowed at all outside `[patch]`.
- Whether `test/` should take part in the hash (it does not: only what is compiled does).
- Whether an application's files other than `src/main.qz` may hold statements (a `require_relative`d helper that prints at load would stop working).
- What `[cog] link` looks like once FFI exists.
- Repositories that use SHA-256 object ids (64 hexadecimal digits) are not supported yet: commit ids are SHA-1's 40 digits, and a longer one is refused as not a commit id (*not yet*).
- `[dev-dependencies]` are read and validated, but nothing uses them until `quarz test` exists (*not yet*).
