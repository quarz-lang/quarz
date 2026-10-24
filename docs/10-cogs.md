# Cogs: Packages

日本語版: [10-cogs.ja.md](10-cogs.ja.md)

A Quarz package is a **cog**: a git repository with a `Quarz.toml` at its root, fetched as source and compiled with the program that uses it. The program being built, with every cog it brings in, is a **movement**. There is no registry and nothing is distributed as a binary: a cog is named by the URL of its repository, and the lock file pins it to one commit.

This document is the design; none of it is built yet. Today `require "name"` only loads a standard library module, and `require_relative` a file (see [01-syntax.md](01-syntax.md) §2).

## 1. Vocabulary and Shape

```
httpx/                      a cog
├── Quarz.toml              its manifest
├── Quarz.lock              its lock file (committed by an application, optional for a library)
├── src/
│   ├── httpx.qz            the entry file: `require "httpx"` loads it
│   └── httpx/
│       ├── client.qz       `require "httpx/client"`
│       └── response.qz
└── test/
```

- A cog is identified by its git URL (`https://github.com/foo/httpx`, `ssh://git@host/path`); a `subdir` picks a cog inside a larger repository (a monorepo).
- The entry file is `src/<name>.qz`; the rest of the cog's files sit under `src/<name>/` and are loaded by `require "<name>/path"` from outside or `require_relative` from within.
- Versions are git tags named `vMAJOR.MINOR.PATCH` (semantic versioning). A commit that no tag names gets a *pseudo-version* (§4).

## 2. The Manifest: `Quarz.toml`

```toml
[cog]
name    = "webkit"
version = "0.3.1"
module  = "Webkit"      # the module the cog's declarations live in; default: `name` in CamelCase
quarz   = "0.1"         # the language version it is written for

[dependencies]
# key = the name used in `require`; `git` is required, with at most one of tag/rev/branch
httpx  = { git = "https://github.com/foo/httpx", tag = "v1.4.0" }
tomlz  = { git = "https://github.com/bar/tomlz", rev = "3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e" }
utils  = { git = "https://github.com/baz/mono",  tag = "v2.0.0", subdir = "libs/utils" }
autil  = { git = "https://github.com/a/util",    tag = "v2.0.0", namespace = "AUtil" }   # §6
butil  = { git = "https://github.com/b/util",    tag = "v1.1.0", namespace = "BUtil" }
devlib = { git = "ssh://git@internal/devlib",    branch = "main" }                       # development only

[dev-dependencies]          # for `quarz test` and the cog's own development, not for its users
spec = { git = "https://github.com/quarz-lang/spec", tag = "v0.2.0" }

[patch]                     # local replacements while developing several cogs together; never locked
httpx = { path = "../httpx" }
```

- `tag`, `rev` and `branch` say where to look; the commit actually used is recorded in the lock file (§3). A `branch` moves with every `quarz cog update`, so it is for development; `quarz cog add` writes a `tag` or `rev`, never a `branch`.
- Dependency keys are local to the cog that declares them: `httpx` refers to a dependency of *this* manifest, and another cog may call the same repository something else.
- The names of standard library modules (`json`, `socket`, …) are reserved and cannot be dependency keys.
- `quarz` is the minimum language version the cog needs (as `go 1.21` in a `go.mod` and `minimum_zig_version` in Zig); a program refuses to build with an older `quarz`.
- A cog with `extern "C"` declarations will need to name the C libraries to link; `[cog] link = ["ssl"]` is reserved for that and not designed further here.

## 3. The Lock File: `Quarz.lock`

`Quarz.lock` is generated, and an application commits it; a library may commit it for its own development, but its users ignore it (as Cargo and Bundler do).

```toml
version = 1

[[cog]]
name    = "httpx"
source  = "git+https://github.com/foo/httpx"
version = "1.4.0"
rev     = "9b1c4e2f0a7d3b6c8e5f1a2b3c4d5e6f7a8b9c0d"
hash    = "h1:Zk3q…"
dependencies = ["tomlz"]

[[cog]]
name    = "tomlz"
source  = "git+https://github.com/bar/tomlz"
version = "0.8.1-0.20261023141500.3f2a9c1e0b4d"       # a pseudo-version: no tag names the commit
rev     = "3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e"
hash    = "h1:Q8ua…"
dependencies = []
```

- `rev` is the key for fetching, `hash` the key for verification: a hash of the cog's files at that commit (`Quarz.toml` and everything under `src/`, path and content in sorted order). The two are kept apart because a git commit id is a SHA-1 of the repository's history, not of the files Quarz compiles: after fetching, a tree whose hash differs from the lock (a rewritten history, a force-pushed tag, a tampered mirror) is refused. The `h1:` prefix names the algorithm so it can change.
- The lock lists only what the resolution chose: one entry per cog, whatever the manifests asked for. `[patch]` entries are not recorded.

## 4. Version Resolution

Resolution follows Go's *minimal version selection*: every manifest in the graph names, for each dependency, the lowest version it accepts (the one its `tag` or `rev` denotes), and the version chosen for a cog is the highest of the lowest versions asked for. There is no search and no solver, the result is a function of the manifests alone, and the lock file records it rather than steering it.

- **One version per cog.** A cog's declarations live in one module (§6) and a class is one class, so the same cog cannot appear twice in a movement. When the chosen version does not share its major with every requirement (its minor, while the major is `0`), the resolution fails and names the two requirements; the application pins one side with `rev` or replaces it with `[patch]`.
- **A `rev` in the application's own manifest pins.** Elsewhere a `rev` is a lower bound like any other, but in the movement's manifest it is also the ceiling: a dependency that asks for a newer version is an error, not a silent upgrade.
- **Pseudo-versions.** A commit that no tag names is ordered as `1.4.1-0.20261023141500.3f2a9c1e0b4d`: the patch after the nearest tag among its ancestors (`0.0.0` when there is none), a `0` so that it sorts below any real pre-release of that patch, the commit's time in UTC, and twelve hex digits of its id. Semantic versioning's precedence rules then order it between the tag and the next release, as Go's pseudo-versions do.
- `quarz cog update [name]` re-resolves and rewrites the lock; nothing else moves a locked version. `quarz run`, `quarz build` and `quarz check` use the lock when it is present and consistent with the manifest, resolve and write it when it is absent, and fail with `--locked` when it would have to change.

## 5. Fetching, Cache and Vendoring

- Repositories are mirrored under `~/.cache/quarz/git/<host>/<path>.git` (a bare clone), and only the commit the lock names is fetched (`git fetch --depth 1 origin <rev>`), so a large history costs nothing.
- The cog's tree is checked out, read-only, into `~/.cache/quarz/src/<name>-<first 12 hex digits of rev>/` and verified against the lock's `hash` before anything is compiled. The directory never changes once written: a pinned commit is immutable, so the type-check results and the `.qzi` of a cog ([05-execution.md](05-execution.md) §2) can be cached by `(hash, quarz version, back end)` and never invalidated.
- `quarz cog vendor` copies every locked cog into `vendor/` next to the manifest; when that directory exists, nothing is fetched. `--offline` resolves from the cache and `vendor/` only.
- Private repositories use git's own authentication (SSH keys, credential helpers); Quarz adds no credential handling of its own.

## 6. Namespaces: a Cog Is a Module

The declarations of a cog never reach the top level. Its files are the body of one module, the one `[cog] module` names (by default the cog's name in CamelCase), as if each file were written inside `module Httpx … end`:

```ruby
# httpx/src/httpx.qz          → everything here is inside `Httpx`
class Client
  def get(url: String) -> Response … end
end
class Response … end

def self.get(url: String) -> Response   # a module function: `Httpx.get`
  Client.new.get(url)
end

def helper(…) … end                      # a top-level `def` stays private to its file, as always
```

The user of the cog requires its entry file and sees it under that module:

```ruby
require "httpx"
require "httpx/client"

res = Httpx.get("https://example.com")
client = Httpx::Client.new
```

- **The root module is an ordinary module** and follows the ordinary rules: it cannot be reopened (no `module Httpx` anywhere, inside or outside the cog, since classes and modules are never reopened), including or extending it warns as including any namespace module does ([01-syntax.md](01-syntax.md) §6), and `extension`s a cog defines take effect only where a file says `using Httpx::StringExt`. A cog cannot monkey-patch its users.
- **`namespace`** in the dependency table gives the application another name for the root: `namespace = "AUtil"` binds the constant `AUtil` to the root module of that cog in the application's scope, as `AUtil = Util` would. It is needed only when two cogs declare the same module name, which is otherwise an error that names both; the cog's own code is unaffected, so its `.qzi` is shared by every user whatever they call it. (Swift PM's `moduleAliases`, .NET's `extern alias` and Cabal's `mixins` solve the same collision the same way.)
- **The dependencies of a cog are resolved by its own manifest.** When `httpx` requires `tomlz`, the name comes from `httpx`'s `[dependencies]` and the module from `tomlz`'s `[cog] module`, whatever the application calls either. A class is the same class under every name, so a `Tomlz::Value` built by `httpx` and one built by the application have one type.
- `require "name"` resolves `name` in this order: a standard library module; a dependency key of the requiring cog, loading `src/name.qz` of that cog (`require "name/path"` loads `src/name/path.qz`); otherwise an error. `require_relative` stays within the cog.
- The application (the root cog of a movement) and a plain script are not wrapped: their declarations are at the top level, as today.

### The `cog` keyword

Inside a cog its own declarations are visible by their bare names, so the root is rarely named. For the cases where it must be, `cog` is a keyword that denotes the current cog's root module (Rust's `crate`):

```ruby
cog::Response        # the root's `Response`, when a nested scope shadows the name
cog.get(url)         # the root's module function, from inside a class
cog.name             # "httpx", from the manifest
cog.version          # "1.4.0", from the manifest: no second copy in the source
```

In the application and in a script, `cog` is the top level; `cog.name` is then the name in the application's manifest, or the file's name without its extension when there is no manifest, and `cog.version` is its version or `"0.0.0"`. `cog` is a keyword rather than a predefined constant so that no cog can shadow it, and it is not spelled `::` because Ruby's `::Foo` (the top level) is still needed to reach a standard class that the cog's own declarations hide.

## 7. Commands

| Command | Behavior |
|---|---|
| `quarz cog init` | Write a `Quarz.toml` for the current directory |
| `quarz cog add <git-url> [--tag v1.4.0 \| --rev <hash>] [--name key] [--subdir dir] [--dev]` | Add a dependency and resolve; a `--tag` or the default branch's head is recorded as a `tag` or `rev` |
| `quarz cog update [name]` | Re-resolve (one cog or all) and rewrite the lock |
| `quarz cog fetch` | Fetch and verify everything the lock names, compiling nothing |
| `quarz cog vendor` | Copy the locked cogs into `vendor/` |
| `quarz cog tree` | Print the resolved dependency graph |
| `quarz cog outdated` | Show, for each cog, the newest tag beyond the locked version |
| `quarz cog verify` | Check the cache and `vendor/` against the lock's hashes |
| `quarz run`/`build`/`check` | Use the lock, or resolve and write it; `--locked` fails instead of writing, `--offline` fetches nothing |

## 8. Design Notes

- **Git, not a registry.** A registry needs a server, an account system and a policy for names; a URL needs none of these and leaves the publisher in control of their repository. Discovery (a searchable index of known cogs) can be added later without changing how a cog is named or fetched, as Go's `pkg.go.dev` was.
- **Source, not binaries.** A cog is compiled on the user's machine with the user's `quarz`; the fetched tree is verified by content, and the cache keyed by content keeps the cost to the first build. Separate compilation ([05-execution.md](05-execution.md) §2) is what makes this cheap.
- **A commit, not a version, is what the lock pins.** Tags move; a commit does not. The version is derived from the tag for ordering, and the content hash is checked for safety.
- **Minimal version selection over a solver.** Cargo's and Bundler's resolvers can pick any version that satisfies the constraints, so the result depends on the resolver and the lock file is the only record of it. With MVS the manifests determine the result, the lock is a cache of it, and a dependency upgrade never lowers a version. The price is that a cog cannot say "below 2.0" except by the major-version rule; Go pays the same price.
- **An alias, not a rewrap.** The application's `namespace` is a constant alias, not a re-nesting of the cog's source under another module: the alternative would make the cog's type-check results depend on every user's choice of name and break cross-cog references.
- **Declarations are wrapped from the start.** Ruby's `Namespace` (Feature #19744) has to load libraries written for the top level into a namespace after the fact, which matz called hard ("もともとトップレベルに読み込まれるべく作られたモジュールをトップレベル以外に読み込んで来るのは無理がある", [ruby-dev:725]). A Quarz cog is written inside its module from its first line, so there is nothing to retrofit.
- **Rejected: URLs in `require`** (Deno). Two files could then name two versions of one library, which a movement with one global class table cannot hold; and a URL in every file is not Ruby.
- **Rejected: coexisting versions of one cog** (Cargo, Java shading). Technically open, since every cog has its own root, but two `Tomlz::Value` types in one program would confuse more than they help. If needed later it can be allowed per dependency without changing the manifest's shape.

## 9. Open Questions

- The name a class prints: the diagnostic at a use site can show the name visible there (`AUtil::Table`), while `Class#name` at run time gives the declared one (`Util::Table`); Ruby's `Namespace` has the same question open (Bug #21316).
- Whether `branch` should be allowed at all outside `[patch]`.
- The hash's exact scope (whether `test/` and the lock of a library take part) and algorithm.
- What `[cog] link` looks like once FFI exists.
