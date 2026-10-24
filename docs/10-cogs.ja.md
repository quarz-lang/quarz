# Cog: パッケージ

Quarz のパッケージは **cog**(歯車)です。ルートに `Quarz.toml` を持つ git リポジトリで、ソースのまま取得され、使う側のプログラムと一緒にコンパイルされます。ビルドされるプログラムと、それが組み込む cog の全体を **movement**(ムーブメント)と呼びます。レジストリはなく、バイナリも配布しません。cog はリポジトリの URL で識別され、ロックファイルが 1 つのコミットに固定します。

この文書は設計で、どれもまだ実装されていません。今日の `require "name"` は標準ライブラリのモジュールだけを、`require_relative` はファイルを読み込みます([01-syntax.ja.md](01-syntax.ja.md) §2)。

## 1. 語彙と形

```
httpx/                      1 つの cog
├── Quarz.toml              マニフェスト
├── Quarz.lock              ロックファイル(アプリケーションはコミットする。ライブラリは任意)
├── src/
│   ├── httpx.qz            入口ファイル: `require "httpx"` が読み込む
│   └── httpx/
│       ├── client.qz       `require "httpx/client"`
│       └── response.qz
└── test/
```

- cog は git の URL(`https://github.com/foo/httpx`、`ssh://git@host/path`)で識別します。`subdir` で大きなリポジトリ(モノレポ)の中の cog を選べます。
- 入口ファイルは `src/<name>.qz` です。残りのファイルは `src/<name>/` の下に置き、外からは `require "<name>/path"`、中からは `require_relative` で読み込みます。
- バージョンは `vMAJOR.MINOR.PATCH` という名前の git タグ(セマンティックバージョニング)です。どのタグも指さないコミットには*擬似バージョン*が付きます(§4)。

## 2. マニフェスト: `Quarz.toml`

```toml
[cog]
name    = "webkit"
version = "0.3.1"
module  = "Webkit"      # この cog の宣言が入るモジュール。既定は `name` の CamelCase
quarz   = "0.1"         # 書かれた対象の言語バージョン

[dependencies]
# キー = `require` で使う名前。`git` は必須、tag/rev/branch は多くとも 1 つ
httpx  = { git = "https://github.com/foo/httpx", tag = "v1.4.0" }
tomlz  = { git = "https://github.com/bar/tomlz", rev = "3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e" }
utils  = { git = "https://github.com/baz/mono",  tag = "v2.0.0", subdir = "libs/utils" }
autil  = { git = "https://github.com/a/util",    tag = "v2.0.0", namespace = "AUtil" }   # §6
butil  = { git = "https://github.com/b/util",    tag = "v1.1.0", namespace = "BUtil" }
devlib = { git = "ssh://git@internal/devlib",    branch = "main" }                       # 開発時のみ

[dev-dependencies]          # `quarz test` とこの cog 自身の開発用。利用者には渡らない
spec = { git = "https://github.com/quarz-lang/spec", tag = "v0.2.0" }

[patch]                     # 複数の cog を同時に開発するときのローカル差し替え。ロックには残らない
httpx = { path = "../httpx" }
```

- `tag`、`rev`、`branch` は「どこを見るか」の指示で、実際に使うコミットはロックファイルに記録されます(§3)。`branch` は `quarz cog update` のたびに動くので開発用です。`quarz cog add` が書くのは `tag` か `rev` で、`branch` は書きません。
- 依存のキーは、それを宣言した cog の中だけで有効です。`httpx` は*この*マニフェストの依存を指し、別の cog は同じリポジトリを別の名前で呼んでいてかまいません。
- 標準ライブラリのモジュール名(`json`、`socket`、…)は予約されており、依存のキーには使えません。
- `quarz` はその cog が必要とする最低の言語バージョンです(`go.mod` の `go 1.21`、Zig の `minimum_zig_version` と同じ)。それより古い `quarz` ではビルドを拒みます。
- `extern "C"` 宣言を持つ cog はリンクする C ライブラリを名指しする必要が出ます。そのために `[cog] link = ["ssl"]` を予約しておき、ここでは設計しません。

## 3. ロックファイル: `Quarz.lock`

`Quarz.lock` は生成されるファイルで、アプリケーションはコミットします。ライブラリは自分の開発のためにコミットしてもよく、利用者はそれを無視します(Cargo や Bundler と同じ)。

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
version = "0.8.1-0.20261023141500.3f2a9c1e0b4d"       # 擬似バージョン: どのタグもこのコミットを指さない
rev     = "3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e"
hash    = "h1:Q8ua…"
dependencies = []
```

- `rev` は取得の鍵、`hash` は検証の鍵です。`hash` はそのコミットにおける cog のファイル(`Quarz.toml` と `src/` 以下すべて。パスと内容をソート順で)のハッシュです。二つを分けるのは、git のコミット id がリポジトリの履歴の SHA-1 であって、Quarz がコンパイルするファイルのハッシュではないからです。取得後、ロックとハッシュが一致しないツリー(書き換えられた履歴、force-push されたタグ、改変されたミラー)は拒否します。`h1:` という接頭辞はアルゴリズムを名指しし、後で変えられるようにしています。
- ロックには解決の結果だけが載ります。マニフェストが何を求めていても、cog ごとに 1 項目です。`[patch]` は記録しません。

## 4. バージョン解決

解決は Go の*最小バージョン選択*(MVS)に従います。グラフ中の各マニフェストは、依存ごとに受け入れられる最低のバージョン(その `tag` や `rev` が表すもの)を述べ、ある cog に選ばれるのは、求められた最低バージョンのうち最も高いものです。探索もソルバもなく、結果はマニフェストだけの関数で、ロックファイルは解決を操るのではなく結果を記録します。

- **1 つの cog に 1 つのバージョン。** cog の宣言は 1 つのモジュールに入り(§6)、クラスは 1 つのクラスなので、同じ cog が movement に二度現れることはありません。選ばれたバージョンのメジャー(メジャーが `0` の間はマイナー)が、要求のどれかと一致しないときは解決に失敗し、二つの要求を名指しします。アプリケーションは一方を `rev` で固定するか、`[patch]` で差し替えます。
- **アプリケーション自身のマニフェストの `rev` は固定です。** ほかの場所の `rev` はただの下限ですが、movement のマニフェストでは上限でもあります。より新しいバージョンを求める依存があればエラーで、黙って上げることはしません。
- **擬似バージョン。** どのタグも指さないコミットは `1.4.1-0.20261023141500.3f2a9c1e0b4d` として順序付けます。祖先の中で最も近いタグの次のパッチ(タグがなければ `0.0.0`)、そのパッチの本物のプレリリースより下に並ぶための `0`、コミット時刻(UTC)、コミット id の先頭 12 桁です。セマンティックバージョニングの優先順位規則で、タグと次のリリースの間に並びます(Go の擬似バージョンと同じ)。
- `quarz cog update [name]` が再解決してロックを書き直します。ロックされたバージョンを動かすものはほかにありません。`quarz run`、`quarz build`、`quarz check` は、ロックがありマニフェストと整合していればそれを使い、なければ解決して書き、`--locked` では変更が必要なら失敗します。

## 5. 取得、キャッシュ、ベンダリング

- リポジトリは `~/.cache/quarz/git/<host>/<path>.git` にミラー(ベアクローン)し、ロックが名指しするコミットだけを取得します(`git fetch --depth 1 origin <rev>`)。大きな履歴にコストはかかりません。
- cog のツリーは `~/.cache/quarz/src/<name>-<rev の先頭 12 桁>/` に読み取り専用でチェックアウトし、何かをコンパイルする前にロックの `hash` と照合します。このディレクトリは一度書かれたら変わりません。固定されたコミットは不変なので、cog の型検査結果と `.qzi`([05-execution.ja.md](05-execution.ja.md) §2)は `(hash, quarz のバージョン, バックエンド)` を鍵にキャッシュでき、無効化は一切要りません。
- `quarz cog vendor` はロックされた全 cog をマニフェストの隣の `vendor/` にコピーします。このディレクトリがあれば何も取得しません。`--offline` はキャッシュと `vendor/` だけで解決します。
- 非公開リポジトリは git 自身の認証(SSH 鍵、credential helper)を使います。Quarz は独自の認証情報の扱いを持ちません。

## 6. 名前空間: cog はモジュール

cog の宣言はトップレベルには届きません。cog のファイルは、`[cog] module` が名指しする 1 つのモジュール(既定は cog 名の CamelCase)の本文で、各ファイルを `module Httpx … end` の中に書いたのと同じです。

```ruby
# httpx/src/httpx.qz          → ここにあるものはすべて `Httpx` の中
class Client
  def get(url: String) -> Response … end
end
class Response … end

def self.get(url: String) -> Response   # モジュール関数: `Httpx.get`
  Client.new.get(url)
end

def helper(…) … end                      # トップレベルの `def` はこれまでどおりファイル私有
```

利用側は入口ファイルを require し、そのモジュールの下に見ます。

```ruby
require "httpx"
require "httpx/client"

res = Httpx.get("https://example.com")
client = Httpx::Client.new
```

- **ルートモジュールは普通のモジュール**で、普通の規則に従います。再オープンできません(クラスもモジュールも再オープンされないので、cog の内外どこにも `module Httpx` は書けません)。include や extend は、名前空間モジュールを include したときと同じ警告になります([01-syntax.ja.md](01-syntax.ja.md) §6)。cog が定義する `extension` は、ファイルが `using Httpx::StringExt` と書いた場所でだけ効きます。cog は利用者をモンキーパッチできません。
- 依存テーブルの **`namespace`** は、アプリケーションにルートの別名を与えます。`namespace = "AUtil"` は、`AUtil = Util` と書いたのと同じように、アプリケーションのスコープで定数 `AUtil` をその cog のルートモジュールに束縛します。必要になるのは二つの cog が同じモジュール名を宣言したときだけで、それ以外ではそれはエラー(両方を名指しする)です。cog 自身のコードには影響しないので、その `.qzi` は利用者が何と呼んでいても共有されます(Swift PM の `moduleAliases`、.NET の `extern alias`、Cabal の `mixins` は同じ衝突を同じ方法で解いています)。
- **cog の依存は、その cog 自身のマニフェストで解決します。** `httpx` が `tomlz` を require するとき、名前は `httpx` の `[dependencies]` から、モジュールは `tomlz` の `[cog] module` から来ます。アプリケーションがどちらを何と呼んでいても変わりません。クラスはどの名前の下でも同じクラスなので、`httpx` が作った `Tomlz::Value` とアプリケーションが作ったものは 1 つの型です。
- `require "name"` は `name` をこの順に解決します。標準ライブラリのモジュール、要求元 cog の依存キー(その cog の `src/name.qz` を読み込む。`require "name/path"` は `src/name/path.qz`)、どちらでもなければエラー。`require_relative` は cog の中にとどまります。
- アプリケーション(movement のルート cog)と素のスクリプトは包まれません。その宣言は今日と同じくトップレベルです。

### キーワード `cog`

cog の中では自分の宣言が素の名前で見えるので、ルートを名指しすることはまれです。必要になる場面のために、`cog` は現在の cog のルートモジュールを表すキーワードです(Rust の `crate`)。

```ruby
cog::Response        # 入れ子のスコープが名前を隠しているときの、ルートの `Response`
cog.get(url)         # クラスの中から呼ぶ、ルートのモジュール関数
cog.name             # "httpx"。マニフェストから
cog.version          # "1.4.0"。マニフェストから。ソースに二度書かない
```

アプリケーションとスクリプトでは `cog` はトップレベルです。そのとき `cog.name` はアプリケーションのマニフェストの名前、マニフェストがなければ拡張子を除いたファイル名で、`cog.version` はそのバージョンか `"0.0.0"` です。`cog` を定義済み定数ではなくキーワードにするのは、どの cog にも隠されないためです。`::` と綴らないのは、cog 自身の宣言が隠した標準クラスに届くために Ruby の `::Foo`(トップレベル)が引き続き必要だからです。

## 7. コマンド

| コマンド | 動作 |
|---|---|
| `quarz cog init` | 現在のディレクトリに `Quarz.toml` を書く |
| `quarz cog add <git-url> [--tag v1.4.0 \| --rev <hash>] [--name key] [--subdir dir] [--dev]` | 依存を追加して解決する。`--tag` か既定ブランチの先頭が `tag` または `rev` として記録される |
| `quarz cog update [name]` | 再解決(1 つまたは全部)してロックを書き直す |
| `quarz cog fetch` | ロックが名指しするものを取得して検証する。コンパイルはしない |
| `quarz cog vendor` | ロックされた cog を `vendor/` にコピーする |
| `quarz cog tree` | 解決された依存グラフを表示する |
| `quarz cog outdated` | cog ごとに、ロックされたバージョンより新しい最新のタグを示す |
| `quarz cog verify` | キャッシュと `vendor/` をロックのハッシュと照合する |
| `quarz run`/`build`/`check` | ロックを使う、またはロックを解決して書く。`--locked` は書く代わりに失敗し、`--offline` は何も取得しない |

## 8. 設計ノート

- **レジストリではなく git。** レジストリにはサーバ、アカウント、名前の方針が要ります。URL にはどれも要らず、公開者が自分のリポジトリの主導権を持ち続けます。発見(既知の cog の検索できる索引)は、cog の名付け方と取得の仕方を変えずに後から足せます(Go の `pkg.go.dev` がそうでした)。
- **バイナリではなくソース。** cog は利用者のマシンで利用者の `quarz` によってコンパイルされます。取得したツリーは内容で検証し、内容を鍵にしたキャッシュがコストを初回のビルドに留めます。これを安くするのが分割コンパイル([05-execution.ja.md](05-execution.ja.md) §2)です。
- **ロックが固定するのはバージョンではなくコミット。** タグは動き、コミットは動きません。バージョンは順序付けのためにタグから導き、安全のために内容ハッシュを照合します。
- **ソルバではなく最小バージョン選択。** Cargo や Bundler のリゾルバは制約を満たすどのバージョンでも選べるので、結果はリゾルバに依存し、ロックファイルがその唯一の記録になります。MVS ではマニフェストが結果を決め、ロックはそのキャッシュで、依存の更新がバージョンを下げることはありません。代償は、cog が「2.0 未満」をメジャーバージョンの規則以外では言えないことで、Go も同じ代償を払っています。
- **包み直しではなく別名。** アプリケーションの `namespace` は定数の別名で、cog のソースを別のモジュールの下に入れ直すものではありません。入れ直しだと、cog の型検査結果が利用者ごとの名前の選択に依存し、cog 同士の参照が壊れます。
- **宣言は最初から包まれている。** Ruby の `Namespace`(Feature #19744)は、トップレベル向けに書かれたライブラリを後から名前空間に読み込まねばならず、matz はそれを難しいと述べています(「もともとトップレベルに読み込まれるべく作られたモジュールをトップレベル以外に読み込んで来るのは無理がある」[ruby-dev:725])。Quarz の cog は最初の行からモジュールの中に書かれるので、後付けするものがありません。
- **却下: `require` に URL**(Deno)。二つのファイルが一つのライブラリの二つのバージョンを名指しできてしまい、1 つのグローバルなクラス表を持つ movement には収まりません。それに、全ファイルに URL があるのは Ruby ではありません。
- **却下: 同じ cog の複数バージョンの共存**(Cargo、Java の shading)。技術的には開いています(各 cog は自分のルートを持つので)が、1 つのプログラムに二つの `Tomlz::Value` 型があるのは助けより混乱が大きいでしょう。後で必要になれば、マニフェストの形を変えずに依存ごとに許せます。

## 9. 未決の論点

- クラスが表示する名前。使用箇所の診断はそこで見える名前(`AUtil::Table`)を、実行時の `Class#name` は宣言された名前(`Util::Table`)を出す、という分け方が候補です。Ruby の `Namespace` でも同じ問題が未決です(Bug #21316)。
- `[patch]` の外で `branch` を許すべきかどうか。
- ハッシュの正確な範囲(`test/` とライブラリのロックを含めるか)とアルゴリズム。
- FFI が入ったときの `[cog] link` の形。
