# Quarz

Quarz(クォーツ)は、Ruby のような書き心地を持ちながら、静的型付け・不変性・並行性の上に築かれたプログラミング言語です。

- **Ruby に近い文法と組み込みクラス** — `def ... end`、ブロックと `yield`、`case/in`、`#{}`、`Enumerable`/`Comparable`、例外処理はそのまま。
- **静的なクラス・メソッド定義** — クラスの再オープン、`define_method`、`method_missing`、`eval` はない。メソッド呼び出しはコンパイル時に解決され、クラス階層はプログラム全体で確定する。既存の型への追加は字句スコープに閉じた `extension`/`using` で行う。
- **原則 immutable な組み込みデータ** — `String`/`Array`/`Hash`/`Set` は不変で、更新は新しい値を返す(元の値は変わらない)。参照が一意ならその場で更新されるので、素直なループが可変配列と同程度に速い。可変が必要な場面には Ruby と同じ API を持つ Builder 型を使う。
- **軽量タスク** — goroutine / Erlang プロセスのように M:N スケジュールされる `Task`、型付き `Channel`、構造化並行性(`Task.scope`)、不変値を共有する `Atom`。可変オブジェクトはタスク境界を越えられないことを型(`Shareable`)で検査し、データ競合をコンパイル時に排除する。
- **インタプリタと AOT コンパイラの両立** — 型検査済みプログラムから生成する 1 つの中間表現(QIR)と 1 つのランタイム(libquarz)を共有し、`quarz run` でその場実行・REPL、`quarz build` で機械語へ。両者の挙動は同一で、差は性能だけ。

## 一目でわかる Quarz

```ruby
data WordCount(word: String, count: Int)
  include Comparable[WordCount]
  def <=>(other: WordCount) -> Int = other.count <=> count
end

def count_words(text: String) -> Hash[String, Int]
  text.downcase.scan(/[a-z']+/).tally
end

# ファイルごとに軽量タスクを起こし、全部終わるまで待つ
counts = Task.scope do |scope|
  ARGV.map { |path| scope.spawn { count_words(File.read(path)) } }
      .map(&:await)
end

total = counts.reduce({}) { |acc, h| acc.merge(h) { |_, a, b| a + b } }

total.map { |word, count| WordCount.new(word, count) }
     .sort
     .first(10)
     .each { |wc| puts "#{wc.word}: #{wc.count}" }
```

Ruby との違いが現れているのは、引数の型(`text: String`)と戻り値型(`-> Hash[String, Int]`)、`data` による不変レコード、`Task.scope`/`spawn`/`await` の 3 箇所だけです。残りは Ruby そのものです。

```ruby
enum Shape
  variant Circle(radius: Float)
  variant Rect(width: Float, height: Float)

  def area -> Float
    case self                       # 網羅性はコンパイル時に検査される
    in Circle(radius:) then Math::PI * radius ** 2
    in Rect(width:, height:) then width * height
    end
  end
end

class Account
  @id: Int                 # 不変フィールド(initialize でのみ代入)
  var @balance: Int = 0    # 可変フィールド → このクラスは Shareable ではない
  attr_reader :id, :balance
  def initialize(@id: Int); end
  def deposit(amount: Int) -> Void
    @balance += amount
  end
end

counter = Atom.new(0)
Task.scope do |scope|
  100.times { scope.spawn { counter.update { |n| n + 1 } } }
end
puts counter.value        # => 100
```

## 設計文書

[quarz.dev](https://quarz.dev/ja/docs/) でも読めます。標準ライブラリの API リファレンスは [quarz.dev/std](https://quarz.dev/std/) にあります。

| 文書 | 内容 |
|---|---|
| [docs/01-syntax.md](docs/01-syntax.ja.md) | 文法。クラス、`data`、`enum`、`module`、`extension`/`using`、メソッド定義、ブロック、パターンマッチ、例外 |
| [docs/02-types.md](docs/02-types.ja.md) | 型システム。合併型と nil 安全性、ジェネリクスと変位、推論、フロー型付け、多重定義 |
| [docs/03-data-model.md](docs/03-data-model.ja.md) | 不変データと Builder、`Shareable` の導出規則、等価性、文字列、Ruby の慣用句の書き換え |
| [docs/04-concurrency.md](docs/04-concurrency.ja.md) | タスク、構造化並行性とキャンセル、チャネルと `Channel.select`、`Atom`、アクターと監視、ランタイム |
| [docs/05-execution.md](docs/05-execution.ja.md) | インタプリタと AOT コンパイラ、QIR、分割コンパイル、参照カウントによるメモリ管理、ブートストラップ計画 |
| [docs/06-stdlib.md](docs/06-stdlib.ja.md) | 標準ライブラリ。Ruby の組み込みクラスとの対応 |
| [docs/07-ruby-diff.md](docs/07-ruby-diff.ja.md) | Ruby からの変更点 早見表 |
| [docs/08-crystal-diff.md](docs/08-crystal-diff.ja.md) | Crystal との違い 早見表 |
| [docs/09-grammar.md](docs/09-grammar.ja.md) | 文法スケッチ(EBNF) |
| [docs/10-cogs.md](docs/10-cogs.ja.md) | cog(パッケージ)。コミットで固定する git リポジトリ、`Cog.toml`/`Cog.lock`、cog ごとに 1 モジュール、`require` 不要、キーワード `cog` |
| [docs/11-http.md](docs/11-http.ja.md) | HTTP サーバ。応答を返すハンドラ、接続ごとのタスク、ルータ、`Signal`。`HTTP::Client` は後から |
| [docs/12-testing.md](docs/12-testing.ja.md) | テスト。Test::Unit 風の `Test::Case`、コンパイラが見つけるテスト、型付きの assertion、データ駆動、`quarz test` |
| [docs/13-doc-comments.md](docs/13-doc-comments.ja.md) | ドキュメントコメント。宣言の上のコメント、Markdown、検査されるリンク、`quarz test` が実行する例、`quarz doc` |
| [examples/](examples/) | サンプルコード(`hello`、`shapes`、`wordcount`、`pipeline`、`bank_actor`、`extension`、`builder`) |

## 設計上の主な判断

| 判断 | 選んだもの | 理由 |
|---|---|---|
| 型注釈の位置 | 引数と戻り値は必須(戻り値を省略すると nil)、ローカルは推論 | コンパイル時間の短縮とエラーの質のため |
| 引数の型の書き方 | `name: Type`、キーワード専用は `*` の後 | Ruby のラベル構文を流用でき、空白に意味を持たせずに済む |
| `nil` | 独立した型。`T?` でのみ許容 | 実行時の `NoMethodError` をコンパイル時に |
| 直和型 | `enum` | メッセージ型と `case/in` の網羅性検査のため |
| 既存クラスの拡張 | `extension` + `using`(静的 refinements) | 再オープンを許さず、影響範囲を字句スコープに限定 |
| コレクション | 不変の値(共有されていればコピーして更新)+ Builder | 共有の安全性と、一意性を利用したその場更新による速度 |
| 共有可変状態 | 禁止。`Atom` と `Channel` のみ | データ競合をコンパイル時に排除。ロック不要 |
| 軽量スレッド | スタックを持つ M:N タスク(`mmap` 予約 + 遅延コミット) | async/await の色分けなしに Ruby 風の同期コードを書ける |
| メモリ管理 | 参照カウント + その場更新 + 可変オブジェクト限定のサイクル回収 | AOT との相性(スタックマップ不要)、不変値のその場更新 |
| `arr[i]`/`h[k]` | 範囲外・欠損は例外。`[]?` が `nil` | 静的型の下で `nil` 検査を書く手間を減らす(Crystal の実績) |

## 状態

インタプリタが [examples/](examples/) のすべてのプログラムを実行できます。Rust で書かれており、`quarz-syntax`(字句・構文解析)、`quarz-types`(型検査)、`quarz-ir`/`quarz-lower`(中間表現 QIR とそこへの変換)、`quarz-vm`(ランタイム、QIR インタプリタ、スケジューラ、組み込みクラス)、`quarz-aot`(`clang` 経由の LLVM によるネイティブコード生成。`quarz build` が使う)からなります。現在の実装で出来ること・出来ないことは [docs/05-execution.md](docs/05-execution.ja.md) §9 を参照してください。

```sh
cargo build --release
./target/release/quarz run examples/shapes.qz      # 型検査して実行
./target/release/quarz check examples/shapes.qz    # 型検査のみ
./target/release/quarz parse examples/shapes.qz    # 構文木を表示
./target/release/quarz ir examples/shapes.qz       # QIR を表示
./target/release/quarz build examples/shapes.qz -o shapes && ./shapes   # ネイティブ実行ファイルにコンパイル
./target/release/quarz repl                        # 対話セッション(行編集・履歴・補完)
cargo test                                         # 字句・構文・型検査・VM・コンパイラのテスト
```

## ライセンス

[MIT No Attribution](LICENSE)(MIT-0)です。
