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

言語の短い入門は [quarz.dev のガイド](https://quarz.dev/guide/)(英語)にあります。標準ライブラリの API リファレンスは [quarz.dev/std](https://quarz.dev/std/) にあります。

設計文書 `docs/0N-*.md` は言語とその実装を詳しく説明します。一覧と設計上の主な判断は [docs/README.ja.md](docs/README.ja.md) にあります。

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
