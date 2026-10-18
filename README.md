# Quarz

Quarz(クォーツ)は、Ruby の書き心地を保ったまま「静的」「不変」「並行」を言語の基礎に据えたプログラミング言語の設計です。

- **Ruby に近い文法と組み込みクラス** — `def ... end`、ブロックと `yield`、`case/in`、`#{}`、`Enumerable`/`Comparable`、例外処理はそのまま。
- **静的なクラス・メソッド定義** — クラスの再オープン、`define_method`、`method_missing`、`eval` はない。メソッド呼び出しはコンパイル時に解決され、クラス階層はプログラム全体で確定する。既存の型への追加は字句スコープに閉じた `extension`/`using` で行う。
- **原則 immutable な組み込みデータ** — `String`/`Array`/`Hash`/`Set` は永続データ構造で、更新は新しい値を返す。参照が一意ならその場で更新されるので、素直なループが可変配列と同程度に速い。可変が必要な場面には Ruby と同じ API を持つ Builder 型を使う。
- **軽量タスク** — goroutine / Erlang プロセスのように M:N スケジュールされる `Task`、型付き `Channel`、構造化並行性(`Task.scope`)、不変値を共有する `Atom`。可変オブジェクトはタスク境界を越えられないことを型(`Shareable`)で検査し、データ競合をコンパイル時に排除する。
- **インタプリタと AOT コンパイラの両立** — 1 つの型付き中間表現(QIR)と 1 つのランタイム(libquarz)を共有し、`quarz run` でその場実行・REPL、`quarz build` で機械語へ。両者の挙動は同一で、差は性能だけ。

## 一目でわかる Quarz

```ruby
data WordCount(word: String, count: Int) do
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
  Circle(radius: Float)
  Rect(width: Float, height: Float)

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
  def deposit(amount: Int) -> Nil
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

| 文書 | 内容 |
|---|---|
| [docs/01-syntax.md](docs/01-syntax.md) | 文法。クラス、`data`、`enum`、`module`、`extension`/`using`、メソッド定義、ブロック、パターンマッチ、例外 |
| [docs/02-types.md](docs/02-types.md) | 型システム。合併型と nil 安全性、ジェネリクスと変位、推論、フロー型付け、多重定義 |
| [docs/03-data-model.md](docs/03-data-model.md) | 不変データと Builder、`Shareable` の導出規則、等価性、文字列、Ruby の慣用句の書き換え |
| [docs/04-concurrency.md](docs/04-concurrency.md) | タスク、構造化並行性とキャンセル、チャネルと `select`、`Atom`、アクターと監視、ランタイム |
| [docs/05-execution.md](docs/05-execution.md) | インタプリタと AOT コンパイラ、QIR、分割コンパイル、参照カウントによるメモリ管理、ブートストラップ計画 |
| [docs/06-stdlib.md](docs/06-stdlib.md) | 標準ライブラリ。Ruby の組み込みクラスとの対応 |
| [docs/07-ruby-diff.md](docs/07-ruby-diff.md) | Ruby からの変更点 早見表 |
| [docs/08-grammar.md](docs/08-grammar.md) | 文法スケッチ(EBNF) |
| [examples/](examples/) | サンプルコード(`hello`、`shapes`、`wordcount`、`pipeline`、`bank_actor`、`extension`、`builder`) |

## 設計上の主な判断

| 判断 | 選んだもの | 理由 |
|---|---|---|
| 型注釈の位置 | 引数は必須、戻り値とローカルは推論 | 分割コンパイルと高速な型検査。全体推論(Crystal)はコンパイル時間とエラーの質で不利 |
| 引数の型の書き方 | `name: Type`、キーワード専用は `*` の後 | Ruby のラベル構文を流用でき、空白に意味を持たせずに済む |
| `nil` | 独立した型。`T?` でのみ許容 | 実行時の `NoMethodError` をコンパイル時に |
| 直和型 | `enum` | メッセージ型と `case/in` の網羅性検査のため |
| 既存クラスの拡張 | `extension` + `using`(静的 refinements) | 再オープンを許さず、影響範囲を字句スコープに限定 |
| コレクション | 不変の永続データ構造 + Builder | 共有の安全性と、一意性を利用した在場更新による速度 |
| 共有可変状態 | 禁止。`Atom` と `Channel` のみ | データ競合をコンパイル時に排除。ロック不要 |
| 軽量スレッド | スタックを持つ M:N タスク(`mmap` 予約 + 遅延コミット) | async/await の色分けなしに Ruby 風の同期コードを書ける |
| メモリ管理 | 参照カウント + 在場更新 + 可変オブジェクト限定のサイクル回収 | AOT との相性(スタックマップ不要)、停止時間なし、不変値の在場更新 |
| `arr[i]`/`h[k]` | 範囲外・欠損は例外。`[]?` が `nil` | 静的型の下で `nil` 検査を書く手間を減らす(Crystal の実績) |

## 状態

この時点では設計文書のみです。実装は [docs/05-execution.md](docs/05-execution.md) §8 の計画に沿って、Ruby で書く stage0 コンパイラ(C 出力)と C のランタイムから始める想定です。
