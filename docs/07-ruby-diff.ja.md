# Ruby からの変更点 早見表

Ruby を知っている人が Quarz を書き始めるときに最初に引っかかる点をまとめます。

## 共通点

`def ... end`、`class`/`module`、`include`/`extend`、`attr_reader` など、ブロック(`do ... end`/`{ }`)、`yield`、`&block`、`&:sym`、`if`/`unless`/`while`/`until` と修飾子、`case/when`、`case/in`(パターンマッチ)、`begin/rescue/ensure/retry`、`raise`、文字列補間、ヒアドキュメント、`%w[]`/`%i[]`、シンボル、範囲、正規表現リテラル、`&.`、`||=`、多重代入、`*splat`、キーワード引数の呼び出し構文、`private`/`protected`、`self.` メソッド、演算子定義、`<=>` と `Comparable`、`Enumerable`、`super`、`alias`、`__FILE__`/`__LINE__`、`ARGV`、`ENV`、`puts`/`p`/`pp`。

## 違い

| 項目 | Ruby | Quarz |
|---|---|---|
| メソッドの引数 | `def f(a, b = 1, k:)` | `def f(a: Int, b: Int = 1, *, k: Bool)` — 引数型は必須 |
| 戻り値型 | 言語の一部ではない(シグネチャはコードとは別の RBS ファイルか、Sorbet の `sig` で書ける) | `def f(...) -> Int`(省略すると推論) |
| キーワード引数の宣言 | `k:` ラベル | `*` の後ろに書く。`*` の前の引数は位置でもキーワードでも渡せる |
| インスタンス変数 | 代入すれば生える | `@x: Int` でクラス本体に宣言。既定で不変、可変は `var @x: Int` |
| 未初期化のインスタンス変数 | `nil` | 見えない。型が `nil` を許さず初期化子もないフィールドは、`initialize` のすべての経路で、オブジェクトを使う前に代入する(しなければコンパイルエラー) |
| クラスの再オープン | できる | できない。`extension` + `using` で字句スコープ内に追加 |
| `define_method`、`method_missing`、`send`、`eval`、`instance_eval`、`instance_variable_get` | ある | ない(レシーバ付きの型を持つブロック用に `instance_exec` はある) |
| `Struct`/`Data` | `Data.define(:x, :y)` | `data Point = (x: Int, y: Int)` |
| 直和型 | 専用の構文はない。クラス階層や複数の `Data` 型で書く | `enum` |
| インターフェース | ダックタイピング | `abstract def` を持つ `module`。後付けは `extension T; include M; end` |
| `nil` | どの変数にも入る | `T?` と書いた型にしか入らない。`if x` などで絞り込む |
| 配列・ハッシュ・文字列 | 可変 | 不変。`push`/`put` は新しい値を返す。可変が必要なら `Array::Builder` など |
| `arr << x`、`h[k] = v`、`str << "a"`、`sort!` | 破壊的更新 | 不変型にはない。`arr = arr.push(x)`、`h = h.put(k, v)`、Builder |
| `arr[i]`、`h[k]` | 範囲外・欠損で `nil` | 例外。`nil` が欲しければ `arr[i]?`、`h[k]?` |
| `gets`、`IO#read` | EOF で `nil` | `gets?` が `nil`、`gets` は `EOFError` |
| `Integer` | 任意精度。リテラルは `Integer` | `Int` は 64 ビットで、整数リテラルは `Int` です。`2 ** 70` は `OverflowError` になります。`Integer` は任意精度で(`2.to_integer ** 70`)、`Int` からの暗黙の変換はありません。固定幅の `Int32` などは予定 |
| 文字列のエンコーディング | 多重 | UTF-8 固定。バイナリは `Bytes` |
| `freeze`、`frozen?`、`dup` | ある | `frozen?` が偽になるのは Builder だけ。`dup` は組み込みの不変な値(配列、文字列など)をそのまま返し、Builder とオブジェクトはコピーする。Builder の `freeze` は中身を不変な値として渡す |
| `eql?` | `==` と別 | 廃止。`==`/`hash` のみ |
| グローバル変数 `$x`、クラス変数 `@@x` | ある | ない。定数 + `Atom` |
| 定数 | 再代入は警告 | 再代入不可、Shareable 必須 |
| `Proc.new`、`proc` | ある | `->` とブロックのみ。手続きは常に lambda 意味論 |
| `for x in xs` | ループ。変数はループの後も見える | 本体の値を返す内包表記(`map`、複数の反復には `flat_map`、`when` による絞り込みには `filter`)。変数は中にとどまる。ループには `each` を使う |
| `Thread`、`Mutex`、`Queue`、`Fiber` | ある | `spawn`、`Task.scope`、`Channel`、`Atom` |
| `Thread#join`、`Thread#value` | スレッドの終了を待つ(値を受け取る) | `Task#await` |
| `require` | 実行時に読み込み | コンパイル時に解決(構文は同じ) |
| RubyGems、Bundler(`Gemfile`) | rubygems.org からインストールし、`require` するパッケージ | cog: `Cog.lock` でコミットに固定する git リポジトリ。それぞれ自身のモジュールの下に入り、`require` なしで見える([10-cogs.ja.md](10-cogs.ja.md)、予定) |
| トップレベルの `def` | `Object` のプライベートメソッド | そのファイル内の関数 |
| クラス本体の任意の式 | 実行される | 宣言のみ(定数の初期化子は可) |
| `respond_to?` | 実行時 | コンパイル時定数 |
| `obj.method(:foo)` | `Method` | `obj.:foo`(手続き) |
| `Comparable`、`Enumerable` | モジュール | 同じ。ただしジェネリック(`Comparable[T]`、`Enumerable[T]`) |
| `Array[1, 2]` | 配列を作る | `Array[Int]` は型。配列は `[1, 2]` |
| 同名メソッドの再定義 | 上書き | 引数型による多重定義。同じシグネチャの再定義はエラー |
| 例外 `rescue => e` | `StandardError` | 同じ。`Task::Cancelled` は `Exception` 直下なので捕まらない |

## 追加機能

- 型注釈: `x: Int`、`-> Int`、`T?`、`A | B`、`Array[T]`、`(A) -> B`、`[A, B]`
- `data`、`enum`、`var`、`abstract`、`override`、`extension`、`using`(キーワード化)、`type`、`extern`
- `as`/`as?`
- `Array::Builder` などの Builder 型と `Array.build { }`
- `spawn`、`Task`、`Task.scope`、`Task.blocking`、`Channel`、`select`、`Atom`(`Supervisor` は予定)
- `Result[T, E]`
- `Shareable`(自動導出のマーカー)
- `obj.:method`(メソッド参照)
- DSL 向けのレシーバ付きブロック(`Html.() -> Nil` を `instance_exec` で実行)と `using M do ... end`
- `[]?`、`gets?` などの `nil` 許容版

## 書き換えの例

```ruby
# Ruby
class Inventory
  def initialize
    @items = Hash.new(0)
  end

  def add(name, qty = 1)
    @items[name] += qty
  end

  def report
    @items.map { |name, qty| "#{name}: #{qty}" }.join("\n")
  end
end
```

```ruby
# Quarz(不変スタイル)
class Inventory
  @items: Hash[String, Int]

  def initialize(@items: Hash[String, Int] = {}); end

  def add(name: String, qty: Int = 1) -> Inventory
    Inventory.new(@items.update(name) { |q| (q || 0) + qty })
  end

  def report -> String
    @items.map { |name, qty| "#{name}: #{qty}" }.join("\n")
  end
end

puts Inventory.new.add("apple").add("pear", 2).report
```

```ruby
# Quarz(可変スタイル。タスク局所で使う場合)
class Inventory
  var @items: Hash[String, Int] = {}

  def add(name: String, qty: Int = 1) -> Nil
    @items = @items.update(name) { |q| (q || 0) + qty }
  end

  def report -> String
    @items.map { |name, qty| "#{name}: #{qty}" }.join("\n")
  end
end
```
