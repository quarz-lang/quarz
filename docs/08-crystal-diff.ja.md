# Crystal との違い 早見表

Crystal は Quarz に最も近い言語です。Ruby の構文を持つ、静的型付けのコンパイル言語です。このページは、Crystal を知っている人が最初に気づく違いをまとめたものです。表面の大部分は共通で、違うのは、型を書く必要がある場所、可変性、メモリ管理と並行処理の仕組み、コンパイル時に変えられるものの範囲です。

## 共通点

`def ... end`、`class`/`module`、`include`/`extend`、`abstract class`/`abstract def`(継承・include した抽象メソッドの実装はどちらでも検査される)、単一継承、`super`、ブロックと `yield`、`->(x) { }` の手続き、`case/when` と `case/in`、`begin/rescue/ensure`、`raise`、文字列補間とヒアドキュメント、`require`、`private`/`protected`、演算子メソッド、合併型と `T?`(`T | Nil`)、`if x`・`x.nil?`・`is_a?`・`case/in` による絞り込み、`as`/`as?`(検査付きのキャスト)、型引数を持つジェネリクス、名前でも渡せる位置引数と `*` の後のキーワード専用引数、フィールドへの代入を兼ねる `def initialize(@x: T)`、そして `nil` を許さない型のフィールドを `initialize` がすべての経路で代入しなければエラーになること。文字列はどちらでも不変で、どちらも `String.build { |b| b << ... }` で組み立てます(どちらでも `String::Builder` です。Crystal のものは `IO` でもあるので、`print` などのメソッドや `to_s(io)` がそこに書き込めます)。

## 違い

| 項目 | Crystal | Quarz |
|---|---|---|
| 型注釈の書き方 | `x : Int32`、`def f(a : Int32) : Bool` | `x: Int`、`def f(a: Int) -> Bool`(コロンの前に空白を入れず、戻り値の型は `->`) |
| メソッドの引数の型 | 省略できる。型のないメソッドは引数の型の組み合わせごとに具体化され、そのためにプログラム全体をまとめて型検査する | 必須(既定値から型が決まる場合を除く)。戻り値の型と局所変数は推論する。書く量は増え、ファイルごとに検査できる([02-types.ja.md](02-types.ja.md) §10) |
| ジェネリック型の書き方 | `Array(Int32)`、`Hash(String, Int32)`、`Proc(Int32, Bool)` | `Array[Int]`、`Hash[String, Int]`、`(Int) -> Bool` |
| 空のリテラル | `[] of Int32`、`{} of String => Int32` | 文脈から型が決まる: `xs: Array[Int] = []`、`h: Hash[String, Int] = {}` |
| 整数 | 既定は `Int32`(`Int64` は `1_i64`)。溢れると `OverflowError` | `Int` は任意精度(溢れると Ruby と同じく多倍長整数になる)。固定幅の型は FFI 用に予定 |
| 浮動小数点数 | `Float64`(`Float32`) | `Float`(`Float32` は予定) |
| インスタンス変数 | 宣言するか代入から推論。可変 | クラス本体で宣言(`@x: Int`)。既定で不変、`var @x: Int` で可変 |
| `initialize` でフィールドの代入前にオブジェクトを使う | `self` を使ったり渡したりするとエラー。呼んだメソッドが未代入のフィールドを読んでもエラー。そのようなフィールドに触れないメソッドの呼び出しは許される | そのようなフィールドがすべて代入されるまで、`self` の使用もクラスのメソッドの呼び出しもすべてエラー(呼ぶメソッドの中身は見ない)。[01-syntax.ja.md](01-syntax.ja.md) §3 を参照 |
| アクセサ | `getter`、`setter`、`property` | `attr_reader`、`attr_writer`、`attr_accessor`(書き込み側は `var` フィールドのみ) |
| `Array`、`Hash`、`Set` | 可変(`<<`、`[]=`、`delete`) | 不変で永続的。`push`/`put`/`delete` は新しい値を返し、共有されていなければその場で更新する(`xs = xs.push(x)`)。タスク内で組み立てるための可変な `Array::Builder` など |
| `arr[i]`、`h[k]` | 範囲外・キーなしで例外。`[]?` は `nil` を返す | 同じ |
| レコード | `record Point, x : Int32, y : Int32`。getter、フィールドごとの `==`/`hash`、`copy_with` を持つ struct | `data Point = (x: Int, y: Int)`。不変で、構造的な `==`/`hash`、`with`、パターンを持つ。小さいものは保持するオブジェクトの中にそのまま置かれる |
| `struct` | 可変な値型。代入でコピーされる | ユーザ定義の値型はない。`data` は不変なので、コピーと共有の違いは観察できない |
| `enum` | 名前付きの整数定数(フラグも可)。直和型は型の合併か、抽象 struct の階層で書く | 代数的データ型: `enum Shape = Circle(r: Float) \| Rect(w: Float, h: Float)`。`case/in` で網羅性を検査する |
| `&.method` の短縮形 | `xs.map(&.upcase)` | `xs.map(&:upcase)`(Ruby の書き方) |
| ブロック引数の型 | `&block : Int32 -> Int32` | `&block: (Int) -> Int`。`yield` するメソッドはブロックを宣言する(`&: (Int) -> Nil`) |
| クラスの再オープン | どこでもでき、プログラム全体に効く | できない。既存の型へのメソッド追加は `extension` で行い、`using` が有効な範囲でだけ効く |
| 既存の型をモジュールに適合させる | 型を再オープンしてモジュールを include する(`struct Int32; include M; ...; end`)。どこでも効く。型のない引数は、必要なメソッドを持つものなら何でも受け付ける(ダックタイピング) | `extension Int; include M; ...; end`。トップレベルに書けばどこでも有効で、モジュールの中に書けば `using` でそのモジュールを持ち込んだ範囲で有効になる。引数には型があるので、値は適合していなければならない |
| 型の別名 | `alias UserId = Int32` | `type UserId = Int` |
| メソッド参照 | `->obj.method` | `obj.:method` |
| レシーバ付きのブロック(DSL) | `with obj yield`。ブロックが何であれ、暗黙のレシーバが `obj` になる | レシーバはブロックの型の一部(`Html.() -> Nil`)で、`obj.instance_exec(&block)` で実行する |
| マクロ | `macro`、`{{ }}`、`@type`、アノテーション | ない。コンパイラによるコード生成は `data` や `attr_*` などに限る |
| フィールドの絞り込み | インスタンス変数は絞り込まれない(局所変数に代入する) | 不変フィールドと `data` のフィールドは絞り込まれる。`var` フィールドは絞り込まれない |
| `to_s` | `to_s(io : IO)` を上書きする | `def to_s -> String` |
| タプル | `Tuple`、`NamedTuple`(`{1, "a"}`、`{x: 1}`) | タプル型 `[Int, String]` を配列リテラルで書く。名前付きのフィールドは `data` で |
| 並行処理 | メモリを共有するファイバー(`spawn`、`Channel(T)`、`Mutex`、`Atomic(T)`)。どんなオブジェクトもファイバー間で受け渡せ、実行コンテキストでファイバーを複数のスレッドで動かせる | タスク(`spawn`、キャンセル付きの `Task.scope`、`Channel[T]`、`select`、`Atom[T]`)。タスクの境界を越えられるのは `Shareable` な(不変な)値だけで、コンパイラが検査する。ロックはない。現在のスケジューラはタスクを 1 つのスレッドで動かし、`Task.blocking { }` はブロックを補助スレッドで実行する |
| メモリ管理 | トレース型 GC(Boehm) | 参照カウント。参照が一意な値はその場で更新する |
| C との連携 | `lib LibC; fun strlen(s : UInt8*) : SizeT; end` | `extern "C"; def strlen(s: CString) -> SizeT; end` |
| プログラムの実行 | コンパイルする(`crystal run` も先にコンパイルする)。`crystal i` は実験的なインタプリタで、それを含めてビルドした Crystal でだけ使える | `quarz run` は解釈実行する。`quarz build` は LLVM か Cranelift でコンパイルする |

## 追加機能

- `data`、代数的な `enum`、`var`、`override`、`extension`/`using`
- 不変なコレクションと、それを組み立てる可変な Builder(`Array::Builder`、`Hash::Builder`、`Set::Builder`。`Array.build { |b| b << x }` は不変な配列を返す)。Crystal の `Array.build(capacity) { |buffer| ... }` は別物の低水準 API で、生のポインタのバッファに書き込み、書いた要素数を返す
- `Task.scope`(キャンセル付きの構造化並行性)、コンパイラが導出する `Shareable` マーカー、`Shareable` な値を入れる `Atom[T]`(`update { |old| ... }` で更新する CAS ループ)
- `for` 内包表記と `for` ループ
- `Result[T, E]`
- 日常的な実行手段としてのインタプリタ(`quarz run`、REPL)。ランタイムはコンパイラと共有する

## 書き換えの例

```crystal
# Crystal
struct Vec2
  getter x : Float64, y : Float64
  def initialize(@x, @y); end
  def +(o : Vec2)
    Vec2.new(x + o.x, y + o.y)
  end
end

class Particle
  property pos : Vec2
  def initialize(@pos : Vec2, @vel : Vec2); end
  def step(dt : Float64)
    @pos = Vec2.new(@pos.x + @vel.x * dt, @pos.y + @vel.y * dt)
  end
end

ps = [] of Particle
3.times { |i| ps << Particle.new(Vec2.new(i.to_f, 0.0), Vec2.new(1.0, 0.5)) }
ps.each &.step(0.1)
puts ps.map(&.pos.x).sum
```

```ruby
# Quarz
data Vec2(x: Float, y: Float)
  def +(o: Vec2) -> Vec2 = Vec2.new(x + o.x, y + o.y)
end

class Particle
  var @pos: Vec2
  @vel: Vec2
  attr_reader :pos
  def initialize(@pos: Vec2, @vel: Vec2); end
  def step(dt: Float) -> Nil
    @pos = Vec2.new(@pos.x + @vel.x * dt, @pos.y + @vel.y * dt)
  end
end

ps: Array[Particle] = []
3.times { |i| ps = ps.push(Particle.new(Vec2.new(i.to_f, 0.0), Vec2.new(1.0, 0.5))) }
ps.each { |p| p.step(0.1) }
puts ps.map { |p| p.pos.x }.sum
```

粒子は可変オブジェクトのまま(`var @pos`)なので、作ったタスクの中にとどまります。それを保持する配列は不変で、`ps = ps.push(...)` で伸ばします。ほかに参照がないので、その場で更新されます。
