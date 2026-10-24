# 文法

Quarz の文法は Ruby を基礎にし、「静的に定義する」「不変を既定とする」ために必要な最小限の変更だけを加えたものです。この文書は Ruby との差分を中心に説明します。Ruby と同じ部分(演算子の優先順位、文字列リテラル、ヒアドキュメント、`%w[]`、`if` 修飾子、`unless`/`until`、`begin/rescue/ensure`、三項演算子、`&.` など)は原則として Ruby 3.x の仕様に従います。

## 1. 字句

- ソースファイルは UTF-8。拡張子は `.qz`。
- コメントは `#` のみ(`=begin`/`=end` は廃止)。
- `$` で始まるグローバル変数、`@@` で始まるクラス変数は**存在しない**(共有可変状態を言語から排除するため。代替は [04-concurrency.ja.md](04-concurrency.ja.md) の `Atom`)。
- 数値リテラル: `42`、`1_000_000`、`0xff`、`0b1010`、`0o755`、`3.14`、`1e-9`。`r`/`i` 接尾辞は廃止。
- シンボル `:foo`、`:"with space"`、`%i[a b]` はコンパイル時にインターンされる。
- 正規表現リテラル `/.../`、`%r{...}` はコンパイル時にコンパイルされ、`Regexp` 定数になる。
- 文字列系のリテラルは `"..."`、`'...'`、`%q()`、`%Q()`、`%()`、`%w[]`、`%i[]`、ヒアドキュメント(`<<~EOS`、`<<-EOS`、`<<EOS`、`<<~'EOS'`)。Ruby の `?a` 文字リテラル、`%W`/`%I`(補間付き配列)、`%s`、`%x`、バッククォートは廃止。
- `__END__` だけの行で字句解析は終わり、以降は無視される(`DATA`(`IO`)として読めるようにするのは予定)。

### 文脈キーワード

次の語は**宣言位置でのみ**キーワードとして扱われ、それ以外では通常の識別子として使えます(`type = "json"` や `data = fetch` は有効)。

| 語 | 認識される文脈 |
|---|---|
| `data` | 行頭で `data 定数名 =` か `data 定数名(` が続くとき |
| `enum` | 行頭で `enum 定数名` が続くとき |
| `variant` | `enum` の本体で `variant 定数名` が続くとき |
| `var` | `var @名前` / `var @名前:` が続くとき |
| `abstract` | `abstract class` / `abstract def` |
| `override` | `override def` |
| `extension` | 行頭で `extension 型` が続くとき |
| `using` | 行頭で `using 定数` が続くとき |
| `type` | 行頭で `type 定数 =` が続くとき |
| `extern` | 行頭で `extern def` / `extern "C"` が続くとき(FFI は予定。§14) |
| `for` | `for 変数 in`(内包表記。§11) |

Ruby の予約語のうち `defined?`、`undef`、`redo`、`BEGIN`、`END`、`__ENCODING__` は廃止(`for` は意味を変えて文脈キーワードとして戻る。§11)。それ以外(`alias`、`retry`、`yield`、`super`、`self`、`and`/`or`/`not` など)は維持します。

## 2. プログラムの構造

- 1 ファイル = 1 コンパイル単位(モジュール)。`require "name"` は標準ライブラリのモジュール(`std/name.qz`、インタプリタに埋め込み)を、`require_relative "path"` は要求元ファイルからの相対パスのファイル(拡張子がなければ `.qz` を補う)を読み込みます。どちらも**コンパイル時**に解決され、依存グラフは静的に決まり、各ファイルは一度だけ読み込まれ、循環する `require` はエラーです。プログラムが名指しする標準ライブラリのモジュール(`JSON`、`TCPSocket`)も、プログラム自身がその名前を宣言していない限り `require` なしで読み込まれます。**cog**(git リポジトリから取得するパッケージ)は、それを名指しするマニフェストから `require` なしに丸ごと読み込まれ、その宣言は cog 自身のモジュールの下に現れます([10-cogs.ja.md](10-cogs.ja.md))。
- トップレベルには文を書けます。`quarz run hello.qz` で `puts "Hello"` 一行のスクリプトが動きます。要求されたファイルのトップレベル文は、要求したファイルの文より先に一度だけ実行されます(依存先が先、深さ優先の順)。
- 要求されたファイルで宣言されたクラス・モジュール・`data`・`enum`・定数・型エイリアスはどこからでも見えます。トップレベルの `def` と `using` はそのファイルの中だけで有効です。
- トップレベルの `def` はそのファイル内でのみ見える関数になります(Ruby のように `Object` のプライベートメソッドにはなりません)。
- 宣言(`class`/`module`/`data`/`enum`/`def`/`type`/定数)は**巻き上げ**られます。ファイル内で定義より前の行から参照でき、相互再帰も書けます。
- プログラムの引数は `ARGV`、環境変数は `ENV`、標準入出力は `STDIN`/`STDOUT`/`STDERR` 定数です。

```ruby
# hello.qz
require "json"

def greet(name: String) -> String
  "Hello, #{name}!"
end

puts greet(ARGV.first? || "world")
```

## 3. クラス

```ruby
class Account
  @id: Int                 # 不変フィールド。initialize でのみ代入できる
  @owner: String
  var @balance: Int = 0    # 可変フィールド。このクラスは Shareable でなくなる

  attr_reader :id, :owner, :balance

  def initialize(id: Int, owner: String)
    @id = id
    @owner = owner
  end

  def deposit(amount: Int) -> Nil
    raise ArgumentError, "amount must be positive" unless amount > 0
    @balance += amount
  end

  def to_s -> String = "#{owner}: #{balance}"
end

acct = Account.new(1, "alice")
acct.deposit(100)
puts acct          # => alice: 100
```

Ruby との違い:

- **フィールドは宣言が必要**。`@名前: 型` で宣言し、オブジェクトのレイアウトはコンパイル時に確定します。宣言のないインスタンス変数への代入はコンパイルエラーです。
- **フィールドは既定で不変**。`initialize` の中で代入しなければなりません(確定代入解析)。`initialize` の中では再代入もできます。初期化子付き(`@tags: Array[String] = []`)なら省略できます。
- **フィールドは代入前に見えません**。型が `nil` を許さず初期化子もないフィールドは(`var` かどうかによらず)、`initialize` のすべての経路で代入されなければなりません。そのようなフィールドがすべて代入されるまで、オブジェクトは使えません。`self`、暗黙のレシーバに対するクラス(またはそれが include するモジュール)のメソッドの呼び出し、まだ代入されていないフィールドの読み出し、これらを行うブロックはどれも不可です。`raise` や `puts` のような関数は使えます。`return` は代入の後でなければなりません。サブクラスは自分のそのようなフィールドを `super` を呼ぶ *前に* 代入し(スーパークラスの `initialize` が呼んでサブクラスが上書きしたメソッドからも見えるように)、`super` が継承したフィールドを代入します。自分のクラスにそのようなフィールドがあるクラスは `initialize` を定義しなければなりません。フィールドの初期化子は先に宣言順に評価され、それより前に宣言されたフィールドは読めますが、それ以外にオブジェクトを使うことはできません。こうしてフィールドは常に宣言した型の値を持ちます(`@x: Float` は `Float` で、`nil` にはなりません)。コンパイル済みコードはこれを前提にします。
- **可変フィールドは `var`** で宣言します。`var` フィールドを持つクラス、または Shareable でない型のフィールドを持つクラスは Shareable になりません([03-data-model.ja.md](03-data-model.ja.md))。
- **クラスは再オープンできません**。同名のクラスを二度定義するとエラーです。既存クラスへのメソッド追加は `extension`(§7)で行います。
- **クラス本体は宣言のみ**。フィールド宣言、メソッド定義、`include`/`extend`、`attr_*`、定数、入れ子の型、可視性指定(`private`/`protected`/`public`)が書けます。任意の式は書けません。
- **可視性は Ruby と同じ規則で静的に検査します**。`private` なメソッドは `self` に対してだけ(省略するか `self.` を付けて)呼べます。`protected` なメソッドは別の受け手に対しても呼べますが、呼び出す側の `self` が、そのメソッドを定義したクラスかモジュールのインスタンス(子孫のものを含む)である場合に限ります(`def richer?(o: Account) = balance > o.balance`)。クラスメソッドの `self` はクラスなので、インスタンスの protected なメソッドは呼べません。`private`/`protected`/`public` は、後に続くメソッド、前置したメソッド(`private def f`)、名前を挙げたメソッド(`protected :f`)に適用されます。
- `attr_reader`/`attr_writer`/`attr_accessor` は組み込みの宣言で、宣言済みのフィールドに対するアクセサメソッドを生成します(`attr_writer`/`attr_accessor` は `var` フィールドにのみ使えます)。
- `initialize` の引数に `@` を付けると、そのフィールドへの代入を兼ねます(Crystal と同じ):

```ruby
class Account
  @id: Int
  @owner: String
  var @balance: Int = 0

  def initialize(@id: Int, @owner: String); end
end
```

### 継承と抽象クラス

```ruby
abstract class Shape
  abstract def area -> Float

  def describe -> String = "#{self.class.name} with area #{area}"
end

class Circle < Shape
  @radius: Float
  def initialize(@radius: Float); end

  override def area -> Float = Math::PI * @radius ** 2
end
```

- 単一継承。`abstract class` はインスタンス化できず、`abstract def` は本体を持ちません。
- `override` は任意ですが、付けたメソッドが親に存在しなければエラー、付けずに親メソッドを上書きすると警告です。(現状では `override` は受け付けるだけで検査しておらず、どちらの診断も予定です。)
- クラス階層はプログラム全体でコンパイル時に確定するので、コンパイラは上書きのないメソッドを自動的に静的呼び出しにします(`final` は不要)。
- `super` は Ruby 同様。引数なしの `super` は同じ引数を渡します。

## 4. データ型(`data`)

不変のレコード型です。Ruby 3.2 の `Data` に相当します。

```ruby
data Point = (x: Int, y: Int)

data Line(from: Point, to: Point)
  def length -> Float
    Math.sqrt((to.x - from.x) ** 2 + (to.y - from.y) ** 2)
  end
end

p1 = Point.new(1, 2)
p2 = Point.new(x: 3, y: 4)         # キーワードでも可
p3 = p1.with(y: 10)                # 一部を変えたコピー
p1 == Point.new(1, 2)              # => true(構造的等価)
case p3
in Point(x:, y:) then puts "#{x}, #{y}"
end
```

`data` は次を自動生成します: フィールド(不変)、読み出しメソッド、`initialize`、`==`/`hash`、`to_s`/`inspect`、`with`、`to_h`(`deconstruct`/`deconstruct_keys` メソッドは生成しません。パターンは宣言されたフィールドを直接読みます。§11)。メソッドのない `data` は、一行形式の `enum` と同じく `=` を使って 1 行で書きます(`data Point = (x: Int, y: Int)`)。`=` がなければメソッドを書く本体が続き、`end` で閉じます。`data` は継承できません(`include` はできます)。


### その場に格納される data 値

宣言された型が小さな不変の data 型であるフィールド(クラスのフィールドでも、別の data 型のフィールドでも)は、オブジェクトの中に**値として**格納されます。対象となるのは、フィールドがすべて `Int`・`Float`・`Bool` またはそのような data 型で、型引数を持たず、独自の `==`・`hash`・`equal?` を定義していない data 型です。`var @pos: Vec2` は `x` と `y` を粒子自身の中に保持するので、`@pos = @pos + @vel.scale(dt)` は何も割り当てません。そのフィールドを読むと格納された値と等しい値が得られますが、同じオブジェクトではありません。`p.pos.equal?(p.pos)` は、`Vec2.new(1.0, 2.0)` を二つ作ったときと同様に false です。それ以外(`==`、`hash`、`inspect`、`with`、`to_h`、パターン、JSON)はすべて宣言どおりのフィールドを見ます。nil を許すフィールド(`Vec2?`)、union 型、独自の等値を持つ data 型は参照のまま保持されます。

## 5. 列挙型(`enum`)

直和型(代数的データ型)です。各バリアントはデータを持てます。本体では `variant` で宣言し、一行形式では合併型と同じく `|` で区切ります。

```ruby
enum Color = Red | Green | Blue              # 本体なし: 一行で書け、end は不要

enum Shape
  variant Circle(radius: Float)
  variant Rect(width: Float, height: Float)
  variant Point

  def area -> Float
    case self
    in Circle(radius:) then Math::PI * radius ** 2
    in Rect(width:, height:) then width * height
    in Point then 0.0
    end
  end
end

s = Shape::Circle.new(2.0)
s.area
```

- バリアントは `Shape::Circle` のように入れ子の型として参照でき、それぞれ `Shape` のサブタイプです。
- データを持たないバリアント(`Point`)はシングルトンで、`Shape::Point` と書けば値になります。
- `case/in` は網羅性を検査します。バリアントを取りこぼすとコンパイルエラーです。
- ブロック形式では、`def` がメソッドを宣言するのと同じく、`variant` がバリアントを宣言します。1 行に 1 つでも複数でも書けます(`variant Hearts, Spades`)。一行形式 `enum Name = A | B` は本体を持たない enum を宣言し、`end` は不要です(`data Name = (...)` と同じ)。行末が `|` なら次の行に続きます。
- 標準ライブラリの `Result[T, E]` は `enum Result[T, E] = Ok(value: T) | Err(error: E)` にメソッドを加えたものです。

## 6. モジュール

Ruby と同じく、名前空間と mixin の両方に使います。抽象メソッドを持つモジュールが Ruby の「ダックタイピングで期待されるインターフェース」の静的な置き換えになります。

```ruby
module Comparable[T]
  abstract def <=>(other: T) -> Int

  def <(other: T) -> Bool = (self <=> other) < 0
  def between?(min: T, max: T) -> Bool = self >= min && self <= max
  # ...
end

data Version(major: Int, minor: Int)
  include Comparable[Version]
  def <=>(other: Version) -> Int
    [major, minor] <=> [other.major, other.minor]
  end
end
```

- `include` でインスタンス側に、`extend` でクラス側(`self.` メソッド)に取り込みます。
- **契約は検査されます。** 具象クラス(`abstract` でない `class`、`data`、enum のバリアント)は、継承または `include` した抽象メソッドをすべて実装しなければならず、欠けているとコンパイルエラーです(`` `Version` must implement `<=>` (abstract in `Comparable`) ``)。`extend M` したクラスは `M` の抽象メソッドを `def self.name` で実装します。モジュールの既定実装はクラス側でもそのまま動きます(`extend Named` で `Thing.greeting` が `Thing.label` を呼ぶ)。
- モジュールの役割は名前空間(`Math`、`JSON`)、既定実装付きの契約(`Comparable`、`Enumerable`)、印(`Shareable`)の 3 つで、キーワードは一つです。名前は契約なら形容詞・`-able`、名前空間なら名詞にします。インスタンスメソッドを持たない名前空間モジュールを `include`/`extend` しても何も増えないので、警告になります。
- `prepend`、`module_function`、`included` フックなどの動的機構はありません。
- モジュールは型として使えます(`def sort[T: Comparable[T]](xs: Array[T])`)。

## 7. 拡張(`extension`)と `using`

既存の型にメソッドを後付けする仕組みです。Ruby の refinements の静的版で、**字句スコープ**に閉じています。

```ruby
module StringShout
  extension String
    def shout -> String = upcase + "!"
  end

  extension Int
    include Describable           # 既存の型をモジュールに後から適合させる
    def describe -> String = "the number #{self}"
  end
end

using StringShout
"hi".shout          # => "HI!"
```

- `using` はファイル、`class`/`module` 本体、メソッド本体やブロック本体の中に書け、その字句スコープ(書かれた文の並び)の末尾まで有効です。`using M do ... end` / `using M { ... }` は式で、拡張は本体の中だけ有効、値は本体の値です。
- ブロック引数には `using` を付けられます: `def where(&: () -> Cond using SqlDSL)`。呼び出し位置に書かれたブロック字面は、先頭に `using SqlDSL` があるものとして検査されます(入れ子のブロックも含む)。DSL が自分の拡張を呼び出し側のブロックに黙って効かせる、Ruby の `Proc#refined` の静的版です。`using` は手続きの型の一部ではなく、`&proc` で渡した既存の手続き値には影響しません。
- 拡張メソッドの解決は**完全にコンパイル時**です。レシーバの静的型と、その位置で有効な `using` だけで決まり、実行時のテーブル書き換えはありません。特に、モジュール内の extension は動的ディスパッチには関与しません。上位型経由の呼び出し(`Circle` を保持する `s: Shape` に対する `s.name`)は `using` の中でもクラス自身のメソッドを実行し、`using` の外では extension には到達できません。例外は適合です。extension が `include` したモジュールのメソッドは、値がどこへ行っても extension の実装にディスパッチされます(そのモジュール型の値は extension が見えていた場所で作られたかもしれないからです)。`&:name` は、それが書かれた位置でブロック引数の型に対して解決されたメソッドを使います。モジュールの外で宣言した extension はどこでも有効で、動的ディスパッチでも使われます。
- 拡張で既存メソッドと同名のメソッドを定義すると、そのスコープでは拡張側が静的に選ばれます(Ruby の refinements と同じ「見えている範囲だけ上書き」)。意図しない上書きを防ぐため、`override` がなければ警告です(§3 のクラスと同じく予定)。
- 拡張の中の `include` により、既存の型を後からモジュールに適合させられます(Swift の `extension Int: Describable` 相当)。これが「自分の書いていないクラスにインターフェースを満たさせる」唯一の方法です。
- ジェネリック型にも、型引数に制約を付けて拡張できます: `extension Array[T: Describable]; def describe_all -> String = map(&:describe).join(", "); end`。

## 8. 型エイリアスと定数

```ruby
type UserId = Int
type Handler = (Request) -> Response

MAX_RETRY = 3
DEFAULT_HEADERS = { "Content-Type" => "application/json" }
```

- 定数は一度だけ束縛され、値は Shareable でなければなりません(定数は全タスクから見えるため)。
- 定数の初期化子はモジュールのロード時に依存順で一度だけ評価されます。(現状では、定数を初めて使うときに評価します。別のタスクが初期化子を実行している定数を使うタスクは、それが終わるまで待ちます。自身の初期化子の中で使われた定数は `RuntimeError` を送出します。初期化子が例外を送出した定数は、次に使うときにもう一度評価します。)
- 初期化子がクラスやモジュールを指す定数パスである定数は、その別名にもなります。`P = Geometry::Point` の後、`P` は値(`P.new`)としてだけでなく、定数パス(`G = Geometry` の後の `G::Point`)、型(`p: P`)、パターン(`in P`)、`is_a?` に使えます。クラスの名前は変わりません(`P.name` は `"Geometry::Point"`)。

## 9. メソッド定義

```ruby
def name(a: Int, b: String = "x", *rest: Int, *, flag: Bool, limit: Int? = nil, **opts: String, &block: (Int) -> Nil) -> Ret
```

| 構文 | 意味 |
|---|---|
| `a: Int` | 必須引数。位置でもキーワード(`name(a: 1)`)でも渡せる |
| `b: String = "x"` / `b = "x"` | 省略可能引数。既定値から型を推論できるなら型は省略可 |
| `*rest: Int` | 可変長引数。`rest` の型は `Array[Int]` |
| `*` | これ以降はキーワード専用(`*rest` の後ろも同様) |
| `flag: Bool` (`*` の後) | 必須キーワード引数 |
| `**opts: String` | 残余キーワード。型は `Hash[Symbol, String]` |
| `&block: (Int) -> Nil` | ブロック引数。型は手続き型で、`block` は手続きの値(`block.call`、`block.()`、`block[]`) |
| `&: (Int) -> Nil` | 無名のブロック引数。`yield` と `f(&)` での転送からだけ使える |
| `-> Ret` | 戻り値型。省略すると本体から推論(再帰メソッドでは必須) |

- **引数の型は必須**です(既定値から推論できる場合を除く)。メソッドの境界で型が確定しているため、ファイル単位の分割コンパイルと高速な型検査ができます。
- Ruby 3 の「位置引数とキーワード引数の分離」は、Quarz では引数リストが暗黙に `Hash` になることがないので不要です。`*` より前の引数は位置・キーワードのどちらでも渡せます(Python/Crystal と同じ)。
- 戻り値型が `Nil` のメソッドは本体の最後の式の値を捨てます(`void` 相当)。
- 同名メソッドを引数の個数・型で**多重定義**できます。解決はコンパイル時です。
- `def x -> Int = @x` のような一行定義(endless def)が書けます。
- 演算子メソッド(`+`、`[]`、`<=>`、`-@`、`==`、`call` など)は Ruby と同じ名前で定義します。`[]=` は可変型にしか定義できません(まだ検査していない)。単項演算子は `-@`、`+@`、`~`、`!` です(`!` と `~` は `!@`/`~@` とも書けます)。`!x` は、その型が `!` を定義していればそれを呼び、そうでなければ組み込みの否定(`nil` と `false` で真)です。決めるのは静的な型なので、`Object` 型のオペランドは、そのクラスが `!` を定義していても組み込みの否定になります。そのぶん組み込みの否定には実行時の検査がありません。合併型では、値ごとに、その要素が `!` を定義していればそれを呼び、そうでなければ組み込みの否定になります(`u: Cond | Nil` の `!u` は、`Cond` ならその `!` を呼び、`nil` は否定する)。同じ値は `Cond` を通しても `Cond | Nil` を通しても同じ答えになり、そのための型の検査は、そのような合併型が静的な型である箇所でだけかかります。
- `&&` と `||` も定義できます。右オペランドを、引数のないブロックとして受け取ります(`def &&(&rhs: () -> Cond) -> Cond`)。そのとき `a && b`(`a and b`、`a || b`、`a or b` も同じ)は呼び出し `a.&&() { b }` になり、`b` を評価するかどうかは、ブロックを呼ぶかどうかでメソッドが決めます。戻り値の型は自由です(クエリの DSL なら式を組み立てて返します)。`x &&= v` は `x = x.&&() { v }` で、戻り値をそのまま代入します。`!` と同じく、決めるのは左オペランドの静的な型で、実行時の検査はありません。`!` と違い、合併型(`Cond?`)では組み込みの短絡評価のままなので、`c && c.name` で `c` は今までどおり絞り込まれます。`Bool` と `Nil` には定義できません。
- `def self.create(...)` でクラスメソッド。Ruby と同じく、クラスメソッドは呼ばれたクラスの上で動きます。`Shape` から継承した `Circle.describe` の中の暗黙の呼び出し(`label`)は `Circle.label` に行き、`new` は `Circle` を作ります(`def self.build -> Self = new` は `Circle` を返す)。`new` を呼ぶクラスメソッドを継承するサブクラスは、`initialize` で同じ引数を受け付けるか(省略可能な引数は足せる)、そのクラスメソッドを上書きしなければなりません。`private`/`protected`/`public` は Ruby と同じ書き方で、コンパイル時に検査されます(`protected` は受け付けるだけで、まだ強制していない)。
- `alias new_name old_name` は静的に別名を作ります。

### ブロック、`yield`、手続き

```ruby
def each_pair(&: (Int, Int) -> Nil) -> Nil     # 無名ブロック: yield で呼ぶ
  yield 1, 2
  yield 3, 4
end

def map[U](&: (T) -> U) -> Array[U]
  Array.build do |out|
    each { |x| out << yield(x) }
  end
end

def twice(&block: (Int) -> Int) -> Int          # 名前付き: 手続きの値として使う
  block.call(1) + block.(2) + block[3]
end

def forward(&: (Int) -> Int) -> Int = twice(&)  # `&` は無名ブロックをそのまま渡す

each_pair { |a, b| puts a + b }
each_pair do |a, b|
  puts a * b
end

double = ->(x: Int) { x * 2 }          # 手続き(Ruby の lambda に相当)
[1, 2, 3].map(&double)
[1, 2, 3].map(&:to_s)
```

- ブロックの引数型は、呼び出し先のブロック引数の型から推論されます。明示したければ `{ |x: Int| ... }` と書けます(予定。型付きのブロック引数はまだ構文解析できない)。分解する引数(`|(a, b), c|`)は使えないので、本体でマッチします(`pair => [a, b]`)。
- `yield` にはブロック引数(名前付きでも無名でも)の宣言が必要です。ブロックの型は宣言から決まるためで、ブロックなしでそのメソッドを呼ぶとコンパイルエラーになります。省略可能なブロックは `&block: ((Int) -> Nil)?` と書きます(予定。今はブロックを取るメソッドには必ずブロックを渡す)。
- `yield` で呼ばれるだけのブロック(エスケープしないブロック)は、コンパイラがクロージャを割り当てずに展開します。`&block` を変数に保存したり返したりして**エスケープ**させた場合にだけ、ヒープ上のクロージャになります。
- ブロックの中の `break`/`next`/`return` の意味は Ruby と同じです。`next` はブロックの値を返し、`break` はブロックを渡した呼び出しから抜け、`return` は囲んでいるメソッドから戻ります。
- `->(x) { }` は Ruby の lambda と同じ(引数の個数が厳密、`return` は手続きから戻る)。`Proc.new` と `proc` は廃止し、手続きは `->` かブロックから作ります。
- `&:name` は `{ |x| x.name }` へのコンパイル時変換です。
- 手続きの型は `(Int, String) -> Bool` のように書きます。ブロックを取らないメソッドにブロックを渡すとコンパイルエラーです。

### レシーバ付きブロック

手続きの型にはレシーバを付けられます。`Html.() -> Nil` は `self` を `Html` にして走るブロックです(Kotlin の `Html.() -> Unit`)。名前付きのブロック引数として受け取り、`self` を差し替える `instance_exec` で実行します。DSL はこれで作ります。

```ruby
class Html
  var @parts: Array[String] = []
  def title(s: String) -> Nil = (@parts = @parts.push("<title>#{s}</title>"))
  def body(&b: Body.() -> Nil) -> Nil
    node = Body.new
    node.instance_exec(&b)              # ブロックの self は node
    @parts = @parts.push(node.render)
  end
end

def html(&build: Html.() -> Nil) -> Html
  h = Html.new
  h.instance_exec(&build)
  h
end

page = html do
  title "Hello"                         # Html#title
  body do
    p "world"                           # Body#p
  end
end
```

- ブロックの中では `self` がレシーバで、暗黙の受け手の呼び出しはまずレシーバで探します。レシーバにないメソッドは外側のレシーバ、最後に字句上の `self` で探すので、`html { title(page_title) }` のように囲むクラスの `page_title` に届きます。両方にあればレシーバのものが呼ばれ、コンパイラが警告します。
- `@x` はレシーバのフィールドを指しますが、他のフィールド参照と同じく、ブロックがそのクラスの本体の中に字句上あるときだけ許されます。
- `return` は囲むメソッドから、`break` は `instance_exec` の呼び出しから、`next` はブロックから抜け、`yield` は囲むメソッドのブロックへ行きます。普通のブロックと同じです。
- `instance_exec` は `Object#instance_exec[R](&: Self.() -> R) -> R`(引数 1 つ・2 つの多重定義あり)で、`5.instance_exec { self * 2 }` は `10` です。`yield` ではレシーバ付きブロックを実行できません。引数に名前を付けて `recv.instance_exec(&name)` と書きます。`->` のラムダは代入先の型からレシーバを得ます(`f: String.() -> String = -> { upcase }`)。
- レシーバの位置は反変です。`Object.() -> R` のブロックは `Html.() -> R` が期待される所に渡せますが、レシーバ付きとなしのブロックは互換ではありません。
- 印のモジュール `DslScope` を include したクラスは、入れ子のビルダーを混ぜません。レシーバに印のあるブロックの中では、外側のブロックのレシーバのうち印のあるものは暗黙に使えず(名前で呼ぶ)、囲むメソッドの `self` は使えます。Kotlin の `@DslMarker` に相当します。
- `instance_exec` に直接書いたブロックリテラル(`h.instance_exec { ... }`)は、`self` をレシーバに置き換えてその場にコンパイルされ、クロージャは作られません(本体がクロージャを作る場合を除く)。名前で渡されたブロック(`&build`)は本物のクロージャです。

## 10. 変数と代入

```ruby
x = 1                  # Int と推論
x = "one"              # エラー: ローカル変数の型は宣言時に決まる(再代入は同じ型のみ)
y: Int? = nil          # 型注釈付き
y = 10                 # OK
a, b = 1, "x"          # 多重代入(右辺はタプル [Int, String])
first, *rest = [1, 2, 3]
count += 1
name ||= "anon"        # name が T? のとき
xs.push!(4)            # xs = xs.push(4): `!` 付きのメソッド呼び出しはレシーバを束縛し直す
```

- ローカル変数の型は最初の代入で決まります。型を広げたいときは注釈(`y: Int? = nil`)を付けます。
- 代入の後は**フロー型付け**により型が絞り込まれます(`y = 10` の後、`y` は `Int` として扱えます)。
- 変数の宣言とスコープの規則(`if` の中で代入した変数はその後も見える、ブロックパラメータはブロック内のみ、など)は Ruby と同じです。
- `@ivar` への代入は、不変フィールドなら `initialize` の中でのみ可能です。
- `x.foo!(args)` は、レシーバの型に `foo!` が無ければ `x = x.foo(args)` の糖衣です。レシーバはローカル変数かフィールドで、結果はその型に収まる必要があり(`s.size!` はエラー)、式の値は新しい値です。連鎖は同じ場所を順に束縛し直します(`s.strip!.upcase!`)。変わるのは変数の束縛だけで、同じ値を参照している他のものは元のままです(`b = a; a.push!(1)` のあと `b` は変わらない)。これは Ruby の破壊的な `!` メソッドとの違いです。本物の `foo!`(ビルダーの `sort!` など可変オブジェクトの破壊的メソッド)は普通に呼ばれます。コレクションのよくある更新(`push!`、`put!`、`add!`、`set!`、`delete!`)は、他に参照がなければその場で行われます。レシーバを他のオブジェクトの属性にはできません。`obj.items.push!(x)` はエラーで、`obj.items = obj.items.push(x)` は `push` の間も `obj` が配列を持っているため毎回コピーになります(ループでは二乗の時間)。他のオブジェクトが持つコレクションを更新したければ、そのオブジェクトにメソッドを足し、その中で `@items.push!(x)` と書きます。そこではその場更新になります。

## 11. 式と制御構造

Ruby と同じもの: `if`/`unless`/`elsif`/`else`、`while`/`until`、修飾子形式、`case/when`、`case/in`、`begin/rescue/else/ensure`、`loop`、`break`/`next`/`retry`/`return`、`and`/`or`/`not`、`&&`/`||`/`!`、`..`/`...`(端のない範囲を含む)、`&.`、`=>`(右代入・パターン)、`in`(パターン判定)、文字列補間 `#{}`、`__FILE__`/`__LINE__`/`__method__`(Quarz では `String`、Ruby では `Symbol`)。

Ruby と違うもの:

- `for … do … end` は下記の内包表記(式)です。値が使われない位置では、ループ(`each` の入れ子)として実行し、コレクションを作りません。
- すべての制御構造は式です(Ruby と同じ)が、`if` の各枝の型が異なると結果は合併型になります。`if` に `else` がないときは `T?` です。
- 真偽判定は Ruby と同じく `nil` と `false` だけが偽です。ただし型から常に真/常に偽と分かる条件(`if 3`、`if some_int`)には警告が出ます。
- `while` の条件や `if` の条件によって変数の型が絞り込まれます([02-types.ja.md](02-types.ja.md) §6)。

### `for` 内包表記

入れ子のブロックを平らに書くための式です。`flat_map`/`filter`/`map` の連鎖に脱糖されます(Ruby の Feature #22132 と同じ形)。本体は `do` の後に書くか、次の行から書きます。

```ruby
def pairs(n: Int, v: Int) -> Array[[Int, Int]]
  for i in 0...n,
      j in 0...n when i + j == v
    [i, j]
  end
end
# => (0...n).flat_map { |i| (0...n).filter { |j| i + j == v }.map { |j| [i, j] } }

for x in xs when x.even? do x * 2 end       # 一行形式
for k, v in hash do "#{k}=#{v}" end          # タプルの分解(ブロック引数と同じ)
for u in find_user(id), o in latest_order(u) do [u, o] end   # Result[[User, Order], E]
```

- イテレータが 1 つなら `map`、複数なら最後以外が `flat_map`。`when` はそのイテレータの列への `filter`。`in` の右辺と `when` の条件は引数レベルの式です(コンマや修飾子 `if` を含まない)。
- 変数はブロック引数なので外に漏れません。後続のイテレータ、`when`、本体から先行の変数が見えます。`when` のブロックと本体のブロックは兄弟なので、`when` の中で代入した一時変数は本体から見えません。
- `flat_map`/`map`(と `when` に必要な `filter`)を持つ型なら何でも使えます: `Enumerable`、`Range`、`Result`(`flat_map` は `and_then` の別名。`when` は使えません)。型は脱糖後の式から普通に推論されます。
- 本体は組み合わせごとに順に 1 回ずつ実行され、その値が結果の要素になります。`next v` はその要素を `v` にし、`return` は囲むメソッドから戻ります。本体や `when` の中の `break` はコンパイルエラーです(どのブロックを抜けるかが読めないため)。
- 値が使われない位置(本体の最後より前の文、値を捨てる本体の最後の文。つまり `Nil` を返すと宣言したメソッドやブロック、ファイルのトップレベル)では、反復元がすべて `each` を持つ `for` は、`each` の入れ子(`source.each { |x| if 条件 then … end }`)として実行します。コレクションは作りません。本体は、やはり組み合わせごとに順に 1 回ずつ実行されます。`each` を持たない反復元(`Result`)があれば、どの位置でも内包表記です。
- `for` は文脈キーワードで、`for 変数 in` の形のときだけ内包表記です。

### パターンマッチ

Ruby 3 の `case/in` をそのまま採用し、静的検査を加えています。

```ruby
case event
in Click(x:, y:) if x > 100 then handle_right(x, y)
in Key(code: :escape | :q) then quit
in Key(code:) then type(code)
in [first, *rest] then ...
in { name: String => name, age: Int => age } then ...
in ^expected then ...
in Int | Float => n then ...
in nil then ...
end
```

- 使える型: 値パターン、ピン `^x`、選択 `|`、配列パターン(`*rest`、find パターン)、ハッシュパターン、`Const(...)`/`Const[...]`(クラス・`data`・バリアントの宣言されたフィールドにマッチ)、束縛 `=> name`、ガード `if`/`unless`、`nil`。
- `data`/`enum`/合併型に対する `case/in` は網羅性を検査します。網羅していないと `else` が必要で、`else` も網羅もないときはコンパイルエラーです。クラス階層に対する `case/in` は開かれているので、`else` がなければ実行時に `NoMatchingPatternError` になります(警告付き)。
- パターンによって束縛された変数と、絞り込まれたレシーバの型は、その枝の中で静的に分かります。
- `expr => Point(x:, y:)` は失敗すると例外、`expr in Point` は `Bool` を返して絞り込みます。

## 12. 例外

```ruby
class ParseError < StandardError
  @line: Int
  attr_reader :line
  def initialize(message: String, @line: Int)
    super(message)
  end
end

begin
  parse(src)
rescue ParseError => e
  warn "line #{e.line}: #{e.message}"
  retry if (tries += 1) < 3
rescue IOError, SystemCallError => e
  warn "I/O error: #{e.message}"
else
  puts "ok"
ensure
  cleanup
end

value = risky rescue default   # 修飾子形式も可
```

- 例外階層は Ruby に準じます(`Exception` > `StandardError` > ...)。`raise` の引数は例外クラス、例外オブジェクト、または文字列(`RuntimeError`)。処理中の例外を再送出する引数のない `raise` は予定です。今は `rescue E => e` と `raise e` で書きます(`rescue A, B => e` でも同じ)。
- 例外は投げたタスクの中で処理されます。タスクの外に漏れた例外の扱いは [04-concurrency.ja.md](04-concurrency.ja.md)。
- 例外オブジェクトは Shareable である必要があります(他タスクに伝播するため。まだ強制していない)。
- `raise` の型は `Nothing`(ボトム型)なので、`x = arg || raise ArgumentError` のような絞り込みができます。

## 13. 文字列・配列・ハッシュのリテラル

```ruby
s  = "name: #{name}\n"     # String
s2 = 'raw \n'
s3 = <<~EOS
  heredoc
EOS
a  = [1, 2, 3]             # Array[Int]
t  = [1, "a"]              # [Int, String]: 型の違う要素はタプルになる(02-types.ja.md §5)
h  = { name: "alice", age: 30 }     # Hash[Symbol, String | Int]
h2 = { "a" => 1, "b" => 2 }         # Hash[String, Int]
r  = 1..10                 # Range[Int]
set = Set[1, 2, 3]         # Set[Int]
bytes = b"\x00\xff"        # Bytes(バイナリ)
```

- 文字列は常に UTF-8 で、不変です。バイナリデータは別の型 `Bytes` です。
- リテラルから作られる `Array`/`Hash`/`Set` は不変で、更新は新しい値を返します。`[]` や `{}` の空リテラルは文脈から要素型を決めます(§[02-types.ja.md](02-types.ja.md) §5)。
- `{ a: 1 }` のキーは `Symbol`、`{ "a" => 1 }` のキーは `String` です。混在すると `Hash[Symbol | String, Int]` になります。

## 14. FFI

```ruby
extern "C"
  def strlen(s: CString) -> SizeT
  def getpid -> Int32
end

puts strlen("hello")
```

C の関数を直接宣言して呼べます。`CString`、`Pointer[T]`、固定幅整数などの FFI 用の型があります。ブロックする可能性のある C 関数は `Task.blocking { }` の中で呼びます。(FFI は予定です。`extern "C"` のブロックは構文解析できますが、チェッカーが拒否し、FFI 用の型もまだありません。)
