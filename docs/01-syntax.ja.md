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
- `__END__` だけの行で字句解析は終わり、以降は `DATA`(`IO`)として読める。

### 文脈キーワード

次の語は**宣言位置でのみ**キーワードとして扱われ、それ以外では通常の識別子として使えます(`type = "json"` や `data = fetch` は有効)。

| 語 | 認識される文脈 |
|---|---|
| `data` | 行頭で `data 定数名(` が続くとき |
| `enum` | 行頭で `enum 定数名` が続くとき |
| `var` | `var @名前` / `var @名前:` が続くとき |
| `abstract` | `abstract class` / `abstract def` |
| `override` | `override def` |
| `extension` | 行頭で `extension 型` が続くとき |
| `using` | 行頭で `using 定数` が続くとき |
| `type` | 行頭で `type 定数 =` が続くとき |
| `extern` | 行頭で `extern def` / `extern "C"` が続くとき |

Ruby の予約語のうち `defined?`、`undef`、`redo`、`BEGIN`、`END`、`__ENCODING__`、`for` は廃止。それ以外(`alias`、`retry`、`yield`、`super`、`self`、`and`/`or`/`not` など)は維持します。

## 2. プログラムの構造

- 1 ファイル = 1 コンパイル単位(モジュール)。`require "name"` は標準ライブラリのモジュール(`std/name.qz`、インタプリタに埋め込み)を、`require_relative "path"` は要求元ファイルからの相対パスのファイル(拡張子がなければ `.qz` を補う)を読み込みます。どちらも**コンパイル時**に解決され、依存グラフは静的に決まり、各ファイルは一度だけ読み込まれ、循環する `require` はエラーです。
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
- **フィールドは既定で不変**。`initialize` の中でちょうど一度代入しなければなりません(確定代入解析)。初期化子付き(`@tags: Array[String] = []`)なら省略できます。
- **可変フィールドは `var`** で宣言します。`var` フィールドを持つクラス、または Shareable でない型のフィールドを持つクラスは Shareable になりません([03-data-model.ja.md](03-data-model.ja.md))。
- **クラスは再オープンできません**。同名のクラスを二度定義するとエラーです。既存クラスへのメソッド追加は `extension`(§7)で行います。
- **クラス本体は宣言のみ**。フィールド宣言、メソッド定義、`include`/`extend`、`attr_*`、定数、入れ子の型、可視性指定(`private`/`protected`/`public`)が書けます。任意の式は書けません。
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
- `override` は任意ですが、付けたメソッドが親に存在しなければエラー、付けずに親メソッドを上書きすると警告です。
- クラス階層はプログラム全体でコンパイル時に確定するので、コンパイラは上書きのないメソッドを自動的に静的呼び出しにします(`final` は不要)。
- `super` は Ruby 同様。引数なしの `super` は同じ引数を渡します。

## 4. データ型(`data`)

不変のレコード型です。Ruby 3.2 の `Data` に相当します。

```ruby
data Point(x: Int, y: Int)

data Line(from: Point, to: Point) do
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

`data` は次を自動生成します: フィールド(不変)、読み出しメソッド、`initialize`、`==`/`hash`、`to_s`/`inspect`、`with`、`deconstruct`/`deconstruct_keys`、`to_h`。メソッドを追加したいときは `do ... end` に書きます。`data` は継承できません(`include` はできます)。

## 5. 列挙型(`enum`)

直和型(代数的データ型)です。各バリアントはデータを持てます。

```ruby
enum Shape
  Circle(radius: Float)
  Rect(width: Float, height: Float)
  Point

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
- 標準ライブラリの `Result[T, E]` は `enum Result[T, E]; Ok(value: T); Err(error: E); end` です。

## 6. モジュール

Ruby と同じく、名前空間と mixin の両方に使います。抽象メソッドを持つモジュールが Ruby の「ダックタイピングで期待されるインターフェース」の静的な置き換えになります。

```ruby
module Comparable[T]
  abstract def <=>(other: T) -> Int

  def <(other: T) -> Bool = (self <=> other) < 0
  def between?(min: T, max: T) -> Bool = self >= min && self <= max
  # ...
end

data Version(major: Int, minor: Int) do
  include Comparable[Version]
  def <=>(other: Version) -> Int
    [major, minor] <=> [other.major, other.minor]
  end
end
```

- `include` でインスタンス側に、`extend` でクラス側(`self.` メソッド)に取り込みます。
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

- `using` はファイル、または `class`/`module` 本体の中に書け、その字句スコープの末尾まで有効です。
- 拡張メソッドの解決は**完全にコンパイル時**です。レシーバの静的型と、その位置で有効な `using` だけで決まり、実行時のテーブル書き換えはありません。
- 拡張で既存メソッドと同名のメソッドを定義すると、そのスコープでは拡張側が静的に選ばれます(Ruby の refinements と同じ「見えている範囲だけ上書き」)。意図しない上書きを防ぐため、`override` がなければ警告です。
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
- 定数の初期化子はモジュールのロード時に依存順で一度だけ評価されます。

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
| `&block: (Int) -> Nil` | ブロック引数。型は手続き型 |
| `-> Ret` | 戻り値型。省略すると本体から推論(再帰メソッドでは必須) |

- **引数の型は必須**です(既定値から推論できる場合を除く)。メソッドの境界で型が確定しているため、ファイル単位の分割コンパイルと高速な型検査ができます。
- Ruby 3 の「位置引数とキーワード引数の分離」は、Quarz では引数リストが暗黙に `Hash` になることがないので不要です。`*` より前の引数は位置・キーワードのどちらでも渡せます(Python/Crystal と同じ)。
- 戻り値型が `Nil` のメソッドは本体の最後の式の値を捨てます(`void` 相当)。
- 同名メソッドを引数の個数・型で**多重定義**できます。解決はコンパイル時です。
- `def x -> Int = @x` のような一行定義(endless def)が書けます。
- 演算子メソッド(`+`、`[]`、`<=>`、`-@`、`==`、`call` など)は Ruby と同じ名前で定義します。`[]=` は可変型にしか定義できません。
- `def self.create(...)` でクラスメソッド。`private`/`protected`/`public` は Ruby と同じ書き方で、コンパイル時に検査されます。
- `alias new_name old_name` は静的に別名を作ります。

### ブロック、`yield`、手続き

```ruby
def each_pair(&block: (Int, Int) -> Nil) -> Nil
  yield 1, 2
  yield 3, 4
end

def map[U](&block: (T) -> U) -> Array[U]
  Array.build do |out|
    each { |x| out << yield(x) }
  end
end

each_pair { |a, b| puts a + b }
each_pair do |a, b|
  puts a * b
end

double = ->(x: Int) { x * 2 }          # 手続き(Ruby の lambda に相当)
[1, 2, 3].map(&double)
[1, 2, 3].map(&:to_s)
```

- ブロックの引数型は、呼び出し先の `&block` の型から推論されます。明示したければ `{ |x: Int| ... }` と書けます。
- `yield` で呼ばれるだけのブロック(エスケープしないブロック)は、コンパイラがクロージャを割り当てずに展開します。`&block` を変数に保存したり返したりして**エスケープ**させた場合にだけ、ヒープ上のクロージャになります。
- ブロックの中の `break`/`next`/`return` の意味は Ruby と同じです。`next` はブロックの値を返し、`break` はブロックを渡した呼び出しから抜け、`return` は囲んでいるメソッドから戻ります。
- `->(x) { }` は Ruby の lambda と同じ(引数の個数が厳密、`return` は手続きから戻る)。`Proc.new` と `proc` は廃止し、手続きは `->` かブロックから作ります。
- `&:name` は `{ |x| x.name }` へのコンパイル時変換です。
- 手続きの型は `(Int, String) -> Bool` のように書きます。ブロックを取らないメソッドにブロックを渡すとコンパイルエラーです。

## 10. 変数と代入

```ruby
x = 1                  # Int と推論
x = "one"              # エラー: ローカル変数の型は宣言時に決まる(再代入は同じ型のみ)
y: Int? = nil          # 型注釈付き
y = 10                 # OK
a, b = 1, 2            # 多重代入(タプル)
first, *rest = [1, 2, 3]
count += 1
name ||= "anon"        # name が T? のとき
```

- ローカル変数の型は最初の代入で決まります。型を広げたいときは注釈(`y: Int? = nil`)を付けます。
- 代入の後は**フロー型付け**により型が絞り込まれます(`y = 10` の後、`y` は `Int` として扱えます)。
- 変数の宣言とスコープの規則(`if` の中で代入した変数はその後も見える、ブロックパラメータはブロック内のみ、など)は Ruby と同じです。
- `@ivar` への代入は、不変フィールドなら `initialize` の中でのみ可能です。

## 11. 式と制御構造

Ruby と同じもの: `if`/`unless`/`elsif`/`else`、`while`/`until`、修飾子形式、`case/when`、`case/in`、`begin/rescue/else/ensure`、`loop`、`break`/`next`/`retry`/`return`、`and`/`or`/`not`、`&&`/`||`/`!`、`..`/`...`(端のない範囲を含む)、`&.`、`=>`(右代入・パターン)、`in`(パターン判定)、文字列補間 `#{}`、`__FILE__`/`__LINE__`/`__method__`。

Ruby と違うもの:

- `for` はありません(`each` を使ってください)。
- すべての制御構造は式です(Ruby と同じ)が、`if` の各枝の型が異なると結果は合併型になります。`if` に `else` がないときは `T?` です。
- 真偽判定は Ruby と同じく `nil` と `false` だけが偽です。ただし型から常に真/常に偽と分かる条件(`if 3`、`if some_int`)には警告が出ます。
- `while` の条件や `if` の条件によって変数の型が絞り込まれます([02-types.ja.md](02-types.ja.md) §6)。

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

- 使える型: 値パターン、ピン `^x`、選択 `|`、配列パターン(`*rest`、find パターン)、ハッシュパターン、`Const(...)`/`Const[...]`(`deconstruct`/`deconstruct_keys`)、束縛 `=> name`、ガード `if`/`unless`、`nil`。
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
rescue IOError, SystemCallError
  raise
else
  puts "ok"
ensure
  cleanup
end

value = risky rescue default   # 修飾子形式も可
```

- 例外階層は Ruby に準じます(`Exception` > `StandardError` > ...)。`raise` の引数は例外クラス、例外オブジェクト、または文字列(`RuntimeError`)。
- 例外は投げたタスクの中で処理されます。タスクの外に漏れた例外の扱いは [04-concurrency.ja.md](04-concurrency.ja.md)。
- 例外オブジェクトは Shareable である必要があります(他タスクに伝播するため)。
- `raise` の型は `Nothing`(ボトム型)なので、`x = arg || raise ArgumentError` のような絞り込みができます。

## 13. 文字列・配列・ハッシュのリテラル

```ruby
s  = "name: #{name}\n"     # String
s2 = 'raw \n'
s3 = <<~EOS
  heredoc
EOS
a  = [1, 2, 3]             # Array[Int]
t  = [1, "a"]              # 文脈がタプル型を要求すれば [Int, String]、さもなくば Array[Int | String]
h  = { name: "alice", age: 30 }     # Hash[Symbol, String | Int]
h2 = { "a" => 1, "b" => 2 }         # Hash[String, Int]
r  = 1..10                 # Range[Int]
set = Set[1, 2, 3]         # Set[Int]
bytes = b"\x00\xff"        # Bytes(バイナリ)
```

- 文字列は常に UTF-8 で、不変です。バイナリデータは別の型 `Bytes` です。
- リテラルから作られる `Array`/`Hash`/`Set` は不変の永続データ構造です。`[]` や `{}` の空リテラルは文脈から要素型を決めます(§[02-types.ja.md](02-types.ja.md) §5)。
- `{ a: 1 }` のキーは `Symbol`、`{ "a" => 1 }` のキーは `String` です。混在すると `Hash[Symbol | String, Int]` になります。

## 14. FFI

```ruby
extern "C"
  def strlen(s: CString) -> SizeT
  def getpid -> Int32
end

puts strlen("hello")
```

C の関数を直接宣言して呼べます。`CString`、`Pointer[T]`、固定幅整数などの FFI 用の型があります。ブロックする可能性のある C 関数は `Task.blocking { }` の中で呼びます。
