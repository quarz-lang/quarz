# データモデルと不変性

Quarz では「値は既定で不変、可変は明示的かつタスク局所」が原則です。この原則が、並行プログラミングの安全性(共有可変状態の排除)と実行効率(参照カウントによる一意性検出で、不変値をその場で更新する)の両方を支えます。

## 1. すべてはオブジェクト

Ruby と同じく、整数も `nil` もオブジェクトで、メソッドを持ちます(`3.times`、`nil.to_s`)。ただし表現はコンパイラが決めます。`Int` の小さな値はタグ付きの即値、`Float` は静的に型が分かる場所では非ボックスの倍精度値、`Bool`/`Nil` は即値です。ヒープに置かれるのは文字列、コレクション、ユーザー定義クラスのインスタンス、`Integer`、クロージャだけです。

## 2. 不変な組み込みデータ

次の型は**不変**です。値を変更するメソッドは存在せず、「変更した新しい値」を返すメソッドだけがあります。

| 型 | 実装 | 主な「更新」操作(新しい値を返す) |
|---|---|---|
| `String` | フラットな UTF-8 バイト列(大きな連結は一時的にロープ) | `+`、`*`、`sub`、`gsub`、`upcase`、`strip`、`insert`… |
| `Array[T]` | 32 分木の永続ベクタ(RRB-Tree)。32 要素以下は 1 ノード | `push`、`pop`、`shift`、`unshift`、`set`、`insert`、`delete_at`、`+`、`map`、`select`、`sort`、`concat`… |
| `Hash[K, V]` | HAMT + 挿入順を保つ永続ベクタ。8 要素以下は線形配列 | `put`、`delete`、`merge`、`update`、`select`、`transform_values`… |
| `Set[T]` | HAMT | `add`、`delete`、`\|`、`&`、`-`… |
| `Range[T]`、`Tuple`、`Symbol`、数値、`Bool`、`Nil`、`Regexp` | | |

「実装」の列は設計です。現状では、`Array` はフラットなベクタ(`Int` だけ・`Float` だけの配列は機械語の語を持つ)、`Hash` は挿入順を保つハッシュ表(キーと値がすべて `Int` のものは非ボックス化して持つ)、`Set` は挿入順を保つハッシュ集合、`String` はフラットな UTF-8 文字列(14 バイト以下は値そのものの中。ロープはない)です。更新は、下に書くとおり参照が一意ならその場で行い、そうでなければコレクション全体を O(n) でコピーします。

```ruby
a = [1, 2, 3]
b = a.push(4)        # a は [1, 2, 3] のまま、b は [1, 2, 3, 4]
h = { name: "alice" }
h2 = h.put(:city, "Paris")
s = "abc"
t = s + "d"
```

Ruby の破壊的メソッド(`push`/`<<`/`[]=`/`sort!`/`map!`/`concat`/`delete`/`clear`/`gsub!`…)のうち、不変型にあるのは「新しい値を返す版」だけです。`<<` と `[]=` と `!` 付きメソッドは不変型には定義されていません。`arr << x` と書くと、コンパイラは `Array::Builder` を使うか `arr = arr.push(x)` と書くよう提案するエラーを出します(`Set`・`String`・`Bytes` の `<<` や、`Array`・`Hash` の `[]=` も同様)。

純粋なメソッドの結果を捨てると警告が出ます。今の対象は組み込みの不変型(`Array`・`Hash`・`Set`・`String`・`Bytes`、およびそれらに対する `Enumerable`/`Comparable`)のブロックを取らないメソッドで、`xs.push(1)` や `xs.sort` を文として書くと警告されます。ほかのメソッドや型に印を付ける方法は予定です。

```ruby
arr.push(4)          # 警告: 結果が使われていない。arr は変わらない
arr = arr.push(4)    # OK
```

### 計算量と「一意なら、その場で更新」

設計どおりの永続データ構造なら更新は `O(log32 n)` で実用上は定数ですが、今は共有されたコレクションの更新はそれをコピーするので O(n) です。どちらの場合も、Quarz のメモリ管理は参照カウントなので([05-execution.ja.md](05-execution.ja.md) §5)、`arr.push(4)` の時点で `arr` への参照がその一つしかなければ、新しい配列を作らずに**元の配列の領域をその場で更新**します。

```ruby
def collect(n: Int) -> Array[Int]
  acc: Array[Int] = []
  n.times { |i| acc = acc.push(i * i) }   # acc の参照は常に 1 つ → 毎回その場で追記、償却 O(1)
  acc
end
```

値を渡しても、その変数をもう読まないなら参照は増えません。値は呼び出しにムーブされ、仮引数がそれを引き継ぎます。更新したコレクションを返す補助メソッドを挟んでも参照は一意のままなので、次のループも線形です。

```ruby
def add(xs: Array[Int], v: Int) -> Array[Int] = xs.push(v)

ys: Array[Int] = []
n.times { |i| ys = add(ys, i) }   # ys は add にムーブされ、xs.push がその場で追加する
```

これは Lean 4 / Koka の「functional but in-place」と同じ技法で、Ruby 風の素直なループが可変配列と同程度に速く動きます。参照が共有されていれば自動的にコピー(パス上のノードのみ。現状はコレクション全体)にフォールバックするので、意味論は常に不変のままです。

## 3. Builder(可変・タスク局所)

複雑な構築処理や、FFI との境界、どうしても可変が必要なアルゴリズム(ヒープソート、グラフ探索の訪問済み集合など)のために、可変版の型を提供します。

```ruby
buf = String::Builder.new
buf << "hello" << " " << "world"
buf.to_s                            # => "hello world"(O(1): バッファを凍結して引き渡す)

squares = Array.build do |b|        # b: Array::Builder[Int]
  10.times { |i| b << i * i }
end                                 # => Array[Int]

index = Hash.build do |b|           # b: Hash::Builder[String, Int]
  words.each_with_index { |w, i| b[w] = i }
end

str = String.build { |b| b << "x" * 3; b << "y" }
```

- Builder は Ruby の可変 `Array`/`Hash`/`String` とほぼ同じ API を持ちます(`<<`、`[]=`、`push`、`pop`、`sort!`、`map!`、`delete`、`clear`、`concat`…)。破壊的メソッドは `self` を返します。
- `to_a`/`to_h`/`to_s`/`freeze` は不変値を O(1) で取り出します。中身をそのまま渡し、Builder は空になってまた詰められます。繰り返し覗きたいだけなら `snapshot`(O(n) コピー)を使います。
- Builder は **Shareable ではありません**。チャネルに送る、`Task.spawn` のブロックで捕捉する、`Atom` に入れる、定数にする、はどれもコンパイルエラーで、Builder のフィールドを持つクラスは Shareable になりません。
- `Array.build { }` の形は、Builder がブロックの外へエスケープしないことをコンパイラが保証でき、割り当てを最適化できます。

## 4. ユーザー定義クラスの不変性

```ruby
class Node
  @value: Int
  @children: Array[Node] = []
  def initialize(@value: Int, @children: Array[Node] = []); end
  def add(child: Node) -> Node = Node.new(@value, @children.push(child))
end

class Counter
  var @count: Int = 0
  def increment -> Nil
    @count += 1
  end
end
```

- フィールドは既定で不変です。`initialize` で代入し、その外では変更できません。
- `var @x: T` で可変フィールドになります。可変フィールドを持つオブジェクトは**可変オブジェクト**です。
- 可変オブジェクトは、それを作ったタスクの中でだけ使えます(§5。まだどこでも強制されているわけではなく、タスクの結果は検査されません)。
- `data` のフィールドはすべて不変で、`with` で「一部を変えたコピー」を作ります。

Ruby 流の「`attr_accessor` を並べて setter で状態を変える」設計は、Quarz では `var` を書くことで意図を明示することになります。`var` の数がそのクラスの「並行性に対する危うさ」の尺度になります。

### 生存期間と `deinitialize`

メモリは参照カウントで管理されるので([05-execution.ja.md](05-execution.ja.md) §5)、値は最後の参照がなくなったときに解放され、ほとんどの値は最後の使用で解放されます。解放が観測できる値は、Swift(5.7 以降)、C++、Rust と同じく、代わりにスコープの終わりまで生きます。

```ruby
class TempFile
  @path: String
  def initialize(@path: String) end
  def deinitialize
    File.delete(@path)
  end
end

def with_scratch -> Nil
  f = TempFile.new("/tmp/scratch")
  File.write("/tmp/scratch", "data")   # f はこの行より後で使われないが、
  run_tool("/tmp/scratch")             # ファイルはまだある
end                                    # ここで f がなくなり、ファイルも消える
```

- `def deinitialize`(パラメータなし。クラスか、クラスが include するモジュールに定義する。`data`、enum、組み込みの値クラス、extension には定義できない)は、インスタンスの最後の参照がなくなったときに実行されます。そこで送出された例外は標準エラーに警告として表示され、それ以上は伝わりません。
- ローカル変数、パラメータ、ブロックパラメータは、型がそのような値を含みうるとき、スコープの終わり(メソッド、またはブロックの各回)か再代入まで生きます。対象は、クラス型とモジュール型すべて(サブクラスが `deinitialize` を定義したり IO を持ったりしうるため。Shareable と同じくサブクラスは見ません)、手続き(捕捉したもの)、`Enumerator`、型パラメータ、そしてこれらを含む組み込みのコレクション、`data`、enum、union、タプルです。`Int`、`String`、`Array[Int]`、`data Point = (x: Float, y: Float)` は最後の使用で解放され、§2 のその場での更新も変わりません。そのため、ポート番号を知るためだけに使ったサーバーソケットも開いたままです。`server = TCPServer.new(host, 0); port = server.local_address.port` の後、メソッドの残りでそこに接続できます。
- そのような型の、使われない文の値(1行だけの `Lock.new(..)`)は文の終わりで解放されます。メソッドから返した値は、呼び出し側で生き続けます。
- `deinitialize` は、解放がスコープや文の終わり、またはそのような変数の再代入で起きるときはその場で実行されます(再代入では、古い値を最後に読んだのがそれより前、たとえばその値に対するループであっても、古い値は再代入の時点で解放されます)。それ以外の場所での解放(ブロックが捕捉した変数の再代入、コレクションから外れた要素など)では、解放したメソッドが戻るときか、次のスコープの終わりの早いほうで実行されます。最後の参照を手放したワーカーで、そこで動いているタスクの一部として実行されます。
- プログラムの終了時にまだ参照されているオブジェクトの `deinitialize` は実行されません。決まった時点で行う必要があることには `ensure`(またはブロックを取る API、`File.open(path) { }`)を使ってください。`deinitialize` はオブジェクトが所有するものを解放するためのものです。

## 5. Shareable(共有可能性)

ある型の値を**他のタスクに安全に渡せる**とき、その型は `Shareable` です。`data` と `enum` については、コンパイラがフィールドから導出します。クラスは `include Shareable` で宣言し(祖先から受け継ぐこともあります)、コンパイラはそのクラスとすべてのサブクラスを、それぞれの定義の場所で規則に照らして検査します。フィールドが不変なだけのクラスは Shareable になりません。サブクラスが可変な状態を足すことができ、そのクラスの型の値がサブクラスの値であることもあるためです。

Shareable であるもの:

- `Nil`、`Bool`、数値、`Symbol`、`String`、`Bytes`、`Regexp`、`Range[T]`(T が Shareable)
- 不変コレクション `Array[T]`/`Hash[K, V]`/`Set[T]`/タプル(要素型がすべて Shareable)
- `data` 型(フィールドがすべて Shareable)、`enum` 型(すべての variant のフィールドが Shareable)。型引数を持つものは、型引数が Shareable なとき
- `Shareable` を include するクラス(直接、または祖先や include したモジュールを通して)。どれも `var` フィールドを持たず、フィールドはすべて Shareable でなければならず、すべてのサブクラスも同じです。満たさない定義はエラーです(`var` フィールドを持つ `class Oops < RuntimeError` はエラーになります。`Exception` が `Shareable` を include しているためです)
- `Channel[T]`、`Task[T]`、`Atom[T]`、`Scope`(これらは内部で同期されている)
- Shareable な手続き、`shareable (A) -> R`([02-types.ja.md](02-types.ja.md) §9)。それが期待される位置に書いたブロックやラムダは、`Task.spawn` のブロックと同じく値で捕捉するので、捕捉する値は Shareable でなければならず、それに代入することもできません。ほかの手続きの型は Shareable ではありません
- 例外オブジェクト(`Exception` が `Shareable` を include しているので、すべての例外クラスが規則に照らして検査されます)
- `IO` ハンドル(標準入出力、開いたファイル、ソケット)。アクセスはランタイムが直列化する

Shareable でないもの:

- Builder 各種
- `Enumerator`(位置を持ち、受け手が可変なオブジェクトのこともあるため)
- `Shareable` を include しないクラス(フィールドにかかわらず)。`var` フィールドや Shareable でないフィールドを持つクラスが include するとエラーです
- `Shareable` を include しないモジュール。include するモジュールは Shareable なクラスしか include できません(Shareable でないクラスに `extension` で include するとエラーです)
- Builder や可変オブジェクトを捕捉した手続き、外側のローカル変数に代入する手続き

Shareable が要求される場所:

| 場所 | 理由 |
|---|---|
| `Channel[T]` の `T` | 他タスクに送られる |
| `Task.spawn`/`scope.spawn` のブロックが捕捉する変数 | 新しいタスクで実行される |
| `Atom[T]` の `T` | 複数タスクから読み書きされる |
| 定数 | すべてのタスクから見える |
| `Task[T]` の `T`(戻り値) | `await` で別タスクに渡る(`Task.spawn`・`scope.spawn`・`Task.blocking` のブロックの結果) |
| 例外 | タスク境界を越えて伝播する |

```ruby
counter = Counter.new            # 可変
Task.spawn { counter.increment }      # エラー: Counter は Shareable ではない

total = 0
Task.spawn { total += 1 }             # エラー: spawn のブロックは外側の変数に代入できない

n = Atom.new(0)
Task.spawn { n.update { |v| v + 1 } } # OK

class Account
  include Shareable              # 約束。ここと、すべてのサブクラスで検査される
  @inbox: Channel[Msg]
end
class Audited < Account
  var @count: Int = 0            # エラー: `Audited` は Shareable でなければならない
end
```

可変オブジェクトを別タスクに渡したいときは、不変値に変換します。Builder の `to_a` は O(1) です。

## 6. 等価性と同一性

- `==` は**構造的等価**です。`data`/`enum` は自動生成、コレクションは要素ごと、ユーザークラスは既定で同一性(上書き可。クラス独自の `==` は `Object` を取り、クラスは自分で確かめます。01-syntax.ja.md §3)。
- `hash` は `==` と整合するように定義します。`data`/`enum`/コレクションは自動生成。
- `equal?` は同一性で、再定義できません。不変値については、同一性に意味を持たせないでください。実装は同じ値を共有したり、コピーしたりして構いません(小さな文字列のインターン、`with` でフィールドが変わらない場合の自己返却など)。
- `eql?` は廃止します。静的型により `{ 1 => "a" }[1.0]` のような混同は型エラーになるため、`==`/`hash` の一組で十分です。
- `Hash` のキーと `Set` の要素は `Hashable`(`==` と `hash` を持つ)でなければなりません。Shareable である必要はありませんが、可変オブジェクトをキーにすると `hash` が変わりうることは Ruby と同じ注意点です。(現状では `Hashable` という制約はなく、キーは組み込みの型と `data`/`enum` の値では `==` と同じに比べ、クラスのインスタンスは同一性で比べます。ユーザ定義の `==`/`hash` はまだ使いません。)それ以外で値を探すものは、Ruby と同じく、要素をレシーバとして要素自身の `==` に尋ねます。`include?`、`index`、`rindex`、`find_index`、`count`、`delete`、`Hash#value?`、`Hash#key` がそうで、`Array#==` と `Hash#==` も要素と値をそう比べます(キーはキーとしての比較)。

## 7. 文字列

- `String` は常に UTF-8 の正しい列で、不変です。Ruby の多重エンコーディングはありません。他のエンコーディングは `Bytes`、`String#encode`、`Bytes#decode` で扱います(UTF-8、ASCII、ISO-8859-1。`Encoding` モジュールは予定)。
- `size`/`[]`/`each_char` はコードポイント単位、`bytesize` はバイト単位(`byteslice` は予定)、`graphemes` は書記素単位です。ASCII のみの文字列を内部フラグにより O(1) で添字アクセスするのは予定です。
- 文字列補間 `"#{a}#{b}"` と `+` の連鎖は、コンパイラが 1 回のバッファ確保にまとめます。
- `Symbol` と `String` は別の型です。`to_sym`/`to_s` で変換します。

## 8. Ruby の慣用句の書き換え

| Ruby | Quarz |
|---|---|
| `arr << x` | `arr = arr.push(x)`、または `Array.build { \|b\| b << x }` |
| `h[k] = v` | `h = h.put(k, v)` |
| `h[k] \|\|= []` | `h = h.put(k, h.fetch(k, []))`、または `h.fetch(k) { [] }` |
| `str << "x"` | `String.build { \|b\| b << "x" }` |
| `arr.sort!` / `arr.map!` | `arr = arr.sort` / `arr = arr.map { }` |
| `arr.delete(x)` | `arr = arr.delete(x)` |
| `obj.freeze` | 不要(既定で不変) |
| `obj.dup` | 不変値には不要(`dup` は組み込みの不変な値をそのまま返す) |
| `Struct.new(:a, :b)` | `data X = (a: T, b: U)` |
| `attr_accessor :x` | `var @x: T` + `attr_accessor :x` |
| `@cache \|\|= compute` | `var @cache: T? = nil` + `@cache \|\|= compute`(`Lazy`/`memoize` は予定) |
| `$stdout.puts` | `STDOUT.puts` |
| `@@count += 1` | `COUNT = Atom.new(0)` + `COUNT.update { \|n\| n + 1 }` |

## 9. 採用しなかった案

- **Rust 風の所有権・借用**: 可変オブジェクトの「移動」を型で追えますが、Ruby らしさが失われます。Quarz では可変オブジェクトを単純にタスク内に閉じ込め、境界を越えるときは不変値に変換させます。Builder の凍結が O(1) なので、実用上の損失は小さいと判断しました。
- **Erlang 風のメッセージの深いコピー**: 不変値を共有できるので、コピーは不要です。
- **`freeze` によるオブジェクト単位の動的な不変化**: 不変性が型に現れないため、静的検査に使えません。
- **可変コレクションを既定にして `freeze` を推奨**: Ruby との互換性は高まりますが、「既定で安全」になりません。Builder 側に Ruby の可変 API をそのまま残すことで、書き換えの負担を抑えています。
