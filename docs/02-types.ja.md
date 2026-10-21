# 型システム

Quarz は静的型付きです。クラス・モジュール・メソッドの構造がコンパイル時に確定し、メソッド呼び出しはすべてコンパイル時に解決されます。ただし Ruby らしい書き心地を保つため、メソッドの境界以外では型を書く必要がほとんどないように設計しています。

設計方針:

1. **メソッドの境界では型を書く、中では書かない。** 引数型は必須、戻り値型とローカル変数は推論。これによりファイル単位の分割コンパイルと、インタプリタ起動時の高速な型検査が両立します。
2. **nil は普通の型の値ではない。** `String` 型の値が `nil` であることはなく、`nil` を取りうるなら `String?` と書きます。
3. **合併型とフロー型付け。** `Int | String` のような合併型を直接扱え、`if`/`case/in`/`is_a?` で絞り込めます。
4. **不変なものは共変。** 不変コレクションは要素型について共変なので、`Array[Int]` を `Array[Int | Nil]` として渡せます。

## 1. 型の構文

| 型 | 例 | 説明 |
|---|---|---|
| クラス・モジュール | `Int`、`String`、`Comparable[T]` | 名前的(nominal)型 |
| ジェネリクス | `Array[Int]`、`Hash[String, Int]` | 角括弧で型引数 |
| nil 許容 | `String?` | `String \| Nil` の省略形 |
| 合併 | `Int \| String \| Nil` | |
| タプル | `[Int, String]` | 長さと各要素の型が固定 |
| 手続き | `(Int, String) -> Bool`、`() -> Nil` | ブロック・lambda の型 |
| トップ | `Object` | すべての型のスーパータイプ |
| ボトム | `Nothing` | `raise`、`exit`、無限ループの型。すべての型のサブタイプ |
| 型変数 | `T`、`K`、`V` | 宣言した型パラメータ |
| 自己型 | `self` | `def dup -> self` のように使う |

式の文脈で `Array[Int]` と書くと型そのものを指す式になり、`Array[Int].new` のように使えます(Ruby の `Array.[]` によるコンストラクタはありません)。

## 2. 組み込み型

| 型 | Ruby での対応 | 備考 |
|---|---|---|
| `Nil` | `NilClass` | 値は `nil` のみ |
| `Bool` | `TrueClass`/`FalseClass` | `true`/`false` |
| `Int` | `Integer` | **任意精度**。実装は 63 ビットのタグ付き整数をあふれたらヒープ上の多倍長に昇格(Ruby と同じ挙動) |
| `Int8`..`Int64`、`UInt8`..`UInt64` | - | 固定幅整数(*予定*)。あふれると例外(`--release` では未定義ではなくラップ、ではなく常に例外) |
| `Float` | `Float` | IEEE 754 倍精度 |
| `Float32` | - | FFI と数値計算向け(*予定*) |
| `String` | `String` | 不変。常に UTF-8 |
| `Bytes` | 文字列(ASCII-8BIT) | 不変のバイト列 |
| `Symbol` | `Symbol` | |
| `Array[out T]` | `Array` | 不変・永続 |
| `Hash[K, out V]` | `Hash` | 不変・永続・挿入順保持 |
| `Set[out T]` | `Set` | 不変・永続 |
| `Range[T]` | `Range` | |
| `Regexp`、`MatchData` | 同名 | |
| `Proc` = `(A...) -> R` | `Proc` | 手続き型の総称 |
| `Enumerator[T]`、`Lazy[T]` | 同名 | 外部イテレータ(`Lazy[T]` は*予定*) |
| `Channel[T]`、`Task[T]`、`Atom[T]`、`Scope` | - | 並行プリミティブ |
| `Array::Builder[T]`、`Hash::Builder[K, V]`、`String::Builder`、`Bytes::Builder`、`Set::Builder[T]` | 可変の `Array` など | 可変・タスク局所 |
| `Class` | `Class` | `obj.class` の型(型引数なしで書く)。`name` などごく限られたリフレクション |

数値の演算は Ruby と同じ意味です。`7 / 2` は `3`、`-7 / 2` は `-4`、`7 % -2` は `-1`、`1 + 1.5` は `2.5`。混在演算は `Int#+(Float) -> Float` などの多重定義として定義されています。固定幅整数(予定)と `Int` の混在は暗黙には行わず、`to_i`/`to_i64` などで明示的に変換する予定です。

## 3. ジェネリクス

```ruby
class Stack[T]
  @items: Array[T] = []
  def push(x: T) -> Stack[T] = Stack[T].from(@items.push(x))
  def peek -> T? = @items.last?
end

def max_by[T, U: Comparable[U]](xs: Array[T], &key: (T) -> U) -> T?
  ...
end

module Container[out T]      # 共変
  abstract def get -> T
end
```

- クラス、モジュール、`data`、`enum`、メソッドが型パラメータを持てます。
- 制約は `T: Comparable[T]` のように書きます。複数は `T: Comparable[T] & Describable`(任意のモジュール)。
- 変位は `out`(共変)/`in`(反変)で宣言し、無印は不変です。共変の型パラメータはメソッドの引数位置に現れてはならない、といった検査をコンパイラが行います(予定。今は変位を部分型の判定に使うだけで、位置は検査していない)。
- メソッドの型引数は呼び出し時に推論されます。明示したいときは `max_by[Person, Int](people) { |p| p.age }`。
- 実装は**単相化**(monomorphization)を既定とし、`Int`/`Float` などの非ボックス型についてはそれぞれ専用のコードが生成されます。参照型どうしはコードを共有します。インタプリタでも同じ方針です(予定。今はジェネリックなコードをタグ付きの値に対して 1 度だけコンパイルする)。

## 4. 合併型と nil 安全性

```ruby
def find(id: Int) -> User?
  users[id]?
end

user = find(1)
user.name              # エラー: User? に name はない
user.name if user      # OK: 絞り込み
user&.name             # String?
name = user&.name || "anon"
u = find(1) || raise NotFound    # raise の型は Nothing なので u は User
```

- `nil` は `Nil` 型の唯一の値で、他のどの型の値でもありません。
- `T?` は `T | Nil` の糖衣です。`Int | String | Nil` のような任意の合併型も書けます。
- 合併型の値に対して呼べるのは、すべての構成型に共通する(かつ戻り値型が互換な)メソッドだけです。それ以外は絞り込んでから呼びます。
- 合併型は正規化されます: `Int | Int` → `Int`、`Int | Object` → `Object`、`(Int | String) | Nil` → `Int | String | Nil`。

## 5. 型推論

推論は**双方向・局所的**です。メソッドの引数型が既知なので、推論は 1 メソッド本体で閉じ、プログラム全体の推論は行いません(Crystal のような全体推論は、コードが大きくなるとコンパイル時間が線形以上に伸びるので採用しません)。

- **ローカル変数**: 最初の代入の型。`x = 1` なら `Int`。
- **戻り値型**: 省略時は本体の型(`return` の型と最後の式の合併)。再帰呼び出しがあるメソッド、`abstract def`、`extern def`、公開 API として `.qzi` に書き出されるメソッド(予定)で戻り値型が推論不能なときはエラーになり、注釈を求めます。
- **空リテラル**: `[]`、`{}`、`Set[]` は期待型があればそれに従い、なければ `Array[?T]` のような型変数を持ち、同じメソッドの中のあとの使い方で決まります。

```ruby
counts = words.reduce({}) { |h, w| h.put(w, h.fetch(w, 0) + 1) }   # {} は Hash[String, Int]
names: Array[String] = []          # 期待型から
xs = []                            # ここではまだ Array[?T]
xs = xs.push(1)                    # ここで決まり、xs は Array[Int]
```

- **ブロックの引数**: 渡し先の `&block` の型から決まります。`[1, 2].map { |x| x * 2 }` の `x` は `Int`。
- **ジェネリックメソッドの型引数**: 引数とブロックの型から単一化で決まります。
- **数値リテラル**: 期待型が `Float` なら `1` は `Float` として扱われ、期待型が `Int32` なら `Int32` になります(固定幅整数ができてから)。既定は `Int`/`Float`。
- **タプルと配列**: 配列リテラルは期待型(タプルか配列)に従います。期待型がなければ、要素の型を合わせると合併型になるときはタプル、共通の型があるときは配列です。`[w, w.size]` は `[String, Int]`、`[1, 2]` は `Array[Int]`、`[circle, rect]` は `Array[Shape]`。`return a, b` と多重代入の右辺も同じ規則です。タプルは要素の型を合わせた型の配列でもあるので、配列のメソッドが使えます。要素がすべて比較できるタプルは、要素ごとに比較できます(`<`、`<=>`、`sort`、`max`)。比較できる型を要素に持つ配列も同じです。タプルのリテラルを代入したローカル変数(`t = [1, "a"]`)は、その配列の型で宣言され、タプルに絞り込まれます。`t[0]` は `Int` で、`t = t.push(2)` もできます。

## 6. フロー型付け(絞り込み)

条件分岐によってローカル変数の型が絞り込まれます。

```ruby
def describe(x: Int | String | Nil) -> String
  return "nothing" if x.nil?          # 以降 x: Int | String
  if x.is_a?(Int)
    "int #{x + 1}"                    # x: Int
  else
    "str #{x.upcase}"                 # x: String
  end
end

case v
in Int => n then n + 1
in String => s then s.size
end

while (line = io.gets?)             # line: String(ループ内)
  puts line
end
```

絞り込みが効く条件: 真偽判定(`if x`)、`x.nil?`、`x.is_a?(T)`、`x in Pattern`(真の分岐だけ)、`case/in`、`nil` との `==`/`!=` による比較(`true`/`false`/enum の空バリアントとの比較は予定)、`&&`/`||`/`!`/`and`/`or`/`not` の組み合わせ、`return`/`raise`/`next`/`break` による早期脱出、代入。

絞り込まれるのは**ローカル変数、不変フィールド(`@x`)、`data` のフィールド**です(`data` の本体の中で `@name` として読んだとき。`p.name` のような読み出しはメソッド呼び出しです)。`var` フィールドや任意のメソッド呼び出し結果(`user.name`)は、途中で変わりうるので絞り込まれません。一度ローカル変数に受けてください。可変フィールドを持たない設計が既定なので、Ruby の `@x && @x.foo` のような慣用句の多くはそのまま通ります。

## 7. キャスト

```ruby
n = obj.as(Int)         # 失敗すると TypeError
n = obj.as?(Int)        # Int?
f = n.to_f              # 変換メソッド(キャストではない)
```

ダウンキャストは実行時検査付きです。安全でない再解釈キャストは FFI 層(`Pointer#cast`)にしかありません。

## 8. メソッド解決と多重定義

- 呼び出しはレシーバの静的型で解決されます。候補は、そのクラス、スーパークラス、include したモジュール、スコープで有効な `extension` のメソッドです。
- 同名メソッドの多重定義があるときは、引数の個数、キーワード、型によって最も特定的なものが選ばれます。曖昧ならエラーです。(現状では、宣言順で最初に合う多重定義が選ばれ、曖昧さは報告されません。)
- サブクラスで上書きされうるメソッドは仮想呼び出し(vtable)になります。クラス階層はプログラム全体で確定するため、上書きのないメソッドはリンク時に静的呼び出しへ置き換えられます(クラス階層解析)。
- モジュール型のレシーバへの呼び出しはインターフェース呼び出し(クラスごとのモジュール実装テーブル)です。
- `respond_to?` はコンパイル時定数に畳まれます。`send`/`public_send`/`method`/`define_method`/`method_missing`/`instance_variable_get` は存在しません。

## 9. Shareable(共有可能性)

`Shareable` はコンパイラが自動的に導出するマーカーモジュールで、「他のタスクに安全に渡せる型」を表します。詳細は [03-data-model.ja.md](03-data-model.ja.md) §5 ですが、型システムの観点では次のように使われます。

```ruby
class Channel[T: Shareable]
class Atom[T: Shareable]
def spawn[T: Shareable](&block: () -> T) -> Task[T]   # ブロックの捕捉変数も Shareable である必要がある
                                                       # (T の制約はまだ強制していない)
```

ユーザーが `include Shareable` と書くことはできません。型の構造から決まります。(現状では `include Shareable` は受け付けられて無視されます。エラーにするのは予定です。)

## 10. 採用しなかった案

- **構造的型付け(Go のインターフェース、TypeScript)**: ダックタイピングに近く魅力的ですが、Ruby では「`each` を持つ」だけでなく「`each` の意味」を期待しています。名前的なモジュール + `extension` による後付け適合で同じ柔軟性を得つつ、適合の意図を明示させる方を選びました。
- **動的型 `Dynamic`**: 試作時の手軽さのために検討しましたが、1 つでもあるとすべてのクラスに実行時メソッドテーブルが必要になり、インタプリタと AOT の両方で最適化を妨げます。試作の手軽さは推論の強化で得ることにします。
- **全体推論(Crystal)**: 引数型を省けますが、コンパイル時間とエラーメッセージの質が犠牲になります。「メソッドの境界では書く」が Quarz の割り切りです。
