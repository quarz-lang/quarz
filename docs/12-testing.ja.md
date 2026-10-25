# テスト: `quarz test`

`require "test"` で `Test` モジュールが使え、`quarz test` が cog やスクリプトのテストを実行します。形は Ruby の Test::Unit です。テストは `Test::Case` を継承したクラスの `test_*` メソッドで、`setup`/`teardown` と `assert_*` を使います。違いは言語の性質と、Go、Rust、Zig、Swift Testing から来ています。Quarz にはリフレクションがないので、`go test` が `TestXxx` 関数を見つけるように、コンパイラがテストを見つけます。assertion には型が付きます。可変な状態はタスクをまたがないので、テストごとの印なしに並列実行できます。

これは設計で、まだ何も実装されていません(docs/05 と docs/06 では `quarz test` と `test` は予定になっています)。

## 1. 形

```ruby
# test/stack_test.qz
require "test"

class StackTest < Test::Case
  # フィクスチャは初期化子付きのフィールド。インスタンスはテストごとに
  # 作られるので、これが Test::Unit の `setup` に当たる
  @stack: Stack[Int] = Stack[Int].new.push(1).push(2)

  def test_pop
    rest, top = @stack.pop
    assert_equal(2, top)
    assert_equal(1, rest.size)
  end

  def test_empty_pop
    e = assert_raise(Stack::Empty) { Stack[Int].new.pop }
    assert_match(/empty/, e.message)
  end
end
```

```
$ quarz test
Loaded suite test
Started
..F.
Finished in 0.012 seconds.

Failure: test_pop(StackTest) [test/stack_test.qz:12]:
<2> expected but was
<1>

4 tests, 7 assertions, 1 failure, 0 errors, 0 pendings, 0 omissions
```

- **テスト**は、`Test::Case` のサブクラスの公開インスタンスメソッドで、名前が `test_` で始まり、パラメータを取らないもの(またはデータ付きで 1 つ取るもの。§4)です。コンパイラが一覧を作り、実行時には何も登録しません。テストファイル自身にはトップレベルの文がありません。
- **テストケース**のインスタンスは、Test::Unit と同じくテストごとに作ります。その上で `setup`、テスト、`teardown` が動き、フィールドはそのインスタンスのものです。フィクスチャは初期化子付きのフィールドです(フィールドは宣言の場所か `initialize` で値を決めなければなりません。[01-syntax.ja.md](01-syntax.ja.md) §3)。`setup` は副作用のあること(ソケットやファイルを開くなど)のためで、`teardown` がそれを戻します。`setup` で作らなければならないフィクスチャは `var @x: T? = nil` のフィールドにし、使うたびに絞り込みます。インスタンスはテストを実行するタスクに閉じているので、同じクラスのテストも別のクラスのテストも並列に実行できます(§6)。
- テストファイルにトップレベルの文があれば、ファイルを読み込んだときに、どのテストより前に実行されます。スクリプトのテストが `require_relative` でスクリプトを読むのはここです。
- `quarz test` は、テストファイル、生成したランナー、ライブラリからプログラムを組み立て、型検査して実行します。テストファイルの型エラーは、ほかのコンパイルエラーと同じように報告されて実行全体を失敗させます。そのテストだけ飛ばすことはしません。

## 2. ファイルと発見

- cog(アプリケーションかライブラリ。[10-cogs.ja.md](10-cogs.ja.md))では、`quarz test` は `test/**/*_test.qz` を実行します。`test/test_helper.qz` があれば最初に読み込みます(テストファイルは Ruby と同じく `require_relative "test_helper"` と書きます。ランナーも読み込むので、書き忘れても変わりません)。`test/` の下のほかのファイルは、テストファイルが require したときだけ読み込みます。
- テストファイルは、ライブラリの cog をその利用者と同じようにモジュール名の下に見ます(`Webkit::Router`)。cog の `[dependencies]` と `[dev-dependencies]` も見えます。`quarz test` は、テストファイルとランナーからなる合成のルートを作り、cog をその依存として読み込みます。ルートのインポートは cog のモジュールと両方の依存の表です。テストファイルは cog のモジュールの一部ではないので、cog のファイル単位の `def` には届きません(Go の外部テストパッケージと同じ)。内部の細部のテストは、その細部のある `src/` の側に、公開 API から呼ばれる private メソッドとして書きます。アプリケーションの宣言は、そのファイル同士がそうであるようにそのまま見え、`src/main.qz` の文は実行しません(そのファイルは宣言だけとして読み込みます)。
- `[dev-dependencies]` はほかの依存と一緒に解決して固定します(`Cog.lock` に載ります。Cargo のロックと同じです。今は読んで検証するだけで使っていません)。テストファイルはスクリプトのファイルのように読み込み、ファイル同士の `require_relative` が使えます。cog の `src/`(すべてのファイルを読み込み、`require_relative` は拒否する)とは違います。
- スクリプトは `quarz test path/to/foo_test.qz` で試します(複数のパスやディレクトリも指定できます)。`require_relative` したファイルも一緒に読み込まれます。
- コンパイラは、読み込んだすべてのファイルから、`Test::Case` を継承し `abstract` でないクラスを集め、それぞれについて(自身のメソッド、継承したもの、include したモジュールのもの)`test_*` メソッドを、ファイルの順、宣言の順に並べます。データ用以外のパラメータを取る `test_*` メソッドや公開でないものは、メソッド名を挙げたコンパイルエラーです。黙って飛ばしません。
- `quarz test --list` は見つけたテストを `StackTest#test_pop` の形で表示して終わります。

## 3. ライブラリ

```ruby
module Test
  class Case
    # 各テストの前後。インスタンスはテストごとに新しい
    def setup -> Nil = nil
    def teardown -> Nil = nil
    # クラスのテスト全体の前後に 1 回。インスタンスなし(クラスメソッド)
    def self.startup -> Nil = nil
    def self.shutdown -> Nil = nil

    # このクラスのテストの制限時間(既定は実行全体のもの、60 秒)
    def self.timeout -> Duration? = nil

    def assert(value: Object, message: String? = nil) -> Nil         # 真
    def refute(value: Object, message: String? = nil) -> Nil         # 偽
    def assert_true(value: Bool, message: String? = nil) -> Nil
    def assert_false(value: Bool, message: String? = nil) -> Nil
    def assert_equal[T](expected: T, actual: T?, message: String? = nil) -> Nil
    def refute_equal[T](expected: T, actual: T?, message: String? = nil) -> Nil
    def assert_nil(value: Object?, message: String? = nil) -> Nil
    def refute_nil(value: Object?, message: String? = nil) -> Nil
    def assert_same(expected: Object, actual: Object, message: String? = nil) -> Nil   # equal?
    def assert_in_delta(expected: Float, actual: Float, delta: Float = 0.001, message: String? = nil) -> Nil
    def assert_in_epsilon(expected: Float, actual: Float, epsilon: Float = 0.001, message: String? = nil) -> Nil
    def assert_match(pattern: Regexp, actual: String, message: String? = nil) -> Nil
    def refute_match(pattern: Regexp, actual: String, message: String? = nil) -> Nil
    def assert_includes[T](collection: Enumerable[T], element: T, message: String? = nil) -> Nil
    def refute_includes[T](collection: Enumerable[T], element: T, message: String? = nil) -> Nil
    def assert_empty(collection: Enumerable[Object], message: String? = nil) -> Nil
    def refute_empty(collection: Enumerable[Object], message: String? = nil) -> Nil
    def assert_empty(text: String, message: String? = nil) -> Nil
    def assert_compare[T: Comparable[T]](lhs: T, op: Symbol, rhs: T, message: String? = nil) -> Nil   # :<, :<=, :>, :>=
    def assert_raise(klass: Class, message: String? = nil, &: () -> Nil) -> Exception   # klass かそのサブクラス
    def assert_raise_message(pattern: Regexp | String, &: () -> Nil) -> Exception
    def assert_nothing_raised(message: String? = nil, &: () -> Nil) -> Nil

    def flunk(message: String = "Flunked") -> Nothing
    def pend(message: String = "pending") -> Nothing     # 数えるが失敗ではない
    def omit(message: String = "omitted") -> Nothing     # テストはここで終わり、省略として数える
    def omit_if(condition: Bool, message: String = "omitted") -> Nil
    def omit_unless(condition: Bool, message: String = "omitted") -> Nil
    def notify(message: String) -> Nil                   # 報告に載せるメモ
  end
end
```

- **型付きの assertion。** `assert_equal[T](expected: T, actual: T?)`。`T` は `expected` で決まり、`actual` は `T` か nil でなければなりません(よくある `assert_equal(1, h["k"]?)` の nil は、型エラーではなく失敗です)。なので `assert_equal(1, "1")` と `assert_equal(2, 2.0)` はコンパイルエラーで、Test::Unit なら実行時に失敗するところです。リテラルは actual の型で書きます(`x: Float` に対する `assert_equal(2.0, x)`、`xs: Array[Int]` に対する `assert_equal([1, 2], xs)`)。本当に型が違うときは、意図して変換します(`assert_equal("1", n.to_s)`)。nil には `assert_nil(x)` を使います。`assert_equal(nil, x)` は `T = Nil` に決まり、ほかの値を取りません。`assert_predicate` はなく、`assert(x.empty?)` と書きます。
- **失敗のメッセージ。** `assert_equal` は `inspect` を使って `<expected> expected but was <actual>` と出し、改行を含む文字列同士やコレクション同士では行の差分を添えます。任意の `message` は先頭に出ます。
- **失敗した場所。** 失敗した assertion は `Test::AssertionFailed < Exception` を投げます(`StandardError` ではないので、テスト対象のコードの `rescue => e` に飲み込まれません)。報告には、その assertion のあるテストファイルと行を出します。バックトレースのうち `test` ライブラリの外の最初のフレームです。なので、テストクラスの補助メソッドの中の assertion は、その中の行で報告されます(Go の `t.Helper()` のように補助メソッドの呼び出し元で報告するには `helper!` を呼ぶ……*最初の版にはありません*)。
- **`assert_raise`** は例外を返すので、続けて中身を確かめられます。例外クラスは値(`Class`)として取り、そのサブクラスも通ります。ライブラリは `Exception` を rescue して `e.kind_of?(klass)` で確かめます。これはこの作業で足すネイティブで、`Object#kind_of?(klass: Class) -> Bool` はクラスの*値*を調べます(`is_a?(T)` は*型*を調べて絞り込むので、その名前はそのために残します)。結果は `Exception` です(`message` は使えます。サブクラスのフィールドには `as` が要ります)。メッセージを渡すと、投げられた例外のメッセージがそれと等しくなければなりません。型付きの形 `assert_raise[E: Exception](klass: Class[E]) -> E` は、型システムに `Class[T]` が入るのを待ちます(§9)。
- **保留と省略。** `pend` は失敗すると分かっているテストに付けます(Test::Unit の `pend`)。保留として数え、その後でテストが*通った*ときは失敗(「pending test passed」)にして、直ったことに気づけるようにします。`omit` はテストをそこで終え、省略として数えます(環境に何かが欠けているとき)。どちらも要約に出て、`-v` では名前つきで出ます。
- `Test::Unit::TestCase` は Ruby での名前のままの `Test::Case` で、移植したテストのためにあります。

## 4. データ駆動のテスト

Test::Unit の `data` は、1 つのテストメソッドを複数の入力で実行します。ここではデータはメソッドなので、コンパイラが検査できます。

```ruby
class ParseTest < Test::Case
  def data_parse -> Hash[String, [String, Int]]
    {
      "decimal" => ["42", 42],
      "hex"     => ["0x2a", 42],
      "signed"  => ["-7", -7],
    }
  end

  def test_parse(data: [String, Int])
    text, expected = data
    assert_equal(expected, Parser.parse(text))
  end
end
```

- パラメータを 1 つ取るテストメソッドは、同じクラスの `data_<名前>` メソッドからデータを取ります。それはパラメータの型 `T` に対して `Hash[String, T]` を返します(ランナーをコンパイルするときに検査されます。行はテストのタスクへ渡りうるので、`T` は Shareable です)。各エントリが `test_parse[hex]` という名前の独立したテストになり、インスタンス、`setup`、`teardown` もそれぞれで、`-n` で選べます。`--list` は名前を出すために `data_*` メソッドを呼ぶので、その分だけテストのコードを実行します。
- これは行ごとに名前のある Go のテーブルテストであり、コードを実行するクラス本体なしの Test::Unit の `data` です(クラス本体は宣言しかできません)。

## 5. ランナー

`quarz test` は、`go test` が `main` を生成するようにランナーを生成するので、ライブラリにもプログラムにもリフレクションは要りません。

```ruby
# 生成されるもの
Test.run(ARGV, [
  Test::Suite.new("StackTest", "test/stack_test.qz", -> { StackTest.new }, [
    Test::Entry.new("test_pop", 10, ->(c: Test::Case) { c.as(StackTest).test_pop }),
    Test::Entry.new("test_empty_pop", 16, ->(c: Test::Case) { c.as(StackTest).test_empty_pop }),
  ]),
  Test::Suite.new("ParseTest", "test/parse_test.qz", -> { ParseTest.new }, [
    Test::Entry.each("test_parse", 12,
                     ->(c: Test::Case) { c.as(ParseTest).data_parse },
                     ->(c: Test::Case, d: [String, Int]) { c.as(ParseTest).test_parse(d) }),
  ]),
])
```

- `Test::Suite` は、クラス名、ファイル、インスタンスの作り方(`shareable () -> Test::Case`。`Test::Case` のサブクラスはパラメータ付きの `initialize` を持てません。持つとランナーの `.new` がコンパイルできず、そう報告されます)、エントリを持ちます。`Test::Entry` はテストの名前、行、呼び出し(`shareable (Test::Case) -> Nil`)です。どちらもジェネリックではありません。複数のクラスのスイートを 1 つの配列に入れるためで、`Suite[C]` ではそれができません(`Suite[StackTest]` と `Suite[ParseTest]` の配列は union であって `Suite[Case]` ではありません)。そのため生成されるラムダは、インスタンスをスイートのクラスへ `as` でキャストします。これは失敗しません。どちらも Shareable で、手続きは `shareable` です。生成されるラムダは何も捕捉しないのでこれを満たし、テストを別のタスクで実行できます(§6)。`Test.run` がそれらを実行し、報告を出し、失敗かエラーがあれば 1 で終了します(すべて通過か保留か省略なら 0)。
- ランナーは、テストファイルを宣言・検査した後に生成します(何が `Test::Case` を継承するかは構文からは見えません。別名や抽象クラスの基底があるためです)。そして、REPL が 1 行を足すのと同じ方法(`Session`)で、検査済みのプログラムにもう 1 つの単位として加えます。全体を 2 回検査するのではありません。
- 1 つのテストは次のように動きます。クラスの最初のテストの前に `startup` を 1 回。各テストでは新しいインスタンスに `setup`、テスト、`teardown`(失敗の後も)。各テストは `Task.timeout(limit)` の中で動くので、永遠に待つテスト(チャネル、ソケット、`sleep`)はエラー(「timed out after 60 s」)になって、実行全体は止まりません。待たないループは、どのプログラムでもそうであるように実行を止めてしまいます([04-concurrency.ja.md](04-concurrency.ja.md) §2)。タイムアウトは `StandardError` の `Task::Timeout` なので、テスト対象のコードの `rescue => e` が飲み込むことがあり、そのときランナーはテストを終わらなかったものとして失敗にします。自分のタスクを待ちたいテストは自分で `Task.scope` を開きます。残した `Task.spawn` のタスクは、どのプログラムでもそうであるように動き続け、ランナーには見えません。クラスの最後のテストの後に `shutdown`。テストのタスクにはテストの名前(`StackTest#test_pop`)を付けるので、ランタイムのメッセージにその名前が出ます。
- テストが投げた `Test::AssertionFailed` 以外のものは**エラー**(E)で、クラス、メッセージ、バックトレースを出します。`DeadlockError`(すべてのタスクが待っていて、タイマーもない)はどのプログラムでもそうであるようにプロセスを終わらせ、ランナーには捕まえられません。制限時間付きで動いているテストの間はタイマーがあるので起きず、`--timeout=0` のときだけ起きます。そのときはランタイムのメッセージにテストのタスクの名前が出ます。
- 順序はファイルの順、そして宣言の順です(Go、Zig)。順序依存を見つけるには `--order=random` と `--seed=N`(seed は表示されます。Test::Unit の既定はアルファベット順、Rust と minitest はランダム)。
- 出力は Test::Unit の進行表示(`.` 成功、`F` 失敗、`E` エラー、`P` 保留、`O` 省略)、次に失敗とエラーを順に、最後に要約の行です。`-v` では各テストの終わりに名前と時間を 1 行出します。テストが出力したものはそのまま STDOUT に出ます(捕捉はしません。§9)。

オプション:

| オプション | 意味 |
|---|---|
| `-n NAME`、`--name=NAME` | `Class#method`(またはメソッド名、または `method[label]`)に `NAME` を含むテストを実行する。`/regexp/` でパターン。繰り返せる |
| `-v`、`--verbose` | テストごとに 1 行、時間つき |
| `--list` | テストを表示して終わる |
| `--order=defined\|random`、`--seed=N` | 順序。`random` は seed を表示する |
| `--fail-fast` | 最初の失敗かエラーで止める |
| `--parallel[=N]` | 最大 N 個のタスクで同時に実行する(§6。既定はワーカー数) |
| `--timeout=DURATION` | テストごとの制限時間(`60s`。クラスの `self.timeout` が優先。`0` でなし) |
| `--release` | 解釈実行でなくネイティブにコンパイルして実行する(`quarz build`)。始まりは遅く、走りは速い |
| `--junit=PATH` | JUnit XML の報告も書く(CI 用) |

## 6. 並列実行

`--parallel` では各テストがタスクになり、同時に最大 N 個が動きます。クラスは単位ではありません。`startup`/`shutdown` はクラスごとに 1 回、最初のテストの前と最後のテストの後に動きます。プログラム自身の状態については、言語によって安全です。テストのインスタンスはタスクに閉じ、共有するものは Shareable か `Atom` でなければなりません。プロセスの状態(カレントディレクトリ、環境変数、ファイル、ポート)については安全ではなく、どの並列ランナーでもそうであるように、テストはそれらを共有します。単独で動かなければならないテストを持つクラスは `def self.serial? -> Bool = true` を定義します(そのテストは 1 つずつ動き、その間ほかのテストは動きません)。並列のテストの出力行はスケジューリングのとおりに交じります。並列を既定にしない(Rust は既定)のは、この出力とプロセスの状態のためです。利点があるのは IO や `sleep` の多いスイートで、CPU を使うスイートはテスト自身のタスクですでにワーカーを使っています。*(`--parallel` を既定にするかは、スイートが出てきてからの判断です)*

## 7. 補助と共有

- 補助メソッドはテストクラスに書くか、テストクラスが `include` するモジュールに書きます(`module Factories; def user(name: String) -> User ... end; end`)。モジュールは `test_*` メソッドも持てます。それは include したすべてのクラスのテストになります(Test::Unit も許しています)。
- 複数のテストクラスの基底は `abstract class ApiTest < Test::Case` と宣言します。その自身の `test_*` メソッドはその上では実行されず(インスタンスがない)、具体的なサブクラスの上でだけ実行されます。
- 高くつくフィクスチャは `self.startup` で定数に近い `Atom` に作るか、テストごとに要るなら `setup` で作ります。
- モックやスタブはありません。テストが置き換える依存はパラメータかモジュール型にし、テストが自前の `data` やクラスで実装します(型は名前で決まるので、偽物はそのモジュールを include します)。Go と同じ答えです。

## 8. スクリプトのテスト

スクリプトのテストはその隣に `foo_test.qz` として置き、`require_relative "foo"` して、`quarz test foo_test.qz` で実行します。`quarz run foo_test.qz` はそのファイルのトップレベルの文だけを実行し、テストファイルにはそれがないので、何も出しません。ランナーを足すのは `quarz test` で、ライブラリの `at_exit`(Test::Unit の autorun)ではありません。実行時にテストを一覧できるものがないからです。

## 9. 後で

- `Class[T]`。クラスオブジェクトの型にインスタンスの型を添えたもので、`assert_raise[E](klass: Class[E]) -> E` と、型パラメータに対する `rescue` のため。`kind_of?` にも型付きの形ができます。
- `capture_output { }`(ブロックが STDOUT/STDERR に出したもの。タスクごと)には、ランタイムがタスクの標準ストリームを差し替える仕組みが要ります。それを使う `assert_output`。
- 補助メソッドの呼び出し元で失敗を報告する `helper!`(Go の `t.Helper()`)。
- ベンチマーク(`bench_*` メソッドと `quarz test --bench`。Go と同じ)、`--coverage`。
- `Test::Case` の中の `test "説明" do ... end` 宣言(Zig の `test "name" {}`、Rails の `test "..."`)。文法の追加で、コンパイラが `test_説明` と名付けます。
- 式そのものを表示する assertion(Swift Testing の `expect(x == 1)`)には、コンパイラがソースの文字列を渡す必要があります。後で組み込みとして可能です。

## 10. 採用しなかった案

- **`describe`/`it`(RSpec、Crystal の spec):** 実行時に登録する入れ子のブロックと、`should`/`expect(x).to eq(y)` のマッチャ。リフレクションが要らないので最も楽な道でしたが、クラスと型付きメソッドの言語には Test::Unit のクラスとメソッドが合います。テストはメソッド、フィクスチャは型のあるフィールド、補助はメソッドで、コンパイラがそれらを見つけて検査します。
- **実行時の発見(`at_exit` の autorun、`methods.grep(/^test_/)`):** Quarz にリフレクションはなく、このために足すとすべてのプログラムにメソッド表の費用がかかります。
- **属性(`#[test]`、`@Test`):** Quarz に属性はありません。`Test::Case` のメソッドの `test_` 接頭辞が約束で、コンパイラが検査できます(形の違う `test_*` メソッドはエラー)。
- **ファイルごとに 1 クラス、cog のモジュールの中のテストファイル(Go の内部テスト、Rust の `mod tests`):** 内部の細部が見えるテストは細部を試したくなります。cog のモジュールの境界が API で、テストはその最初の利用者です。
