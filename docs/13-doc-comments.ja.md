# ドキュメントコメント: `quarz doc`

宣言の直上に書いたコメントが、その宣言のドキュメントになります。本文は Markdown で、クラスやメソッドの名前を書いたコードスパンはリンクに、フェンス付きコードブロックは `quarz test` がコンパイルして実行する例になります。`quarz doc` は名前のドキュメントを端末に出力し、cog のサイトを生成します。形は Ruby のもの(RDoc と Crystal は定義の上のコメントをドキュメントにします)で、検査されるリンクと実行される例は Rust と Elixir のものです。

## 1. 形

```ruby
# `T` の後入れ先出しのコレクション。不変で、`push` と `pop` は
# `Array#push` と同じく新しいスタックを返す。
#
# ```
# s = Stack[Int].new.push(1).push(2)
# s.size                 # => 2
# s.pop[1]               # => 2
# Stack[Int].new.pop     # raises Stack::Empty
# ```
class Stack[T]
  # 要素。底が先。
  @items: Array[T]

  # 空のスタックへの `pop` が投げる。
  class Empty < StandardError
  end

  def initialize(items: Array[T] = [])
    @items = items
  end

  # `x` を頂上に載せたスタック。
  def push(x: T) -> Stack[T] = Stack[T].new(@items.push(x))

  # 頂上を除いたスタックと、その頂上。
  #
  # ## Raises
  #
  # 要素がなければ `Empty`。先に `empty?` で確かめる。
  def pop -> [Stack[T], T]
    raise Empty.new("empty stack") if @items.empty?
    [Stack[T].new(@items[0...-1]), @items[-1]]
  end

  def size -> Int = @items.size
  def empty? -> Bool = @items.empty?
end
```

```
$ quarz doc Stack#pop
Stack#pop -> [Stack[T], T]

  頂上を除いたスタックと、その頂上。

  Raises

    要素がなければ Empty。先に empty? で確かめる。

$ quarz test
...
12 tests, 20 assertions, 0 failures, 0 errors, 0 pendings, 0 omissions, 0 notifications
```

- **ドキュメントコメント**は、宣言の直上に続く行全体のコメントの連なりで、宣言との間に空行がないものです。空行で離れたコメント、ドキュメントの対象でないもの(`include`、`using`、`require`、裸の `private`、文)の上のコメント、コード行の末尾のコメントは普通のコメントです。印(`///`、`##`)はありません。Ruby、Crystal、Go は印を使わず、空行の規則で実装上のメモとドキュメントを区別できます。
- 本文は、各コメント行から `#` と空白 1 つを除いたものです。**最初の段落が要約**で、一覧、補完、外側のクラスの `quarz doc` に出ます。
- コメント中の例は `quarz test` がコンパイルして実行します(§4)。`Stack#pop` と `Array#push` は検査されるリンクです(§3)。
- この例はアプリケーションの cog のファイルで、クラスはスクリプトと同じくそのまま見えます。ライブラリの cog では読者は `Mathx::Stack` と書くので、例もそう書きます(§4)。

## 2. 何に書けるか

ドキュメントコメントは次の上に書きます。

- `class`、`module`、`data`、`enum` と enum の `variant` の行(`variant Hearts, Diamonds` は並んだバリアントそれぞれのドキュメント。1 行の形 `enum Color = Red | Green` のバリアントには個別のドキュメントはなく、enum のものがカバーします)。
- `def`。多重定義はそれぞれ別に(`:ditto:` は §5)。`native def` にも書け、標準ライブラリはこの形でドキュメントされます。1 行の定義が並ぶ上のコメントは、Go と同じく最初のものだけのドキュメントです。
- フィールド(`@items: Array[T]`、`var @n: Int = 0`)。`attr_reader`/`attr_accessor` が作るアクセサもそれを引き継ぎます。`attr_reader :a, :b` の行に書けば、フィールドにコメントのないアクセサそれぞれのドキュメントになります。
- 複数行の形の `data` や `variant` のフィールド。その行の上に書きます。

  ```ruby
  data Suite = (
    # クラスの名前。`StackTest` など。
    name: String,
    # 宣言されているファイル。
    file: String
  )
  ```

- 定数(`LIMIT = 10`)、型の別名、`alias`(コメントがなければ元のメソッドのドキュメントを示す)、`extension`。

cog の概要は、crate や gem と同じく `README.md` です。生成されるサイトはそれで始まり、ルートモジュールのページがそのファイルです。ルートモジュールの `module` 宣言は言語にはなく、ファイルの先頭のコメントは何もドキュメントしません(ファイルは API の単位ではありません)。標準ライブラリのモジュール(`require "http"`)は、その `module HTTP` の上のコメントでドキュメントします。

private と protected のメソッド、アクセサのないフィールドは、`--private` を付けない限り出力に入りません。例外は `Kernel` の関数(`puts`、`rand`、`exit`)です。レシーバなしで呼べるように private ですが、プログラムの関数なので、`quarz doc puts` で見られます。公開された宣言のコメントの先頭行を `:nodoc:` にすると、その宣言とそのメンバーは出力から隠れます。コンパイラはそれでもコメントを読み、例は実行され(§4)、`--private` では表示されます。

## 3. 本文: Markdown

本文は CommonMark で、次の約束があります。

- **見出し**は `##` 以下です。ページの `#` の見出しは宣言の名前です。なのでソースでは節を `# ## Examples` と書きます。慣用の節は `Examples`、`Raises`(メソッドが投げる例外。型には現れません)、`See also` です。
- **宣言の名前を書いたコードスパンはリンク**で、コンパイラが検査します。`` `Array#push` ``(インスタンスメソッド)、`` `Array.new` ``(クラスメソッド)、`` `Stack::Empty` ``(クラス、モジュール、定数)、`` `#pop` `` と `` `.new` ``(ドキュメントしているクラスのインスタンスメソッドとクラスメソッド)、`` `pop` ``(同じ。クラスにその名前の公開メソッドがあればリンク、なければ普通のコード。パラメータの名前など)。名前は宣言のスコープで解決するので、cog 自身のコメントではその cog のクラスにモジュールの接頭辞は要りません。解決できたスパンはリンクとして描かれ、できなかったものは普通のコードです。`quarz doc --check` は、名前の形(`Foo`、`Foo::Bar`、`Foo#bar`、`Foo.bar`、`#bar`、`.bar`)のスパンが何にも解決しないか、出力に入らない private の宣言に解決するときに警告します。
- `extension` のメソッドは `using` の下でだけ届く(01-syntax.ja.md §7)ので、その extension を持つモジュールのページでドキュメントします(`quarz doc Shout` は `extension String` と `shout` を並べます)。そのモジュール自身のコメントからは `` `shout` `` でリンクでき、ほかの場所のコメントは文章で名前を挙げます。prelude の常に有効な extension(`extension Array[T <: Comparable[T]]`)は、どのプログラムから見てもそのクラスのメソッドなので、対象のクラスのページに出ます。
- **注記**: `NOTE:`、`WARNING:`、`DEPRECATED:`、`EXPERIMENTAL:` で始まる段落は目立つように描きます(Crystal の慣習)。
- **生の HTML は使えません**。タグは文字として表示するので、生成されるサイトには生成器が書いたものしか含まれません。
- リスト、強調、表、リンク(`[text](url)`)は Markdown のとおりです。字下げによるコードブロックはコードとして表示され、例にはなりません。

パラメータ、結果、ブロックは文章で説明します。シグネチャがすでに型と名前を示しているので、`@param x [Int]` の一覧(YARD)は繰り返しになります。

## 4. 例はテスト

ドキュメントコメントの中のフェンス付きコードブロックは Quarz のプログラムで、`quarz test` がコンパイルして実行します。`cargo test` が Rust のドキュメントの例を実行するのと同じで、ドキュメントがコードから離れていけないようにするためです。

```ruby
# ```
# Stack[Int].new.push(1).size   # => 1
# Stack[Int].new.pop            # raises Stack::Empty
# words = %w[b a].sort
# # => ["a", "b"]
# ```
```

- `expr # => text` は `expr.inspect` が `text` であることを確かめます(両端の空白は除きます)。対象はその行で終わる式文で、代入なら代入した値です。文の次の行に単独で書いた `# => text` はその文に対するものです。`expr # raises Klass` は、`Klass` かそのサブクラスが投げられることを確かめます。プログラムが出力したものは比べません(12-testing.ja.md §9 の `capture_output`)。出力する代わりに結果を書きます。このドキュメント群のほかの場所では `# =>` は `puts` が出力したものを示しますが、例の中では `inspect` です。`quarz doc --check` は、値が `nil` の `puts` や `print` の後の `# =>` を警告します(`p` は引数を返すので、`p x # => 2` は成り立ちます)。
- フェンスの情報文字列: なしか `quarz` なら実行します。`quarz no_run` はコンパイルだけ(サーバのループ、ネットワークへの接続)。それ以外の言語(`text`、`sh`、`toml`)は表示だけです。(この文書群 `docs/*.md` では、Quarz のコードのフェンスを `ruby` と書き、Ruby そのもののコードのフェンスを `rb` と書きます。`ruby` は GitHub で色が付き、Web サイトでは `quarz` として読みます。)
- 各例はそれぞれ 1 つのテストで、宣言の名前から `Stack#pop#example 1` と名付けられ(`-n Stack#pop` で選べます)、`quarz test` のほかのテストと一緒に報告されます。失敗した `# =>` は `src/stack.qz:12: expected => 2, was 3` と出します。`quarz test --doc` は例だけを、`--no-doc` は例を除いて実行します。`quarz test --doc --std` は標準ライブラリの例を実行します(コンパイラに埋め込まれているので、ファイルとしては渡しません)。`quarz test FILE...`(12-testing.ja.md §8)は、渡したファイルとそれが `require_relative` するファイルの例も実行します。
- 例は cog を利用者と同じように見ます(12-testing.ja.md §2)。ライブラリはそのモジュールの下に(`Mathx.square(3)`、`Mathx::Stack`)、アプリケーションはそのまま。extension のメソッドの例は、利用者のファイルと同じく `using Shout` で始めます。標準ライブラリの例は `HTTP::Response` と書き、`require` はしません。モジュールは名前で読み込まれます。
- 例はクラスやメソッドを宣言できます。各例は 1 つの単位なので、その `def` はファイルのものと同じくその例のものです(01-syntax.ja.md §2)。クラスはグローバルなので、例のクラスはほかの例、cog、テストのクラスと名前がぶつかってはいけません。cog の例は 1 つのプログラムにコンパイルされるからです(§7)。名前を分けます(一方は `Point`、もう一方は `Point3`)。

## 5. 継承と繰り返し

- ドキュメントコメントのないオーバーライドは、オーバーライドされたメソッドのものを出所つき(`from Base`)で示します。include したクラスのページには、モジュールのメソッドがそのドキュメントとともに並びます。自分のコメントを持つメソッドは、それを完全に置き換えます。
- `Stack.new` は `initialize` のコメントでドキュメントされ、`data` が生成するメソッド(`new`、`with`、`to_h`、フィールドの読み出し)は型とフィールドのコメントから生成されます。
- コメント全体を `:ditto:` にすると、直前の宣言のコメントを繰り返します。パラメータの型だけが違う多重定義のためです。

  ```ruby
  # 先頭の `n` 要素。
  def first(n: Int) -> Array[T] = take(n)
  # :ditto:
  def first(range: Range[Int]) -> Array[T] = self[range]
  ```

## 6. コマンド

| コマンド | 意味 |
|---|---|
| `quarz doc [FILE] NAME` | `NAME`(`Stack`、`Stack#pop`、`Stack.new`、`HTTP::Response.text`、`puts`)のドキュメントをシグネチャつきのテキストで出す。クラスなら、その要約とメンバーの要約。カレントディレクトリの周りの cog で解決する。スクリプト `FILE` を渡せばそれと require するファイルで、どちらもなければ標準ライブラリだけで解決する |
| `quarz doc` | cog の公開 API を宣言ごとに 1 行で |
| `quarz doc --html [-o DIR]` | cog の静的サイト(既定は `doc/`)。クラスとモジュールごとに 1 ページ、表紙は `README.md`、検索ボックス(ページが読む JSON の索引)、各メンバーにシグネチャ、本文、ソースの位置。`--std` は標準ライブラリのものを生成する |
| `quarz doc --check` | 解決しないリンク(§3)、閉じていないフェンス、`puts` や `print` の後の `# =>` を報告する。`--missing` はコメントのない公開宣言も報告する(CI 向けに 0 か 1 で終了) |
| `quarz doc --json` | API とそのドキュメントを JSON で。ほかのツールのため |
| `quarz test [--doc\|--no-doc] [--std]` | §4 |

`--private` を付けると、どれでも private と protected のメンバーが含まれます。依存先の名前(`Httpx::Client`)の `quarz doc` は、ロックに載っている cog についてそのソースから動きます。

REPL の補完は候補の要約を示します。

## 7. 実装

- **構文解析器。** 構文解析器はすべてのコメントの位置を集め(`Parsed::comments`)、そこからドキュメントコメントを取り出します(`quarz_syntax::doc::extract`)。連続する行の行全体のコメントの連なりごとに、その本文、位置、ドキュメントする行(空行でもコメントでもない次の行)を持ちます。これは宣言のノードごとのフィールドではなく、行ごとの表として `Program::docs` に入るので、AST の形は変わりません。`doc_at(offset)` が、宣言の始まる位置からそのドキュメントを見つけます(位置はファイルをまたいで一意です)。
- **宣言。** `declare.rs` が各ファイルの表を `World::docs` に加えます。検査済みの `World` を持つものはすべてドキュメントを持つことになります(`World::doc_at(span)`)。`quarz doc`、REPL の補完、後には言語サーバです。
- **`quarz doc`**(`crates/quarz-cli/src/doc.rs`)は、cog(ライブラリはテストから見えるのと同じくそのモジュールの下に)、スクリプト、または標準ライブラリを読み込んで検査し、`World` を歩きます。公開宣言を名前空間ごとに、多重定義は順に、継承したドキュメントは `ancestors` で、extension のメソッドはそのモジュールのページに、`data` が生成するメソッドは型とフィールドのコメントから。ドキュメントが持ち主のものと同じメンバー(1 行の `data` のフィールド、1 行の `enum` のバリアント)は自分のドキュメントを持ちません。リンクは型検査器の名前解決で、宣言のスコープで解決します。スパンの中の 1 文字の名前やジェネリックな型(`T`、`Array[Int]`)は型で、リンクではありません。Markdown は `pulldown-cmark`(CommonMark。`quarz-cli` だけの依存で、ランタイムには入れない)で解析します。テキスト出力は Markdown をプレーンテキストにし、HTML 出力は静的なファイルで、検索の索引はスクリプトにして `file://` でも動くようにします。cog で見つからない名前は標準ライブラリで探します。
- **例**はテストの仕組み(12-testing.ja.md §5)を使います。cog の検査の後、その cog 自身のファイルの例を `World` から集めます(`doc/examples.rs`)。各例は 1 つの単位になります。宣言はトップレベルに、文は生成する `Test::DocCase`(`std/test.qz`)のサブクラスの唯一の `test_example` メソッドに置き、`expr # => text` は `doc_expect((expr), "text", "file:line")` に、`expr # raises K` は `doc_raises(K, "file:line") { expr; nil }` に書き換えます。`quarz no_run` の例の文は、型検査器が畳み込めない条件の下で動きます。`check_with_extra` は複数の単位(`ExtraSource`。それぞれが属する cog を持つので、ライブラリの例はライブラリのモジュールを見ます)を受け取って一緒に宣言し、ランナーは例のスイートを自分で並べます(テストクラスを読む `World` にはまだないからです)。`quarz test --list` は `Stack#pop#example 1` と出します。生成した各単位は、その行ごとにコメントの行を持ち、診断はそこで報告されます。
- **分割コンパイル**が来たとき(05-execution.ja.md §2): インターフェースファイルはエクスポートするもののドキュメントを持ち、`quarz doc` と言語サーバは依存先についてインターフェースだけで動くようになります。
- **標準ライブラリ。** `std/prelude.qz` と `std/*.qz` はおおむね宣言の上にコメントが書かれていて、それらがドキュメントになります。そうするには、コンパイラの助け(`--missing` と、ドキュメントになるコメントの一覧)を借りてファイルを一度見直します。ファイル先頭のモジュールの見出し(`std/http.qz`、`std/test.qz`、`std/json.qz`)はその `module` の上へ移す。1 行の定義の並びの上のコメント(「Aliases that Ruby programs use.」)はそれぞれの上へ移すか、残りを `:ditto:` にする。定義の直上の実装上のメモ(「compiled code compares inline」、「Lowering calls it」)は空行の下か本体の中へ移す。ファイルの最初のクラスの上に置かれた概要(`std/socket.qz`)はモジュールへ移す。字下げで書かれた例(`std/json.qz`)は `# =>` の検査つきのフェンスにする。リポジトリのテストが標準ライブラリの例を実行し(`quarz test --doc --std`)、docs/06-stdlib.ja.md は概要のままです。

## 8. 後で

- 呼び出し側でのコンパイラの警告としての `DEPRECATED:`(型検査器がドキュメントを持っている)。`--deny-deprecated`。
- エディタでのホバーと補完のドキュメント(言語サーバ)と、REPL の `help` コマンド。REPL には今コマンドの層がなく(すべての行が式で、`Stack#pop` はコメントになる)、それが要ります。
- cog のドキュメントのホスティング(cog の `docs.rs`。10-cogs.ja.md §8 は発見の仕組みを後に回しています)。標準ライブラリのものは [quarz.dev/std](https://quarz.dev/std/) にあり、quarz-lang/quarz.dev がこのリポジトリの main から毎日作っています。
- `quarz doc --missing` の出力にドキュメントのカバレッジを百分率で。
- プログラムの出力を確かめる例(`capture_output`、12-testing.ja.md §9)。

## 9. 採用しなかった案

- **印(`///`、`//!`、`##`、`#:`)。** Rust に印が要るのは、アイテムの間のどこにでも `//` コメントがあるからです。Ruby、Crystal、Go では定義の上のコメントがそのドキュメントで、空行の規則が実装上のメモを除きます。印があると、標準ライブラリの既存のコメントは一つずつ直すまでドキュメントになりません。印がなければ、§7 の見直しは書き直しではなく確認です。
- **タグ(YARD や Javadoc の `@param`、`@return`、`@raise`)。** シグネチャが名前と型を持っています。タグは繰り返しで、古くなります。`Raises` は節にします。型が示さないからです。
- **RDoc の記法(`+code+`、`= Heading`)。** Markdown は、このドキュメントの読者がほかの場所で書いているもので、どのレンダラやエディタも表示できます。
- **値としてのドキュメント文字列(Elixir の `@doc "..."`、`def` の下に書く Python の docstring)。** クラス本体は宣言しかできず、メソッドの前の文字列は文になってしまいます。コメントならドキュメントがプログラムのメモリに載りません。
- **例の隠し行(Rust の `# ` 接頭辞)。** `#` のコメントの中では、行の最初の `#` はすでに Quarz のコメント行か Markdown の見出しを始めます。3 つ目の意味は多すぎます。例は全部を見せます。
- **求められたときだけ例を実行する。** 実行する意味は、気づかないうちに古くなれないことにあります。フラグが要るならそうなってしまいます。
- **Google/NumPy 式の節(`Args:`、`Returns:`)。** 見出しと文章で足り、型付きのシグネチャが引数の一覧を不要にします。
