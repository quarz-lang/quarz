# 並行プログラミング

Quarz の並行モデルは次の 3 つの部品からなります。

1. **タスク** — goroutine / Erlang プロセスに相当する軽量スレッド。M:N スケジューリングで、数十万個を同時に動かせる。
2. **チャネル** — 型付きのメッセージキュー。タスク間の通信と同期はこれで行う。
3. **Atom** — 不変値を保持する共有セル。CAS による更新で、複数タスクから安全に読み書きできる。

そして言語全体にわたるルールが 1 つ: **可変オブジェクトはタスクの境界を越えない**([03-data-model.ja.md](03-data-model.ja.md) §5)。これにより、データ競合はコンパイル時に排除されます。ロックは言語レベルでは提供しません(FFI 用の `Mutex` は `FFI` モジュールにあります)。

## 1. タスク

```ruby
t = spawn { heavy_computation(42) }   # Task[Int]
puts t.await                          # 完了を待って値を受け取る

Task.sleep(100.ms)
Task.yield                            # 他のタスクに譲る
Task.current                          # 自分の Task
```

- `spawn { }` は新しいタスクを作ってスケジューラに登録し、すぐ戻ります。戻り値 `Task[T]` の `T` はブロックの型です。
- ブロックは**値で捕捉**します。外側のローカル変数は spawn の時点の値がコピーされ、ブロック内から外側の変数へ代入することはできません。捕捉される値はすべて Shareable でなければなりません。
- `await` はタスクの完了を待ち、値を返します。タスクが例外で終わっていれば、その例外を `await` した側で再送出します。
- タスクはコンパイラが挿入する安全点(メソッド入口、ループの後方分岐、チャネル操作、割り当て)で協調的に切り替わります。純粋な計算ループでもループ境界で切り替わるため、1 つのタスクがスケジューラを占有することはありません。
- 各タスクは独自のスタックを持ち(§7)、Ruby のメソッドを普通に再帰呼び出しできます。`async`/`await` のような関数の色分けはありません。ブロックする操作(チャネル、IO、`sleep`)はどこからでも呼べ、呼んだタスクだけが停止します。

## 2. 構造化並行性(`Task.scope`)

実用上のほとんどの並行処理は「いくつか仕事を投げて全部待つ」です。`Task.scope` はそれを安全に書くための基本形です。

```ruby
results = Task.scope do |scope|
  tasks = urls.map { |url| scope.spawn { fetch(url) } }
  tasks.map(&:await)
end
```

- `Task.scope` のブロックを抜けるとき、`scope.spawn` で作ったすべてのタスクの完了を待ちます。ブロックの値がそのまま `Task.scope` の値です。
- スコープ内のタスクが例外で終わると、**残りのタスクはキャンセル**され、完了を待った後、その例外が `Task.scope` の呼び出し元に再送出されます。複数のタスクが失敗した場合は最初の例外が送出され、残りは `cause` 連鎖として付きます。
- ブロック本体が例外を投げた場合も同様に、子タスクをキャンセルして待ってから伝播します。
- スコープは入れ子にできます。キャンセルは入れ子の内側へ伝播します。
- トップレベルの `spawn`(`scope` なし)はプログラムのルートスコープに属します。メインのトップレベルコードが終わるとプログラムは終了し、残っているタスクはキャンセルされます(Ruby のメインスレッド終了と同じ)。長く生きるサービスは明示的に `Task.scope` で待ってください。

### キャンセル

```ruby
Task.scope do |scope|
  worker = scope.spawn { loop { process(queue.receive) } }
  Task.sleep(1.second)
  worker.cancel
end

Task.timeout(5.seconds) { slow_call }     # 超過すると Task::Timeout を送出
```

- `cancel` は対象タスクに「キャンセル要求」を立てます。要求されたタスクは、次にブロックする操作(チャネル、IO、`sleep`、`await`)を行う時点、または `Task.check_cancel` を呼んだ時点で `Task::Cancelled` 例外を受け取ります。
- `Task::Cancelled` は `StandardError` ではなく `Exception` 直下のクラスなので、`rescue => e` では捕まりません。`ensure` は通常どおり実行されるので、後始末はそこに書きます。
- キャンセルは要求であって強制ではありません。計算のみのループは `Task.check_cancel` を適宜呼ぶ必要があります(安全点で自動的に検査するオプションもあります: `--cancel-at-safepoints`)。

## 3. チャネル

```ruby
ch = Channel[String].new               # 容量 0(同期)
ch = Channel[String].new(capacity: 16) # 有界バッファ

ch.send("hello")     # バッファが満杯なら受信されるまで待つ
msg = ch.receive     # 空なら送信されるまで待つ。閉じていて空なら Channel::Closed
msg = ch.receive?    # 閉じていて空なら nil(型は String?)
ch.try_send("x")     # 待たずに Bool を返す
ch.close             # 以後 send は Channel::Closed。残りの要素は受信できる
ch.each { |m| ... }  # 閉じられるまで受信し続ける
```

- `Channel[T]` の `T` は Shareable でなければなりません。
- 容量 0 のチャネルは送信側と受信側のランデブーで、同期に使えます。
- `send`/`receive` は happens-before を確立します。`send` の前に行った更新は、対応する `receive` の後から見えます。これが Quarz のメモリモデルのすべてです(共有可変状態がないため、他に規定すべきことがありません)。
- 全タスクがチャネル待ちになってデッドロックした場合、ランタイムは `DeadlockError` でプログラムを停止します(Go の "all goroutines are asleep" と同じ)。

### `select`

複数のチャネル操作のうち、最初に可能になったものを 1 つ実行します。

```ruby
select do |s|
  s.receive(jobs) { |job| handle(job) }
  s.receive(quit) { |_| done = true }
  s.send(results, value) { puts "sent" }
  s.after(1.second) { puts "timeout" }
  s.default { puts "nothing ready" }       # あると非ブロッキング
end
```

`select` は同じ構造を `loop` の中で使うことが多いので、`Channel.select_loop` も用意しています。ハンドラの中で `s.stop` を呼ぶとループを抜けます(ハンドラはそれぞれ別のブロックなので、Ruby の規則どおり `break` は `s.receive` から抜けるだけで、ループは止まりません)。

## 4. Atom

複数のタスクから更新される状態は `Atom` に入れます。中身は不変値なので、更新は「古い値から新しい値を計算して差し替える」操作になります。

```ruby
counter = Atom.new(0)
counter.update { |n| n + 1 }         # CAS ループで原子的に更新。衝突したらブロックを再実行
counter.value                        # 読み出し
counter.set(0)
counter.compare_and_set(old, new)    # Bool

registry = Atom[Hash[String, Channel[Message]]].new({})
registry.update { |h| h.put(name, ch) }
```

- `update` のブロックは副作用を持たない純粋なものにしてください(再実行されることがあります)。
- 永続データ構造の更新は構造共有により安価なので、大きな `Hash` を `Atom` に入れても `update` は O(log n) です。
- `Atom` を定数に入れれば、Ruby のクラス変数やグローバル変数の代替になります。

```ruby
STATS = Atom.new({ requests: 0, errors: 0 })
STATS.update { |s| s.put(:requests, s[:requests] + 1) }
```

## 5. アクターと Erlang 風の設計

Erlang のプロセス + メールボックスは、タスク + 1 本のチャネルで表現できます。メッセージの型は `enum` にすると、`receive` と `case/in` の組み合わせで網羅性が検査されます。

```ruby
enum Msg
  Deposit(amount: Int)
  | Withdraw(amount: Int, reply: Channel[Result[Int, String]])
  | Balance(reply: Channel[Int])
  | Stop
end

def account_actor(inbox: Channel[Msg]) -> Nil
  balance = 0
  inbox.each do |msg|
    case msg
    in Msg::Deposit(amount:)
      balance += amount
    in Msg::Withdraw(amount:, reply:)
      if amount <= balance
        balance -= amount
        reply.send(Result::Ok.new(balance))
      else
        reply.send(Result::Err.new("insufficient funds"))
      end
    in Msg::Balance(reply:)
      reply.send(balance)
    in Msg::Stop
      break
    end
  end
end

Task.scope do |scope|
  inbox = Channel[Msg].new(capacity: 64)
  scope.spawn { account_actor(inbox) }

  inbox.send(Msg::Deposit.new(100))
  reply = Channel[Result[Int, String]].new
  inbox.send(Msg::Withdraw.new(30, reply))
  case reply.receive
  in Result::Ok(value:) then puts "balance: #{value}"
  in Result::Err(error:) then warn error
  end
  inbox.send(Msg::Stop)
end
```

アクターの状態(`balance`)はタスクのローカル変数なので、そのタスク以外からは触れません。Builder などの可変オブジェクトもアクター内に閉じて使う分には問題ありません。

### 監視と再起動

Erlang のスーパーバイザは、`Task.scope` と再起動ループの組み合わせで書けます。標準ライブラリに `Supervisor` を用意します。

```ruby
Supervisor.run(strategy: :one_for_one, max_restarts: 5, within: 10.seconds) do |sup|
  sup.child(:db) { db_actor(db_inbox) }
  sup.child(:http) { http_server(8080) }
end
```

- 子タスクが例外で終わると、戦略に従って再起動します。
- `Task#on_exit { |result| }` で終了通知を受け取れます(Erlang の `monitor` 相当)。`link` 相当は `Task.scope` そのものです。

## 6. ブロッキング処理と IO

- 標準ライブラリの IO は呼び出したタスクだけを止めます。コードは同期的に書けます。ソケット(`TCPSocket`、`TCPServer`、`UDPSocket`、`UNIXSocket`、`UNIXServer`)はノンブロッキングの記述子で、スケジューラのリアクタ(`polling` クレート経由の `epoll`/`kqueue`)が監視します。ブロックしそうな操作は記述子の準備が整うまでタスクを止め、実行ループは走れるタスクがないときリアクタで待ちます。ファイル全体の操作(`File.read`、`File.write` …)、名前解決、`connect`、子プロセス(`Process.run`)は補助スレッドで実行し、完了をリアクタ経由でタスクに通知します。開いた `File` ハンドルへの読み書きはバッファ付きの同期処理です。
- 待機中の IO は他の待機と同じように中断されます。`Task.timeout` や `cancel` は待っているタスクに例外を送出し、ソケットはその後も使えます。
- 標準ストリーム(`STDIN`、`STDOUT`、`STDERR`)は今のところブロッキングで、端末からの読み込み中はスケジューラが止まります。
- `IO` ハンドルは所有するタスクから使うべきものです。他のタスクに読み書きさせたければ、チャネルで仲介します。
- `Task.blocking { }` はブロックを補助スレッドで実行し(空きがなければ新しいスレッドを起こすので、長い計算がファイル IO を塞ぐことはありません)、呼び出したタスクだけが待ちます。値は一つのスレッドに属するので、ブロックは補助スレッドへ**複製**されます。捕捉する変数は Shareable でなければならず(`spawn` と同じ規則)、ブロックの中で代入できず、越えて渡せるのは不変の値だけです(数値、文字列、シンボル、配列、ハッシュ、集合、範囲、`data`/`enum` の値、それらを捕捉した手続き)。`Channel`・`Atom`・`Task` や可変の値は、複製ではなく共有が必要になるため `ArgumentError` で拒否されます。ブロックの結果や例外は同じ経路で戻り、ブロックが出力したものは終了時に書き出されます。長い計算や、ブロックする外部関数の呼び出しに使います。IO は標準ライブラリがタスクだけを止めるので不要です。

```ruby
digest = Task.blocking { expensive_hash(data) }     # 他のタスクは動き続ける
```

```ruby
rows = Task.blocking { legacy_c_query(sql) }
```

## 7. ランタイムの構造

- **スケジューラ**: OS スレッド(既定で CPU コア数)ごとに実行キューを持つワークスティーリング型。`QUARZ_THREADS=1` で単一スレッドに固定でき、決定性が必要なテストに使えます。
- **スタック**: タスクごとに仮想メモリを `mmap` で予約(既定 1 MiB、`spawn(stack: 8.mib)` で変更可)し、物理ページは触れたときだけコミットします。先頭にガードページを置き、あふれると `SystemStackError`。64 ビット環境ではアドレス空間が十分にあるため、100 万タスクでも実メモリは実際に使った分(通常 4〜8 KiB/タスク)だけです。Go のようなスタックのコピーは、AOT コンパイルされたコードのスタック内ポインタを書き換える必要があり採用しませんでした。
- **プリエンプション**: 協調的(安全点)。将来、シグナルによる非同期プリエンプションを追加する余地を残します。
- **タイマー**: タイミングホイール。`sleep`/`after`/`timeout` が使います。
- **チャネル**: ロックフリーの MPMC キュー + 待機者リスト。
- **参照カウントとの関係**: タスク境界を越える値(チャネルで送る、`spawn` で捕捉する、`Atom` に入れる)は、その時点で「共有済み」フラグが立ち、以後の参照カウント操作だけが原子的になります(Lean 4 と同じ方式)。タスク内に閉じた値は非原子的なカウント操作のままです。

## 8. 採用しなかった案

- **ロックと可変共有メモリ(Java/Go の Mutex)**: Go ですらデータ競合は検出ツール頼みです。可変オブジェクトをタスクに閉じ込め、共有は不変値と `Atom` で行う方が、Ruby プログラマにとっても「ロックを忘れた」バグを根絶できます。
- **async/await(関数の色分け)**: ブロック操作の呼び出し位置に印をつける必要があり、Ruby 風の素朴なコード(`gets` を呼ぶだけ)が書けなくなります。スタックを持つ軽量タスクはコストが小さく、Ruby らしさを保てます。
- **Erlang 風のプロセスごとのヒープ**: 不変値を共有できる以上、ヒープを分ける理由はメッセージコピーの回避ではなく GC の独立性ですが、参照カウントなら GC の停止はそもそもありません。
- **Ruby の Ractor**: 目指すところは近いですが、Quarz は Shareable を型として静的に検査し、実行時のエラーにしません。
