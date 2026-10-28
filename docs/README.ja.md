# 設計文書

このディレクトリの文書は、言語とその実装を説明します。各文書には英語版 `NN-name.md` があります([README.md](README.md) が一覧です)。言語の短い入門は [quarz.dev のガイド](https://quarz.dev/guide/)(英語)にあります。標準ライブラリの API リファレンスは [quarz.dev/std](https://quarz.dev/std/) にあります。

## 文書

| 文書 | 内容 |
|---|---|
| [01-syntax.ja.md](01-syntax.ja.md) | 文法。クラス、`data`、`enum`、`module`、`extension`/`using`、メソッド定義、ブロック、パターンマッチ、例外 |
| [02-types.ja.md](02-types.ja.md) | 型システム。合併型と nil 安全性、ジェネリクスと変位、推論、フロー型付け、多重定義 |
| [03-data-model.ja.md](03-data-model.ja.md) | 不変データと Builder、`Shareable` の導出規則、等価性、文字列、Ruby の慣用句の書き換え |
| [04-concurrency.ja.md](04-concurrency.ja.md) | タスク、構造化並行性とキャンセル、チャネルと `Channel.select`、`Atom`、アクターと監視、ランタイム |
| [05-execution.ja.md](05-execution.ja.md) | インタプリタと AOT コンパイラ、QIR、分割コンパイル、参照カウントによるメモリ管理、ブートストラップ計画 |
| [06-stdlib.ja.md](06-stdlib.ja.md) | 標準ライブラリ。Ruby の組み込みクラスとの対応 |
| [07-ruby-diff.ja.md](07-ruby-diff.ja.md) | Ruby からの変更点 早見表 |
| [08-crystal-diff.ja.md](08-crystal-diff.ja.md) | Crystal との違い 早見表 |
| [09-grammar.ja.md](09-grammar.ja.md) | 文法スケッチ(EBNF) |
| [10-cogs.ja.md](10-cogs.ja.md) | cog(パッケージ)。コミットで固定する git リポジトリ、`Cog.toml`/`Cog.lock`、cog ごとに 1 モジュール、`require` 不要、キーワード `cog` |
| [11-http.ja.md](11-http.ja.md) | HTTP サーバ。応答を返すハンドラ、接続ごとのタスク、ルータ、`Signal`。`HTTP::Client` は後から |
| [12-testing.ja.md](12-testing.ja.md) | テスト。Test::Unit 風の `Test::Case`、コンパイラが見つけるテスト、型付きの assertion、データ駆動、`quarz test` |
| [13-doc-comments.ja.md](13-doc-comments.ja.md) | ドキュメントコメント。宣言の上のコメント、Markdown、検査されるリンク、`quarz test` が実行する例、`quarz doc` |
| [examples/](../examples/) | サンプルコード(`hello`、`shapes`、`wordcount`、`pipeline`、`bank_actor`、`extension`、`builder`) |

## 設計上の主な判断

| 判断 | 選んだもの | 理由 |
|---|---|---|
| 型注釈の位置 | 引数と戻り値は必須(戻り値を省略すると nil)、ローカルは推論 | コンパイル時間の短縮とエラーの質のため |
| 引数の型の書き方 | `name: Type`、キーワード専用は `*` の後 | Ruby のラベル構文を流用でき、空白に意味を持たせずに済む |
| `nil` | 独立した型。`T?` でのみ許容 | 実行時の `NoMethodError` をコンパイル時に |
| 直和型 | `enum` | メッセージ型と `case/in` の網羅性検査のため |
| 既存クラスの拡張 | `extension` + `using`(静的 refinements) | 再オープンを許さず、影響範囲を字句スコープに限定 |
| コレクション | 不変の値(共有されていればコピーして更新)+ Builder | 共有の安全性と、一意性を利用したその場更新による速度 |
| 共有可変状態 | 禁止。`Atom` と `Channel` のみ | データ競合をコンパイル時に排除。ロック不要 |
| 軽量スレッド | スタックを持つ M:N タスク(`mmap` 予約 + 遅延コミット) | async/await の色分けなしに Ruby 風の同期コードを書ける |
| メモリ管理 | 参照カウント + その場更新 + 可変オブジェクト限定のサイクル回収 | AOT との相性(スタックマップ不要)、不変値のその場更新 |
| `arr[i]`/`h[k]` | 範囲外・欠損は例外。`[]?` が `nil` | 静的型の下で `nil` 検査を書く手間を減らす(Crystal の実績) |
