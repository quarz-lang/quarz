# 文法スケッチ

Ruby と異なる部分(宣言、型、引数、パターン)を EBNF 風に示します。式・文・リテラルの文法は Ruby 3.x に準じ、ここでは差分だけを書きます。`NEWLINE` と `;` は文の区切りで、Ruby と同じ規則で省略されます。本格的な文法は実装時に Lrama 形式で書き直す前提の下書きです。

```ebnf
program        = { toplevel } ;
toplevel       = declaration | statement ;

declaration    = class_decl | module_decl | data_decl | enum_decl | extension_decl
               | method_decl | type_alias | const_decl | using_decl | extern_decl
               | require_stmt ;

(* ---- クラス・モジュール ---- *)
class_decl     = [ "abstract" ] "class" const_path [ type_params ] [ "<" type ] NEWLINE
                 class_body "end" ;
module_decl    = "module" const_path [ type_params ] NEWLINE class_body "end" ;
class_body     = { class_member } ;
class_member   = field_decl | method_decl | attr_decl | include_decl | visibility
               | const_decl | type_alias | class_decl | module_decl | data_decl
               | enum_decl | using_decl | "alias" method_name method_name ;

field_decl     = [ "var" ] IVAR ":" type [ "=" expression ] ;
attr_decl      = ( "attr_reader" | "attr_writer" | "attr_accessor" ) SYMBOL { "," SYMBOL } ;
include_decl   = ( "include" | "extend" ) type { "," type } ;
visibility     = ( "private" | "protected" | "public" ) [ method_decl | SYMBOL { "," SYMBOL } ] ;

(* ---- data / enum ---- *)
data_decl      = "data" CONST [ type_params ] "(" [ field_list ] ")" [ "is" NEWLINE class_body "end" ] ;
field_list     = field { "," field } ;
field          = IDENT ":" type [ "=" expression ] ;

enum_decl      = "enum" CONST [ type_params ] NEWLINE { variant NEWLINE } class_body "end" ;
variant        = CONST [ "(" field_list ")" ] ;

(* ---- 拡張 ---- *)
extension_decl = "extension" type NEWLINE class_body "end" ;
using_decl     = "using" const_path ;

(* ---- メソッド ---- *)
method_decl    = { modifier } "def" [ "self" "." ] method_name [ type_params ]
                 [ "(" [ param_list ] ")" ] [ "->" type ]
                 ( "=" expression | NEWLINE body "end" ) ;
modifier       = "abstract" | "override" | "private" | "protected" | "public" ;
method_name    = IDENT [ "?" | "!" | "=" ] | operator ;
operator       = "+" | "-" | "*" | "/" | "%" | "**" | "==" | "!=" | "<" | "<=" | ">" | ">="
               | "<=>" | "===" | "=~" | "<<" | ">>" | "&" | "|" | "^" | "~" | "!"
               | "[]" | "[]=" | "+@" | "-@" | "call" ;

param_list     = param { "," param } ;
param          = positional_param | "*" [ IDENT [ ":" type ] ] | "**" IDENT [ ":" type ]
               | "&" IDENT [ ":" proc_type ]
               | "&" ":" proc_type ;
positional_param = [ "@" ] IDENT [ ":" type ] [ "=" expression ] ;
    (* "*" 単独の後ろの positional_param はキーワード専用引数 *)

type_params    = "[" type_param { "," type_param } "]" ;
type_param     = [ "out" | "in" ] CONST [ ":" type_bound ] ;
type_bound     = type { "&" type } ;

(* ---- 型 ---- *)
type           = union_type ;
union_type     = primary_type { "|" primary_type } ;
primary_type   = const_path [ "[" type { "," type } "]" ] [ "?" ]
               | "[" [ type { "," type } ] "]"                      (* タプル *)
               | proc_type [ "?" ]
               | "(" type ")" [ "?" ]
               | "self" | "Nothing" ;
proc_type      = "(" [ type { "," type } ] ")" "->" type ;

type_alias     = "type" CONST [ type_params ] "=" type ;
const_decl     = const_path "=" expression ;
const_path     = [ "::" ] CONST { "::" CONST } ;

(* ---- 変数の型注釈 ---- *)
typed_assign   = IDENT ":" type "=" expression ;        (* 文の先頭でのみ *)

(* ---- 手続きリテラル ---- *)
lambda         = "->" [ "(" [ param_list ] ")" ] [ "->" type ] ( "{" body "}" | "do" body "end" ) ;
block          = "{" [ "|" block_params "|" ] body "}" | "do" [ "|" block_params "|" ] body "end" ;
block_params   = param_list ;                           (* 型は省略可。推論される *)
method_ref     = expression ".:" method_name ;

(* ---- キャスト・型式 ---- *)
cast           = expression "." ( "as" | "as?" ) "(" type ")" ;
type_expr      = const_path "[" type { "," type } "]" ;  (* 式の位置: Array[Int].new など *)

(* ---- パターン(Ruby 3 の case/in と同一。再掲) ---- *)
pattern        = alt_pattern [ "=>" IDENT ] [ ( "if" | "unless" ) expression ] ;
alt_pattern    = prim_pattern { "|" prim_pattern } ;
prim_pattern   = literal | "^" IDENT | "^(" expression ")" | IDENT | "nil"
               | const_path                                       (* 型・値の一致 *)
               | const_path "(" [ sub_patterns ] ")"              (* deconstruct / deconstruct_keys *)
               | const_path "[" [ sub_patterns ] "]"
               | "[" [ array_sub ] "]"
               | "{" [ hash_sub ] "}"
               | range_pattern ;
sub_patterns   = array_sub | hash_sub ;
array_sub      = pattern { "," pattern } [ "," "*" [ IDENT ] { "," pattern } ]
               | "*" [ IDENT ] { "," pattern } ;
hash_sub       = key_pattern { "," key_pattern } [ "," "**" ( IDENT | "nil" ) ] ;
key_pattern    = LABEL [ pattern ] ;

(* ---- FFI ---- *)
extern_decl    = "extern" STRING NEWLINE { "def" IDENT "(" [ param_list ] ")" "->" type NEWLINE } "end" ;
```

## 曖昧さの解消

- **`name: Type` と `name: value`**: 引数リストの中では常に型、ハッシュリテラルとメソッド呼び出しの中では常に値。文の先頭の `ident: Type = expr` は型注釈付き代入。ラベルは字句解析器ではなく構文解析器が「識別子(または文字列)の直後に空白なしで `:` が続く」ことで判定する。これにより `a ? b : c` の三項演算子と衝突しない(`a ? b:c` のように詰めて書くと `b:` はラベルと見なされエラー)。
- **コマンド呼び出し(括弧なし)の引数と二項演算子**: `foo -x`、`foo *x`、`foo &x`、`foo [1]`、`foo /re/`、`foo %w[a]`、`foo <<EOS` は、識別子の後に空白があり、記号の後に空白がなければ引数(単項・リテラル)、それ以外は二項演算子として扱う(Ruby と同じ規則。字句解析器は各トークンに「直前に空白があったか」を記録する)。
- **`/` と `%` と `<<`**: 直前のトークンが値(識別子、定数、リテラル、`)`/`]`/`}`、`end`、`self` など)なら演算子、そうでなければ正規表現・`%` リテラル・ヒアドキュメントの開始。上のコマンド呼び出しの規則が優先される。
- **`->` の二義性**: `def` のシグネチャ中の `->` は戻り値型、式の位置の `->` は lambda。lambda の `->(x: Int) -> Int { }` は 1 つ目が lambda、2 つ目が戻り値型。
- **`Const[...]`**: 型の位置では型引数。式の位置では、`[` の中身が型として解釈できるなら型式(`Array[Int].new`)、そうでなければ `Const.[](...)` の呼び出し(ユーザー定義の `self.[]`)。組み込みの `Array`/`Hash`/`Set` は `self.[]` を持たないため常に型式。
- **`{ }` のブロックとハッシュ**: Ruby と同じ規則。
- **文脈キーワード**: `data`/`enum`/`var`/`abstract`/`override`/`extension`/`using`/`type`/`extern`/`is` は、上記の宣言位置で後続トークンが宣言の形を取るときだけキーワード。
- **`is ... end` の `data`**: 本体のない `data` 宣言は `end` で終わらないので、本体を続ける語がないとパーサは本体と後続の文を区別できない。`data X(...)` の直後の `is` が本体を開く。
