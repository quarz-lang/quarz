# Grammar Sketch

日本語版: [08-grammar.ja.md](08-grammar.ja.md)

This shows the parts that differ from Ruby (declarations, types, parameters, patterns) in EBNF style. The grammar of expressions, statements and literals follows Ruby 3.x, and only the differences are written here. `NEWLINE` and `;` are statement separators and are omitted under the same rules as in Ruby. This is a draft, on the assumption that the full grammar will be rewritten in Lrama format at implementation time.

```ebnf
program        = { toplevel } ;
toplevel       = declaration | statement ;

declaration    = class_decl | module_decl | data_decl | enum_decl | extension_decl
               | method_decl | type_alias | const_decl | using_decl | extern_decl
               | require_stmt ;

(* ---- classes and modules ---- *)
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

(* ---- extensions ---- *)
extension_decl = "extension" type NEWLINE class_body "end" ;
using_decl     = "using" const_path ;

(* ---- methods ---- *)
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
               | "&" IDENT [ ":" proc_type ] ;
positional_param = [ "@" ] IDENT [ ":" type ] [ "=" expression ] ;
    (* a positional_param after a bare "*" is a keyword-only parameter *)

type_params    = "[" type_param { "," type_param } "]" ;
type_param     = [ "out" | "in" ] CONST [ ":" type_bound ] ;
type_bound     = type { "&" type } ;

(* ---- types ---- *)
type           = union_type ;
union_type     = primary_type { "|" primary_type } ;
primary_type   = const_path [ "[" type { "," type } "]" ] [ "?" ]
               | "[" [ type { "," type } ] "]"                      (* tuple *)
               | proc_type [ "?" ]
               | "(" type ")" [ "?" ]
               | "self" | "Nothing" ;
proc_type      = "(" [ type { "," type } ] ")" "->" type ;

type_alias     = "type" CONST [ type_params ] "=" type ;
const_decl     = const_path "=" expression ;
const_path     = [ "::" ] CONST { "::" CONST } ;

(* ---- type annotations on variables ---- *)
typed_assign   = IDENT ":" type "=" expression ;        (* only at the start of a statement *)

(* ---- procedure literals ---- *)
lambda         = "->" [ "(" [ param_list ] ")" ] [ "->" type ] ( "{" body "}" | "do" body "end" ) ;
block          = "{" [ "|" block_params "|" ] body "}" | "do" [ "|" block_params "|" ] body "end" ;
block_params   = param_list ;                           (* types may be omitted; they are inferred *)
method_ref     = expression ".:" method_name ;

(* ---- casts and type expressions ---- *)
cast           = expression "." ( "as" | "as?" ) "(" type ")" ;
type_expr      = const_path "[" type { "," type } "]" ;  (* in expression position: Array[Int].new etc. *)

(* ---- patterns (identical to Ruby 3's case/in; repeated here) ---- *)
pattern        = alt_pattern [ "=>" IDENT ] [ ( "if" | "unless" ) expression ] ;
alt_pattern    = prim_pattern { "|" prim_pattern } ;
prim_pattern   = literal | "^" IDENT | "^(" expression ")" | IDENT | "nil"
               | const_path                                       (* type / value match *)
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

## Disambiguation

- **`name: Type` vs. `name: value`**: always a type inside a parameter list; always a value inside hash literals and method calls. `ident: Type = expr` at the start of a statement is a type-annotated assignment. Labels are recognized by the parser, not the lexer, by the rule "an identifier (or string) immediately followed by `:` with no intervening whitespace". This avoids conflicts with the ternary operator `a ? b : c` (if written tightly as `a ? b:c`, `b:` is taken as a label and is an error).
- **Arguments of command calls (no parentheses) vs. binary operators**: in `foo -x`, `foo *x`, `foo &x`, `foo [1]`, `foo /re/`, `foo %w[a]`, `foo <<EOS`, if there is whitespace after the identifier and none after the symbol, it is an argument (unary operator or literal); otherwise it is a binary operator (the same rule as Ruby; the lexer records for each token whether it was preceded by whitespace).
- **`/`, `%` and `<<`**: if the previous token is a value (identifier, constant, literal, `)`/`]`/`}`, `end`, `self`, etc.) it is an operator; otherwise it starts a regexp, a `%` literal or a heredoc. The command-call rule above takes precedence.
- **The two meanings of `->`**: `->` in a `def` signature is the return type; `->` in expression position is a lambda. In `->(x: Int) -> Int { }`, the first is the lambda and the second is the return type.
- **`Const[...]`**: in type position, type arguments. In expression position, a type expression (`Array[Int].new`) if the contents of `[` can be interpreted as types, otherwise a call to `Const.[](...)` (a user-defined `self.[]`). The built-in `Array`/`Hash`/`Set` have no `self.[]`, so they are always type expressions.
- **`{ }` as block vs. hash**: the same rule as Ruby.
- **Contextual keywords**: `data`/`enum`/`var`/`abstract`/`override`/`extension`/`using`/`type`/`extern`/`is` are keywords only in the declaration positions above, when the following tokens take the form of a declaration.
- **`is ... end` of `data`**: a `data` declaration without a body does not end with `end`, so a body needs an introducing word for the parser to tell it from the following statements; `is` right after `data X(...)` opens the body.
