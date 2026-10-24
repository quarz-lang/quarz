//! A hand-written recursive-descent parser (with precedence climbing for
//! binary operators).
//!
//! The parser pulls tokens from the lexer lazily into a buffer, which allows
//! bounded lookahead and local backtracking (used for `Const[...]` type
//! applications). It declares local variables in the lexer's [`LocalTable`]
//! as it sees assignments, parameters and pattern bindings, so that both the
//! lexer's `foo /re/` heuristic and the parser's own identifier resolution
//! know which names are variables.

use crate::ast::*;
use crate::diagnostic::Diagnostic;
use crate::lexer::Lexer;
use crate::source::Span;
use crate::token::{Keyword as K, StringKind, Token, TokenKind as T};

/// The result of parsing a file.
#[derive(Debug)]
pub struct Parsed {
    pub program: Program,
    pub diagnostics: Vec<Diagnostic>,
    pub comments: Vec<Span>,
    pub data_offset: Option<usize>,
}

pub fn parse(src: &str) -> Parsed {
    parse_with_bases(src, 0, 0)
}

/// Parse with spans offset by `span_base` and node ids starting at
/// `id_base`, so that several files can share the checker's tables.
pub fn parse_with_bases(src: &str, span_base: u32, id_base: NodeId) -> Parsed {
    parse_repl(src, span_base, id_base, &[])
}

/// What `cog.name` and `cog.version` stand for in a file: the name and
/// version of the cog it belongs to (from its `Cog.toml`), or of a script.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CogMeta {
    pub name: String,
    pub version: String,
}

impl Default for CogMeta {
    fn default() -> Self {
        CogMeta {
            name: "main".to_string(),
            version: "0.0.0".to_string(),
        }
    }
}

/// Parse a file of a cog (or a script) whose `cog.name` and
/// `cog.version` are `meta`'s.
pub fn parse_cog_file(src: &str, span_base: u32, id_base: NodeId, meta: &CogMeta) -> Parsed {
    let mut parser = Parser::with_bases(src, span_base, id_base);
    parser.cog = meta.clone();
    parser.finish(src, span_base)
}

/// Parse REPL input: `locals` are the variables declared by earlier
/// inputs.
pub fn parse_repl(src: &str, span_base: u32, id_base: NodeId, locals: &[String]) -> Parsed {
    let mut parser = Parser::with_bases(src, span_base, id_base);
    for name in locals {
        parser.declare(name);
    }
    parser.finish(src, span_base)
}

impl Parser<'_> {
    fn finish(mut self, src: &str, span_base: u32) -> Parsed {
        let body = self.parse_statements(&[]);
        let span = Span::new(span_base as usize, span_base as usize + src.len());
        let eof = self.peek().clone();
        if !matches!(eof.kind, T::Eof) {
            self.error_at(format!("unexpected {}", describe(&eof.kind)), eof.span);
        }
        let mut diagnostics = self.lexer.take_diagnostics();
        diagnostics.append(&mut self.diagnostics);
        diagnostics.sort_by_key(|d| (d.span.start, d.span.end));
        Parsed {
            program: Program { body, span },
            diagnostics,
            comments: self.lexer.comments().to_vec(),
            data_offset: self.lexer.data_offset(),
        }
    }
}

#[derive(Debug)]
pub struct ParseError;

type PResult<T> = Result<T, ParseError>;

fn describe(kind: &T) -> String {
    match kind {
        T::Newline => "end of line".to_string(),
        T::Eof => "end of file".to_string(),
        T::Ident(name) => format!("identifier `{name}`"),
        T::Const(name) => format!("constant `{name}`"),
        T::Keyword(k) => format!("`{}`", k.as_str()),
        other => other.to_string(),
    }
}

pub struct Parser<'src> {
    lexer: Lexer<'src>,
    tokens: Vec<Token>,
    idx: usize,
    diagnostics: Vec<Diagnostic>,
    next_id: NodeId,
    /// Set while parsing the arguments of a parenthesis-less command call or
    /// the condition of `while`/`until`, so that a `do` block binds to the
    /// outer construct.
    no_do: bool,
    /// Inside the body or guard of a `for` comprehension (where `break`
    /// is rejected, as it would leave only the innermost generated block).
    in_comprehension: bool,
    /// `expr in pattern` is not a match while parsing a `case` subject.
    allow_in_match: bool,
    last_span_end: u32,
    /// What `cog.name` and `cog.version` read.
    cog: CogMeta,
}

impl<'src> Parser<'src> {
    pub fn new(src: &'src str) -> Parser<'src> {
        Parser::with_bases(src, 0, 0)
    }

    pub fn with_bases(src: &'src str, span_base: u32, id_base: NodeId) -> Parser<'src> {
        let mut lexer = Lexer::with_base(src, span_base);
        lexer.locals.push_scope(true);
        Parser {
            lexer,
            tokens: Vec::new(),
            idx: 0,
            diagnostics: Vec::new(),
            next_id: id_base,
            no_do: false,
            in_comprehension: false,
            allow_in_match: true,
            last_span_end: 0,
            cog: CogMeta::default(),
        }
    }

    // ----- token access ----------------------------------------------------

    fn fill(&mut self, n: usize) {
        while self.tokens.len() <= self.idx + n {
            let tok = self.lexer.next_token();
            let eof = tok.kind.is_eof();
            self.tokens.push(tok);
            if eof {
                // Pad with EOF so lookahead never runs out.
                while self.tokens.len() <= self.idx + n {
                    let last = self.tokens.last().unwrap().clone();
                    self.tokens.push(last);
                }
                break;
            }
        }
    }

    fn peek(&mut self) -> &Token {
        self.fill(0);
        &self.tokens[self.idx]
    }

    fn peek_at(&mut self, n: usize) -> &Token {
        self.fill(n);
        &self.tokens[self.idx + n]
    }

    fn kind(&mut self) -> &T {
        &self.peek().kind
    }

    fn kind_at(&mut self, n: usize) -> &T {
        &self.peek_at(n).kind
    }

    fn bump(&mut self) -> Token {
        self.fill(0);
        let tok = self.tokens[self.idx].clone();
        if !tok.kind.is_eof() {
            self.idx += 1;
        }
        self.last_span_end = tok.span.end;
        tok
    }

    fn at(&mut self, kind: &T) -> bool {
        self.kind() == kind
    }

    fn at_kw(&mut self, kw: K) -> bool {
        matches!(self.kind(), T::Keyword(k) if *k == kw)
    }

    fn eat(&mut self, kind: &T) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: K) -> bool {
        if self.at_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &T, what: &str) -> PResult<Token> {
        if self.at(kind) {
            Ok(self.bump())
        } else {
            Err(self.error_expected(what))
        }
    }

    fn expect_kw(&mut self, kw: K) -> PResult<Token> {
        if self.at_kw(kw) {
            Ok(self.bump())
        } else {
            Err(self.error_expected(&format!("`{}`", kw.as_str())))
        }
    }

    fn mark(&self) -> usize {
        self.idx
    }

    fn reset(&mut self, mark: usize) {
        self.idx = mark;
    }

    fn skip_newlines(&mut self) {
        while self.at(&T::Newline) {
            self.bump();
        }
    }

    fn span_from(&mut self, start: Span) -> Span {
        Span::new(
            start.start as usize,
            self.last_span_end.max(start.end) as usize,
        )
    }

    fn node(&mut self, span: Span, kind: ExprKind) -> Expr {
        let id = self.next_id;
        self.next_id += 1;
        Expr { id, span, kind }
    }

    // ----- errors ----------------------------------------------------------

    fn error_at(&mut self, message: impl Into<String>, span: Span) -> ParseError {
        self.diagnostics.push(Diagnostic::error(message, span));
        ParseError
    }

    fn error_expected(&mut self, what: &str) -> ParseError {
        let tok = self.peek().clone();
        self.error_at(
            format!("expected {what}, found {}", describe(&tok.kind)),
            tok.span,
        )
    }

    /// Skip to the end of the current statement after an error.
    fn recover(&mut self, stop: &[K]) {
        let mut depth = 0i32;
        loop {
            match self.kind().clone() {
                T::Eof => return,
                T::Newline if depth <= 0 => {
                    self.bump();
                    return;
                }
                T::Keyword(k) if depth <= 0 && stop.contains(&k) => return,
                T::LParen | T::LBracket | T::LBrace => depth += 1,
                T::RParen | T::RBracket | T::RBrace => depth -= 1,
                _ => {}
            }
            self.bump();
        }
    }

    // ----- local variables -------------------------------------------------

    fn declare(&mut self, name: &str) {
        self.lexer.locals.declare(name);
    }

    fn is_local(&self, name: &str) -> bool {
        self.lexer.locals.is_declared(name)
    }

    fn push_scope(&mut self, hard: bool) {
        self.lexer.locals.push_scope(hard);
    }

    fn pop_scope(&mut self) {
        self.lexer.locals.pop_scope();
    }

    // ----- statements ------------------------------------------------------

    /// Parse statements until one of `stop` keywords (or a closing bracket /
    /// EOF) is reached. The stop token is not consumed.
    fn parse_statements(&mut self, stop: &[K]) -> Vec<Expr> {
        let mut stmts = Vec::new();
        loop {
            self.skip_newlines();
            match self.kind() {
                T::Eof | T::RParen | T::RBrace | T::RBracket | T::EmbExprEnd => break,
                T::Keyword(k) if stop.contains(k) => break,
                _ => {}
            }
            match self.parse_statement() {
                Ok(stmt) => {
                    stmts.push(stmt);
                    match self.kind() {
                        T::Newline => {}
                        T::Eof | T::RParen | T::RBrace | T::RBracket | T::EmbExprEnd => {}
                        T::Keyword(k) if stop.contains(k) => {}
                        _ => {
                            self.error_expected("end of line");
                            self.recover(stop);
                        }
                    }
                }
                Err(_) => self.recover(stop),
            }
        }
        stmts
    }

    fn parse_statement(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let mut expr = self.parse_statement_head()?;
        // Modifiers.
        loop {
            match self.kind().clone() {
                T::Keyword(K::If) | T::Keyword(K::Unless) => {
                    let negate = self.at_kw(K::Unless);
                    self.bump();
                    let cond = self.parse_expr_stmt()?;
                    let cond = if negate { self.not(cond) } else { cond };
                    let span = self.span_from(start);
                    expr = self.node(
                        span,
                        ExprKind::If {
                            cond: Box::new(cond),
                            then: vec![expr],
                            els: None,
                        },
                    );
                }
                T::Keyword(K::While) | T::Keyword(K::Until) => {
                    let negate = self.at_kw(K::Until);
                    self.bump();
                    let cond = self.parse_expr_stmt()?;
                    let do_while = matches!(expr.kind, ExprKind::Begin(_));
                    let span = self.span_from(start);
                    expr = self.node(
                        span,
                        ExprKind::While {
                            cond: Box::new(cond),
                            body: vec![expr],
                            negate,
                            do_while,
                        },
                    );
                }
                T::Keyword(K::Rescue) => {
                    self.bump();
                    let fallback = self.parse_expr_stmt()?;
                    expr = self.rescue_modifier(expr, fallback, start);
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn rescue_modifier(&mut self, body: Expr, fallback: Expr, start: Span) -> Expr {
        let span = self.span_from(start);
        let rescue_span = fallback.span;
        self.node(
            span,
            ExprKind::Begin(Box::new(BeginBlock {
                body: vec![body],
                rescues: vec![Rescue {
                    classes: vec![],
                    var: None,
                    body: vec![fallback],
                    span: rescue_span,
                }],
                else_body: None,
                ensure: None,
            })),
        )
    }

    fn not(&mut self, expr: Expr) -> Expr {
        let span = expr.span;
        self.node(span, ExprKind::Not(Box::new(expr)))
    }

    /// A statement before its modifiers: declarations, multiple assignment,
    /// typed declarations, or an expression.
    fn parse_statement_head(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        match self.kind().clone() {
            T::Keyword(K::Class) => return self.parse_class(false),
            T::Keyword(K::Module) => return self.parse_module(),
            T::Keyword(K::Def) => return self.parse_def(None, false, false, false),
            T::Keyword(K::Alias) => return self.parse_alias(),
            T::Star => return self.parse_multi_assign(None),
            T::IVar(name) if self.is_adjacent_colon(1) => {
                return self.parse_field_decl(false, &name);
            }
            T::Ident(name) => {
                if let Some(expr) = self.parse_contextual_declaration(&name)? {
                    return Ok(expr);
                }
                if self.is_adjacent_colon(1) && !self.is_local(&name) {
                    return self.parse_typed_decl(&name);
                }
            }
            T::Const(name) if matches!(self.kind_at(1), T::Assign) => {
                // CONST = value
                self.bump();
                self.bump();
                self.skip_newlines();
                let value = self.parse_expr()?;
                let span = self.span_from(start);
                return Ok(self.node(
                    span,
                    ExprKind::ConstAssign {
                        name,
                        value: Box::new(value),
                    },
                ));
            }
            _ => {}
        }

        let expr = self.parse_expr_stmt()?;
        if self.at(&T::Comma) && self.lvalue_of(&expr).is_some() {
            return self.parse_multi_assign(Some(expr));
        }
        Ok(expr)
    }

    /// Whether token `n` is a `:` immediately following token `n - 1`.
    fn is_adjacent_colon(&mut self, n: usize) -> bool {
        let prev_end = self.peek_at(n - 1).span.end;
        let tok = self.peek_at(n);
        matches!(tok.kind, T::Colon) && !tok.space_before && tok.span.start == prev_end
    }

    /// Contextual keywords at statement start.
    fn parse_contextual_declaration(&mut self, name: &str) -> PResult<Option<Expr>> {
        let next = self.kind_at(1).clone();
        let expr = match name {
            "data" if matches!(next, T::Const(_)) => self.parse_data()?,
            "enum" if matches!(next, T::Const(_)) => self.parse_enum()?,
            "extension" if matches!(next, T::Const(_)) => self.parse_extension()?,
            "using" if matches!(next, T::Const(_) | T::ColonColon | T::Keyword(K::Cog)) => {
                let start = self.bump().span;
                let path = self.parse_const_path()?;
                let span = self.span_from(start);
                let using = self.node(span, ExprKind::Using(path));
                // `using M do ... end` / `using M { ... }`: the extensions
                // are active in the body only, whose value is the result.
                let block = if self.at_kw(K::Do) && !self.no_do {
                    Some(self.parse_do_block()?)
                } else if self.at(&T::LBrace) {
                    Some(self.parse_brace_block()?)
                } else {
                    None
                };
                match block {
                    Some(b) => {
                        let mut stmts = vec![using];
                        stmts.extend(b.body);
                        let span = self.span_from(start);
                        self.node(span, ExprKind::Seq(stmts))
                    }
                    None => using,
                }
            }
            "type" if matches!(next, T::Const(_)) => self.parse_type_alias()?,
            "var" if matches!(next, T::IVar(_)) => {
                self.bump();
                let T::IVar(field) = self.kind().clone() else {
                    unreachable!()
                };
                self.parse_field_decl(true, &field)?
            }
            "extern" if matches!(next, T::StringBegin(_)) => self.parse_extern()?,
            "abstract" | "override" | "native" | "private" | "protected" | "public"
                if matches!(next, T::Keyword(K::Def | K::Class) | T::Ident(_)) =>
            {
                return self.parse_modified_declaration();
            }
            "private" | "protected" | "public"
                if matches!(next, T::Symbol(_) | T::Newline | T::Eof) =>
            {
                let start = self.bump().span;
                let visibility = visibility_of(name);
                let names = self.parse_symbol_list()?;
                let span = self.span_from(start);
                self.node(span, ExprKind::Visibility { visibility, names })
            }
            "attr_reader" | "attr_writer" | "attr_accessor" if matches!(next, T::Symbol(_)) => {
                let start = self.bump().span;
                let kind = match name {
                    "attr_reader" => AttrKind::Reader,
                    "attr_writer" => AttrKind::Writer,
                    _ => AttrKind::Accessor,
                };
                let names = self.parse_symbol_list()?;
                let span = self.span_from(start);
                self.node(span, ExprKind::AttrDecl { kind, names })
            }
            "include" | "extend" if matches!(next, T::Const(_) | T::ColonColon) => {
                let start = self.bump().span;
                let kind = if name == "include" {
                    MixinKind::Include
                } else {
                    MixinKind::Extend
                };
                let mut types = vec![self.parse_type()?];
                while self.eat(&T::Comma) {
                    self.skip_newlines();
                    types.push(self.parse_type()?);
                }
                let span = self.span_from(start);
                self.node(span, ExprKind::Mixin { kind, types })
            }
            "require" | "require_relative" if matches!(next, T::StringBegin(_)) => {
                let start = self.bump().span;
                let path = self.parse_plain_string()?;
                let span = self.span_from(start);
                self.node(
                    span,
                    ExprKind::Require {
                        path,
                        relative: name == "require_relative",
                    },
                )
            }
            _ => return Ok(None),
        };
        Ok(Some(expr))
    }

    /// `abstract def`, `private def`, `override def`, `abstract class`, and
    /// combinations such as `private abstract def`.
    fn parse_modified_declaration(&mut self) -> PResult<Option<Expr>> {
        let mark = self.mark();
        let mut is_abstract = false;
        let mut is_override = false;
        let mut is_native = false;
        let mut visibility = None;
        loop {
            match self.kind().clone() {
                T::Ident(m) if m == "abstract" => is_abstract = true,
                T::Ident(m) if m == "override" => is_override = true,
                T::Ident(m) if m == "native" => is_native = true,
                T::Ident(m) if matches!(m.as_str(), "private" | "protected" | "public") => {
                    visibility = Some(visibility_of(&m))
                }
                T::Keyword(K::Def) => {
                    let def = self.parse_def(visibility, is_abstract, is_override, is_native)?;
                    return Ok(Some(def));
                }
                T::Keyword(K::Class) if is_abstract && !is_override && !is_native => {
                    return Ok(Some(self.parse_class(true)?));
                }
                _ => {
                    // Not a declaration after all (e.g. `private` used as a
                    // method call with arguments).
                    self.reset(mark);
                    return Ok(None);
                }
            }
            self.bump();
        }
    }

    fn parse_symbol_list(&mut self) -> PResult<Vec<String>> {
        let mut names = Vec::new();
        while let T::Symbol(name) = self.kind().clone() {
            self.bump();
            names.push(name);
            if !self.eat(&T::Comma) {
                break;
            }
            self.skip_newlines();
        }
        Ok(names)
    }

    fn parse_plain_string(&mut self) -> PResult<String> {
        let expr = self.parse_primary()?;
        match expr.kind {
            ExprKind::Str(parts) if parts.iter().all(|p| matches!(p, StrPart::Lit(_))) => Ok(parts
                .into_iter()
                .map(|p| match p {
                    StrPart::Lit(s) => s,
                    _ => unreachable!(),
                })
                .collect()),
            _ => Err(self.error_at("expected a plain string literal", expr.span)),
        }
    }

    fn parse_typed_decl(&mut self, name: &str) -> PResult<Expr> {
        let start = self.bump().span;
        self.expect(&T::Colon, "`:`")?;
        let ty = self.parse_type()?;
        self.expect(&T::Assign, "`=`")?;
        self.skip_newlines();
        self.declare(name);
        let value = self.parse_expr()?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::TypedDecl {
                name: name.to_string(),
                ty,
                value: Box::new(value),
            },
        ))
    }

    fn parse_field_decl(&mut self, mutable: bool, name: &str) -> PResult<Expr> {
        let start = self.bump().span; // @name
        self.expect(&T::Colon, "`:`")?;
        let ty = self.parse_type()?;
        let default = if self.eat(&T::Assign) {
            self.skip_newlines();
            Some(self.parse_expr()?)
        } else {
            None
        };
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::FieldDecl(Box::new(FieldDecl {
                name: name.to_string(),
                ty,
                mutable,
                default,
                span,
            })),
        ))
    }

    fn parse_multi_assign(&mut self, first: Option<Expr>) -> PResult<Expr> {
        let start = first
            .as_ref()
            .map(|e| e.span)
            .unwrap_or_else(|| self.peek().span);
        let mut targets = Vec::new();
        if let Some(first) = first {
            let lv = self.lvalue_of(&first).unwrap();
            self.declare_lvalue(&lv);
            targets.push(MultiTarget::Single(lv));
            if !self.eat(&T::Comma) {
                return Err(self.error_expected("`,`"));
            }
        }
        loop {
            if self.at(&T::Assign) {
                break; // trailing comma: `a, = list`
            }
            let target = self.parse_multi_target()?;
            targets.push(target);
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.expect(&T::Assign, "`=`")?;
        self.skip_newlines();
        let value = self.parse_rhs_list()?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::MultiAssign {
                targets,
                value: Box::new(value),
            },
        ))
    }

    fn parse_multi_target(&mut self) -> PResult<MultiTarget> {
        if self.eat(&T::Star) {
            if matches!(self.kind(), T::Comma | T::Assign) {
                return Ok(MultiTarget::Splat(None));
            }
            let lv = self.parse_single_target()?;
            return Ok(MultiTarget::Splat(Some(lv)));
        }
        if self.eat(&T::LParen) {
            let mut nested = Vec::new();
            loop {
                nested.push(self.parse_multi_target()?);
                if !self.eat(&T::Comma) {
                    break;
                }
            }
            self.expect(&T::RParen, "`)`")?;
            return Ok(MultiTarget::Nested(nested));
        }
        let lv = self.parse_single_target()?;
        Ok(MultiTarget::Single(lv))
    }

    fn parse_single_target(&mut self) -> PResult<LValue> {
        let expr = self.parse_primary_postfix()?;
        match self.lvalue_of(&expr) {
            Some(lv) => {
                self.declare_lvalue(&lv);
                Ok(lv)
            }
            None => Err(self.error_at("cannot assign to this expression", expr.span)),
        }
    }

    /// The right-hand side of a multiple assignment: `1, 2` becomes an array.
    fn parse_rhs_list(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let first = self.parse_arg_value()?;
        if !self.at(&T::Comma) {
            return Ok(match first {
                Arg::Positional(e) => e,
                Arg::Splat(e) => {
                    let span = e.span;
                    self.node(span, ExprKind::Array(vec![Arg::Splat(e)]))
                }
                other => {
                    let span = other.span();
                    return Err(self.error_at("unexpected argument form", span));
                }
            });
        }
        let mut items = vec![first];
        while self.eat(&T::Comma) {
            self.skip_newlines();
            items.push(self.parse_arg_value()?);
        }
        let span = self.span_from(start);
        Ok(self.node(span, ExprKind::Array(items)))
    }

    fn lvalue_of(&self, expr: &Expr) -> Option<LValue> {
        match &expr.kind {
            ExprKind::Local(name) => Some(LValue::Local {
                name: name.clone(),
                span: expr.span,
            }),
            ExprKind::IVar(name) => Some(LValue::IVar(name.clone())),
            ExprKind::Const(path) if path.names.len() == 1 && !path.absolute && !path.cog => {
                Some(LValue::Const(path.names[0].clone()))
            }
            ExprKind::Call(call) => {
                if call.block.is_some() || !call.type_args.is_empty() {
                    return None;
                }
                match (&call.recv, call.name.as_str()) {
                    (None, name) if call.args.is_empty() && !call.has_parens => {
                        Some(LValue::Local {
                            name: name.to_string(),
                            span: expr.span,
                        })
                    }
                    (Some(recv), "[]") => Some(LValue::Index {
                        recv: recv.clone(),
                        args: call.args.clone(),
                    }),
                    (Some(recv), name) if call.args.is_empty() && !call.has_parens => {
                        Some(LValue::Attr {
                            recv: recv.clone(),
                            name: name.to_string(),
                            safe_nav: call.safe_nav,
                        })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn declare_lvalue(&mut self, lv: &LValue) {
        if let LValue::Local { name, .. } = lv {
            self.declare(name);
        }
    }

    // ----- expressions -----------------------------------------------------

    /// Expression with `not`/`and`/`or` (lowest precedence).
    fn parse_expr_stmt(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let mut lhs = self.parse_not_expr()?;
        // Rightward pattern matching: `value => pattern` / `value in pattern`.
        let allow_in = self.allow_in_match;
        let raises = match self.kind() {
            T::FatArrow => true,
            T::Keyword(K::In) if allow_in => false,
            _ => return self.parse_and_or_rest(lhs, start),
        };
        self.bump();
        let pattern = self.parse_pattern_top()?;
        let span = self.span_from(start);
        lhs = self.node(
            span,
            ExprKind::MatchPattern {
                value: Box::new(lhs),
                pattern: Box::new(pattern),
                raises,
            },
        );
        self.parse_and_or_rest(lhs, start)
    }

    fn parse_and_or_rest(&mut self, mut lhs: Expr, start: Span) -> PResult<Expr> {
        loop {
            let is_and = match self.kind() {
                T::Keyword(K::And) => true,
                T::Keyword(K::Or) => false,
                _ => break,
            };
            self.bump();
            self.skip_newlines();
            let rhs = self.parse_not_expr()?;
            let span = self.span_from(start);
            lhs = if is_and {
                self.node(span, ExprKind::And(Box::new(lhs), Box::new(rhs)))
            } else {
                self.node(span, ExprKind::Or(Box::new(lhs), Box::new(rhs)))
            };
        }
        Ok(lhs)
    }

    fn parse_not_expr(&mut self) -> PResult<Expr> {
        if self.at_kw(K::Not) {
            let start = self.bump().span;
            let operand = self.parse_not_expr()?;
            let span = self.span_from(start);
            return Ok(self.node(span, ExprKind::Not(Box::new(operand))));
        }
        self.parse_expr()
    }

    /// An expression including assignment (right-associative) but not
    /// `and`/`or`/`not`.
    pub fn parse_expr(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let lhs = self.parse_ternary()?;
        // `value in pattern` is allowed inside argument lists too.
        if self.at_kw(K::In) && self.allow_in_match {
            self.bump();
            let pattern = self.parse_pattern_top()?;
            let span = self.span_from(start);
            return Ok(self.node(
                span,
                ExprKind::MatchPattern {
                    value: Box::new(lhs),
                    pattern: Box::new(pattern),
                    raises: false,
                },
            ));
        }
        match self.kind().clone() {
            T::Assign => {
                let Some(target) = self.lvalue_of(&lhs) else {
                    return Err(self.error_at("cannot assign to this expression", lhs.span));
                };
                self.bump();
                self.skip_newlines();
                self.declare_lvalue(&target);
                let mut value = self.parse_expr()?;
                if self.at_kw(K::Rescue) {
                    self.bump();
                    let fallback = self.parse_expr()?;
                    let vstart = value.span;
                    value = self.rescue_modifier(value, fallback, vstart);
                }
                let span = self.span_from(start);
                Ok(self.node(
                    span,
                    ExprKind::Assign {
                        target: Box::new(target),
                        value: Box::new(value),
                    },
                ))
            }
            T::OpAssign(op) => {
                let Some(target) = self.lvalue_of(&lhs) else {
                    return Err(self.error_at("cannot assign to this expression", lhs.span));
                };
                if let LValue::Local { name, .. } = &target {
                    if !self.is_local(name) {
                        self.error_at(format!("undefined local variable `{name}`"), lhs.span);
                    }
                }
                self.bump();
                self.skip_newlines();
                let value = self.parse_expr()?;
                let span = self.span_from(start);
                Ok(self.node(
                    span,
                    ExprKind::OpAssign {
                        target: Box::new(target),
                        op,
                        value: Box::new(value),
                    },
                ))
            }
            _ => Ok(lhs),
        }
    }

    fn parse_ternary(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let cond = self.parse_range()?;
        if !self.at(&T::Question) {
            return Ok(cond);
        }
        self.bump();
        self.skip_newlines();
        let then = self.parse_ternary()?;
        self.skip_newlines();
        self.expect(&T::Colon, "`:` of the conditional operator")?;
        self.skip_newlines();
        let els = self.parse_ternary()?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::If {
                cond: Box::new(cond),
                then: vec![then],
                els: Some(vec![els]),
            },
        ))
    }

    fn parse_range(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        if matches!(self.kind(), T::DotDot | T::DotDotDot) {
            // Beginless range.
            let exclusive = self.at(&T::DotDotDot);
            self.bump();
            let hi = self.parse_binary(0)?;
            let span = self.span_from(start);
            return Ok(self.node(
                span,
                ExprKind::Range {
                    lo: None,
                    hi: Some(Box::new(hi)),
                    exclusive,
                },
            ));
        }
        let lo = self.parse_binary(0)?;
        if !matches!(self.kind(), T::DotDot | T::DotDotDot) {
            return Ok(lo);
        }
        let exclusive = self.at(&T::DotDotDot);
        self.bump();
        let hi = if self.starts_expression() {
            Some(Box::new(self.parse_binary(0)?))
        } else {
            None
        };
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::Range {
                lo: Some(Box::new(lo)),
                hi,
                exclusive,
            },
        ))
    }

    /// Whether the current token can begin an expression (used for endless
    /// ranges and optional arguments).
    fn starts_expression(&mut self) -> bool {
        match self.kind() {
            T::Ident(_)
            | T::Const(_)
            | T::IVar(_)
            | T::Int { .. }
            | T::Float(_)
            | T::Symbol(_)
            | T::StringBegin(_)
            | T::Words(_)
            | T::Symbols(_)
            | T::LParen
            | T::LBracket
            | T::LBrace
            | T::Arrow
            | T::Minus
            | T::Bang
            | T::Tilde
            | T::ColonColon
            | T::DotDot
            | T::DotDotDot => true,
            T::Keyword(k) => matches!(
                k,
                K::Nil
                    | K::True
                    | K::False
                    | K::SelfKw
                    | K::Cog
                    | K::Not
                    | K::If
                    | K::Unless
                    | K::While
                    | K::Until
                    | K::Case
                    | K::Begin
                    | K::Def
                    | K::Yield
                    | K::Super
                    | K::File
                    | K::Line
                    | K::Method
            ),
            _ => false,
        }
    }

    fn parse_binary(&mut self, min_prec: u8) -> PResult<Expr> {
        let start = self.peek().span;
        let mut lhs = self.parse_unary()?;
        while let Some((prec, op)) = binary_op(self.kind()) {
            if prec < min_prec {
                break;
            }
            self.bump();
            self.skip_newlines();
            let rhs = self.parse_binary(prec + 1)?;
            let span = self.span_from(start);
            lhs = match op {
                BinOp::And => self.node(span, ExprKind::And(Box::new(lhs), Box::new(rhs))),
                BinOp::Or => self.node(span, ExprKind::Or(Box::new(lhs), Box::new(rhs))),
                BinOp::Method(name) => self.call_node(
                    span,
                    Some(lhs),
                    name.to_string(),
                    vec![Arg::Positional(rhs)],
                    None,
                    false,
                    true,
                ),
            };
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        match self.kind().clone() {
            T::Bang => {
                self.bump();
                let operand = self.parse_unary()?;
                let span = self.span_from(start);
                Ok(self.node(span, ExprKind::Not(Box::new(operand))))
            }
            T::Minus => {
                if matches!(self.kind_at(1), T::Int { .. } | T::Float(_))
                    && !self.peek_at(1).space_before
                {
                    // `-2` is a literal (see parse_primary / parse_power).
                    return self.parse_power();
                }
                self.bump();
                let operand = self.parse_unary()?;
                let span = self.span_from(start);
                Ok(self.call_node(
                    span,
                    Some(operand),
                    "-@".to_string(),
                    vec![],
                    None,
                    false,
                    true,
                ))
            }
            T::Plus => {
                self.bump();
                let operand = self.parse_power()?;
                let span = self.span_from(start);
                Ok(self.call_node(
                    span,
                    Some(operand),
                    "+@".to_string(),
                    vec![],
                    None,
                    false,
                    true,
                ))
            }
            T::Tilde => {
                self.bump();
                let operand = self.parse_unary()?;
                let span = self.span_from(start);
                Ok(self.call_node(
                    span,
                    Some(operand),
                    "~".to_string(),
                    vec![],
                    None,
                    false,
                    true,
                ))
            }
            T::Amp | T::Star | T::StarStar => {
                let tok = self.bump();
                Err(self.error_at(
                    format!("{} is only allowed in argument lists", tok.kind),
                    tok.span,
                ))
            }
            _ => self.parse_power(),
        }
    }

    fn parse_power(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let negative_literal = self.at(&T::Minus);
        let mut base = self.parse_primary_postfix()?;
        if self.at(&T::StarStar) {
            self.bump();
            self.skip_newlines();
            let exp = self.parse_unary()?; // right-associative, allows -1
            let span = self.span_from(start);
            // `-2 ** 2` is `-(2 ** 2)`, as in Ruby: undo the literal's sign.
            let negate =
                negative_literal && matches!(base.kind, ExprKind::Int(_) | ExprKind::Float(_));
            if negate {
                if let Some(lit) = negate_literal(&base) {
                    base = self.node(base.span, lit);
                }
            }
            let pow = self.call_node(
                span,
                Some(base),
                "**".to_string(),
                vec![Arg::Positional(exp)],
                None,
                false,
                true,
            );
            if negate {
                return Ok(self.call_node(
                    span,
                    Some(pow),
                    "-@".to_string(),
                    vec![],
                    None,
                    false,
                    true,
                ));
            }
            return Ok(pow);
        }
        Ok(base)
    }

    #[allow(clippy::too_many_arguments)]
    fn call_node(
        &mut self,
        span: Span,
        recv: Option<Expr>,
        name: String,
        args: Vec<Arg>,
        block: Option<Block>,
        safe_nav: bool,
        has_parens: bool,
    ) -> Expr {
        self.node(
            span,
            ExprKind::Call(Box::new(Call {
                recv,
                name,
                args,
                block,
                safe_nav,
                has_parens,
                type_args: vec![],
            })),
        )
    }

    // ----- postfix: method calls, indexing, blocks -------------------------

    fn parse_primary_postfix(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let mut expr = self.parse_primary()?;
        loop {
            match self.kind().clone() {
                T::Dot | T::SafeNav => {
                    let safe_nav = self.at(&T::SafeNav);
                    self.bump();
                    self.skip_newlines();
                    expr = self.parse_method_call_after_dot(expr, safe_nav, start)?;
                }
                T::DotColon => {
                    self.bump();
                    let name = self.parse_method_name()?;
                    let span = self.span_from(start);
                    expr = self.node(
                        span,
                        ExprKind::MethodRef {
                            recv: Box::new(expr),
                            name,
                        },
                    );
                }
                T::ColonColon => match self.kind_at(1).clone() {
                    T::Const(name) if !matches!(self.kind_at(2), T::LParen) => {
                        self.bump();
                        self.bump();
                        expr = match expr.kind {
                            ExprKind::Const(mut path) => {
                                path.names.push(name);
                                let span = self.span_from(start);
                                self.node(span, ExprKind::Const(path))
                            }
                            _ => {
                                let span = self.span_from(start);
                                return Err(self.error_at("`::` must follow a constant", span));
                            }
                        };
                        expr = self.maybe_type_app(expr)?;
                    }
                    T::Ident(_) | T::Const(_) => {
                        self.bump();
                        expr = self.parse_method_call_after_dot(expr, false, start)?;
                    }
                    _ => break,
                },
                T::LBracket
                    if !self.peek().space_before || !matches!(expr.kind, ExprKind::Call(_)) =>
                {
                    self.bump();
                    let saved = self.no_do;
                    self.no_do = false;
                    self.skip_newlines();
                    let args = self.parse_call_args_until(&T::RBracket)?;
                    self.no_do = saved;
                    self.expect(&T::RBracket, "`]`")?;
                    // `xs[i]?` calls `[]?`.
                    let name = if self.at(&T::Question) && !self.peek().space_before {
                        self.bump();
                        "[]?"
                    } else {
                        "[]"
                    };
                    let span = self.span_from(start);
                    expr =
                        self.call_node(span, Some(expr), name.to_string(), args, None, false, true);
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    /// After `recv.`: a method name, optional arguments and block.
    fn parse_method_call_after_dot(
        &mut self,
        recv: Expr,
        safe_nav: bool,
        start: Span,
    ) -> PResult<Expr> {
        if self.at(&T::LParen) {
            // `recv.(args)`
            let args = self.parse_paren_args()?;
            let block = self.parse_block_opt()?;
            let span = self.span_from(start);
            return Ok(self.call_node(
                span,
                Some(recv),
                "call".to_string(),
                args,
                block,
                safe_nav,
                true,
            ));
        }
        let name = self.parse_method_name()?;
        self.finish_call(Some(recv), name, safe_nav, start)
    }

    fn parse_method_name(&mut self) -> PResult<String> {
        let tok = self.bump();
        match tok.kind {
            T::Ident(name) | T::Const(name) => Ok(name),
            T::Keyword(k) => Ok(k.as_str().to_string()),
            other => {
                let s = operator_method_name(&other).map(str::to_string);
                match s {
                    Some(s) => Ok(s),
                    None => Err(self.error_at(
                        format!("expected a method name, found {}", describe(&other)),
                        tok.span,
                    )),
                }
            }
        }
    }

    /// Parse the arguments and block of a call whose name has been consumed.
    fn finish_call(
        &mut self,
        recv: Option<Expr>,
        name: String,
        safe_nav: bool,
        start: Span,
    ) -> PResult<Expr> {
        let mut type_args = Vec::new();
        let mut has_parens = false;
        let mut args = Vec::new();

        // Explicit type arguments: `name[Int, String](...)`.
        if self.at(&T::LBracket)
            && !self.peek().space_before
            && matches!(self.kind_at(1), T::Const(_))
        {
            let mark = self.mark();
            let diag_mark = self.diagnostics.len();
            match self.parse_type_args() {
                Ok(tys) if self.at(&T::LParen) => type_args = tys,
                _ => {
                    self.reset(mark);
                    self.diagnostics.truncate(diag_mark);
                }
            }
        }

        if self.at(&T::LParen) && !self.peek().space_before {
            args = self.parse_paren_args()?;
            has_parens = true;
        } else if self.starts_command_arg() {
            args = self.parse_command_args()?;
            has_parens = true;
        }

        let block = self.parse_block_opt()?;
        let span = self.span_from(start);
        let mut expr = self.call_node(span, recv, name, args, block, safe_nav, has_parens);
        if let ExprKind::Call(call) = &mut expr.kind {
            call.type_args = type_args;
        }
        Ok(expr)
    }

    /// `foo x`: can the current token start a parenthesis-less argument?
    fn starts_command_arg(&mut self) -> bool {
        let tok = self.peek().clone();
        if !tok.space_before {
            return false;
        }
        let next_space = self.peek_at(1).space_before;
        match tok.kind {
            T::Ident(_)
            | T::Const(_)
            | T::IVar(_)
            | T::Int { .. }
            | T::Float(_)
            | T::Symbol(_)
            | T::StringBegin(_)
            | T::Words(_)
            | T::Symbols(_)
            | T::Arrow
            | T::ColonColon
            | T::Bang
            | T::Tilde => true,
            // `foo -x`, `foo *x`, `foo &blk`, `foo [1]`, `foo (x)`: an argument
            // only with no space after the operator.
            T::Minus | T::Star | T::StarStar | T::Amp | T::LBracket | T::LParen => !next_space,
            T::Keyword(k) => matches!(
                k,
                K::Nil
                    | K::True
                    | K::False
                    | K::SelfKw
                    | K::Cog
                    | K::Not
                    | K::Case
                    | K::Begin
                    | K::Yield
                    | K::Super
                    | K::File
                    | K::Line
                    | K::Method
                    | K::Def
            ),
            _ => false,
        }
    }

    fn parse_paren_args(&mut self) -> PResult<Vec<Arg>> {
        self.expect(&T::LParen, "`(`")?;
        let saved = self.no_do;
        self.no_do = false;
        self.skip_newlines();
        let args = self.parse_call_args_until(&T::RParen)?;
        self.skip_newlines();
        self.no_do = saved;
        self.expect(&T::RParen, "`)`")?;
        Ok(args)
    }

    fn parse_command_args(&mut self) -> PResult<Vec<Arg>> {
        let saved = self.no_do;
        self.no_do = true;
        let mut args = Vec::new();
        loop {
            args.push(self.parse_arg()?);
            if !self.at(&T::Comma) {
                break;
            }
            self.bump();
            self.skip_newlines();
        }
        self.no_do = saved;
        Ok(args)
    }

    fn parse_call_args_until(&mut self, close: &T) -> PResult<Vec<Arg>> {
        let mut args = Vec::new();
        loop {
            self.skip_newlines();
            if self.at(close) {
                break;
            }
            args.push(self.parse_arg()?);
            self.skip_newlines();
            if !self.eat(&T::Comma) {
                break;
            }
        }
        Ok(args)
    }

    /// One argument: positional, `*splat`, `**splat`, `&block`, or
    /// `label: value`.
    fn parse_arg(&mut self) -> PResult<Arg> {
        let start = self.peek().span;
        match self.kind().clone() {
            T::Star if !self.peek_at(1).space_before => {
                self.bump();
                let e = self.parse_expr()?;
                return Ok(Arg::Splat(e));
            }
            T::StarStar if !self.peek_at(1).space_before => {
                self.bump();
                let e = self.parse_expr()?;
                return Ok(Arg::DoubleSplat(e));
            }
            // `f(&)`: forward the anonymous block.
            T::Amp if matches!(self.kind_at(1), T::RParen | T::Comma) => {
                let span = self.bump().span;
                return Ok(Arg::BlockPass(
                    self.node(span, ExprKind::Local("&".to_string())),
                ));
            }
            T::Amp if !self.peek_at(1).space_before => {
                self.bump();
                let e = self.parse_expr()?;
                return Ok(Arg::BlockPass(e));
            }
            _ => {}
        }
        if let Some(name) = self.label_ahead() {
            self.bump();
            self.bump();
            self.skip_newlines();
            // `f(x:)` shorthand passes the variable or method `x`.
            let value = if matches!(
                self.kind(),
                T::Comma | T::RParen | T::RBracket | T::Newline | T::Eof
            ) {
                self.ident_value(&name, start)
            } else {
                self.parse_expr_no_label()?
            };
            let span = self.span_from(start);
            return Ok(Arg::Keyword { name, value, span });
        }
        // A string label: `"key": value` inside argument lists is not
        // supported for keyword arguments (only in hash literals).
        let e = self.parse_expr_no_label()?;
        Ok(Arg::Positional(e))
    }

    fn parse_arg_value(&mut self) -> PResult<Arg> {
        self.parse_arg()
    }

    /// `parse_expr` with `not`/`and`/`or` disallowed, but accepting the
    /// `rescue` modifier is not needed here.
    fn parse_expr_no_label(&mut self) -> PResult<Expr> {
        if self.at_kw(K::Not) {
            return self.parse_not_expr();
        }
        self.parse_expr()
    }

    /// If the tokens ahead are `name:` (an identifier, constant, keyword or
    /// plain string immediately followed by `:`), return the label name.
    fn label_ahead(&mut self) -> Option<String> {
        let name = match self.kind().clone() {
            T::Ident(n) | T::Const(n) => n,
            T::Keyword(k) => k.as_str().to_string(),
            _ => return None,
        };
        if self.is_adjacent_colon(1) && !matches!(self.kind_at(2), T::Colon) {
            Some(name)
        } else {
            None
        }
    }

    fn ident_value(&mut self, name: &str, span: Span) -> Expr {
        if self.is_local(name) {
            self.node(span, ExprKind::Local(name.to_string()))
        } else {
            self.call_node(span, None, name.to_string(), vec![], None, false, false)
        }
    }

    fn parse_block_opt(&mut self) -> PResult<Option<Block>> {
        let no_do = self.no_do;
        match self.kind() {
            T::LBrace => Ok(Some(self.parse_brace_block()?)),
            T::Keyword(K::Do) if !no_do => Ok(Some(self.parse_do_block()?)),
            _ => Ok(None),
        }
    }

    fn parse_brace_block(&mut self) -> PResult<Block> {
        let start = self.expect(&T::LBrace, "`{`")?.span;
        let saved = self.no_do;
        let saved_comp = self.in_comprehension;
        self.no_do = false;
        self.in_comprehension = false;
        self.push_scope(false);
        self.skip_newlines();
        let params = self.parse_block_params()?;
        let body = self.parse_statements(&[]);
        self.pop_scope();
        self.no_do = saved;
        self.in_comprehension = saved_comp;
        self.expect(&T::RBrace, "`}`")?;
        let span = self.span_from(start);
        Ok(Block {
            params,
            body,
            span,
            braces: true,
            ret: None,
        })
    }

    fn parse_do_block(&mut self) -> PResult<Block> {
        let start = self.expect_kw(K::Do)?.span;
        let saved = self.no_do;
        let saved_comp = self.in_comprehension;
        self.no_do = false;
        self.in_comprehension = false;
        self.push_scope(false);
        self.skip_newlines();
        let params = self.parse_block_params()?;
        let body = self.parse_body_with_rescue(&[K::End])?;
        self.pop_scope();
        self.no_do = saved;
        self.in_comprehension = saved_comp;
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        Ok(Block {
            params,
            body,
            span,
            braces: false,
            ret: None,
        })
    }

    fn parse_block_params(&mut self) -> PResult<Params> {
        if !self.at(&T::Pipe) {
            if self.at(&T::OrOr) {
                // `{ || ... }`
                self.bump();
            }
            return Ok(Params::empty());
        }
        self.bump();
        let params = self.parse_param_list(&T::Pipe)?;
        self.expect(&T::Pipe, "`|`")?;
        Ok(params)
    }

    // ----- primary expressions ---------------------------------------------

    fn parse_primary(&mut self) -> PResult<Expr> {
        let tok = self.peek().clone();
        let start = tok.span;
        if self.at_for_comprehension() {
            return self.parse_for_comprehension();
        }
        match tok.kind {
            T::Int { digits, base } => {
                self.bump();
                Ok(self.node(start, ExprKind::Int(IntLit::new(digits, base))))
            }
            T::Float(text) => {
                self.bump();
                let value: f64 = text.parse().unwrap_or(f64::NAN);
                Ok(self.node(start, ExprKind::Float(value)))
            }
            T::StringBegin(_) => self.parse_string_literal(),
            T::Symbol(name) => {
                self.bump();
                Ok(self.node(start, ExprKind::Symbol(name)))
            }
            T::Words(words) => {
                self.bump();
                let items = words
                    .into_iter()
                    .map(|w| {
                        Arg::Positional(self.node(start, ExprKind::Str(vec![StrPart::Lit(w)])))
                    })
                    .collect();
                Ok(self.node(start, ExprKind::Array(items)))
            }
            T::Symbols(words) => {
                self.bump();
                let items = words
                    .into_iter()
                    .map(|w| Arg::Positional(self.node(start, ExprKind::Symbol(w))))
                    .collect();
                Ok(self.node(start, ExprKind::Array(items)))
            }
            T::LBracket => self.parse_array_literal(),
            T::LBrace => self.parse_hash_literal(),
            T::LParen => {
                self.bump();
                let saved = self.no_do;
                self.no_do = false;
                let stmts = self.parse_statements(&[]);
                self.no_do = saved;
                self.expect(&T::RParen, "`)`")?;
                let span = self.span_from(start);
                Ok(match stmts.len() {
                    1 => {
                        let mut e = stmts.into_iter().next().unwrap();
                        e.span = span;
                        e
                    }
                    _ => self.node(span, ExprKind::Seq(stmts)),
                })
            }
            T::Arrow => self.parse_lambda(),
            T::IVar(name) => {
                self.bump();
                Ok(self.node(start, ExprKind::IVar(name)))
            }
            T::ColonColon | T::Const(_) => {
                let path = self.parse_const_path()?;
                let span = self.span_from(start);
                if self.at(&T::LParen) && !self.peek().space_before && path.names.len() == 1 {
                    // `Integer("3")`: a Kernel conversion function.
                    let name = path.names.into_iter().next().unwrap();
                    return self.finish_call(None, name, false, start);
                }
                let expr = self.node(span, ExprKind::Const(path));
                self.maybe_type_app(expr)
            }
            T::Ident(name) => {
                // `using M do ... end` is an expression too.
                if name == "using"
                    && !self.is_local(&name)
                    && matches!(self.kind_at(1), T::Const(_) | T::ColonColon)
                {
                    if let Some(expr) = self.parse_contextual_declaration(&name)? {
                        return Ok(expr);
                    }
                }
                self.bump();
                if self.is_local(&name) && !(self.at(&T::LParen) && !self.peek().space_before) {
                    return Ok(self.node(start, ExprKind::Local(name)));
                }
                self.finish_call(None, name, false, start)
            }
            T::Keyword(kw) => self.parse_keyword_expr(kw),
            T::DotDot | T::DotDotDot => self.parse_range(),
            T::Minus
                if matches!(self.kind_at(1), T::Int { .. } | T::Float(_))
                    && !self.peek_at(1).space_before =>
            {
                self.bump();
                let lit = self.bump();
                let span = self.span_from(start);
                Ok(match lit.kind {
                    T::Int { digits, base } => {
                        self.node(span, ExprKind::Int(IntLit::new(format!("-{digits}"), base)))
                    }
                    T::Float(text) => {
                        let value: f64 = text.parse().unwrap_or(f64::NAN);
                        self.node(span, ExprKind::Float(-value))
                    }
                    _ => unreachable!(),
                })
            }
            T::Minus | T::Bang | T::Tilde | T::Plus => self.parse_unary(),
            _ => Err(self.error_expected("an expression")),
        }
    }

    /// `Const[Type, ...]` in expression position becomes a type application
    /// when the bracket contents parse as types.
    fn maybe_type_app(&mut self, expr: Expr) -> PResult<Expr> {
        if !(self.at(&T::LBracket) && !self.peek().space_before) {
            return Ok(expr);
        }
        let ExprKind::Const(path) = &expr.kind else {
            return Ok(expr);
        };
        let mark = self.mark();
        let diag_mark = self.diagnostics.len();
        match self.parse_type_args() {
            Ok(args) if !args.is_empty() => {
                let span = self.span_from(expr.span);
                let ty = TypeExpr {
                    span,
                    kind: TypeExprKind::Named {
                        path: path.clone(),
                        args,
                    },
                };
                Ok(self.node(span, ExprKind::TypeApp(ty)))
            }
            _ => {
                // Not types: an index expression on a constant.
                self.reset(mark);
                self.diagnostics.truncate(diag_mark);
                Ok(expr)
            }
        }
    }

    fn parse_const_path(&mut self) -> PResult<ConstPath> {
        // `cog::Foo`: a path from the current cog's root module.
        let cog = self.at_kw(K::Cog) && matches!(self.kind_at(1), T::ColonColon);
        if cog {
            self.bump();
            self.bump();
        }
        let absolute = !cog && self.eat(&T::ColonColon);
        let mut names = Vec::new();
        loop {
            match self.kind().clone() {
                T::Const(name) => {
                    self.bump();
                    names.push(name);
                }
                _ => return Err(self.error_expected("a constant name")),
            }
            if self.at(&T::ColonColon) && matches!(self.kind_at(1), T::Const(_)) {
                self.bump();
                continue;
            }
            break;
        }
        Ok(ConstPath {
            absolute,
            cog,
            names,
        })
    }

    fn parse_string_literal(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let T::StringBegin(kind) = self.bump().kind else {
            unreachable!()
        };
        let mut parts = self.parse_string_parts()?;
        let mut flags = String::new();
        if let T::StringEnd { flags: f } = &self.peek().kind {
            flags = f.clone();
        }
        self.expect_string_end()?;
        // Adjacent string literals concatenate: "a" "b".
        if kind == StringKind::String {
            while matches!(self.kind(), T::StringBegin(StringKind::String)) {
                self.bump();
                let more = self.parse_string_parts()?;
                self.expect_string_end()?;
                for part in more {
                    match (parts.last_mut(), part) {
                        (Some(StrPart::Lit(prev)), StrPart::Lit(s)) => prev.push_str(&s),
                        (_, part) => parts.push(part),
                    }
                }
            }
        }
        let span = self.span_from(start);
        let kind = match kind {
            StringKind::String => ExprKind::Str(parts),
            StringKind::Symbol => {
                if parts.iter().all(|p| matches!(p, StrPart::Lit(_))) {
                    let name: String = parts
                        .into_iter()
                        .map(|p| match p {
                            StrPart::Lit(s) => s,
                            _ => unreachable!(),
                        })
                        .collect();
                    ExprKind::Symbol(name)
                } else {
                    ExprKind::DSymbol(parts)
                }
            }
            StringKind::Regexp => ExprKind::Regexp { parts, flags },
            StringKind::Bytes => ExprKind::Bytes(self.decode_bytes_literal(&parts, span)),
        };
        Ok(self.node(span, kind))
    }

    /// Decode the escapes of a `b"..."` literal. Characters outside ASCII
    /// contribute their UTF-8 bytes; `\xNN` and octal escapes any byte.
    fn decode_bytes_literal(&mut self, parts: &[StrPart], span: Span) -> Vec<u8> {
        let mut out = Vec::new();
        for part in parts {
            let StrPart::Lit(text) = part else { continue };
            let b = text.as_bytes();
            let mut i = 0;
            while i < b.len() {
                if b[i] != b'\\' {
                    out.push(b[i]);
                    i += 1;
                    continue;
                }
                i += 1;
                let Some(&c) = b.get(i) else {
                    let _ = self.error_at("invalid escape in a Bytes literal", span);
                    break;
                };
                i += 1;
                match c {
                    b'n' => out.push(b'\n'),
                    b't' => out.push(b'\t'),
                    b'r' => out.push(b'\r'),
                    b's' => out.push(b' '),
                    b'a' => out.push(0x07),
                    b'b' => out.push(0x08),
                    b'e' => out.push(0x1b),
                    b'f' => out.push(0x0c),
                    b'v' => out.push(0x0b),
                    b'\n' => {}
                    b'x' => {
                        let mut value = 0u32;
                        let mut count = 0;
                        while count < 2 && b.get(i).is_some_and(u8::is_ascii_hexdigit) {
                            value = value * 16 + (b[i] as char).to_digit(16).unwrap();
                            i += 1;
                            count += 1;
                        }
                        if count == 0 {
                            let _ = self.error_at("invalid hex escape in a Bytes literal", span);
                        }
                        out.push(value as u8);
                    }
                    b'0'..=b'7' => {
                        let mut value = (c - b'0') as u32;
                        let mut count = 1;
                        while count < 3 && matches!(b.get(i), Some(b'0'..=b'7')) {
                            value = value * 8 + (b[i] - b'0') as u32;
                            i += 1;
                            count += 1;
                        }
                        if value > 0xff {
                            let _ =
                                self.error_at("octal escape above \\377 in a Bytes literal", span);
                        }
                        out.push(value as u8);
                    }
                    b'u' => {
                        let mut value = 0u32;
                        let mut count = 0;
                        while count < 4 && b.get(i).is_some_and(u8::is_ascii_hexdigit) {
                            value = value * 16 + (b[i] as char).to_digit(16).unwrap();
                            i += 1;
                            count += 1;
                        }
                        match (count == 4).then(|| char::from_u32(value)).flatten() {
                            Some(ch) => out.extend_from_slice(ch.to_string().as_bytes()),
                            None => {
                                let _ = self
                                    .error_at("invalid Unicode escape in a Bytes literal", span);
                            }
                        }
                    }
                    other => out.push(other),
                }
            }
        }
        out
    }

    fn expect_string_end(&mut self) -> PResult<()> {
        match self.kind() {
            T::StringEnd { .. } => {
                self.bump();
                Ok(())
            }
            _ => Err(self.error_expected("the end of the string literal")),
        }
    }

    fn parse_string_parts(&mut self) -> PResult<Vec<StrPart>> {
        let mut parts = Vec::new();
        loop {
            match self.kind().clone() {
                T::StringContent(s) => {
                    self.bump();
                    match parts.last_mut() {
                        Some(StrPart::Lit(prev)) => prev.push_str(&s),
                        _ => parts.push(StrPart::Lit(s)),
                    }
                }
                T::EmbExprBegin => {
                    let begin = self.bump().span;
                    let saved = self.no_do;
                    self.no_do = false;
                    let stmts = self.parse_statements(&[]);
                    self.no_do = saved;
                    self.expect(&T::EmbExprEnd, "`}` closing the interpolation")?;
                    let span = self.span_from(begin);
                    let expr = match stmts.len() {
                        0 => self.node(span, ExprKind::Nil),
                        1 => stmts.into_iter().next().unwrap(),
                        _ => self.node(span, ExprKind::Seq(stmts)),
                    };
                    parts.push(StrPart::Interp(expr));
                }
                _ => break,
            }
        }
        Ok(parts)
    }

    fn parse_array_literal(&mut self) -> PResult<Expr> {
        let start = self.expect(&T::LBracket, "`[`")?.span;
        let saved = self.no_do;
        self.no_do = false;
        let items = self.parse_call_args_until(&T::RBracket)?;
        self.skip_newlines();
        self.no_do = saved;
        self.expect(&T::RBracket, "`]`")?;
        let span = self.span_from(start);
        for item in &items {
            if let Arg::Keyword { span, .. } | Arg::DoubleSplat(Expr { span, .. }) = item {
                self.error_at(
                    "keyword arguments are not allowed in an array literal",
                    *span,
                );
            }
        }
        Ok(self.node(span, ExprKind::Array(items)))
    }

    fn parse_hash_literal(&mut self) -> PResult<Expr> {
        let start = self.expect(&T::LBrace, "`{`")?.span;
        let saved = self.no_do;
        self.no_do = false;
        let mut entries = Vec::new();
        loop {
            self.skip_newlines();
            if self.at(&T::RBrace) {
                break;
            }
            entries.push(self.parse_hash_entry()?);
            self.skip_newlines();
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.skip_newlines();
        self.no_do = saved;
        self.expect(&T::RBrace, "`}`")?;
        let span = self.span_from(start);
        Ok(self.node(span, ExprKind::Hash(entries)))
    }

    fn parse_hash_entry(&mut self) -> PResult<HashEntry> {
        let start = self.peek().span;
        if self.at(&T::StarStar) {
            self.bump();
            let e = self.parse_expr()?;
            return Ok(HashEntry::DoubleSplat(e));
        }
        if let Some(name) = self.label_ahead() {
            self.bump();
            self.bump();
            self.skip_newlines();
            let key = self.node(start, ExprKind::Symbol(name.clone()));
            let value = if matches!(self.kind(), T::Comma | T::RBrace | T::Newline) {
                self.ident_value(&name, start)
            } else {
                self.parse_expr()?
            };
            return Ok(HashEntry::Pair { key, value });
        }
        let key = self.parse_expr()?;
        // `"key": value` makes a symbol key.
        if self.at(&T::Colon) && !self.peek().space_before && matches!(key.kind, ExprKind::Str(_)) {
            self.bump();
            self.skip_newlines();
            let key = match key.kind {
                ExprKind::Str(parts) => {
                    let span = key.span;
                    if parts.iter().all(|p| matches!(p, StrPart::Lit(_))) {
                        let name = parts
                            .into_iter()
                            .map(|p| match p {
                                StrPart::Lit(s) => s,
                                _ => unreachable!(),
                            })
                            .collect();
                        self.node(span, ExprKind::Symbol(name))
                    } else {
                        self.node(span, ExprKind::DSymbol(parts))
                    }
                }
                _ => unreachable!(),
            };
            let value = self.parse_expr()?;
            return Ok(HashEntry::Pair { key, value });
        }
        self.skip_newlines();
        self.expect(&T::FatArrow, "`=>`")?;
        self.skip_newlines();
        let value = self.parse_expr()?;
        Ok(HashEntry::Pair { key, value })
    }

    /// `for` is a contextual keyword: `for x in`, `for x, y in`.
    fn at_for_comprehension(&mut self) -> bool {
        if !matches!(self.kind(), T::Ident(name) if name == "for") {
            return false;
        }
        let mut k = 1;
        loop {
            if !matches!(self.kind_at(k), T::Ident(_)) {
                return false;
            }
            match self.kind_at(k + 1) {
                T::Keyword(K::In) => return true,
                T::Comma => k += 2,
                _ => return false,
            }
        }
    }

    /// A `for` comprehension:
    ///
    /// ```text
    /// for x in xs when x.even?, y in ys do [x, y] end
    /// ```
    ///
    /// desugars to `xs.filter { |x| x.even? }.flat_map { |x| ys.map { |y|
    /// [x, y] } }`: one `filter` per guard, `flat_map` for every iterator
    /// but the last, `map` for the last. The variables are block
    /// parameters, so later iterators, guards and the body see the
    /// earlier ones and nothing leaks out.
    fn parse_for_comprehension(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // for
        type Iterator = ForIterator;
        let mut iterators: Vec<Iterator> = Vec::new();
        let saved_comp = self.in_comprehension;
        // Every iterator (and the body) is parsed inside the scopes of the
        // earlier ones, as the generated blocks nest.
        let mut scopes = 0;
        loop {
            let istart = self.peek().span;
            let mut names = Vec::new();
            loop {
                let tok = self.bump();
                let T::Ident(name) = tok.kind else {
                    self.error_at("expected a variable name", tok.span);
                    return Err(ParseError);
                };
                names.push((name, tok.span));
                if !self.eat(&T::Comma) {
                    break;
                }
            }
            self.expect_kw(K::In)?;
            // The source is evaluated in the scope of the earlier
            // iterators but not of this one.
            let saved_in = self.allow_in_match;
            let saved_do = self.no_do;
            self.allow_in_match = false;
            self.no_do = true;
            let source = self.parse_ternary();
            self.allow_in_match = saved_in;
            self.no_do = saved_do;
            let source = source?;
            self.push_scope(false);
            scopes += 1;
            for (name, _) in &names {
                self.declare(name);
            }
            let guard = if self.at_kw(K::When) {
                self.bump();
                self.in_comprehension = true;
                // A `do` after the guard starts the body, not a block of
                // the guard's last call (`when x.odd? do`).
                let saved_do = self.no_do;
                self.no_do = true;
                let g = self.parse_ternary();
                self.no_do = saved_do;
                self.in_comprehension = saved_comp;
                Some(g?)
            } else {
                None
            };
            let span = self.span_from(istart);
            iterators.push(Iterator {
                names,
                source,
                guard,
                span,
            });
            if self.eat(&T::Comma) {
                self.skip_newlines();
                continue;
            }
            break;
        }
        // The body follows `do`, or starts on the next line.
        if self.at_kw(K::Do) {
            self.bump();
        } else if !matches!(self.kind(), T::Newline) {
            self.error_expected("`do` or a new line after the iterators of `for`");
            for _ in 0..scopes {
                self.pop_scope();
            }
            return Err(ParseError);
        }
        self.in_comprehension = true;
        let mut body = self.parse_statements(&[K::End]);
        self.in_comprehension = saved_comp;
        for _ in 0..scopes {
            self.pop_scope();
        }
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        let each = self.for_each_expansion(&iterators, &body, span);
        // Build from the inside out.
        let last = iterators.len() - 1;
        let mut inner: Option<Expr> = None;
        for (k, it) in iterators.into_iter().enumerate().rev() {
            let params = Params {
                list: it
                    .names
                    .iter()
                    .map(|(name, span)| Param {
                        name: name.clone(),
                        kind: ParamKind::Positional,
                        ty: None,
                        default: None,
                        assigns_ivar: false,
                        usings: Vec::new(),
                        span: *span,
                    })
                    .collect(),
            };
            let mut recv = it.source;
            if let Some(guard) = it.guard {
                let gspan = guard.span;
                recv = self.node(
                    gspan,
                    ExprKind::Call(Box::new(Call {
                        recv: Some(recv),
                        name: "filter".to_string(),
                        args: vec![],
                        block: Some(Block {
                            params: params.clone(),
                            body: vec![guard],
                            span: gspan,
                            braces: true,
                            ret: None,
                        }),
                        safe_nav: false,
                        has_parens: false,
                        type_args: vec![],
                    })),
                );
            }
            let body_exprs = match inner.take() {
                Some(e) => vec![e],
                None => std::mem::take(&mut body),
            };
            let name = if k == last { "map" } else { "flat_map" };
            inner = Some(self.node(
                it.span,
                ExprKind::Call(Box::new(Call {
                    recv: Some(recv),
                    name: name.to_string(),
                    args: vec![],
                    block: Some(Block {
                        params,
                        body: body_exprs,
                        span: it.span,
                        braces: true,
                        ret: None,
                    }),
                    safe_nav: false,
                    has_parens: false,
                    type_args: vec![],
                })),
            ));
        }
        let mut comprehension = inner.expect("at least one iterator");
        comprehension.span = span;
        Ok(self.node(
            span,
            ExprKind::For(Box::new(ForExpr {
                comprehension,
                each,
            })),
        ))
    }

    /// The `each` expansion of a `for` (see `ForExpr`): from the inside
    /// out, `source.each { |names| if guard then <rest> end }`, the body
    /// innermost; the same source, guard and body nodes as the
    /// comprehension.
    fn for_each_expansion(&mut self, iterators: &[ForIterator], body: &[Expr], span: Span) -> Expr {
        let mut inner: Vec<Expr> = body.to_vec();
        for it in iterators.iter().rev() {
            if let Some(guard) = &it.guard {
                let gspan = guard.span;
                inner = vec![self.node(
                    gspan,
                    ExprKind::If {
                        cond: Box::new(guard.clone()),
                        then: inner,
                        els: None,
                    },
                )];
            }
            let params = Params {
                list: it
                    .names
                    .iter()
                    .map(|(name, span)| Param {
                        name: name.clone(),
                        kind: ParamKind::Positional,
                        ty: None,
                        default: None,
                        assigns_ivar: false,
                        usings: Vec::new(),
                        span: *span,
                    })
                    .collect(),
            };
            inner = vec![self.node(
                it.span,
                ExprKind::Call(Box::new(Call {
                    recv: Some(it.source.clone()),
                    name: "each".to_string(),
                    args: vec![],
                    block: Some(Block {
                        params,
                        body: inner,
                        span: it.span,
                        braces: true,
                        ret: None,
                    }),
                    safe_nav: false,
                    has_parens: false,
                    type_args: vec![],
                })),
            )];
        }
        let mut each = inner.pop().expect("at least one iterator");
        each.span = span;
        each
    }

    fn parse_lambda(&mut self) -> PResult<Expr> {
        let start = self.expect(&T::Arrow, "`->`")?.span;
        self.push_scope(false);
        let params = if self.at(&T::LParen) {
            self.bump();
            let params = self.parse_param_list(&T::RParen)?;
            self.expect(&T::RParen, "`)`")?;
            params
        } else if matches!(self.kind(), T::Ident(_)) {
            self.parse_param_list_bare()?
        } else {
            Params::empty()
        };
        let ret = if self.eat(&T::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let (body, braces) = if self.at(&T::LBrace) {
            let saved = self.no_do;
            self.no_do = false;
            self.bump();
            let body = self.parse_statements(&[]);
            self.expect(&T::RBrace, "`}`")?;
            self.no_do = saved;
            (body, true)
        } else if self.at_kw(K::Do) {
            let saved = self.no_do;
            self.no_do = false;
            self.bump();
            let body = self.parse_body_with_rescue(&[K::End])?;
            self.expect_kw(K::End)?;
            self.no_do = saved;
            (body, false)
        } else {
            self.pop_scope();
            return Err(self.error_expected("`{` or `do` for the lambda body"));
        };
        self.pop_scope();
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::Lambda(Box::new(Block {
                params,
                body,
                span,
                braces,
                ret,
            })),
        ))
    }

    fn parse_keyword_expr(&mut self, kw: K) -> PResult<Expr> {
        let start = self.peek().span;
        match kw {
            K::Nil => {
                self.bump();
                Ok(self.node(start, ExprKind::Nil))
            }
            K::True => {
                self.bump();
                Ok(self.node(start, ExprKind::True))
            }
            K::False => {
                self.bump();
                Ok(self.node(start, ExprKind::False))
            }
            K::SelfKw => {
                self.bump();
                Ok(self.node(start, ExprKind::SelfRef))
            }
            K::Cog => {
                if matches!(self.kind_at(1), T::ColonColon) {
                    let path = self.parse_const_path()?;
                    let span = self.span_from(start);
                    let expr = self.node(span, ExprKind::Const(path));
                    return self.maybe_type_app(expr);
                }
                self.bump();
                // `cog.name` and `cog.version` are the manifest's, as
                // literals.
                if self.at(&T::Dot) && !matches!(self.kind_at(2), T::LParen) {
                    if let T::Ident(field) = self.kind_at(1).clone() {
                        let value = match field.as_str() {
                            "name" => Some(self.cog.name.clone()),
                            "version" => Some(self.cog.version.clone()),
                            _ => None,
                        };
                        if let Some(value) = value {
                            self.bump();
                            self.bump();
                            let span = self.span_from(start);
                            return Ok(self.node(span, ExprKind::Str(vec![StrPart::Lit(value)])));
                        }
                    }
                }
                let path = ConstPath {
                    absolute: false,
                    cog: true,
                    names: Vec::new(),
                };
                Ok(self.node(start, ExprKind::Const(path)))
            }
            K::File => {
                self.bump();
                Ok(self.node(start, ExprKind::Magic(Magic::File)))
            }
            K::Line => {
                self.bump();
                Ok(self.node(start, ExprKind::Magic(Magic::Line)))
            }
            K::Method => {
                self.bump();
                Ok(self.node(start, ExprKind::Magic(Magic::Method)))
            }
            K::If | K::Unless => self.parse_if(),
            K::While | K::Until => self.parse_while(),
            K::Case => self.parse_case(),
            K::Begin => self.parse_begin(),
            K::Def => self.parse_def(None, false, false, false),
            K::Class => self.parse_class(false),
            K::Module => self.parse_module(),
            K::Return | K::Break | K::Next => {
                if kw == K::Break && self.in_comprehension {
                    self.error_at("`break` cannot be used in a `for` comprehension", start);
                }
                self.bump();
                let value = if self.starts_expression() && !self.at_modifier() {
                    Some(Box::new(self.parse_rhs_list()?))
                } else {
                    None
                };
                let span = self.span_from(start);
                Ok(self.node(
                    span,
                    match kw {
                        K::Return => ExprKind::Return(value),
                        K::Break => ExprKind::Break(value),
                        _ => ExprKind::Next(value),
                    },
                ))
            }
            K::Retry => {
                self.bump();
                Ok(self.node(start, ExprKind::Retry))
            }
            K::Yield => {
                self.bump();
                let args = if self.at(&T::LParen) && !self.peek().space_before {
                    self.parse_paren_args()?
                } else if self.starts_command_arg() {
                    self.parse_command_args()?
                } else {
                    vec![]
                };
                let span = self.span_from(start);
                Ok(self.node(span, ExprKind::Yield(args)))
            }
            K::Super => {
                self.bump();
                let args = if self.at(&T::LParen) && !self.peek().space_before {
                    Some(self.parse_paren_args()?)
                } else if self.starts_command_arg() {
                    Some(self.parse_command_args()?)
                } else {
                    None
                };
                let block = self.parse_block_opt()?.map(Box::new);
                let span = self.span_from(start);
                Ok(self.node(span, ExprKind::Super { args, block }))
            }
            K::Not => self.parse_not_expr(),
            K::Alias => self.parse_alias(),
            _ => Err(self.error_expected("an expression")),
        }
    }

    fn at_modifier(&mut self) -> bool {
        matches!(
            self.kind(),
            T::Keyword(K::If | K::Unless | K::While | K::Until | K::Rescue)
        )
    }

    fn parse_alias(&mut self) -> PResult<Expr> {
        let start = self.expect_kw(K::Alias)?.span;
        let new_name = self.parse_alias_name()?;
        let old_name = self.parse_alias_name()?;
        let span = self.span_from(start);
        Ok(self.node(span, ExprKind::Alias { new_name, old_name }))
    }

    fn parse_alias_name(&mut self) -> PResult<String> {
        match self.kind().clone() {
            T::Symbol(name) => {
                self.bump();
                Ok(name)
            }
            _ => self.parse_method_name(),
        }
    }

    // ----- control flow ----------------------------------------------------

    fn parse_if(&mut self) -> PResult<Expr> {
        let tok = self.bump();
        let start = tok.span;
        let negate = matches!(tok.kind, T::Keyword(K::Unless));
        let cond = self.parse_cond()?;
        let cond = if negate { self.not(cond) } else { cond };
        self.eat_then();
        let then = self.parse_statements(&[K::Elsif, K::Else, K::End]);
        let els = match self.kind() {
            T::Keyword(K::Elsif) => {
                if negate {
                    let tok = self.peek().clone();
                    self.error_at("`unless` cannot have `elsif`", tok.span);
                }
                Some(vec![self.parse_if()?])
            }
            T::Keyword(K::Else) => {
                self.bump();
                let els = self.parse_statements(&[K::End]);
                self.expect_kw(K::End)?;
                Some(els)
            }
            _ => {
                self.expect_kw(K::End)?;
                None
            }
        };
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::If {
                cond: Box::new(cond),
                then,
                els,
            },
        ))
    }

    /// Condition of `if`/`while` etc.: `do` does not attach to calls inside.
    fn parse_cond(&mut self) -> PResult<Expr> {
        let saved = self.no_do;
        self.no_do = true;
        let cond = self.parse_expr_stmt();
        self.no_do = saved;
        cond
    }

    fn eat_then(&mut self) {
        self.skip_newlines();
        if self.eat_kw(K::Then) {
            self.skip_newlines();
        }
    }

    fn parse_while(&mut self) -> PResult<Expr> {
        let tok = self.bump();
        let start = tok.span;
        let negate = matches!(tok.kind, T::Keyword(K::Until));
        let cond = self.parse_cond()?;
        self.skip_newlines();
        self.eat_kw(K::Do);
        let body = self.parse_statements(&[K::End]);
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::While {
                cond: Box::new(cond),
                body,
                negate,
                do_while: false,
            },
        ))
    }

    fn parse_case(&mut self) -> PResult<Expr> {
        let start = self.expect_kw(K::Case)?.span;
        let subject = if self.at(&T::Newline) {
            None
        } else {
            let saved = self.allow_in_match;
            self.allow_in_match = false;
            let subject = self.parse_expr_stmt();
            self.allow_in_match = saved;
            Some(subject?)
        };
        self.skip_newlines();
        match self.kind() {
            T::Keyword(K::When) => {
                let mut whens = Vec::new();
                while self.eat_kw(K::When) {
                    let saved = self.no_do;
                    self.no_do = true;
                    let mut conds = vec![self.parse_arg()?];
                    while self.eat(&T::Comma) {
                        self.skip_newlines();
                        conds.push(self.parse_arg()?);
                    }
                    self.no_do = saved;
                    self.eat_then();
                    let body = self.parse_statements(&[K::When, K::Else, K::End]);
                    whens.push(When { conds, body });
                }
                let els = if self.eat_kw(K::Else) {
                    Some(self.parse_statements(&[K::End]))
                } else {
                    None
                };
                self.expect_kw(K::End)?;
                let span = self.span_from(start);
                Ok(self.node(
                    span,
                    ExprKind::Case {
                        subject: subject.map(Box::new),
                        whens,
                        els,
                    },
                ))
            }
            T::Keyword(K::In) => {
                let Some(subject) = subject else {
                    return Err(self.error_expected("a subject for `case ... in`"));
                };
                let mut arms = Vec::new();
                while self.eat_kw(K::In) {
                    let pattern = self.parse_pattern_top()?;
                    let guard = match self.kind() {
                        T::Keyword(K::If) => {
                            self.bump();
                            Some(Guard {
                                cond: self.parse_cond()?,
                                negate: false,
                            })
                        }
                        T::Keyword(K::Unless) => {
                            self.bump();
                            Some(Guard {
                                cond: self.parse_cond()?,
                                negate: true,
                            })
                        }
                        _ => None,
                    };
                    self.eat_then();
                    let body = self.parse_statements(&[K::In, K::Else, K::End]);
                    arms.push(InArm {
                        pattern,
                        guard,
                        body,
                    });
                }
                let els = if self.eat_kw(K::Else) {
                    Some(self.parse_statements(&[K::End]))
                } else {
                    None
                };
                self.expect_kw(K::End)?;
                let span = self.span_from(start);
                Ok(self.node(
                    span,
                    ExprKind::CaseIn {
                        subject: Box::new(subject),
                        arms,
                        els,
                    },
                ))
            }
            _ => Err(self.error_expected("`when` or `in`")),
        }
    }

    fn parse_begin(&mut self) -> PResult<Expr> {
        let start = self.expect_kw(K::Begin)?.span;
        let block = self.parse_begin_body(&[K::End])?;
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        Ok(self.node(span, ExprKind::Begin(Box::new(block))))
    }

    /// `body [rescue ...]* [else ...] [ensure ...]` up to (not including) a
    /// stop keyword.
    fn parse_begin_body(&mut self, stop: &[K]) -> PResult<BeginBlock> {
        let mut inner_stop = vec![K::Rescue, K::Else, K::Ensure];
        inner_stop.extend_from_slice(stop);
        let body = self.parse_statements(&inner_stop);
        let mut rescues = Vec::new();
        while self.at_kw(K::Rescue) {
            let rstart = self.bump().span;
            let mut classes = Vec::new();
            if !matches!(self.kind(), T::FatArrow | T::Newline | T::Keyword(K::Then)) {
                classes.push(self.parse_type()?);
                while self.eat(&T::Comma) {
                    self.skip_newlines();
                    classes.push(self.parse_type()?);
                }
            }
            let var = if self.eat(&T::FatArrow) {
                match self.kind().clone() {
                    T::Ident(name) => {
                        self.bump();
                        self.declare(&name);
                        Some(name)
                    }
                    _ => return Err(self.error_expected("a variable name after `=>`")),
                }
            } else {
                None
            };
            self.eat_then();
            let body = self.parse_statements(&inner_stop);
            let span = self.span_from(rstart);
            rescues.push(Rescue {
                classes,
                var,
                body,
                span,
            });
        }
        let else_body = if self.at_kw(K::Else) {
            self.bump();
            let mut s = vec![K::Ensure];
            s.extend_from_slice(stop);
            Some(self.parse_statements(&s))
        } else {
            None
        };
        let ensure = if self.at_kw(K::Ensure) {
            self.bump();
            Some(self.parse_statements(stop))
        } else {
            None
        };
        Ok(BeginBlock {
            body,
            rescues,
            else_body,
            ensure,
        })
    }

    /// A method or `do` block body, which may have `rescue`/`ensure`
    /// clauses without an explicit `begin`.
    fn parse_body_with_rescue(&mut self, stop: &[K]) -> PResult<Vec<Expr>> {
        let start = self.peek().span;
        let block = self.parse_begin_body(stop)?;
        if block.rescues.is_empty() && block.else_body.is_none() && block.ensure.is_none() {
            return Ok(block.body);
        }
        let span = self.span_from(start);
        Ok(vec![self.node(span, ExprKind::Begin(Box::new(block)))])
    }

    // ----- patterns --------------------------------------------------------

    /// A top-level pattern: `a, b` without brackets is an array pattern and
    /// `x:, y:` without braces is a hash pattern.
    fn parse_pattern_top(&mut self) -> PResult<Pattern> {
        let start = self.peek().span;
        if self.label_ahead().is_some() {
            let hash = self.parse_hash_pattern_body(&[])?;
            let span = self.span_from(start);
            return Ok(Pattern {
                span,
                kind: PatternKind::Hash(hash),
            });
        }
        let first = self.parse_pattern()?;
        if !self.at(&T::Comma) {
            return Ok(first);
        }
        let mut pre = vec![first];
        let mut rest = None;
        let mut post = Vec::new();
        while self.eat(&T::Comma) {
            if self.at(&T::Star) {
                self.bump();
                rest = Some(self.parse_rest_name());
                continue;
            }
            let p = self.parse_pattern()?;
            if rest.is_some() {
                post.push(p);
            } else {
                pre.push(p);
            }
        }
        let span = self.span_from(start);
        Ok(Pattern {
            span,
            kind: PatternKind::Array(ArrayPattern { pre, rest, post }),
        })
    }

    fn parse_rest_name(&mut self) -> Option<String> {
        match self.kind().clone() {
            T::Ident(name) => {
                self.bump();
                self.declare(&name);
                Some(name)
            }
            _ => None,
        }
    }

    fn parse_pattern(&mut self) -> PResult<Pattern> {
        let start = self.peek().span;
        let mut alts = vec![self.parse_pattern_primary()?];
        while self.at(&T::Pipe) {
            self.bump();
            self.skip_newlines();
            alts.push(self.parse_pattern_primary()?);
        }
        let mut pat = if alts.len() == 1 {
            alts.pop().unwrap()
        } else {
            let span = self.span_from(start);
            Pattern {
                span,
                kind: PatternKind::Alt(alts),
            }
        };
        while self.at(&T::FatArrow) {
            self.bump();
            match self.kind().clone() {
                T::Ident(name) => {
                    self.bump();
                    self.declare(&name);
                    let span = self.span_from(start);
                    pat = Pattern {
                        span,
                        kind: PatternKind::Capture(Box::new(pat), name),
                    };
                }
                _ => return Err(self.error_expected("a variable name after `=>`")),
            }
        }
        Ok(pat)
    }

    fn parse_pattern_primary(&mut self) -> PResult<Pattern> {
        let tok = self.peek().clone();
        let start = tok.span;
        let kind = match tok.kind {
            T::Ident(name) => {
                self.bump();
                self.declare(&name);
                PatternKind::Bind(name)
            }
            T::Caret => {
                self.bump();
                let expr = match self.kind().clone() {
                    T::Ident(name) => {
                        self.bump();
                        if self.is_local(&name) {
                            self.node(start, ExprKind::Local(name))
                        } else {
                            return Err(self.error_at(
                                format!("`^{name}` must refer to a local variable"),
                                start,
                            ));
                        }
                    }
                    T::IVar(name) => {
                        self.bump();
                        self.node(start, ExprKind::IVar(name))
                    }
                    T::LParen => {
                        self.bump();
                        let e = self.parse_expr_stmt()?;
                        self.expect(&T::RParen, "`)`")?;
                        e
                    }
                    _ => return Err(self.error_expected("a variable or `(` after `^`")),
                };
                PatternKind::Pin(expr)
            }
            T::LBracket => {
                self.bump();
                let kind = self.parse_array_pattern_body(&T::RBracket)?;
                self.expect(&T::RBracket, "`]`")?;
                kind
            }
            T::LBrace => {
                self.bump();
                self.skip_newlines();
                let hash = self.parse_hash_pattern_body(&[])?;
                self.skip_newlines();
                self.expect(&T::RBrace, "`}`")?;
                PatternKind::Hash(hash)
            }
            T::Keyword(K::Cog) if !matches!(self.kind_at(1), T::ColonColon) => {
                return Err(self.error_expected("a pattern"));
            }
            T::Const(_) | T::ColonColon | T::Keyword(K::Cog) => {
                let path = self.parse_const_path()?;
                if self.at(&T::LParen) && !self.peek().space_before {
                    self.bump();
                    self.skip_newlines();
                    let kind = if self.label_ahead().is_some() || self.at(&T::StarStar) {
                        let hash = self.parse_hash_pattern_body(&[])?;
                        PatternKind::ConstHash(path, Box::new(hash))
                    } else {
                        match self.parse_array_pattern_body(&T::RParen)? {
                            PatternKind::Array(ap) => PatternKind::ConstArray(path, Box::new(ap)),
                            other => {
                                let span = self.span_from(start);
                                return Err(self
                                    .error_at(format!("unsupported sub-pattern {other:?}"), span));
                            }
                        }
                    };
                    self.skip_newlines();
                    self.expect(&T::RParen, "`)`")?;
                    kind
                } else if self.at(&T::LBracket) && !self.peek().space_before {
                    self.bump();
                    let kind = match self.parse_array_pattern_body(&T::RBracket)? {
                        PatternKind::Array(ap) => PatternKind::ConstArray(path, Box::new(ap)),
                        other => {
                            let span = self.span_from(start);
                            return Err(
                                self.error_at(format!("unsupported sub-pattern {other:?}"), span)
                            );
                        }
                    };
                    self.expect(&T::RBracket, "`]`")?;
                    kind
                } else if matches!(self.kind(), T::DotDot | T::DotDotDot) {
                    let span = self.span_from(start);
                    let lo = self.node(span, ExprKind::Const(path));
                    return self.parse_range_pattern(Some(lo), start);
                } else {
                    PatternKind::Const(path)
                }
            }
            T::Keyword(K::Nil) => {
                self.bump();
                PatternKind::Value(self.node(start, ExprKind::Nil))
            }
            T::DotDot | T::DotDotDot => return self.parse_range_pattern(None, start),
            T::Arrow => PatternKind::Value(self.parse_lambda()?),
            _ => {
                // Literal values: numbers, strings, symbols, regexps,
                // true/false, ranges of literals.
                let value = self.parse_pattern_value()?;
                if matches!(self.kind(), T::DotDot | T::DotDotDot) {
                    return self.parse_range_pattern(Some(value), start);
                }
                PatternKind::Value(value)
            }
        };
        let span = self.span_from(start);
        Ok(Pattern { span, kind })
    }

    fn parse_pattern_value(&mut self) -> PResult<Expr> {
        match self.kind().clone() {
            T::Int { .. }
            | T::Float(_)
            | T::StringBegin(_)
            | T::Symbol(_)
            | T::Words(_)
            | T::Symbols(_)
            | T::Keyword(K::True | K::False | K::SelfKw | K::File | K::Line)
            | T::Minus => self.parse_unary(),
            _ => Err(self.error_expected("a pattern")),
        }
    }

    fn parse_range_pattern(&mut self, lo: Option<Expr>, start: Span) -> PResult<Pattern> {
        let exclusive = self.at(&T::DotDotDot);
        self.bump();
        let hi = if matches!(
            self.kind(),
            T::Int { .. } | T::Float(_) | T::StringBegin(_) | T::Minus | T::Const(_)
        ) {
            Some(self.parse_unary()?)
        } else {
            None
        };
        let span = self.span_from(start);
        Ok(Pattern {
            span,
            kind: PatternKind::Range { lo, hi, exclusive },
        })
    }

    fn parse_array_pattern_body(&mut self, close: &T) -> PResult<PatternKind> {
        let mut pre = Vec::new();
        let mut rest: Option<Option<String>> = None;
        let mut post = Vec::new();
        let mut second_rest: Option<Option<String>> = None;
        loop {
            self.skip_newlines();
            if self.at(close) {
                break;
            }
            if self.at(&T::Star) {
                self.bump();
                let name = self.parse_rest_name();
                if rest.is_none() {
                    rest = Some(name);
                } else if second_rest.is_none() {
                    second_rest = Some(name);
                } else {
                    let tok = self.peek().clone();
                    return Err(self.error_at("too many `*` in a pattern", tok.span));
                }
            } else {
                let p = self.parse_pattern()?;
                if rest.is_some() {
                    post.push(p);
                } else {
                    pre.push(p);
                }
            }
            self.skip_newlines();
            if !self.eat(&T::Comma) {
                break;
            }
        }
        if let Some(post_rest) = second_rest {
            if !pre.is_empty() {
                let tok = self.peek().clone();
                return Err(self.error_at("a find pattern must start with `*`", tok.span));
            }
            return Ok(PatternKind::Find {
                pre_rest: rest.unwrap().clone(),
                middle: post,
                post_rest,
            });
        }
        Ok(PatternKind::Array(ArrayPattern { pre, rest, post }))
    }

    fn parse_hash_pattern_body(&mut self, _stop: &[K]) -> PResult<HashPattern> {
        let mut pairs = Vec::new();
        let mut rest = None;
        loop {
            let start = self.peek().span;
            if self.at(&T::StarStar) {
                self.bump();
                rest = Some(match self.kind().clone() {
                    T::Keyword(K::Nil) => {
                        self.bump();
                        HashPatternRest::Nil
                    }
                    T::Ident(name) => {
                        self.bump();
                        self.declare(&name);
                        HashPatternRest::Bind(name)
                    }
                    _ => return Err(self.error_expected("a name or `nil` after `**`")),
                });
            } else if let Some(key) = self.label_ahead() {
                self.bump();
                self.bump();
                let pattern = if matches!(
                    self.kind(),
                    T::Comma
                        | T::RBrace
                        | T::RParen
                        | T::Newline
                        | T::Keyword(K::Then | K::If | K::Unless)
                ) {
                    self.declare(&key);
                    None
                } else {
                    Some(self.parse_pattern()?)
                };
                let span = self.span_from(start);
                pairs.push(HashPatternPair { key, pattern, span });
            } else {
                return Err(self.error_expected("a `key:` pattern"));
            }
            if !self.at(&T::Comma) {
                break;
            }
            self.bump();
            self.skip_newlines();
            if matches!(self.kind(), T::RBrace | T::RParen) {
                break;
            }
        }
        Ok(HashPattern { pairs, rest })
    }

    // ----- types -----------------------------------------------------------

    pub fn parse_type(&mut self) -> PResult<TypeExpr> {
        let start = self.peek().span;
        let mut members = vec![self.parse_type_postfix()?];
        while self.at(&T::Pipe) {
            self.bump();
            self.skip_newlines();
            members.push(self.parse_type_postfix()?);
        }
        if members.len() == 1 {
            return Ok(members.pop().unwrap());
        }
        let span = self.span_from(start);
        Ok(TypeExpr {
            span,
            kind: TypeExprKind::Union(members),
        })
    }

    fn parse_type_postfix(&mut self) -> PResult<TypeExpr> {
        let start = self.peek().span;
        let mut ty = self.parse_type_primary()?;
        // `Recv.(A) -> R`: a procedure type with a receiver.
        if self.at(&T::Dot)
            && !self.peek().space_before
            && matches!(self.peek_at(1).kind, T::LParen)
            && matches!(ty.kind, TypeExprKind::Named { .. } | TypeExprKind::SelfType)
        {
            self.bump();
            self.expect(&T::LParen, "`(`")?;
            let mut items = Vec::new();
            loop {
                self.skip_newlines();
                if self.at(&T::RParen) {
                    break;
                }
                items.push(self.parse_type()?);
                self.skip_newlines();
                if !self.eat(&T::Comma) {
                    break;
                }
            }
            self.expect(&T::RParen, "`)`")?;
            self.expect(&T::Arrow, "`->`")?;
            let ret = self.parse_type_postfix()?;
            let span = self.span_from(start);
            ty = TypeExpr {
                span,
                kind: TypeExprKind::Proc {
                    recv: Some(Box::new(ty)),
                    params: items,
                    ret: Box::new(ret),
                    shareable: false,
                },
            };
        }
        while self.at(&T::Question) && !self.peek().space_before {
            self.bump();
            let span = self.span_from(start);
            ty = TypeExpr {
                span,
                kind: TypeExprKind::Nilable(Box::new(ty)),
            };
        }
        Ok(ty)
    }

    fn parse_type_primary(&mut self) -> PResult<TypeExpr> {
        let start = self.peek().span;
        match self.kind().clone() {
            // `shareable (A) -> R`, `shareable Recv.(A) -> R`.
            T::Ident(word) if word == "shareable" => {
                self.bump();
                let mut ty = self.parse_type_postfix()?;
                match &mut ty.kind {
                    TypeExprKind::Proc { shareable, .. } => *shareable = true,
                    _ => {
                        return Err(
                            self.error_at("`shareable` applies to a procedure type", ty.span)
                        )
                    }
                }
                ty.span = self.span_from(start);
                Ok(ty)
            }
            T::Const(_) | T::ColonColon | T::Keyword(K::Cog) => {
                let path = self.parse_const_path()?;
                let args = if self.at(&T::LBracket) && !self.peek().space_before {
                    self.parse_type_args()?
                } else {
                    vec![]
                };
                let span = self.span_from(start);
                // `Self`: the receiver's class (where a method hands a
                // value out; see 02-types).
                if path.names.len() == 1 && path.names[0] == "Self" && args.is_empty() {
                    return Ok(TypeExpr {
                        span,
                        kind: TypeExprKind::SelfType,
                    });
                }
                if path.names.len() == 1 && path.names[0] == "Nothing" && args.is_empty() {
                    return Ok(TypeExpr {
                        span,
                        kind: TypeExprKind::Nothing,
                    });
                }
                Ok(TypeExpr {
                    span,
                    kind: TypeExprKind::Named { path, args },
                })
            }
            T::LBracket => {
                self.bump();
                let mut items = Vec::new();
                loop {
                    self.skip_newlines();
                    if self.at(&T::RBracket) {
                        break;
                    }
                    items.push(self.parse_type()?);
                    self.skip_newlines();
                    if !self.eat(&T::Comma) {
                        break;
                    }
                }
                self.expect(&T::RBracket, "`]`")?;
                let span = self.span_from(start);
                Ok(TypeExpr {
                    span,
                    kind: TypeExprKind::Tuple(items),
                })
            }
            T::LParen => {
                self.bump();
                let mut items = Vec::new();
                loop {
                    self.skip_newlines();
                    if self.at(&T::RParen) {
                        break;
                    }
                    items.push(self.parse_type()?);
                    self.skip_newlines();
                    if !self.eat(&T::Comma) {
                        break;
                    }
                }
                self.expect(&T::RParen, "`)`")?;
                if self.at(&T::Arrow) {
                    self.bump();
                    let ret = self.parse_type_postfix()?;
                    let span = self.span_from(start);
                    return Ok(TypeExpr {
                        span,
                        kind: TypeExprKind::Proc {
                            recv: None,
                            params: items,
                            ret: Box::new(ret),
                            shareable: false,
                        },
                    });
                }
                if items.len() == 1 {
                    return Ok(items.pop().unwrap());
                }
                let span = self.span_from(start);
                Err(self.error_at("expected `->` after the parameter types", span))
            }
            _ => Err(self.error_expected("a type")),
        }
    }

    fn parse_type_args(&mut self) -> PResult<Vec<TypeExpr>> {
        self.expect(&T::LBracket, "`[`")?;
        let mut args = Vec::new();
        loop {
            self.skip_newlines();
            if self.at(&T::RBracket) {
                break;
            }
            args.push(self.parse_type()?);
            self.skip_newlines();
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.expect(&T::RBracket, "`]`")?;
        Ok(args)
    }

    fn parse_type_params_opt(&mut self) -> PResult<Vec<TypeParam>> {
        if !(self.at(&T::LBracket) && !self.peek().space_before) {
            return Ok(vec![]);
        }
        self.bump();
        let mut params = Vec::new();
        loop {
            self.skip_newlines();
            if self.at(&T::RBracket) {
                break;
            }
            params.push(self.parse_type_param()?);
            self.skip_newlines();
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.expect(&T::RBracket, "`]`")?;
        Ok(params)
    }

    fn parse_type_param(&mut self) -> PResult<TypeParam> {
        let start = self.peek().span;
        let variance = match self.kind().clone() {
            T::Ident(v) if v == "out" => {
                self.bump();
                Variance::Covariant
            }
            T::Keyword(K::In) => {
                self.bump();
                Variance::Contravariant
            }
            _ => Variance::Invariant,
        };
        let name = match self.kind().clone() {
            T::Const(name) => {
                self.bump();
                name
            }
            _ => return Err(self.error_expected("a type parameter name")),
        };
        let mut bounds = Vec::new();
        if self.at(&T::Colon) {
            self.bump();
            bounds.push(self.parse_type_postfix()?);
            while self.eat(&T::Amp) {
                bounds.push(self.parse_type_postfix()?);
            }
        }
        let span = self.span_from(start);
        Ok(TypeParam {
            name,
            variance,
            bounds,
            span,
        })
    }

    // ----- declarations ----------------------------------------------------

    fn parse_class(&mut self, is_abstract: bool) -> PResult<Expr> {
        let start = self.expect_kw(K::Class)?.span;
        let name = self.parse_const_path()?;
        let type_params = self.parse_type_params_opt()?;
        let superclass = if self.eat(&T::Lt) {
            Some(self.parse_type()?)
        } else {
            None
        };
        self.push_scope(true);
        let body = self.parse_statements(&[K::End]);
        self.pop_scope();
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::ClassDef(Box::new(ClassDef {
                name,
                type_params,
                superclass,
                body,
                is_abstract,
            })),
        ))
    }

    fn parse_module(&mut self) -> PResult<Expr> {
        let start = self.expect_kw(K::Module)?.span;
        let name = self.parse_const_path()?;
        let type_params = self.parse_type_params_opt()?;
        self.push_scope(true);
        let body = self.parse_statements(&[K::End]);
        self.pop_scope();
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::ModuleDef(Box::new(ModuleDef {
                name,
                type_params,
                body,
            })),
        ))
    }

    fn parse_data(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // data
        let name = match self.bump().kind {
            T::Const(name) => name,
            _ => unreachable!(),
        };
        let type_params = self.parse_type_params_opt()?;
        // `data Name = (fields)`: no body and no `end`, like `enum Name =
        // A | B`; `data Name(fields)` opens a body closed by `end`.
        let one_line = self.eat(&T::Assign);
        self.expect(&T::LParen, "`(`")?;
        let fields = self.parse_field_list(&T::RParen)?;
        self.expect(&T::RParen, "`)`")?;
        let body = if one_line {
            if !matches!(self.kind(), T::Newline | T::Eof)
                && !self.at_kw(K::End)
                && !self.at(&T::RBrace)
            {
                return Err(self.error_expected("end of line after the fields"));
            }
            vec![]
        } else {
            if self.at_kw(K::Do) {
                let span = self.peek().span;
                return Err(self.error_at(
                    "the body of a data type starts on the next line, without `do`",
                    span,
                ));
            }
            self.push_scope(true);
            let body = self.parse_statements(&[K::End]);
            self.pop_scope();
            if self.at(&T::Eof) {
                // Most likely a forgotten `=`: the rest of the file was
                // taken for the body.
                return Err(self.error_at(
                    format!(
                        "`data {name}` has no `end`; a data type without a body is written `data {name} = (...)`"
                    ),
                    start,
                ));
            }
            self.expect_kw(K::End)?;
            body
        };
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::DataDef(Box::new(DataDef {
                name,
                type_params,
                fields,
                body,
            })),
        ))
    }

    /// `name: Type [= default], ...` for `data` and `enum` variants.
    fn parse_field_list(&mut self, close: &T) -> PResult<Vec<FieldDecl>> {
        let mut fields = Vec::new();
        loop {
            self.skip_newlines();
            if self.at(close) {
                break;
            }
            let start = self.peek().span;
            let name = match self.kind().clone() {
                T::Ident(name) => {
                    self.bump();
                    name
                }
                _ => return Err(self.error_expected("a field name")),
            };
            self.expect(&T::Colon, "`:`")?;
            let ty = self.parse_type()?;
            let default = if self.eat(&T::Assign) {
                Some(self.parse_expr()?)
            } else {
                None
            };
            let span = self.span_from(start);
            fields.push(FieldDecl {
                name,
                ty,
                mutable: false,
                default,
                span,
            });
            self.skip_newlines();
            if !self.eat(&T::Comma) {
                break;
            }
        }
        Ok(fields)
    }

    fn parse_variant(&mut self) -> PResult<Variant> {
        let vstart = self.peek().span;
        let name = match self.bump().kind {
            T::Const(name) => name,
            _ => return Err(self.error_expected("a variant name")),
        };
        let fields = if self.at(&T::LParen) && !self.peek().space_before {
            self.bump();
            let fields = self.parse_field_list(&T::RParen)?;
            self.expect(&T::RParen, "`)`")?;
            fields
        } else {
            vec![]
        };
        let span = self.span_from(vstart);
        Ok(Variant { name, fields, span })
    }

    /// `A | B(x: Int) | C` after `enum Name =`. A line that ends with `|`
    /// continues on the next, as after a binary operator.
    fn parse_variants(&mut self) -> PResult<Vec<Variant>> {
        let mut variants = Vec::new();
        if !matches!(self.kind(), T::Const(_)) {
            return Ok(variants);
        }
        loop {
            variants.push(self.parse_variant()?);
            if !self.eat(&T::Pipe) {
                break;
            }
            self.skip_newlines();
        }
        Ok(variants)
    }

    /// `variant A, B(x: Int)` in the body of an enum.
    fn at_variant_decl(&mut self) -> bool {
        matches!(self.kind(), T::Ident(name) if name == "variant")
            && matches!(self.kind_at(1), T::Const(_))
    }

    /// `enum Name = A | B(x: Int)` (no body), or `enum Name` followed by a
    /// body of declarations closed by `end`, where `variant A, B(x: Int)`
    /// declares variants, like `def` declares methods.
    fn parse_enum(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // enum
        let name = match self.bump().kind {
            T::Const(name) => name,
            _ => unreachable!(),
        };
        let type_params = self.parse_type_params_opt()?;
        self.push_scope(true);
        let mut body = Vec::new();
        let variants = if self.eat(&T::Assign) {
            // The one-line form: variants only, no `end`.
            let variants = self.parse_variants()?;
            self.pop_scope();
            if variants.is_empty() {
                self.error_expected("a variant after `=`");
            } else if !matches!(self.kind(), T::Newline | T::Eof) {
                self.error_expected("end of line after the variants");
                self.recover(&[K::End]);
            }
            let span = self.span_from(start);
            return Ok(self.node(
                span,
                ExprKind::EnumDef(Box::new(EnumDef {
                    name,
                    type_params,
                    variants,
                    body,
                })),
            ));
        } else {
            let mut variants = Vec::new();
            loop {
                self.skip_newlines();
                if self.at_kw(K::End) || self.at(&T::Eof) {
                    break;
                }
                let decl = if self.at_variant_decl() {
                    self.bump(); // variant
                    while let Ok(v) = self.parse_variant() {
                        variants.push(v);
                        if !self.eat(&T::Comma) {
                            break;
                        }
                        self.skip_newlines();
                    }
                    Ok(())
                } else {
                    self.parse_statement().map(|stmt| body.push(stmt))
                };
                match decl {
                    Ok(()) => {
                        if !matches!(self.kind(), T::Newline | T::Eof | T::Keyword(K::End)) {
                            self.error_expected("end of line");
                            self.recover(&[K::End]);
                        }
                    }
                    Err(_) => self.recover(&[K::End]),
                }
            }
            variants
        };
        self.pop_scope();
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::EnumDef(Box::new(EnumDef {
                name,
                type_params,
                variants,
                body,
            })),
        ))
    }

    fn parse_extension(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // extension
        let tstart = self.peek().span;
        let path = self.parse_const_path()?;
        // `extension Array[T: Describable]`: the bracket declares type
        // parameters with bounds, which also serve as the target's arguments.
        let type_params = self.parse_type_params_opt()?;
        let args = type_params
            .iter()
            .map(|p| TypeExpr {
                span: p.span,
                kind: TypeExprKind::Named {
                    path: ConstPath::simple(p.name.clone()),
                    args: vec![],
                },
            })
            .collect();
        let tspan = self.span_from(tstart);
        let target = TypeExpr {
            span: tspan,
            kind: TypeExprKind::Named { path, args },
        };
        self.push_scope(true);
        let body = self.parse_statements(&[K::End]);
        self.pop_scope();
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::ExtensionDef(Box::new(ExtensionDef {
                target,
                type_params,
                body,
            })),
        ))
    }

    fn parse_type_alias(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // type
        let name = match self.bump().kind {
            T::Const(name) => name,
            _ => unreachable!(),
        };
        let type_params = self.parse_type_params_opt()?;
        self.expect(&T::Assign, "`=`")?;
        let ty = self.parse_type()?;
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::TypeAlias {
                name,
                type_params,
                ty,
            },
        ))
    }

    fn parse_extern(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // extern
        let abi = self.parse_plain_string()?;
        let mut decls = Vec::new();
        loop {
            self.skip_newlines();
            if self.at_kw(K::End) || self.at(&T::Eof) {
                break;
            }
            match self.parse_def(None, false, false, true)? {
                Expr {
                    kind: ExprKind::MethodDef(def),
                    ..
                } => decls.push(*def),
                _ => unreachable!(),
            }
        }
        self.expect_kw(K::End)?;
        let span = self.span_from(start);
        Ok(self.node(span, ExprKind::Extern { abi, decls }))
    }

    fn parse_def(
        &mut self,
        visibility: Option<Visibility>,
        is_abstract: bool,
        is_override: bool,
        is_native: bool,
    ) -> PResult<Expr> {
        let start = self.expect_kw(K::Def)?.span;
        let mut singleton = false;
        if self.at_kw(K::SelfKw) && matches!(self.kind_at(1), T::Dot) {
            self.bump();
            self.bump();
            singleton = true;
        }
        let name = self.parse_def_name()?;
        let type_params = self.parse_type_params_opt()?;
        self.push_scope(true);
        let params = if self.at(&T::LParen) {
            self.bump();
            let params = self.parse_param_list(&T::RParen)?;
            self.expect(&T::RParen, "`)`")?;
            params
        } else if matches!(
            self.kind(),
            T::Ident(_) | T::Star | T::StarStar | T::Amp | T::IVar(_)
        ) && self.peek().space_before
        {
            self.parse_param_list_bare()?
        } else {
            Params::empty()
        };
        let ret = if self.at(&T::Arrow) {
            self.bump();
            Some(self.parse_type()?)
        } else {
            None
        };
        let body = if is_abstract || is_native {
            if !matches!(self.kind(), T::Newline | T::Eof | T::Keyword(K::End)) {
                self.error_expected("end of line (abstract and native methods have no body)");
            }
            None
        } else if self.at(&T::Assign) {
            self.bump();
            self.skip_newlines();
            let expr = self.parse_statement()?;
            Some(vec![expr])
        } else {
            let body = self.parse_body_with_rescue(&[K::End])?;
            self.expect_kw(K::End)?;
            Some(body)
        };
        self.pop_scope();
        let span = self.span_from(start);
        Ok(self.node(
            span,
            ExprKind::MethodDef(Box::new(MethodDef {
                name,
                singleton,
                type_params,
                params,
                ret,
                body,
                is_abstract,
                is_override,
                is_native,
                visibility,
                span,
            })),
        ))
    }

    fn parse_def_name(&mut self) -> PResult<String> {
        let tok = self.bump();
        let mut name = match tok.kind {
            // Unary `!` and `~` are called as `!x`/`~x` whatever the
            // definition is spelled; `-@`/`+@` keep the `@`, as in Ruby.
            T::Ident(name) if name == "!@" || name == "~@" => name[..1].to_string(),
            T::Ident(name) | T::Const(name) => name,
            T::Keyword(k) => k.as_str().to_string(),
            T::LBracket => {
                self.expect(&T::RBracket, "`]`")?;
                if self.at(&T::Assign) && !self.peek().space_before {
                    self.bump();
                    return Ok("[]=".to_string());
                }
                if self.at(&T::Question) && !self.peek().space_before {
                    self.bump();
                    return Ok("[]?".to_string());
                }
                return Ok("[]".to_string());
            }
            other => match operator_method_name(&other) {
                Some(s) => s.to_string(),
                None => {
                    return Err(self.error_at(
                        format!("expected a method name, found {}", describe(&other)),
                        tok.span,
                    ))
                }
            },
        };
        // Setter: `def name=(value)`.
        if self.at(&T::Assign) && !self.peek().space_before && matches!(self.kind_at(1), T::LParen)
        {
            self.bump();
            name.push('=');
        }
        Ok(name)
    }

    /// Parameters up to (not including) `close`.
    fn parse_param_list(&mut self, close: &T) -> PResult<Params> {
        let mut list = Vec::new();
        let mut keyword_only = false;
        loop {
            self.skip_newlines();
            if self.at(close) {
                break;
            }
            if let Some(param) = self.parse_param(&mut keyword_only)? {
                list.push(param);
            }
            self.skip_newlines();
            if !self.eat(&T::Comma) {
                break;
            }
        }
        Ok(Params { list })
    }

    /// Parameters without parentheses (`def foo a, b` / `-> x { }`).
    fn parse_param_list_bare(&mut self) -> PResult<Params> {
        let mut list = Vec::new();
        let mut keyword_only = false;
        loop {
            if let Some(param) = self.parse_param(&mut keyword_only)? {
                list.push(param);
            }
            if !self.eat(&T::Comma) {
                break;
            }
        }
        Ok(Params { list })
    }

    fn parse_param(&mut self, keyword_only: &mut bool) -> PResult<Option<Param>> {
        let start = self.peek().span;
        let (kind, name, assigns_ivar) = match self.kind().clone() {
            T::Star => {
                self.bump();
                // Parameters after `*rest` or a bare `*` are keyword-only.
                *keyword_only = true;
                match self.kind().clone() {
                    T::Ident(name) => {
                        self.bump();
                        (ParamKind::Rest, name, false)
                    }
                    _ => return Ok(None),
                }
            }
            T::StarStar => {
                self.bump();
                match self.kind().clone() {
                    T::Ident(name) => {
                        self.bump();
                        (ParamKind::KeywordRest, name, false)
                    }
                    _ => return Err(self.error_expected("a name after `**`")),
                }
            }
            T::Amp => {
                self.bump();
                match self.kind().clone() {
                    T::Ident(name) => {
                        self.bump();
                        (ParamKind::Block, name, false)
                    }
                    // `&: (Int) -> Nil`: an anonymous block, used with
                    // `yield` or forwarded as `f(&)`.
                    T::Colon => (ParamKind::Block, "&".to_string(), false),
                    _ => return Err(self.error_expected("a name or `:` after `&`")),
                }
            }
            T::IVar(name) => {
                self.bump();
                let kind = if *keyword_only {
                    ParamKind::KeywordOnly
                } else {
                    ParamKind::Positional
                };
                (kind, name, true)
            }
            T::Ident(name) => {
                self.bump();
                let kind = if *keyword_only {
                    ParamKind::KeywordOnly
                } else {
                    ParamKind::Positional
                };
                (kind, name, false)
            }
            T::LParen => {
                // Destructuring block parameters `|(a, b), c|` are not
                // supported; use a pattern inside the block instead.
                let tok = self.peek().clone();
                return Err(self.error_at(
                    "destructuring parameters are not supported; use `=> [a, b]` in the body",
                    tok.span,
                ));
            }
            _ => return Err(self.error_expected("a parameter")),
        };
        self.declare(&name);
        let ty = if self.at(&T::Colon) {
            self.bump();
            Some(self.parse_type()?)
        } else {
            None
        };
        let default = if self.at(&T::Assign) {
            self.bump();
            Some(self.parse_ternary()?)
        } else {
            None
        };
        // `&: (A) -> R using M, N`: the block literal is checked with
        // these modules' extensions active.
        let mut usings = Vec::new();
        if kind == ParamKind::Block && matches!(self.kind(), T::Ident(n) if n == "using") {
            self.bump();
            loop {
                usings.push(self.parse_const_path()?);
                if !self.eat(&T::Comma) {
                    break;
                }
            }
        }
        let span = self.span_from(start);
        Ok(Some(Param {
            name,
            kind,
            ty,
            default,
            assigns_ivar,
            usings,
            span,
        }))
    }
}

/// One `name in source [when guard]` of a `for`.
struct ForIterator {
    names: Vec<(String, Span)>,
    source: Expr,
    guard: Option<Expr>,
    span: Span,
}

enum BinOp {
    And,
    Or,
    Method(&'static str),
}

/// Binary operator precedence (higher binds tighter) and the method it
/// calls.
fn binary_op(kind: &T) -> Option<(u8, BinOp)> {
    Some(match kind {
        T::OrOr => (1, BinOp::Or),
        T::AndAnd => (2, BinOp::And),
        T::Cmp => (3, BinOp::Method("<=>")),
        T::Eq => (3, BinOp::Method("==")),
        T::Eqq => (3, BinOp::Method("===")),
        T::NotEq => (3, BinOp::Method("!=")),
        T::Match => (3, BinOp::Method("=~")),
        T::NotMatch => (3, BinOp::Method("!~")),
        T::Lt => (4, BinOp::Method("<")),
        T::LtEq => (4, BinOp::Method("<=")),
        T::Gt => (4, BinOp::Method(">")),
        T::GtEq => (4, BinOp::Method(">=")),
        T::Pipe => (5, BinOp::Method("|")),
        T::Caret => (5, BinOp::Method("^")),
        T::Amp => (6, BinOp::Method("&")),
        T::Shl => (7, BinOp::Method("<<")),
        T::Shr => (7, BinOp::Method(">>")),
        T::Plus => (8, BinOp::Method("+")),
        T::Minus => (8, BinOp::Method("-")),
        T::Star => (9, BinOp::Method("*")),
        T::Slash => (9, BinOp::Method("/")),
        T::Percent => (9, BinOp::Method("%")),
        _ => return None,
    })
}

fn operator_method_name(kind: &T) -> Option<&'static str> {
    Some(match kind {
        T::AndAnd => "&&",
        T::OrOr => "||",
        T::Plus => "+",
        T::Minus => "-",
        T::Star => "*",
        T::StarStar => "**",
        T::Slash => "/",
        T::Percent => "%",
        T::Eq => "==",
        T::Eqq => "===",
        T::NotEq => "!=",
        T::Lt => "<",
        T::LtEq => "<=",
        T::Gt => ">",
        T::GtEq => ">=",
        T::Cmp => "<=>",
        T::Match => "=~",
        T::NotMatch => "!~",
        T::Shl => "<<",
        T::Shr => ">>",
        T::Amp => "&",
        T::Pipe => "|",
        T::Caret => "^",
        T::Tilde => "~",
        T::Bang => "!",
        _ => return None,
    })
}

fn visibility_of(name: &str) -> Visibility {
    match name {
        "private" => Visibility::Private,
        "protected" => Visibility::Protected,
        _ => Visibility::Public,
    }
}

fn negate_literal(expr: &Expr) -> Option<ExprKind> {
    match &expr.kind {
        ExprKind::Int(lit) => Some(ExprKind::Int(IntLit::new(
            match lit.digits.strip_prefix('-') {
                Some(positive) => positive.to_string(),
                None => format!("-{}", lit.digits),
            },
            lit.base,
        ))),
        ExprKind::Float(f) => Some(ExprKind::Float(-f)),
        _ => None,
    }
}
