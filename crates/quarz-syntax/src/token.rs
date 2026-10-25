//! Tokens produced by the lexer.

use crate::source::Span;
use std::fmt;

/// Reserved words. Contextual keywords (`data`, `enum`, `var`, `abstract`,
/// `extension`, `using`, `type`, `extern`, `out`) are lexed as
/// identifiers and recognized by the parser.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Keyword {
    Alias,
    And,
    Begin,
    Break,
    Case,
    Class,
    /// The current cog's root module (`cog::Foo`, `cog.name`).
    Cog,
    Def,
    Do,
    Else,
    Elsif,
    End,
    Ensure,
    False,
    If,
    In,
    Module,
    Next,
    Nil,
    Not,
    Or,
    Rescue,
    Retry,
    Return,
    SelfKw,
    Super,
    Then,
    True,
    Unless,
    Until,
    When,
    While,
    Yield,
    /// `__FILE__`
    File,
    /// `__LINE__`
    Line,
    /// `__method__`
    Method,
}

impl Keyword {
    /// Every keyword (for completion).
    pub const ALL: &[Keyword] = &[
        Keyword::Alias,
        Keyword::And,
        Keyword::Begin,
        Keyword::Break,
        Keyword::Case,
        Keyword::Class,
        Keyword::Cog,
        Keyword::Def,
        Keyword::Do,
        Keyword::Else,
        Keyword::Elsif,
        Keyword::End,
        Keyword::Ensure,
        Keyword::False,
        Keyword::If,
        Keyword::In,
        Keyword::Module,
        Keyword::Next,
        Keyword::Nil,
        Keyword::Not,
        Keyword::Or,
        Keyword::Rescue,
        Keyword::Retry,
        Keyword::Return,
        Keyword::SelfKw,
        Keyword::Super,
        Keyword::Then,
        Keyword::True,
        Keyword::Unless,
        Keyword::Until,
        Keyword::When,
        Keyword::While,
        Keyword::Yield,
        Keyword::File,
        Keyword::Line,
        Keyword::Method,
    ];

    pub fn from_ident(s: &str) -> Option<Keyword> {
        use Keyword::*;
        Some(match s {
            "alias" => Alias,
            "and" => And,
            "begin" => Begin,
            "break" => Break,
            "case" => Case,
            "class" => Class,
            "cog" => Cog,
            "def" => Def,
            "do" => Do,
            "else" => Else,
            "elsif" => Elsif,
            "end" => End,
            "ensure" => Ensure,
            "false" => False,
            "if" => If,
            "in" => In,
            "module" => Module,
            "next" => Next,
            "nil" => Nil,
            "not" => Not,
            "or" => Or,
            "rescue" => Rescue,
            "retry" => Retry,
            "return" => Return,
            "self" => SelfKw,
            "super" => Super,
            "then" => Then,
            "true" => True,
            "unless" => Unless,
            "until" => Until,
            "when" => When,
            "while" => While,
            "yield" => Yield,
            "__FILE__" => File,
            "__LINE__" => Line,
            "__method__" => Method,
            _ => return None,
        })
    }

    pub fn as_str(self) -> &'static str {
        use Keyword::*;
        match self {
            Alias => "alias",
            And => "and",
            Begin => "begin",
            Break => "break",
            Case => "case",
            Class => "class",
            Cog => "cog",
            Def => "def",
            Do => "do",
            Else => "else",
            Elsif => "elsif",
            End => "end",
            Ensure => "ensure",
            False => "false",
            If => "if",
            In => "in",
            Module => "module",
            Next => "next",
            Nil => "nil",
            Not => "not",
            Or => "or",
            Rescue => "rescue",
            Retry => "retry",
            Return => "return",
            SelfKw => "self",
            Super => "super",
            Then => "then",
            True => "true",
            Unless => "unless",
            Until => "until",
            When => "when",
            While => "while",
            Yield => "yield",
            File => "__FILE__",
            Line => "__LINE__",
            Method => "__method__",
        }
    }

    /// Whether the keyword is itself a value, so that an operator after it is
    /// binary (`self / 2`) rather than the start of a literal (`if /re/`).
    pub fn is_value(self) -> bool {
        use Keyword::*;
        matches!(
            self,
            End | SelfKw | Cog | Nil | True | False | File | Line | Method
        )
    }
}

/// What kind of literal a `StringBegin`..`StringEnd` sequence builds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StringKind {
    String,
    Symbol,
    Regexp,
    /// `b"..."`: escapes are kept verbatim and decoded by the parser.
    Bytes,
}

/// The operator of a compound assignment such as `+=`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum OpAssign {
    Plus,
    Minus,
    Star,
    StarStar,
    Slash,
    Percent,
    Shl,
    Shr,
    Amp,
    Pipe,
    Caret,
    AndAnd,
    OrOr,
}

impl OpAssign {
    pub fn as_str(self) -> &'static str {
        use OpAssign::*;
        match self {
            Plus => "+=",
            Minus => "-=",
            Star => "*=",
            StarStar => "**=",
            Slash => "/=",
            Percent => "%=",
            Shl => "<<=",
            Shr => ">>=",
            Amp => "&=",
            Pipe => "|=",
            Caret => "^=",
            AndAnd => "&&=",
            OrOr => "||=",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    /// A local variable or method name, including a trailing `?` or `!`.
    Ident(String),
    /// A constant (identifier starting with an uppercase letter).
    Const(String),
    /// `@name` (without the `@`).
    IVar(String),
    /// Integer literal. `digits` has prefix and underscores removed.
    Int {
        digits: String,
        base: u8,
    },
    /// Float literal text with underscores removed.
    Float(String),
    /// `:name` or `:+` etc. Quoted symbols are lexed as
    /// `StringBegin(StringKind::Symbol)`.
    Symbol(String),

    // String-like literals are emitted as a sequence:
    //   StringBegin, (StringContent | EmbExprBegin .. EmbExprEnd)*, StringEnd
    StringBegin(StringKind),
    StringContent(String),
    /// `#{`
    EmbExprBegin,
    /// The `}` closing an interpolation.
    EmbExprEnd,
    /// Closing delimiter. `flags` is non-empty only for regexps (`/re/im`).
    StringEnd {
        flags: String,
    },
    /// `%w[...]`
    Words(Vec<String>),
    /// `%i[...]`
    Symbols(Vec<String>),

    Keyword(Keyword),

    // Operators
    Plus,
    Minus,
    Star,
    StarStar,
    Slash,
    Percent,
    /// `=`
    Assign,
    /// `==`
    Eq,
    /// `===`
    Eqq,
    /// `!=`
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    /// `<=>`
    Cmp,
    /// `=~`
    Match,
    /// `!~`
    NotMatch,
    Shl,
    Shr,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Bang,
    AndAnd,
    OrOr,
    OpAssign(OpAssign),

    // Punctuation
    Dot,
    /// `&.`
    SafeNav,
    /// `::`
    ColonColon,
    /// `.:` (method reference)
    DotColon,
    Comma,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    /// `->`
    Arrow,
    /// `=>`
    FatArrow,
    Question,
    Colon,
    DotDot,
    DotDotDot,

    /// A statement terminator: one or more newlines and/or `;`.
    Newline,
    Eof,
    /// Something the lexer could not understand. A diagnostic has been
    /// reported.
    Error,
}

impl TokenKind {
    /// Whether a token of this kind ends a value, so that a following `/`,
    /// `%` or `<<` is a binary operator rather than the start of a literal.
    pub fn ends_value(&self) -> bool {
        use TokenKind::*;
        match self {
            Ident(_)
            | Const(_)
            | IVar(_)
            | Int { .. }
            | Float(_)
            | Symbol(_)
            | StringEnd { .. }
            | Words(_)
            | Symbols(_)
            | RParen
            | RBracket
            | RBrace => true,
            Keyword(k) => k.is_value(),
            _ => false,
        }
    }

    pub fn is_eof(&self) -> bool {
        matches!(self, TokenKind::Eof)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TokenKind::*;
        match self {
            Ident(s) => write!(f, "Ident({s})"),
            Const(s) => write!(f, "Const({s})"),
            IVar(s) => write!(f, "IVar(@{s})"),
            Int { digits, base } => {
                if *base == 10 {
                    write!(f, "Int({digits})")
                } else {
                    write!(f, "Int({digits} base {base})")
                }
            }
            Float(s) => write!(f, "Float({s})"),
            Symbol(s) => write!(f, "Symbol(:{s})"),
            StringBegin(k) => write!(f, "StringBegin({k:?})"),
            StringContent(s) => write!(f, "StringContent({s:?})"),
            EmbExprBegin => write!(f, "EmbExprBegin"),
            EmbExprEnd => write!(f, "EmbExprEnd"),
            StringEnd { flags } if flags.is_empty() => write!(f, "StringEnd"),
            StringEnd { flags } => write!(f, "StringEnd({flags})"),
            Words(ws) => write!(f, "Words({ws:?})"),
            Symbols(ws) => write!(f, "Symbols({ws:?})"),
            Keyword(k) => write!(f, "Keyword({})", k.as_str()),
            OpAssign(op) => write!(f, "`{}`", op.as_str()),
            Newline => write!(f, "Newline"),
            Eof => write!(f, "Eof"),
            Error => write!(f, "Error"),
            _ => write!(f, "`{}`", self.punct_str()),
        }
    }
}

impl TokenKind {
    fn punct_str(&self) -> &'static str {
        use TokenKind::*;
        match self {
            Plus => "+",
            Minus => "-",
            Star => "*",
            StarStar => "**",
            Slash => "/",
            Percent => "%",
            Assign => "=",
            Eq => "==",
            Eqq => "===",
            NotEq => "!=",
            Lt => "<",
            LtEq => "<=",
            Gt => ">",
            GtEq => ">=",
            Cmp => "<=>",
            Match => "=~",
            NotMatch => "!~",
            Shl => "<<",
            Shr => ">>",
            Amp => "&",
            Pipe => "|",
            Caret => "^",
            Tilde => "~",
            Bang => "!",
            AndAnd => "&&",
            OrOr => "||",
            Dot => ".",
            SafeNav => "&.",
            ColonColon => "::",
            DotColon => ".:",
            Comma => ",",
            LParen => "(",
            RParen => ")",
            LBracket => "[",
            RBracket => "]",
            LBrace => "{",
            RBrace => "}",
            Arrow => "->",
            FatArrow => "=>",
            Question => "?",
            Colon => ":",
            DotDot => "..",
            DotDotDot => "...",
            _ => "?",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    /// Whether whitespace (or a newline) separated this token from the
    /// previous one. The parser uses it to disambiguate `foo -x` (a command
    /// call with a unary argument) from `foo - x` and `foo-x`.
    pub space_before: bool,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span, space_before: bool) -> Token {
        Token {
            kind,
            span,
            space_before,
        }
    }
}
