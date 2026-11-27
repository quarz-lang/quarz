//! `init_symbol!("zlib-ng")`: the name of a cog's init function as a
//! string literal (`"qz_cog_init_zlib_hng"`), for `quarz_ext::module!`'s
//! `export_name`. The encoding is `quarz_ext::sys::init_symbol`'s: each
//! `_` as `__`, each `-` as `_h`.

use proc_macro::{Literal, TokenStream, TokenTree};

#[proc_macro]
pub fn init_symbol(input: TokenStream) -> TokenStream {
    // (A literal `macro_rules!` passes on comes in an invisible group.)
    let mut tokens = input.into_iter();
    let mut first = tokens.next();
    while let Some(TokenTree::Group(g)) = &first {
        if g.delimiter() != proc_macro::Delimiter::None {
            break;
        }
        let mut inner = g.stream().into_iter();
        first = inner.next();
    }
    let (Some(TokenTree::Literal(lit)), None) = (first, tokens.next()) else {
        return error("init_symbol! takes the cog's name, a string literal");
    };
    let text = lit.to_string();
    let Some(name) = text.strip_prefix('"').and_then(|t| t.strip_suffix('"')) else {
        return error("init_symbol! takes the cog's name, a string literal");
    };
    let legal = name.starts_with(|c: char| c.is_ascii_lowercase())
        && name
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-' || c == '_');
    if !legal {
        return error(
            "a cog's name is a lowercase letter, then lowercase letters, digits, `-` and `_`",
        );
    }
    let mut symbol = String::from("qz_cog_init_");
    for c in name.chars() {
        match c {
            '_' => symbol.push_str("__"),
            '-' => symbol.push_str("_h"),
            c => symbol.push(c),
        }
    }
    TokenTree::Literal(Literal::string(&symbol)).into()
}

fn error(message: &str) -> TokenStream {
    format!("compile_error!({message:?})")
        .parse()
        .expect("tokens")
}
