use std::{mem, collections::VecDeque};

#[derive(Debug)]
pub(super) enum Token {
    LBrace,
    RBrace,
    LParen,
    RParen,
    Colon,
    Comma,
    Semicolon,
    String(Box<str>),
}

pub(super) fn tokenise(input: &str) -> VecDeque<Token> {
    let mut tokens = VecDeque::new();
    let mut current_string = String::new();
    let mut escape = false;

    for c in input.chars() {
        let (token, skip_char, escape_char) = if escape {
            escape = false;
            (None, false, true)
        } else {
            match c {
                '\\' => {
                    escape = true;
                    (None, true, false)
                },
                '{' => (Some(Token::LBrace), false, false),
                '}' => (Some(Token::RBrace), false, false),
                '(' => (Some(Token::LParen), false, false),
                ')' => (Some(Token::RParen), false, false),
                ':' => (Some(Token::Colon), false, false),
                ',' => (Some(Token::Comma), false, false),
                ';' => (Some(Token::Semicolon), false, false),
                c if c.is_whitespace() => (None, true, false),
                _ => (None, false, false),
            }
        };

        if let Some(token) = token {
            if !current_string.is_empty() {
                tokens.push_back(Token::String(mem::take(&mut current_string).into_boxed_str()));
            }
            tokens.push_back(token);
        } else if token.is_none() && !skip_char {
            let c = if escape_char {
                match c {
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    _ => c,
                }
            } else {
                c
            };
            current_string.push(c);
        }
    }

    if !current_string.is_empty() {
        tokens.push_back(Token::String(current_string.into_boxed_str()));
    }

    tokens
}
