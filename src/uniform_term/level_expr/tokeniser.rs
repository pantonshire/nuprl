use std::{collections::VecDeque, mem};

pub(super) enum Token {
    LParen,
    RParen,
    LBracket,
    RBracket,
    Bar,
    Prime,
    Num(u64),
    String(Box<str>),
}

pub(super) fn tokenise(input: &str) -> VecDeque<Token> {
    let mut tokens = VecDeque::new();
    let mut buf = String::new();
    let mut is_num = false;

    for c in input.chars() {
        let (token, ws) = match c {
            '(' => (Some(Token::LParen), false),
            ')' => (Some(Token::RParen), false),
            '[' => (Some(Token::LBracket), false),
            ']' => (Some(Token::RBracket), false),
            '|' => (Some(Token::Bar), false),
            '\'' => (Some(Token::Prime), false),
            c if c.is_whitespace() => (None, true),
            _ => (None, false),
        };

        if token.is_some() || ws {
            if !buf.is_empty() {
                tokens.push_back(buf_to_token(mem::take(&mut buf), is_num));
            }

            if let Some(token) = token {
                tokens.push_back(token);
            }
        } else {
            if buf.is_empty() {
                is_num = c.is_ascii_digit();
            }
            // FIXME: if `is_num` is true, check if `c` is a valid digit before pushing it.
            buf.push(c);
        }
    }

    if !buf.is_empty() {
        tokens.push_back(buf_to_token(buf, is_num));
    }

    tokens
}

fn buf_to_token(buf: String, is_num: bool) -> Token {
    if is_num {
        Token::Num(buf.parse::<u64>().unwrap())
    } else {
        Token::String(buf.into_boxed_str())
    }
}
