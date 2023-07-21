use crate::uniform_term::token_stream::TokenStream;

use super::{tokeniser::Token, LevelExpr, ParseLevelError};

pub(super) fn parse(ts: &mut TokenStream<Token>) -> Result<LevelExpr, ParseLevelError> {
    let level = parse_incr(ts)?;
    
    // Return an error if there are any tokens left over.
    if ts.peek().is_some() {
        return Err(ParseLevelError);
    }

    Ok(level)
}

fn parse_incr(ts: &mut TokenStream<Token>) -> Result<LevelExpr, ParseLevelError> {
    let mut level = parse_base(ts)?;

    loop {
        match ts.peek() {
            Some(Token::Num(n)) => {
                let n = *n;
                ts.consume();
                level = LevelExpr::Incr(Box::new(level), n);
            },
            
            Some(Token::Prime) => {
                ts.consume();
                level = LevelExpr::Incr(Box::new(level), 1);
            },
            
            _ => break,
        }
    }

    Ok(level)
}

fn parse_base(ts: &mut TokenStream<Token>) -> Result<LevelExpr, ParseLevelError> {
    match ts.consume().ok_or(ParseLevelError)? {
        // Parenthesised level expression `(L)`
        Token::LParen => {
            let level = parse_incr(ts)?;
            ts.consume_if(|tok| matches!(tok, Token::RParen)).ok_or(ParseLevelError)?;
            Ok(level)
        },

        // Maximum of levels `[L | ... | L]`
        Token::LBracket => {
            let mut levels = Vec::new();
            loop {
                let level = parse_incr(ts)?;
                levels.push(level);
                match ts.consume() {
                    // If the token is a bar `|`, then we have more levels to parse.
                    Some(Token::Bar) => (),
                    // If the token is a right bracket `]`, we are done parsing levels.
                    Some(Token::RBracket) => break,
                    _ => return Err(ParseLevelError),
                }
            }
            Ok(LevelExpr::Max(levels.into_boxed_slice()))
        },
        
        // Level variable
        Token::String(s) => {
            Ok(LevelExpr::Var(s))
        },
        
        // Level constant
        Token::Num(n) => {
            Ok(LevelExpr::Const(n))
        },
        
        _ => Err(ParseLevelError),
    }
}
