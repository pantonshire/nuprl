use std::collections::VecDeque;

use super::{tokeniser::Token, Term, ParseTermError, Param, LevelExpr, token_stream::TokenStream};

pub(super) fn parse(tokens: VecDeque<Token>) -> Result<Term, ParseTermError> {
    let mut ts = TokenStream::new(tokens);
    parse_term(&mut ts)
}

fn parse_term(ts: &mut TokenStream<Token>) -> Result<Term, ParseTermError> {
    ts.consume_if(|tok| matches!(tok, Token::LBrace)).ok_or(ParseTermError)?;
    let params = parse_params(ts)?;
    ts.consume_if(|tok| matches!(tok, Token::RBrace)).ok_or(ParseTermError)?;
    
    ts.consume_if(|tok| matches!(tok, Token::LParen)).ok_or(ParseTermError)?;
    let subterms = parse_subterms(ts)?;
    ts.consume_if(|tok| matches!(tok, Token::RParen)).ok_or(ParseTermError)?;
    
    Ok(Term { params, subterms })
}

fn parse_subterms(ts: &mut TokenStream<Token>) -> Result<Box<[Term]>, ParseTermError> {
    if matches!(ts.peek(), Some(Token::RParen)) {
        Ok(Box::default())
    } else {
        let mut subterms = Vec::new();

        subterms.push(parse_term(ts)?);

        while ts.consume_if(|tok| matches!(tok, Token::Semicolon)).is_some() {
            subterms.push(parse_term(ts)?);
        }

        Ok(subterms.into_boxed_slice())
    }
}

fn parse_params(ts: &mut TokenStream<Token>) -> Result<Box<[Param]>, ParseTermError> {
    if matches!(ts.peek(), Some(Token::String(_) | Token::Colon)) {
        let mut params = Vec::new();
        
        params.push(parse_param(ts)?);
        
        while ts.consume_if(|tok| matches!(tok, Token::Comma)).is_some() {
            params.push(parse_param(ts)?);
        }

        Ok(params.into_boxed_slice())
    } else {
        Ok(Box::default())
    }
}

fn parse_param(ts: &mut TokenStream<Token>) -> Result<Param, ParseTermError> {
    let val = match ts.consume_if(|tok| matches!(tok, Token::Colon)) {
        // If just a colon was provided with no string before it, the parameter value is an empty
        // string.
        Some(_) => Box::default(),
        
        None => {
            // If the next token wasn't a colon, expect a string parameter value.
            let Token::String(val) = ts.consume().ok_or(ParseTermError)? else {
                return Err(ParseTermError)
            };

            // Expect a colon separating the parameter value from the parameter kind.
            ts.consume_if(|tok| matches!(tok, Token::Colon)).ok_or(ParseTermError)?;
            
            val
        }
    };

    let Token::String(kind) = ts.consume().ok_or(ParseTermError)? else {
        return Err(ParseTermError)
    };

    match kind.as_ref() {
        "OPID" => Ok(Param::Opid(val)),
        "t" => Ok(Param::Tok(val)),
        // FIXME: arbitrary precision
        "n" => match val.parse::<u64>() {
            Ok(val) => Ok(Param::Nat(val)),
            Err(_) => Ok(Param::Other { val, kind }),
        },
        "v" => Ok(Param::Var(val)),
        "l" => {
            val.parse::<LevelExpr>()
                .map(Param::Level)
                .map_err(|_| ParseTermError)
        },
        "o" => Ok(Param::Obj(val)),
        "b" => match val.as_ref() {
            "T" => Ok(Param::Bool(true)),
            "F" => Ok(Param::Bool(false)),
            _ => Ok(Param::Other { val, kind }) 
        },
        _ => Ok(Param::Other { val, kind }),
    }
}
