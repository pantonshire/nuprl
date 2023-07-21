mod parser;
mod tokeniser;

use std::str;

use serde::Serialize;

use super::token_stream::TokenStream;

#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
pub enum LevelExpr {
    Var(Box<str>),
    Const(u64),
    Incr(Box<LevelExpr>, u64),
    Max(Box<[LevelExpr]>),
}

impl LevelExpr {
    /// Evaluate the level expression to a constant value by taking all variables to be zero.
    pub fn evaluate_zero_vars(&self) -> u64 {
        match self {
            Self::Var(_) => 0,
            Self::Const(level) => *level,
            Self::Incr(level, increment) => level.evaluate_zero_vars() + increment,
            Self::Max(levels) => levels.iter().map(Self::evaluate_zero_vars).max().unwrap_or(0),
        }
    }
}

impl str::FromStr for LevelExpr {
    type Err = ParseLevelError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tokens = tokeniser::tokenise(s);
        parser::parse(&mut TokenStream::new(tokens))
    }
}

#[derive(Debug)]
pub struct ParseLevelError;

#[cfg(test)]
mod tests {
    use super::LevelExpr;

    #[test]
    fn test_parse() {
        assert_eq!(
            "0".parse::<LevelExpr>().unwrap(),
            LevelExpr::Const(0)
        );

        assert_eq!(
            "i".parse::<LevelExpr>().unwrap(),
            LevelExpr::Var("i".into())
        );

        assert_eq!(
            "i'".parse::<LevelExpr>().unwrap(),
            LevelExpr::Incr(
                Box::new(LevelExpr::Var("i".into())),
                1
            )
        );

        assert_eq!(
            "i 5".parse::<LevelExpr>().unwrap(),
            LevelExpr::Incr(
                Box::new(LevelExpr::Var("i".into())),
                5
            )
        );

        assert_eq!(
            "(i 2) 3".parse::<LevelExpr>().unwrap(),
            LevelExpr::Incr(
                Box::new(LevelExpr::Incr(
                    Box::new(LevelExpr::Var("i".into())),
                    2
                )),
                3
            )
        );

        assert_eq!(
            "i 2 3".parse::<LevelExpr>().unwrap(),
            LevelExpr::Incr(
                Box::new(LevelExpr::Incr(
                    Box::new(LevelExpr::Var("i".into())),
                    2
                )),
                3
            )
        );

        assert_eq!(
            "[i 4 | j]".parse::<LevelExpr>().unwrap(),
            LevelExpr::Max(vec![
                LevelExpr::Incr(
                    Box::new(LevelExpr::Var("i".into())),
                    4
                ),
                LevelExpr::Var("j".into()),
            ].into_boxed_slice())
        );
    }

    #[test]
    fn test_evaluate_zero_vars() {
        assert_eq!(
            LevelExpr::Var("x".into()).evaluate_zero_vars(),
            0
        );

        assert_eq!(
            LevelExpr::Const(1).evaluate_zero_vars(),
            1
        );

        assert_eq!(
            LevelExpr::Incr(
                Box::new(LevelExpr::Var("x".into())),
                2
            ).evaluate_zero_vars(),
            2
        );

        assert_eq!(
            LevelExpr::Incr(
                Box::new(LevelExpr::Const(1)),
                2
            ).evaluate_zero_vars(),
            3
        );

        assert_eq!(
            LevelExpr::Max(vec![
                LevelExpr::Const(1),
                LevelExpr::Const(2),
                LevelExpr::Const(0)
            ].into_boxed_slice()).evaluate_zero_vars(),
            2
        );
    }
}
