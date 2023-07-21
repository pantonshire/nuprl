use std::{fmt, error};

use crate::source::{Span, TextSource};

use super::pest_parser::Rule;

#[derive(Debug)]
pub struct ParseError {
    pub span: Span,
    pub kind: ParseErrorKind,
}

impl ParseError {
    pub fn from_pest_error(source: TextSource, err: pest::error::Error<Rule>) -> Self {
        Self { span: source.make_span(err.location), kind: ParseErrorKind::Parse }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ParseErrorKind::Parse => {
                write!(f, "parse error")
            },
            ParseErrorKind::InferenceMissingGoal => {
                write!(f, "no goal provided for inference rule")
            },
            ParseErrorKind::InferenceMissingExt => {
                write!(f, "no extract provided for inference rule")
            },
            ParseErrorKind::InferenceMissingConcl => {
                write!(f, "no conclusion provided")
            },
            ParseErrorKind::InferenceUnexpectedGoal => {
                write!(f, "unexpected goal")
            },
            ParseErrorKind::InferenceUnexpectedExt => {
                write!(f, "unexpected extract")
            },
            ParseErrorKind::InferenceUnexpectedConcl => {
                write!(f, "unexpected conclusion")
            },
            ParseErrorKind::InferenceBadHypothesisOp => {
                write!(f, "hypothesis op not allowed in this context")
            },
            ParseErrorKind::InferenceBadExt => {
                write!(f, "bad subgoal extract")
            },
        }
    }
}

impl error::Error for ParseError {}

#[derive(Debug)]
pub enum ParseErrorKind {
    Parse,
    InferenceMissingGoal,
    InferenceMissingExt,
    InferenceMissingConcl,
    InferenceUnexpectedGoal,
    InferenceUnexpectedExt,
    InferenceUnexpectedConcl,
    InferenceBadHypothesisOp,
    InferenceBadExt,
}
