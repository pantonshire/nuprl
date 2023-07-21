use std::rc::Rc;

use crate::{path::path::LibPathBuf, source::Span};

use super::{
    definition::NamedDef,
    proof::NamedUncheckedTheorem,
    exprkind_def::NamedExprKindDef,
    inf_def::NamedInfDef,
};

pub enum Statement {
    Def(NamedDef),
    Thm(NamedUncheckedTheorem),
    Exp(NamedExprKindDef),
    Inf(NamedInfDef),
    Imp(LibPathBuf, Span),
    Intrinsic(Rc<str>, Span),
}
