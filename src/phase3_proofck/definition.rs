use std::{rc::Rc, fmt};

use rkyv::{Archive, Serialize, Deserialize};

use crate::de_bruijn::DeBruijnIndex;

use super::{expr::RcExpr, library::{ResolveError, Resolver}};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct DefParamIndex(pub usize);

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct Definition {
    params: Rc<[DefParam]>,
    body: RcExpr,
}

impl Definition {
    pub fn new(params: Rc<[DefParam]>, body: RcExpr) -> Self {
        Self { params, body }
    }

    pub fn num_params(&self) -> usize {
        self.params.len()
    }

    pub fn resolve(&self, resolver: &mut Resolver) -> Result<Self, ResolveError> {
        self.body
            .resolve(resolver)
            .map(|body| Self::new(self.params.clone(), body))
    }

    pub fn unfold(&self, args: &[RcExpr]) -> Result<RcExpr, DeltaReductionError> {
        let num_params = self.params.len();

        if args.len() != num_params {
            return Err(DeltaReductionError::BadArgCount {
                expected: num_params,
                actual: args.len(),
            });
        }

        let mut expr = self.body.clone();

        for (param_index, arg) in args.iter().take(num_params).enumerate() {
            let depth = DeBruijnIndex::new(num_params - 1 - param_index);
            expr = expr.subst_at_depth_or_clone(depth, arg);
        }

        Ok(expr)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct DefParam {
    // String names are retained for display / serialisation purposes.
    args: Box<[Rc<str>]>,
    name: Rc<str>,
}

impl DefParam {
    pub fn new(bound_by: Box<[Rc<str>]>, name: Rc<str>) -> Self {
        Self { args: bound_by, name }
    }

    pub fn name(&self) -> &Rc<str> {
        &self.name
    }

    pub fn arity(&self) -> usize {
        self.args.len()
    }
}

impl fmt::Display for DefParam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)?;
        if !self.args.is_empty() {
            f.write_str("[")?;
            let mut write_semicolon = false;
            for arg in &self.args[..] {
                if write_semicolon {
                    f.write_str("; ")?;
                } else {
                    write_semicolon = true;
                }
                f.write_str(arg)?;
            }
            f.write_str("]")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum DeltaReductionError {
    BadArgCount {
        expected: usize,
        actual: usize,
    },
}
