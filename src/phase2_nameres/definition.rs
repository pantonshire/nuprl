use std::{rc::Rc, fmt};

use crate::{
    phase3_proofck::{definition::{DefParam, Definition}, library::Context},
    source::Span,
    var_stack::{VarStack, VarStackEntry},
    metadata::{ObjectMetadata, ObjectMedatataKind},
    path::{path::CanonLibPath, name_tree::NameTree}, stdlib::StdLibObjs,
};

use super::expr::{NamedExpr, NameResolveError};

#[derive(Clone, Debug)]
pub struct NamedDef {
    name: Rc<str>,
    params: Rc<[DefParam]>,
    body: NamedExpr,
    span: Span,
}

impl NamedDef {
    pub fn new(name: Rc<str>, params: Rc<[DefParam]>, body: NamedExpr, span: Span) -> Self {
        Self {
            name,
            params,
            body,
            span,
        }
    }

    pub fn name(&self) -> &Rc<str> {
        &self.name
    }

    pub fn params(&self) -> &Rc<[DefParam]> {
        &self.params
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn resolve(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs
    ) -> Result<(Definition, ObjectMetadata), NameResolveError>
    {
        let mut vars = VarStack::new();

        // Push the arguments onto the stack in order, so that the last argument is on top. The
        // body will be able to refer to the last argument with De Bruijn index 0, the
        // second-to-last with De Bruijn index 1, and so on.
        for param in self.params.iter() {
            vars.push(VarStackEntry::named(param.name().clone(), param.arity()));
        }

        // Allowing it to refer to the definition's arguments, convert the body from using named
        // variables to indexed variables.
        let body = self.body.resolve(ctx, objects, std_objs, &mut vars, None)?;

        let metadata = ObjectMetadata {
            span: self.span,
            kind: ObjectMedatataKind::Def,
        };

        Ok((Definition::new(self.params.clone(), body), metadata))
    }

    pub fn format<W: fmt::Write>(
        &self,
        f: &mut W,
        ctx: Context
    ) -> fmt::Result
    {
        write!(f, "def {} ", self.name)?;
        for param in &self.params[..] {
            write!(f, "{} ", param)?;
        }
        write!(f, "= ")?;
        self.body.format(f, ctx)?;
        Ok(())
    }
}
