use std::{collections::{BTreeMap}, rc::Rc, fmt};

use crate::{
    source::Span,
    path::{path::{CanonLibPath, LibPathBuf}, name_tree::NameTree},
    metadata::{ObjectMetadata, ObjectMedatataKind, TheoremMetadata, ProofNodeMetadata},
    var_stack::VarStack,
    phase3_proofck::{proof::{UncheckedTheorem, OptProof, ProofNodeId, Proof},
    inference::UnresolvedInferenceRule, library::Context},
    stdlib::StdLibObjs,
};

use super::expr::{NamedExpr, NameResolveError};

#[derive(Debug)]
pub struct NamedUncheckedTheorem {
    name: Rc<str>,
    goal: NamedExpr,
    proof: OptGenericProof,
    span: Span,
    _goal_span: Span,
}

impl NamedUncheckedTheorem {
    pub fn new(
        name: Rc<str>,
        goal: NamedExpr,
        proof: OptGenericProof,
        span: Span,
        goal_span: Span,
    ) -> Self
    {
        Self {
            name,
            goal,
            proof,
            span,
            _goal_span: goal_span,
        }
    }

    pub fn name(&self) -> &Rc<str> {
        &self.name
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn reify(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs
    ) -> Result<(UncheckedTheorem, ObjectMetadata), NameResolveError>
    {
        let goal = self.goal
            .resolve(
                ctx,
                objects,
                std_objs,
                &mut VarStack::new(),
                None
            )?;

        let mut node_metadata = BTreeMap::new();

        let proof = self.proof
            .reify(ctx, objects, std_objs, &mut node_metadata)?;

        let metadata = ObjectMetadata {
            span: self.span,
            kind: ObjectMedatataKind::Thm(TheoremMetadata {
                nodes: node_metadata,
                root_id: proof.node_id(),
            }),
        };
        
        Ok((UncheckedTheorem::new(goal, proof), metadata))
    }

    pub fn format<W: fmt::Write>(
        &self,
        f: &mut W,
        ctx: Context
    ) -> fmt::Result
    {
        write!(f, "theorem {}: ", self.name)?;
        self.goal.format(f, ctx)?;
        writeln!(f, " {{")?;
        self.proof.format(f, ctx, 2)?;
        writeln!(f)?;
        write!(f, "}}")?;
        Ok(())
    }
}

// FIXME: better name for this
#[derive(Debug)]
pub struct OptGenericProof {
    node_id: ProofNodeId,
    proof: Option<GenericProof>,
    span: Span,
}

impl OptGenericProof {
    pub fn new(proof: Option<GenericProof>, span: Span, node_id: ProofNodeId) -> Self {
        Self {
            node_id,
            proof,
            span,
        }
    }

    pub fn node_id(&self) -> ProofNodeId {
        self.node_id
    }

    pub fn inner(&self) -> Option<&GenericProof> {
        self.proof.as_ref()
    }

    pub fn inner_mut(&mut self) -> Option<&mut GenericProof> {
        self.proof.as_mut()
    }

    pub fn rule(&self) -> Option<&NamedInferenceRule> {
        self.inner().map(GenericProof::rule)
    }

    pub fn children(&self) -> &[OptGenericProof] {
        self.inner().map(GenericProof::children).unwrap_or_default()
    }

    pub fn children_mut(&mut self) -> &mut [OptGenericProof] {
        self.inner_mut().map(GenericProof::children_mut).unwrap_or_default()
    }

    pub fn span(&self) -> &Span {
        &self.span
    }


    fn reify(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs,
        node_metadata: &mut BTreeMap<ProofNodeId, ProofNodeMetadata>
    ) -> Result<OptProof, NameResolveError>
    {
        node_metadata.insert(self.node_id, ProofNodeMetadata {
            span: self.span
        });

        let proof = match &self.proof {
            Some(proof) => Some(proof.reify(ctx, objects, std_objs, &self.span, node_metadata)?),
            None => None,
        };

        Ok(OptProof::new(self.node_id, proof))
    }

    fn format<W: fmt::Write>(&self, f: &mut W, ctx: Context, indent: usize) -> fmt::Result {
        match &self.proof {
            Some(proof) => {
                write!(f, "{:indent$}", "", indent = indent)?;
                proof.rule.format(f, ctx)?;

                if !proof.children.is_empty() {
                    writeln!(f, " {{")?;
                    for child in &proof.children[..] {
                        child.format(f, ctx, indent.saturating_add(2))?;
                        writeln!(f)?;
                    }
                    write!(f, "{:indent$}}}", "", indent = indent)?;
                }
            },

            None => {
                write!(f, "{:indent$}_", "", indent = indent)?;
            },
        }
        
        Ok(())
    }
}

#[derive(Debug)]
pub struct GenericProof {
    rule: NamedInferenceRule,
    children: Vec<OptGenericProof>,
}

impl GenericProof {
    pub fn new(rule: NamedInferenceRule, children: Vec<OptGenericProof>) -> Self {
        Self { rule, children }
    }

    pub fn rule(&self) -> &NamedInferenceRule {
        &self.rule
    }

    pub fn children(&self) -> &[OptGenericProof] {
        &self.children
    }

    pub fn children_mut(&mut self) -> &mut [OptGenericProof] {
        &mut self.children
    }

    fn reify(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs,
        _span: &Span,
        node_metadata: &mut BTreeMap<ProofNodeId, ProofNodeMetadata>
    ) -> Result<Proof, NameResolveError>
    {
        let rule = self.rule.reify(ctx, objects, std_objs)?;

        let children = self
            .children
            .iter()
            .map(|sub_proof| sub_proof.reify(ctx, objects, std_objs, node_metadata))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Proof::new(rule, children))
    }
}

#[derive(Clone, Debug)]
pub struct NamedInferenceRule {
    path: LibPathBuf,
    args: Vec<NamedExpr>,
}

impl NamedInferenceRule {
    pub fn new(name: LibPathBuf, args: Vec<NamedExpr>) -> Self {
        Self { path: name, args }
    }

    pub fn path(&self) -> &LibPathBuf {
        &self.path
    }

    pub fn reify(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs
    ) -> Result<UnresolvedInferenceRule, NameResolveError>
    {
        let args = self.args
            .iter()
            .map(|arg| arg.resolve(ctx, objects, std_objs, &mut VarStack::new(), None))
            .collect::<Result<_, _>>()?;

        let (id, _, _) = objects.get_obj(ctx, &self.path)
            .map_err(|err| NameResolveError::NameTree { err })?;

        Ok(UnresolvedInferenceRule::new(id, args))
    }

    pub fn format<W: fmt::Write>(
        &self,
        f: &mut W,
        ctx: Context
    ) -> fmt::Result
    {
        write!(f, "{}", self.path)?;
        let mut args = self.args.iter();
        if let Some(arg) = args.next() {
            write!(f, " ")?;
            arg.format(f, ctx)?;
            for arg in args {
                write!(f, ", ")?;
                arg.format(f, ctx)?;
            }
        }
        Ok(())
    }
}
