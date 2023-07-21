use rkyv::{Archive, Serialize, Deserialize};

use super::{
    sequent::{DisplaySequent, Sequent, SequentRef},
    expr::RcExpr,
    inference::{InferenceRule, InferenceResult, UnresolvedInferenceRule},
    library::{Resolver, ResolveError, Context},
    var_names::NameAssignments,
    hypothesis::Hypotheses,
};

/// An identifier which uniquely identifies a proof node within a particular proof tree. Duplicate
/// ids may occur between two different proof trees.
#[derive(Archive, Serialize, Deserialize, serde::Serialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[serde(transparent)]
pub struct ProofNodeId(usize);

#[derive(Debug)]
pub struct ProofNodeIdGen {
    next: usize,
}

impl ProofNodeIdGen {
    pub fn new() -> Self {
        Self { next: 0 }
    }

    pub fn next(&mut self) -> ProofNodeId {
        let id = self.next;
        self.next += 1;
        ProofNodeId(id)
    }
}

#[derive(Debug)]
pub struct UncheckedTheorem {
    goal: RcExpr,
    proof: OptProof,
}

impl UncheckedTheorem {
    pub fn new(goal: RcExpr, proof: OptProof) -> Self {
        Self { goal, proof }
    }

    pub fn goal(&self) -> &RcExpr {
        &self.goal
    }

    pub fn proof(&self) -> &OptProof {
        &self.proof
    }

    pub fn resolve_and_check(&self, resolver: &mut Resolver) -> Result<Theorem, ResolveError> {
        let goal = self.goal.resolve(resolver)?;
        self.proof.resolve_and_check(resolver, goal)
    }
}

#[derive(Debug)]
pub struct OptProof {
    node_id: ProofNodeId,
    proof: Option<Proof>,
}

impl OptProof {
    pub fn new(node_id: ProofNodeId, proof: Option<Proof>) -> Self {
        Self { node_id, proof }
    }

    pub fn node_id(&self) -> ProofNodeId {
        self.node_id
    }

    fn resolve_and_check<G>(
        &self,
        resolver: &mut Resolver,
        goal: G
    ) -> Result<ProofResult<G>, ResolveError>
    where
        G: Goal,
    {
        match &self.proof {
            Some(proof) => proof.resolve_and_check(resolver, goal, self.node_id),
            None => Ok(ProofResult::unrefined(goal, Some(self.node_id))),
        }
    }
}

#[derive(Debug)]
pub struct Proof {
    rule: UnresolvedInferenceRule,
    children: Vec<OptProof>,
}

impl Proof {
    pub fn new(rule: UnresolvedInferenceRule, children: Vec<OptProof>) -> Self {
        Self { rule, children }
    }

    fn resolve_and_check<G>(
        &self,
        resolver: &mut Resolver,
        goal: G,
        node_id: ProofNodeId
    ) -> Result<ProofResult<G>, ResolveError>
    where
        G: Goal,
    {
        let inf_def_obj = resolver.resolve(self.rule.id())?;
        let Some(inf_def) = inf_def_obj.as_inf() else {
            return Err(ResolveError::ExpectedInfRule(inf_def_obj.path().to_owned()))
        };

        let goal_sequent = goal.as_sequent();
        let rule = self.rule.resolve(resolver, goal_sequent.hys())?;

        let refinement_result = match inf_def.apply(resolver.ctx(), rule.args(), goal_sequent) {
            InferenceResult::Ok {
                subgoals,
                validation
            } => {
                let mut children_iter = self.children.iter();

                let sub_proofs = subgoals
                    .into_iter()
                    .map(|subgoal| match children_iter.next() {
                        Some(sub_proof) => sub_proof.resolve_and_check(resolver, subgoal),
                        None => Ok(ProofResult::unrefined(subgoal, None)),
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let extra_proofs = children_iter.collect::<Vec<_>>();

                let theorem = if extra_proofs.is_empty() {
                    let sub_theorems = sub_proofs
                        .iter()
                        .map(ProofResult::theorem_ref)
                        .collect::<Option<Vec<_>>>();

                    match sub_theorems {
                        Some(sub_theorems) => {
                            let extract = validation.eval(&sub_theorems);
                            ExtractResult::Complete { extract }
                        }
                        None => ExtractResult::Incomplete,
                    }
                } else {
                    ExtractResult::TooManySubProofs
                };

                RefinementResult::Ok {
                    children: sub_proofs,
                    extract: theorem,
                }
            },
            InferenceResult::Conflict => RefinementResult::Conflict,
        };

        Ok(ProofResult {
            goal,
            refinement: Refinement::Refined {
                rule,
                result: refinement_result,
            },
            node_id: Some(node_id),
        })
    }
}

pub trait Goal: Clone {
    fn as_sequent(&self) -> SequentRef;
}

impl Goal for RcExpr {
    fn as_sequent(&self) -> SequentRef {
        SequentRef::new(Hypotheses::EMPTY_REF, self)
    }
}

impl Goal for Sequent {
    fn as_sequent(&self) -> SequentRef {
        self.seq_ref()
    }
}

/// The result of checking a top-level theorem. The goal of a sub-theorem cannot have any
/// hypotheses (it must be closed); hence, the goal type is a `ClosedExpr` rather than a `Sequent`.
pub type Theorem = ProofResult<RcExpr>;

pub type SubTheorem = ProofResult<Sequent>;

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct ProofResult<G> {
    node_id: Option<ProofNodeId>,
    goal: G,
    refinement: Refinement,
}

impl<G: Goal> ProofResult<G> {
    pub fn unrefined(goal: G, node_id: Option<ProofNodeId>) -> Self {
        Self {
            goal,
            refinement: Refinement::Unrefined,
            node_id,
        }
    }

    pub fn goal(&self) -> &G {
        &self.goal
    }

    pub fn extract(&self) -> Option<&RcExpr> {
        match &self.refinement {
            Refinement::Refined { rule: _, result } => match result {
                RefinementResult::Ok {
                    children: _,
                    extract: theorem,
                } => match theorem {
                    ExtractResult::Complete { extract } => Some(extract),
                    _ => None,
                },
                RefinementResult::Conflict => None,
            },
            _ => None,
        }
    }

    fn flatten(&self, ctx: Context) -> Vec<DisplayProofNode> {
        let mut nodes = Vec::new();
        self.flatten_rec(ctx, &mut nodes);
        nodes
    }

    fn flatten_rec(&self, ctx: Context, nodes: &mut Vec<DisplayProofNode>) {
        let Some(node_id) = self.node_id else {
            return
        };

        let (sub_proofs, extract) = match &self.refinement {
            Refinement::Refined { rule: _, result } => match result {
                RefinementResult::Ok {
                    children: sub_proofs,
                    extract,
                } => (
                    Some(sub_proofs),
                    match extract {
                        ExtractResult::Complete { extract } => Some(extract),
                        ExtractResult::TooManySubProofs => None,
                        ExtractResult::Incomplete => None,
                    },
                ),
                RefinementResult::Conflict => (None, None),
            },
            Refinement::Unrefined => (None, None),
        };

        let children = sub_proofs.map(|sub_proofs| {
            sub_proofs
                .iter()
                .map(|sub_proof| {
                    let extract = sub_proof.extract().map(|extract| {
                        let mut buf = String::new();
                        extract
                            .format(&mut buf, ctx, &mut NameAssignments::from_hypotheses(sub_proof.goal.hys()))
                            .unwrap();
                        buf
                    });
                    DisplayProofChild {
                        node_id: sub_proof.node_id,
                        goal: sub_proof.goal().as_sequent().display(ctx),
                        extract,
                    }
                })
                .collect::<Vec<_>>()
        });

        if let Some(sub_proofs) = sub_proofs {
            for sub_proof in sub_proofs {
                sub_proof.flatten_rec(ctx, nodes);
            }
        }

        let goal = self.goal.as_sequent();

        let extract_string = extract.map(|extract| {
            let mut buf = String::new();
            extract
                .format(&mut buf, ctx, &mut NameAssignments::from_hypotheses(goal.hys()))
                .unwrap();
            buf
        });

        let conflict = matches!(
            self.refinement,
            Refinement::Refined { rule: _, result: RefinementResult::Conflict }
        );

        let goal = goal.display(ctx);

        nodes.push(
            DisplayProofNode {
                node_id,
                goal,
                children,
                extract: extract_string,
                conflict,
            },
        );
    }
    
}

impl SubTheorem {
    pub fn theorem_ref(&self) -> Option<TheoremRef> {
        self.extract()
            .map(|extract| TheoremRef::new(&self.goal, extract))
    }
}

pub struct DisplayTheorem<'a> {
    pub thm: &'a Theorem,
    pub ctx: Context<'a>,
}

impl<'a> serde::Serialize for DisplayTheorem<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serde::Serialize::serialize(&self.thm.flatten(self.ctx), serializer)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub enum Refinement {
    Refined {
        rule: InferenceRule,
        result: RefinementResult,
    },
    Unrefined,
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
#[archive(bound(serialize = "__S: rkyv::ser::Serializer + rkyv::ser::ScratchSpace + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "__D: rkyv::de::SharedDeserializeRegistry"))]
pub enum RefinementResult {
    Ok {
        #[omit_bounds]
        children: Vec<SubTheorem>,
        extract: ExtractResult,
    },
    Conflict,
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub enum ExtractResult {
    Complete { extract: RcExpr },
    TooManySubProofs,
    Incomplete,
}

#[derive(Clone, Copy)]
pub struct TheoremRef<'a> {
    sequent: &'a Sequent,
    extract: &'a RcExpr,
}

impl<'a> TheoremRef<'a> {
    fn new(sequent: &'a Sequent, extract: &'a RcExpr) -> Self {
        Self { sequent, extract }
    }

    pub fn sequent(self) -> &'a Sequent {
        self.sequent
    }

    pub fn extract(self) -> &'a RcExpr {
        self.extract
    }
}

#[derive(serde::Serialize, Debug)]
#[serde(rename = "ProofNode")]
struct DisplayProofNode {
    node_id: ProofNodeId,
    goal: DisplaySequent,
    children: Option<Vec<DisplayProofChild>>,
    extract: Option<String>,
    conflict: bool,
}

#[derive(serde::Serialize, Debug)]
#[serde(rename = "ProofChild")]
struct DisplayProofChild {
    node_id: Option<ProofNodeId>,
    goal: DisplaySequent,
    extract: Option<String>,
}
