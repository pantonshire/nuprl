mod level_expr;
mod parser;
mod tokeniser;
mod token_stream;

use std::{str, rc::Rc, collections::{HashMap, BTreeMap}, ops::Deref};

use serde::Serialize;

pub use level_expr::LevelExpr;

use crate::{phase2_nameres::{definition::NamedDef, proof::{NamedUncheckedTheorem, OptGenericProof, GenericProof, NamedInferenceRule}, expr::NamedExpr}, phase3_proofck::{proof::{ProofNodeIdGen, ProofNodeId}, object::{UnresolvedObjectKind, UnresolvedObject}, library::{Resolver, ResolveError}, definition::DefParam, expr::{RcExpr, ReductionSteps}}, path::{path::{CanonLibPath, LibPathBuf, CanonLibPathBuf, LibPathNode}, name_tree::NameTree}, source::Span, var_stack::{VarStack, VarStackEntry}, stdlib::StdLibObjs, object_id::ObjectIdGen, DEFAULT_NAMESPACE};

const BECAUSE_CACHE: &str = "because_Cache";

#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
pub struct Term {
    params: Box<[Param]>,
    subterms: Box<[Term]>,
}

impl Term {
    pub fn to_main_parts(
        &self,
        name: Rc<str>,
        resolver: Resolver
    ) -> Result<(Vec<NamedDef>, NamedUncheckedTheorem, Resolver), TermError>
    {
        let mut id_gen = ProofNodeIdGen::new();

        let [abs, _stm, rule, inf_tree, ..] = &self.subterms[..] else {
            return Err(TermError)
        };

        let defs = abs
            .subterms
            .iter()
            .map(|stamp| {
                let [abstraction] = &stamp.subterms[..] else {
                    return Err(TermError)
                };

                abstraction.to_def(resolver.std_objs())
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Temporary library containing definitions only, for use in importing the proof;
        // specifically, it is used to fully resolve proof node goals to find compatible proof
        // nodes to replace `because_Cache` nodes with.
        //
        // This library is *not* the final library that we will end up producing from the imported
        // term file.
        let mut resolver = {
            let (stdlib, std_objs) = resolver.into_lib();

            let std_path = CanonLibPathBuf::from_nodes(["std"]);
            // stdlib.reroot(&std_path);

            let mut names = NameTree::empty_module();

            let (std_entry, _) = names.prepare_entry_last_segment(&std_path)
                .unwrap();
            std_entry.insert(stdlib.names().clone());

            let mut id_gen = ObjectIdGen::new(DEFAULT_NAMESPACE);
            let mut defs_with_ids = Vec::new();

            for def in defs.iter() {
                let (entry, path) = names.prepare_entry(CanonLibPath::ROOT, def.name().clone())
                    .unwrap();

                let id = id_gen.next_id();

                entry.insert(NameTree::Object { id, params: def.params().len() });

                defs_with_ids.push((def, id, path));
            }
            
            let mut lib = BTreeMap::new();

            for (def, id, path) in defs_with_ids.into_iter() {
                let (def, _) = def.resolve(CanonLibPath::ROOT, &mut names, &std_objs)
                    .unwrap();

                lib.insert(id, UnresolvedObject::new(
                    id,
                    CanonLibPathBuf::root(),
                    path,
                    UnresolvedObjectKind::Def(def)
                ));
            }

            let mut resolver = Resolver::new(DEFAULT_NAMESPACE, names, lib, std_objs);
            resolver.extend(stdlib);
            resolver
        };

        //FIXME: what is the point of `STM:t`?

        let rule_stamps = rule.to_rule_stamps()?;

        let theorem = inf_tree.to_theorem(&mut id_gen, name, &rule_stamps, &mut resolver)?;

        Ok((defs, theorem, resolver))
    }

    pub fn to_rule_stamps(&self) -> Result<HashMap<Box<str>, Box<str>>, TermError> {
        match &self.params[..] {
            [Param::Tok(tok)] if tok.as_ref() == "RULE" => (),
            _ => return Err(TermError),
        }
        
        let mut rules = HashMap::new();

        for subterm in &self.subterms[..] {
            let [Param::Obj(stamp)] = &subterm.params[..] else {
                return Err(TermError)
            };

            let [rule_definition] = &subterm.subterms[..] else {
                return Err(TermError)
            };

            match &rule_definition.params[..] {
                [Param::Opid(opid)] if opid.as_ref() == "!rule_definition" => (),
                _ => return Err(TermError),
            }

            let [_, rule, ..] = &rule_definition.subterms[..] else {
                return Err(TermError)
            };

            let name = match &rule.params[..] {
                [Param::Opid(opid), Param::Tok(name)] if opid.as_ref() == "!rule" => name,
                _ => return Err(TermError),
            };

            rules.insert(stamp.clone(), name.clone());
        }

        Ok(rules)
    }

    pub fn to_theorem(
        &self,
        id_gen: &mut ProofNodeIdGen,
        name: Rc<str>,
        rules: &HashMap<Box<str>, Box<str>>,
        resolver: &mut Resolver,
    ) -> Result<NamedUncheckedTheorem, TermError>
    {
        let mut goals = HashMap::new();

        let mut proof = self.to_proof(resolver.std_objs(), id_gen, rules, &mut goals)?;

        // Convert each of the goals to `OpenSequent`s so that they can be compared without having
        // to worry about alpha equivalence.
        let goals_closed = goals
            .iter()
            .filter_map(|(node_id, goal)| {
                goal
                    .resolve(resolver.lib().names(), resolver.std_objs())
                    .and_then(|goal| goal.apply_defs(resolver).ok())
                    .map(|goal| (*node_id, goal))
            })
            .collect::<HashMap<_, _>>();

        // Get the root node's goal from the goals map.
        let Some(goal) = goals.remove(&proof.node_id()) else {
            return Err(TermError);
        };

        // The root goal is not allowed to have any hypotheses.
        if !goal.hys.is_empty() {
            return Err(TermError);
        }

        patch_proof_mut(id_gen, &mut proof, &goals_closed);

        let mut substitutions = Vec::new();
        because_cache_substitutions(&proof, &proof, &goals_closed, &mut substitutions);

        let proof = if substitutions.is_empty() {
            proof
        } else {
            clone_proof_with_substitutions(&proof, id_gen, &goals_closed, &substitutions)
        };

        // FIXME: proper spans
        let span = Span::fixme_dummy_span();
        let goal_span = Span::fixme_dummy_span();
        
        Ok(NamedUncheckedTheorem::new(name, goal.concl, proof, span, goal_span))
    }

    fn to_proof(
        &self,
        std_objs: &StdLibObjs,
        id_gen: &mut ProofNodeIdGen,
        rules: &HashMap<Box<str>, Box<str>>,
        goals: &mut HashMap<ProofNodeId, NamedSequent>
    ) -> Result<OptGenericProof, TermError>
    {
        match &self.params[..] {
            [Param::Opid(opid)] if opid.as_ref() == "!inf_tree" => (),
            _ => return Err(TermError),
        }

        let [goal, rule, cons, ..] = &self.subterms[..] else {
            return Err(TermError)
        };

        let goal = {
            match &goal.params[..] {
                [Param::Opid(opid)] if opid.as_ref() == "!inf_goal" => (),
                _ => return Err(TermError),
            }
    
            let [goal, _] = &goal.subterms[..] else {
                return Err(TermError)
            };
    
            goal.to_sequent(std_objs)?
        };

        let rule = rule.to_rule_instance(std_objs, rules)?;

        let mut cons = cons;
        let mut children = Vec::new();

        loop {
            match &cons.params[..] {
                [Param::Opid(opid)] if opid.as_ref() == "!inf_tree_cons" => (),
                _ => return Err(TermError),
            }

            let [child, next_cons] = match &cons.subterms[..] {
                [] => break,
                [subtree, next_cons] => [subtree, next_cons],
                _ => return Err(TermError),
            };

            let proof = child.to_proof(std_objs, id_gen, rules, goals)?;
            children.push(proof);
            cons = next_cons;
        }        

        // FIXME: proper span
        let span = Span::fixme_dummy_span();

        let node_id = id_gen.next();

        goals.insert(node_id, goal);

        Ok(OptGenericProof::new(
            Some(GenericProof::new(rule, children)),
            span,
            node_id
        ))
    }

    fn to_rule_instance(&self, std_objs: &StdLibObjs, rules: &HashMap<Box<str>, Box<str>>)
        -> Result<NamedInferenceRule, TermError>
    {
        match &self.params[..] {
            [Param::Opid(opid)] if opid.as_ref() == "!inf_primitive_actual" => (),
            _ => return Err(TermError),
        }

        let [rule_instance] = &self.subterms[..] else {
            return Err(TermError)
        };

        let stamp = match &rule_instance.params[..] {
            [Param::Opid(opid), Param::Obj(stamp)] if opid.as_ref() == "!rule_instance" => stamp,
            _ => return Err(TermError),
        };

        let name = rules.get(stamp).ok_or(TermError)?.clone();

        let mut args = Vec::new();

        let [arg_cons] = &rule_instance.subterms[..] else {
            return Err(TermError)
        };

        let mut arg_cons = arg_cons;

        loop {
            match &arg_cons.params[..] {
                [Param::Opid(opid)] if opid.as_ref() == "!rule_arg_cons" => (),
                _ => return Err(TermError),
            }

            let [arg, next_cons] = match &arg_cons.subterms[..] {
                [] => break,
                [arg, next_cons] => [arg, next_cons],
                _ => return Err(TermError),
            };

            args.push(arg.to_expr(std_objs)?);
            arg_cons = next_cons;
        }

        match name.as_ref() {
            "cut" => {
                if let Some(NamedExpr::Nat(i)) = args.get_mut(0) {
                    *i = i.checked_add(1).unwrap();
                }
            },
            _ => (),
        }

        let path = LibPathBuf::new([
            LibPathNode::Named("std".into()),
            LibPathNode::Named(name.into()),
        ].into(), true);
        
        Ok(NamedInferenceRule::new(path, args))
    }

    fn to_sequent(&self, std_objs: &StdLibObjs) -> Result<NamedSequent, TermError> {
        let mut term = self;
        let mut hys = Vec::new();

        let concl = loop {
            match &term.params[..] {
                [Param::Opid(opid), _] if opid.as_ref() == "!inf_sequent" => {
                    let [hy_ty, bound] = &term.subterms[..] else {
                        return Err(TermError)
                    };

                    let hy_ty = hy_ty.to_expr(std_objs)?;

                    let hy_var = match &bound.params[..] {
                        [Param::Opid(opid), Param::Var(var)] if opid.as_ref() == "bound_id" => var,
                        _ => return Err(TermError)
                    };

                    hys.push((hy_var.clone(), hy_ty));

                    let [bound_subterm] = &bound.subterms[..] else {
                        return Err(TermError)
                    };

                    term = bound_subterm
                },

                _ => {
                    let expr = term.to_expr(std_objs)?;
                    break expr;
                },
            }
        };

        Ok(NamedSequent { hys, concl })
    }

    // FIXME: take meta-variables into account; they are currently just discarded.
    pub fn to_def(&self, std_objs: &StdLibObjs) -> Result<NamedDef, TermError> {
        match &self.params[..] {
            [Param::Opid(opid)] if opid.as_ref() == "!abstraction" => (),
            _ => return Err(TermError),
        }

        let [_, def, body] = &self.subterms[..] else {
            return Err(TermError)
        };

        // FIXME: for definitions with meta-variables (e.g. prop), the meta-variables go here after
        // the name.
        let [Param::Opid(name), ..] = &def.params[..] else {
            return Err(TermError)
        };

        let params = def.subterms
            .iter()
            .map(Self::to_def_param)
            .collect::<Result<Rc<[_]>, _>>()?;

        let body = body.to_expr(std_objs).map_err(|_| TermError)?;

        // FIXME: proper span
        let span = Span::fixme_dummy_span();

        Ok(NamedDef::new(name.as_ref().into(), params, body, span))
    }

    fn to_def_param(&self) -> Result<DefParam, TermError> {
        let mut params = self.params.iter();

        let Some(Param::Opid(opid)) = params.next() else {
            return Err(TermError)
        };

        match opid.as_ref() {
            "variable" => {
                let Some(Param::Var(name)) = params.next() else {
                    return Err(TermError)
                };

                let args = self
                    .subterms
                    .iter()
                    .map(|subterm| {
                        match &subterm.params[..] {
                            [Param::Opid(opid), Param::Var(var)]
                                if opid.as_ref() == "variable" =>
                            {
                                if subterm.subterms.is_empty() {
                                    Ok(Rc::<str>::from(var.as_ref()))
                                } else {
                                    Err(TermError)
                                }
                            },
                            _ => Err(TermError)
                        }
                    })
                    .collect::<Result<Box<[_]>, _>>()?;

                Ok(DefParam::new(args, name.as_ref().into()))
            },

            "bound_id" => {
                let [subterm] = &self.subterms[..] else {
                    return Err(TermError)
                };
                subterm.to_def_param()
            },
            
            _ => Err(TermError),
        }
    }

    // FIXME: unit tests for this
    pub fn to_expr(&self, std_objs: &StdLibObjs) -> Result<NamedExpr, TermError> {
        let mut params = self.params.iter();

        let Some(Param::Opid(opid)) = params.next() else {
            return Err(TermError)
        };

        match opid.as_ref() {
            "variable" => {
                let Some(Param::Var(var)) = params.next() else {
                    return Err(TermError)
                };

                let mapping = self
                    .subterms
                    .iter()
                    .map(|subterm| subterm
                        .to_expr(std_objs)
                        .and_then(|subexpr| match subexpr {
                            NamedExpr::Var(var) => Ok(var),
                            _ => Err(TermError),
                        })
                    ).collect::<Result<Box<[_]>, _>>()?;

                Ok(if mapping.is_empty() {
                    NamedExpr::Var(LibPathBuf::new_unitary(var.as_ref().into()))
                } else {
                    NamedExpr::SecondOrderVar {
                        name: LibPathBuf::new_unitary(var.as_ref().into()),
                        mapping,
                    }
                })
            },

            "axiom" => Ok(NamedExpr::Obj {
                id: std_objs.ax.unwrap(),
                args: [].into(),
            }),

            "natural_number" => {
                let Some(Param::Nat(nat)) = params.next() else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Nat(*nat))
            },

            "token" => {
                let Some(Param::Tok(tok)) = params.next() else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Tok(tok.as_ref().into()))
            },

            "lambda" => {
                let [body] = &self.subterms[..] else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Obj {
                    id: std_objs.lambda.unwrap(),
                    args: [
                        body.to_expr(std_objs)?,
                    ].into()
                })
            },

            "apply" => {
                let [lhs, rhs] = &self.subterms[..] else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Jux {
                    lhs: lhs.to_expr(std_objs)?.boxed(),
                    rhs: rhs.to_expr(std_objs)?.boxed(),
                })
            },

            // FIXME: remove hard-coded definition of `prop`
            "universe" | "prop" => {
                let Some(Param::Level(level)) = params.next() else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Obj {
                    id: std_objs.universe.unwrap(),
                    args: [
                        NamedExpr::Nat(level.evaluate_zero_vars())
                    ].into()
                })
            },

            "int" => {
                Ok(NamedExpr::Obj {
                    id: std_objs.int.unwrap(),
                    args: [].into()
                })
            },

            "function" => {
                let [domain, codomain] = &self.subterms[..] else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Obj {
                    id: std_objs.func.unwrap(),
                    args: [
                        domain.to_expr(std_objs)?,
                        codomain.to_expr(std_objs)?,
                    ].into()
                })
            },

            "equal" => {
                let [ty, lhs, rhs] = &self.subterms[..] else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Obj {
                    id: std_objs.eq.unwrap(),
                    args: [
                        ty.to_expr(std_objs)?,
                        lhs.to_expr(std_objs)?,
                        rhs.to_expr(std_objs)?,
                    ].into()
                })
            },

            "isect" => {
                let [lhs, rhs] = &self.subterms[..] else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Obj {
                    id: std_objs.isect.unwrap(),
                    args: [
                        lhs.to_expr(std_objs)?,
                        rhs.to_expr(std_objs)?,
                    ].into()
                })
            },

            "bound_id" => {
                let Some(Param::Var(var)) = params.next() else {
                    return Err(TermError)
                };

                let [body] = &self.subterms[..] else {
                    return Err(TermError)
                };

                match var.as_ref() {
                    "" => body.to_expr(std_objs),
                    _ => Ok(NamedExpr::Bound {
                        var: var.as_ref().into(),
                        body: body.to_expr(std_objs)?.boxed(),
                    })
                }
                
            },

            // FIXME: unbounded (`*`) reduction steps
            "tag" => {
                let Some(Param::Nat(steps)) = params.next() else {
                    return Err(TermError)
                };

                let steps = ReductionSteps::Finite(*steps);

                let [body] = &self.subterms[..] else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Tag {
                    steps,
                    body: body.to_expr(std_objs)?.boxed(),
                })
            },

            "assumption-index" => {
                let Some(Param::Nat(nat)) = params.next() else {
                    return Err(TermError)
                };

                Ok(NamedExpr::Nat(*nat))
            },

            "!parameter" => {
                match params.next() {
                    // FIXME: try to retain meta-variables (e.g. `i` in `i'`) where possible rather
                    // than just setting them all to 0.
                    Some(Param::Level(level)) => {
                        let level = level.evaluate_zero_vars();
                        Ok(NamedExpr::Nat(level))
                    },
                    // FIXME: other cases (e.g. :o for use in lemma_by_obid)
                    _ => Ok(NamedExpr::Tok("".into())),
                }
            },

            opid => {
                let mut expr = NamedExpr::Var(LibPathBuf::new_unitary(opid.into()));

                for subterm in &self.subterms[..] {
                    expr = NamedExpr::Jux {
                        lhs: expr.boxed(),
                        rhs: subterm.to_expr(std_objs)?.boxed(),
                    }
                }

                Ok(expr)
            },
        }
    }

    fn bound(&self) -> Option<(&str, &Self)> {
        let var = match &self.params[..] {
            [Param::Opid(opid), Param::Var(var_name)]
                if opid.as_ref() == "bound_id" =>
            {
                var_name
            },
            _ => return None,
        };

        let bound_term = match &self.subterms[..] {
            [bound_term] => bound_term,
            _ => return None,
        };

        Some((var, bound_term))
    }
}

impl str::FromStr for Term {
    type Err = ParseTermError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tokens = tokeniser::tokenise(s);
        parser::parse(tokens)
    }
}

#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
pub enum Param {
    Opid(Box<str>),
    Tok(Box<str>),
    Nat(u64),
    Var(Box<str>),
    Level(LevelExpr),
    Obj(Box<str>),
    Bool(bool),
    Other {
        val: Box<str>,
        kind: Box<str>,
    },
}

#[derive(Debug)]
pub struct ParseTermError;

#[derive(Debug)]
pub struct TermError;

#[derive(Clone, Debug)]
struct NamedSequent {
    hys: Vec<(Box<str>, NamedExpr)>,
    concl: NamedExpr,
}

impl NamedSequent {
    fn resolve(&self, objects: &NameTree, std_objs: &StdLibObjs) -> Option<OpenSequent> {
        let mut vars = VarStack::new();
        let mut reversing_buf = Vec::with_capacity(self.hys.len());
        let mut hys = Vec::with_capacity(self.hys.len());

        for (hy_var, hy_ty) in self.hys.iter() {
            let hy_ty = hy_ty.resolve(CanonLibPath::ROOT, objects, std_objs, &mut vars, None).ok()?;
            hys.push(hy_ty);

            // Pop all the variables off the stack, so we can push the new variable onto the
            // bottom of the stack.
            while let Some(var) = vars.pop() {
                reversing_buf.push(var);
            }

            vars.push(VarStackEntry::named(hy_var.as_ref().into(), 0));

            while let Some(var) = reversing_buf.pop() {
                vars.push(var);
            }
        }

        let concl = self.concl.resolve(CanonLibPath::ROOT, objects, std_objs, &mut vars, None).ok()?;

        Some(OpenSequent { hys, concl })
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct OpenSequent {
    hys: Vec<RcExpr>,
    concl: RcExpr,
}

impl OpenSequent {
    fn apply_defs(&self, lib: &mut Resolver) -> Result<ClosedSequent, ResolveError> {
        let hys = self
            .hys
            .iter()
            .map(|hy| hy.resolve(lib))
            .collect::<Result<Vec<_>, _>>()?;

        let concl = self.concl.resolve(lib)?;
        
        Ok(ClosedSequent { hys, concl })
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct ClosedSequent {
    hys: Vec<RcExpr>,
    concl: RcExpr,
}

fn proof_node_by_id(proof: &OptGenericProof, id: ProofNodeId) -> Option<&OptGenericProof> {
    if proof.node_id() == id {
        return Some(proof);
    }

    for child in proof.children() {
        if let Some(found_proof) = proof_node_by_id(child, id) {
            return Some(found_proof);
        }
    }

    None
}

fn proof_contains_because_cache(proof: &OptGenericProof) -> bool {
    if proof.rule().map(|rule| is_because_cache(rule.path())).unwrap_or(false) {
        return true;
    }

    proof.children().iter().any(proof_contains_because_cache)
}

fn proof_depth(proof: &OptGenericProof) -> usize {
    1 + proof.children().iter().map(proof_depth).max().unwrap_or(0)
}

fn because_cache_substitutions<'a, 'b>(
    root_proof: &'a OptGenericProof,
    proof: &'a OptGenericProof,
    goals: &'a HashMap<ProofNodeId, ClosedSequent>,
    substitutions: &'b mut Vec<(&'a ClosedSequent, &'a OptGenericProof)>
)
{
    match proof.rule() {
        // If the rule is `because_Cache`, we need to find a substitution for it.
        Some(rule) if is_because_cache(rule.path()) => 'block: {
            // Get the node's goal, or break if we don't know what it is.
            let Some(goal) = goals.get(&proof.node_id()) else {
                break 'block
            };

            // Check that there isn't already a substitution for that goal.
            if substitutions.iter().any(|(subst_goal, _)| *subst_goal == goal) {
                break 'block
            };

            // Create an iterator over nodes we could substitute in which have a compatible goal.
            let compatible_nodes = goals
                .iter()
                .filter_map(|(other_node_id, other_goal)| {
                    // Don't allow a node to be subtituted by itself.
                    if proof.node_id() == *other_node_id {
                        return None;
                    }

                    // Only consider nodes with no more hypotheses than this node.
                    if goal.hys.len() < other_goal.hys.len() {
                        return None;
                    }

                    // Comapre the first `other_goal.hys.len()` hypotheses and the conclusions. We
                    // are allowed to have extra hypotheses at the end that `other_goal` does not
                    // have; if `other_node` is proving the same conclusion with strictly fewer
                    // hypotheses, then we can reuse its proof.
                    if goal.hys[..other_goal.hys.len()] != other_goal.hys
                        || goal.concl != other_goal.concl
                    {
                        return None;
                    }

                    // Find the node in the proof tree.
                    let Some(other_node) = proof_node_by_id(root_proof, *other_node_id) else {
                        return None
                    };

                    // Don't consider nodes with no rule or a `because_Cache` rule.
                    if other_node.rule().map(|rule| is_because_cache(rule.path())).unwrap_or(true) {
                        return None;
                    }

                    // Don't consider any ancestor nodes; doing so could cause infinite recursion!
                    if proof_node_by_id(other_node, proof.node_id()).is_some() {
                        return None;
                    }

                    if proof_contains_because_cache(other_node) {
                        return None;
                    }

                    let depth = proof_depth(other_node);

                    Some((other_node, depth))
                });

            // Find the shallowest compatible node.
            if let Some((compatible_node, _)) = compatible_nodes
                .min_by(|(_, lhs_depth), (_, rhs_depth)| lhs_depth.cmp(rhs_depth))
            {
                substitutions.push((goal, compatible_node));
            }
        },
        _ => {
            for child in proof.children() {
                because_cache_substitutions(root_proof, child, goals, substitutions);
            }
        },
    }
}

fn clone_proof_with_substitutions(
    proof: &OptGenericProof,
    id_gen: &mut ProofNodeIdGen,
    goals: &HashMap<ProofNodeId, ClosedSequent>,
    substitutions: &[(&ClosedSequent, &OptGenericProof)]
) -> OptGenericProof
{
    if proof.rule().map(|rule| is_because_cache(rule.path())).unwrap_or(false) {
        if let Some(goal) = goals.get(&proof.node_id()) {
            if let Some(subst) = substitutions
                .iter()
                .find_map(|(subst_goal, subst)| {
                    (goal == *subst_goal).then_some(subst)
                })
            {
                return clone_proof_with_substitutions(subst, id_gen, goals, substitutions);
            }
        }
    }

    let children = proof
        .children()
        .iter()
        .map(|child| clone_proof_with_substitutions(child, id_gen, goals, substitutions))
        .collect::<Vec<_>>();

    let inner_proof = proof.inner().map(|inner_proof| {
        GenericProof::new(inner_proof.rule().clone(), children)
    });

    OptGenericProof::new(inner_proof, proof.span().clone(), id_gen.next())
}

fn patch_proof_mut(
    id_gen: &mut ProofNodeIdGen,
    proof: &mut OptGenericProof,
    goals: &HashMap<ProofNodeId, ClosedSequent>
) {
    match proof
        .rule()
        .and_then(|rule| rule
            .path()
            .last_named()
            .map(Deref::deref))
    {
        Some("equality") => {
            if let Some(goal) = goals.get(&proof.node_id()) {
                if let Some(hy_equal_to_concl) = goal.hys
                    .iter()
                    .enumerate()
                    .find_map(|(i, hy)| {
                        (hy == &goal.concl)
                            .then_some(i)
                            .and_then(|i| u64::try_from(i).ok())
                            .and_then(|i| i.checked_add(1))
                    })
                {
                    *proof = OptGenericProof::new(
                        Some(GenericProof::new(
                            NamedInferenceRule::new(
                                LibPathBuf::new([
                                    LibPathNode::Named("std".into()),
                                    LibPathNode::Named("hypothesis".into()),
                                ].into(), true),
                                vec![
                                    NamedExpr::Nat(hy_equal_to_concl)
                                ]
                            ),
                            Vec::new()
                        )),
                        proof.span().clone(),
                        id_gen.next()
                    )
                }
            }
        },
        _ => (),
    }

    for child in proof.children_mut() {
        patch_proof_mut(id_gen, child, goals);
    }
}

fn is_because_cache(path: &LibPathBuf) -> bool {
    path
        .last_named()
        .map(Deref::deref)
        .map(|segment| segment == BECAUSE_CACHE)
        .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::{Term, Param};

    #[test]
    fn test_parse() {
        assert_eq!(
            "{bound_id:OPID,x:v}()"
                .parse::<Term>()
                .unwrap(),
            Term {
                params: vec![
                    Param::Opid("bound_id".into()),
                    Param::Var("x".into()),
                ].into_boxed_slice(),
                subterms: Box::default(),
            }
        );

        assert_eq!(
            "{bound_id:OPID,:v}()"
                .parse::<Term>()
                .unwrap(),
            Term {
                params: vec![
                    Param::Opid("bound_id".into()),
                    Param::Var("".into()),
                ].into_boxed_slice(),
                subterms: Box::default(),
            }
        );

        assert_eq!(
            r#"{!stamp\{922506\:n\,3491852726\:time\,48885\:n\,573ffdff_49a0_d00d3908\:t\}:o}()"#
                .parse::<Term>()
                .unwrap(),
            Term {
                params: vec![
                    Param::Obj("!stamp{922506:n,3491852726:time,48885:n,573ffdff_49a0_d00d3908:t}".into()),
                ].into_boxed_slice(),
                subterms: Box::default(),
            }
        );

        assert_eq!(
            "{bound_id:OPID,x:v}({variable:OPID,z:v}())"
                .parse::<Term>()
                .unwrap(),
            Term {
                params: vec![
                    Param::Opid("bound_id".into()),
                    Param::Var("x".into()),
                ].into_boxed_slice(),
                subterms: vec![
                    Term {
                        params: vec![
                            Param::Opid("variable".into()),
                            Param::Var("z".into()),
                        ].into_boxed_slice(),
                        subterms: Box::default(),
                    },
                ].into_boxed_slice(),
            }
        );

        assert_eq!(
            r#"
            {equal:OPID}
            ({variable:OPID,A:v}();
             {variable:OPID,a:v}();
             {variable:OPID,b:v}())
            "#
                .parse::<Term>()
                .unwrap(),
            Term {
                params: vec![
                    Param::Opid("equal".into()),
                ].into_boxed_slice(),
                subterms: vec![
                    Term {
                        params: vec![
                            Param::Opid("variable".into()),
                            Param::Var("A".into()),
                        ].into_boxed_slice(),
                        subterms: Box::default(),
                    },
                    Term {
                        params: vec![
                            Param::Opid("variable".into()),
                            Param::Var("a".into()),
                        ].into_boxed_slice(),
                        subterms: Box::default(),
                    },
                    Term {
                        params: vec![
                            Param::Opid("variable".into()),
                            Param::Var("b".into()),
                        ].into_boxed_slice(),
                        subterms: Box::default(),
                    },
                ].into_boxed_slice(),
            }
        );
    }
}
