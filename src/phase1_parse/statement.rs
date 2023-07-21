use std::rc::Rc;

use pest::Parser;

use crate::{
    source::{TextSource, RangeSpan},
    phase3_proofck::{proof::ProofNodeIdGen, exprkind_def::ExprKindDefParam, definition::DefParam},
    phase2_nameres::{
        exprkind_def::{NamedExprKindDef, NamedBetaReduction},
        inf_def::{
            NamedInfDefParam,
            NamedHypothesisOp,
            NamedHypothesisPattern,
            NamedInfDefSubgoal,
            NamedInfDef,
        },
        expr::NamedExpr,
        statement::Statement,
        definition::NamedDef,
        proof::{OptGenericProof, NamedUncheckedTheorem, GenericProof, NamedInferenceRule},
    },
    unif_var::UnifVarKind, stdlib::StdLibObjs,
};

use super::{
    error::{ParseError, ParseErrorKind},
    expect_child,
    expr::gen_expr,
    next_children,
    pest_parser::{Node, NuprlParser, Rule},
    path::gen_lib_path,
};

pub fn parse_statements(source: TextSource, std_objs: &StdLibObjs) -> Result<Vec<Statement>, ParseError> {
    let root = NuprlParser::parse(Rule::root_statements, source.text())
        .map_err(|err| ParseError::from_pest_error(source, err))?
        .next();

    let root = expect_child(root);
    
    gen_statements(
        source,
        std_objs,
        expect_child(root.into_inner().next()),
    )
}

fn gen_statements(source: TextSource, std_objs: &StdLibObjs, node: Node) -> Result<Vec<Statement>, ParseError> {
    assert_eq!(node.as_rule(), Rule::statements);

    node
        .into_inner()
        .map(|child| gen_statement(source, std_objs, child))
        .collect()
}

fn gen_statement(source: TextSource, std_objs: &StdLibObjs, node: Node) -> Result<Statement, ParseError> {
    match node.as_rule() {
        Rule::statement => {
            gen_statement(source, std_objs, expect_child(node.into_inner().next()))
        },

        Rule::statement_import => {
            let span = source.make_span(node.as_span());
            let path = expect_child(node.into_inner().next());
            let path = gen_lib_path(path);
            Ok(Statement::Imp(path, span))
        },

        Rule::statement_def => {
            let whole_span = source.make_span(node.as_span());

            let [name, params, body] = next_children(&mut node.into_inner()).map(expect_child);

            let name = name.as_str().into();

            let params = params
                .into_inner()
                .map(|def_param| {
                    let [param, bindings] = next_children(&mut def_param.into_inner());
                    
                    let param = expect_child(param).as_str().into();

                    let bindings = bindings
                        .map(|bindings| bindings.into_inner()
                            .map(|ident| ident.as_str().into())
                            .collect())
                        .unwrap_or_default();

                    DefParam::new(bindings, param)
                })
                .collect();

            let body = gen_expr(std_objs, body);

            Ok(Statement::Def(NamedDef::new(name, params, body, whole_span)))
        },

        Rule::statement_theorem => {
            let span = source.make_span(node.as_span());

            let mut children = node.into_inner();

            let [name, goal, proof_trees] = next_children(&mut children);

            let name = expect_child(name).as_str().into();

            let goal_node = expect_child(goal);
            let goal_span = source.make_span(goal_node.as_span());
            let goal = gen_expr(std_objs, goal_node);

            let mut node_id_gen = ProofNodeIdGen::new();
            let proof_trees = expect_child(proof_trees);
            let proof_trees = gen_proof_trees(source, std_objs, proof_trees, &mut node_id_gen);

            // FIXME: reject more than one proof tree at the root
            let proof = proof_trees
                .into_iter()
                .next()
                .unwrap_or_else(|| OptGenericProof::new(None, goal_span, node_id_gen.next()));

            Ok(Statement::Thm(NamedUncheckedTheorem::new(name, goal, proof, span, goal_span)))
        },

        Rule::statement_exprkind => {
            let span = source.make_span(node.as_span());

            let [name, args, reductions] = next_children(&mut node.into_inner()).map(expect_child);

            let name = name.as_str().into();
            let args = gen_exprkind_args(args);
            let reductions = gen_beta_reductions(source, std_objs, reductions);

            Ok(Statement::Exp(NamedExprKindDef::new(name, args, reductions, span)))
        },

        // FIXME: there's a lot of logic in here for checking that the inf def is correctly formed,
        // which should probably be done at a later stage instead.
        Rule::statement_inf_def => {
            let span = source.make_span(node.as_span());
            
            let [name, params, substatements] = next_children(&mut node.into_inner())
                .map(expect_child);
            
            let name = name.as_str().into();
             
            assert_eq!(params.as_rule(), Rule::inf_def_params);

            let params = params
                .into_inner()
                .map(|param| {
                    assert_eq!(param.as_rule(), Rule::inf_def_param);

                    let param = expect_child(param.into_inner().next());

                    match param.as_rule() {
                        Rule::var_name_unif_var => {
                            let name = expect_child(param.into_inner().next());
                            NamedInfDefParam::Var(name.as_str().into())
                        },

                        Rule::expr => {
                            let expr = gen_expr(std_objs, param);
                            NamedInfDefParam::Expr(expr)
                        },
                        
                        rule => panic!("unexpected node type: {:?}", rule),
                    }
                })
                .collect::<Box<[_]>>();

            let mut goal = None;
            let mut ext = None;
            let mut subgoals = Vec::new();

            assert_eq!(substatements.as_rule(), Rule::inf_def_substatements);

            for substatement in substatements.into_inner() {
                assert_eq!(substatement.as_rule(), Rule::inf_def_substatement);

                let substatement = expect_child(substatement.into_inner().next());
                let substatement_span = source.make_span(substatement.as_span());

                match substatement.as_rule() {
                    Rule::inf_def_extract => {
                        if ext.is_some() {
                            return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceUnexpectedExt });
                        }
                        
                        ext = Some(gen_inf_def_extract(std_objs, substatement));
                    },

                    Rule::inf_def_goal => {
                        if goal.is_some() {
                            return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceUnexpectedGoal });
                        }

                        let substatements = expect_child(substatement.into_inner().next());
                        assert_eq!(substatements.as_rule(), Rule::inf_def_goal_substatements);
                        
                        let mut hys = Vec::new();
                        let mut concl = None;

                        for substatement in substatements.into_inner() {
                            assert_eq!(substatement.as_rule(), Rule::inf_def_goal_substatement);

                            let substatement = expect_child(substatement.into_inner().next());
                            let substatement_span = source.make_span(substatement.as_span());

                            match substatement.as_rule() {
                                Rule::inf_def_hypothesis => {
                                    let hy = gen_inf_def_hypothesis(std_objs, substatement);
                                    
                                    let hy = match hy {
                                        NamedHypothesisOp::Insert { pos, var, hy } => {
                                            NamedHypothesisPattern::Hypothesis { pos, var, hy }
                                        },
                                        NamedHypothesisOp::Remove { pos: _ } => {
                                            return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceBadHypothesisOp });
                                        },
                                        NamedHypothesisOp::Len { var } => {
                                            NamedHypothesisPattern::Len { var }
                                        },
                                    };

                                    hys.push(hy);
                                },

                                Rule::inf_def_conclusion => {
                                    if concl.is_some() {
                                        return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceUnexpectedConcl });
                                    }

                                    concl = Some(gen_inf_def_conclusion(std_objs, substatement));
                                }
                                
                                Rule::inf_def_extract => {
                                    if ext.is_some() {
                                        return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceUnexpectedExt });
                                    }

                                    ext = Some(gen_inf_def_extract(std_objs, substatement));
                                },

                                rule => panic!("unexpected node type: {:?}", rule),
                            }
                        }

                        let Some(concl) = concl else {
                            return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceMissingConcl });
                        };

                        goal = Some((hys.into_boxed_slice(), concl));
                    },

                    Rule::inf_def_subgoal => {
                        let substatements = expect_child(substatement.into_inner().next());
                        assert_eq!(substatements.as_rule(), Rule::inf_def_goal_substatements);

                        let mut hys = Vec::new();
                        let mut concl = None;
                        let mut ext = None;
                        
                        for substatement in substatements.into_inner() {
                            assert_eq!(substatement.as_rule(), Rule::inf_def_goal_substatement);

                            let substatement = expect_child(substatement.into_inner().next());
                            let substatement_span = source.make_span(substatement.as_span());

                            match substatement.as_rule() {
                                Rule::inf_def_hypothesis => {
                                    hys.push(gen_inf_def_hypothesis(std_objs, substatement));
                                },

                                Rule::inf_def_conclusion => {
                                    if concl.is_some() {
                                        return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceUnexpectedConcl });
                                    }

                                    concl = Some(gen_inf_def_conclusion(std_objs, substatement));
                                }
                                
                                Rule::inf_def_extract => {
                                    if ext.is_some() {
                                        return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceUnexpectedExt });
                                    }

                                    let ext_expr = gen_inf_def_extract(std_objs, substatement);

                                    match ext_expr {
                                        NamedExpr::UnifVar { var, kind: UnifVarKind::Any } => {
                                            ext = Some(var)
                                        },
                                        _ => {
                                            return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceBadExt });
                                        }
                                    }
                                },

                                rule => panic!("unexpected node type: {:?}", rule),
                            }
                        }

                        let Some(concl) = concl else {
                            return Err(ParseError { span: substatement_span, kind: ParseErrorKind::InferenceMissingConcl });
                        };

                        let subgoal = NamedInfDefSubgoal::new(
                            hys.into_boxed_slice(),
                            concl,
                            ext
                        );

                        subgoals.push(subgoal);
                    },
                    
                    rule => panic!("unexpected node type: {:?}", rule),
                }
            }

            let Some((goal_hys, goal_concl)) = goal else {
                return Err(ParseError { span, kind: ParseErrorKind::InferenceMissingGoal });
            };

            let Some(ext) = ext else {
                return Err(ParseError { span, kind: ParseErrorKind::InferenceMissingExt });
            };

            Ok(Statement::Inf(NamedInfDef::new(
                name,
                params,
                goal_hys,
                goal_concl,
                subgoals.into_boxed_slice(),
                ext,
                span
            )))
        },

        Rule::statement_intrinsic => {
            let span = source.make_span(node.as_span());

            let [name] = next_children(&mut node.into_inner()).map(expect_child);
            let name = name.as_str().into();

            Ok(Statement::Intrinsic(name, span))
        },

        rule => panic!("unexpected node type: {:?}", rule),
    }
}

fn gen_proof_trees(
    source: TextSource,
    std_objs: &StdLibObjs,
    node: Node,
    id_gen: &mut ProofNodeIdGen
) -> Vec<OptGenericProof>
{
    assert_eq!(node.as_rule(), Rule::proof_trees);

    node
        .into_inner()
        .map(|child| gen_proof_tree(source, std_objs, child, id_gen))
        .collect()
}

fn gen_proof_tree(source: TextSource, std_objs: &StdLibObjs, node: Node, id_gen: &mut ProofNodeIdGen) -> OptGenericProof {
    assert_eq!(node.as_rule(), Rule::proof_node);
    
    let id = id_gen.next();
    let root_span = RangeSpan::from(node.as_span());

    let node = expect_child(node.into_inner().next());

    let (proof, span) = match node.as_rule() {
        Rule::proof_tree => {
            let mut children = node.into_inner();
            
            let rule = expect_child(children.next());
            
            let rule_span = RangeSpan::from(rule.as_span());
            
            let rule = gen_inf_rule(std_objs, rule);
            
            let proof_children = children
                .next()
                .map(|child| gen_proof_trees(source, std_objs, child, id_gen))
                .unwrap_or_default();
            
            let proof = GenericProof::new(rule, proof_children);

            (Some(proof), rule_span)
        },

        Rule::proof_hole => {
            (None, root_span)
        },

        rule => panic!("unexpected node type: {:?}", rule),
    };

    let span = source.make_span(span);

    OptGenericProof::new(proof, span, id)
}

fn gen_inf_rule(std_objs: &StdLibObjs, node: Node) -> NamedInferenceRule {
    assert_eq!(node.as_rule(), Rule::inference_rule);

    let mut children = node.into_inner();

    let name = expect_child(children.next());
    let name = gen_lib_path(name);
    let args = children.map(|node| gen_expr(std_objs, node)).collect();

    NamedInferenceRule::new(name, args)
}

fn gen_exprkind_args(node: Node) -> Rc<[ExprKindDefParam]> {
    assert_eq!(node.as_rule(), Rule::exprkind_args);

    node
        .into_inner()
        .map(gen_exprkind_arg)
        .collect()
}

fn gen_exprkind_arg(node: Node) -> ExprKindDefParam {
    assert_eq!(node.as_rule(), Rule::exprkind_arg);

    let node = expect_child(node.into_inner().next());

    let (name, principal) = match node.as_rule() {
        Rule::exprkind_arg_principal => {
            let child = expect_child(node.into_inner().next());
            assert_eq!(child.as_rule(), Rule::ident);
            (child.as_str().into(), true)
        },
        Rule::ident => {
            (node.as_str().into(), false)
        },
        rule => panic!("unexpected node type: {:?}", rule),
    };

    ExprKindDefParam::new(name, principal)
}

fn gen_beta_reductions(source: TextSource, std_objs: &StdLibObjs, node: Node) -> Box<[NamedBetaReduction]> {
    assert_eq!(node.as_rule(), Rule::beta_reductions);
    
    node
        .into_inner()
        .map(|child| gen_beta_reduction(source,  std_objs, child))
        .collect()
}

fn gen_beta_reduction(source: TextSource, std_objs: &StdLibObjs, node: Node) -> NamedBetaReduction {
    assert_eq!(node.as_rule(), Rule::beta_reduction);

    let span = source.make_span(node.as_span());

    let [target, reduced] = next_children(&mut node.into_inner())
        .map(|child| {
            let child = expect_child(child);
            gen_expr(std_objs, child)
        });

    NamedBetaReduction::new(target, reduced, span)
}

fn gen_inf_def_extract(std_objs: &StdLibObjs, node: Node) -> NamedExpr {
    assert_eq!(node.as_rule(), Rule::inf_def_extract);

    let node = expect_child(node.into_inner().next());

    gen_expr(std_objs, node)
}

fn gen_inf_def_conclusion(std_objs: &StdLibObjs, node: Node) -> NamedExpr {
    assert_eq!(node.as_rule(), Rule::inf_def_conclusion);

    let node = expect_child(node.into_inner().next());

    gen_expr(std_objs, node)
}

fn gen_inf_def_hypothesis(std_objs: &StdLibObjs, node: Node) -> NamedHypothesisOp {
    assert_eq!(node.as_rule(), Rule::inf_def_hypothesis);

    let node = expect_child(node.into_inner().next());

    match node.as_rule() {
        Rule::inf_def_hypothesis_insert => {
            let [var, hy, pos] = next_children(&mut node.into_inner()).map(expect_child);

            assert_eq!(var.as_rule(), Rule::unif_var);
            let var = expect_child(var.into_inner().next());
            assert_eq!(var.as_rule(), Rule::ident);
            let var = var.as_str().into();

            let hy = gen_expr(std_objs, hy);

            let pos = gen_expr(std_objs, pos);

            NamedHypothesisOp::Insert { pos, var, hy }
        },

        Rule::inf_def_hypothesis_remove => {
            let pos = expect_child(node.into_inner().next());

            let pos = gen_expr(std_objs, pos);

            NamedHypothesisOp::Remove { pos }
        },

        Rule::inf_def_hypothesis_len => {
            let var = expect_child(node.into_inner().next());
            assert_eq!(var.as_rule(), Rule::unif_var);
            let var = expect_child(var.into_inner().next());
            assert_eq!(var.as_rule(), Rule::ident);
            let var = var.as_str().into();

            NamedHypothesisOp::Len { var }
        },
        
        rule => panic!("unexpected node type: {:?}", rule),
    }
}
