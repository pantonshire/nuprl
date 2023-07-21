use pest::Parser;

use crate::{
    phase2_nameres::expr::NamedExpr,
    source::TextSource,
    unif_var::UnifVarKind,
    phase3_proofck::expr::ReductionSteps,
    stdlib::StdLibObjs,
};

use super::{
    error::ParseError,
    expect_child,
    next_children,
    pest_parser::{Node, NuprlParser, Rule},
    path::gen_lib_path,
};

pub fn parse_expr(source: TextSource, std_objs: &StdLibObjs) -> Result<NamedExpr, ParseError> {
    let root = NuprlParser::parse(Rule::root_expr, source.text())
        .map_err(|err| ParseError::from_pest_error(source, err))?
        .next();

    let root = expect_child(root);
    let expr = expect_child(root.into_inner().next());
    
    Ok(gen_expr(std_objs, expr))
}

pub(super) fn gen_expr(std_objs: &StdLibObjs, node: Node) -> NamedExpr {
    match node.as_rule() {
        Rule::expr
        | Rule::expr_isect_type
        | Rule::expr_func_type
        | Rule::expr_prod_type
        | Rule::expr_neg
        | Rule::expr_base => {
            // These node types all have a single child node which we can recurse on.
            gen_expr(std_objs, expect_child(node.into_inner().next()))
        },

        Rule::expr_eq_type => {
            let mut children = node.into_inner();

            let lhs = gen_expr(std_objs, expect_child(children.next()));

            match children.next() {
                Some(rhs) => {
                    let rhs = gen_expr(std_objs, rhs);
                    let ty = gen_expr(std_objs, expect_child(children.next()));
                    NamedExpr::Obj {
                        // FIXME: return an error instead of panic
                        id: std_objs.eq.unwrap(),
                        args: [ty, lhs, rhs].into(),
                    }
                }

                None => lhs,
            }
        },

        Rule::isect_type => {
            let [var, lhs, rhs] = next_children(&mut node.into_inner()).map(expect_child);
            let var = var.as_str().into();
            let [lhs, rhs] = [lhs, rhs].map(|expr| gen_expr(std_objs, expr));
            NamedExpr::Obj {
                id: std_objs.isect.unwrap(),
                args: [lhs, NamedExpr::Bound { var, body: rhs.boxed() }].into(),
            }
        },

        Rule::dep_func_type => {
            let [var, domain, codomain] = next_children(&mut node.into_inner()).map(expect_child);

            let var = var.as_str().into();

            let [domain, codomain] = [domain, codomain].map(|expr| gen_expr(std_objs, expr));

            NamedExpr::Obj {
                id: std_objs.func.unwrap(),
                args: [domain, NamedExpr::Bound { var, body: codomain.boxed() }].into(),
            }
        },

        Rule::indep_func_type => {
            let mut children = node.into_inner();

            let domain = gen_expr(std_objs, expect_child(children.next()));

            match children.next() {
                Some(codomain) => {
                    let codomain = gen_expr(std_objs, codomain);
                    NamedExpr::Obj {
                        id: std_objs.func.unwrap(),
                        args: [domain, codomain].into(),
                    }
                }

                None => domain,
            }
        },

        Rule::expr_sum_type => {
            let mut children = node.into_inner();

            let lhs = gen_expr(std_objs, expect_child(children.next()));

            match children.next() {
                Some(rhs) => {
                    let rhs = gen_expr(std_objs, rhs);
                    NamedExpr::Obj {
                        id: std_objs.sum.unwrap(),
                        args: [lhs, rhs].into(),
                    }
                }

                None => lhs,
            }
        },

        Rule::dep_prod_type => {
            let [var, lhs, rhs] = next_children(&mut node.into_inner()).map(expect_child);
            let var = var.as_str().into();
            let [lhs, rhs] = [lhs, rhs].map(|expr| gen_expr(std_objs, expr));
            NamedExpr::Obj {
                id: std_objs.prod.unwrap(),
                args: [lhs, NamedExpr::Bound { var, body: rhs.boxed() }].into(),
            }
        },

        Rule::indep_prod_type => {
            let mut children = node.into_inner();

            let lhs = gen_expr(std_objs, expect_child(children.next()));

            match children.next() {
                Some(rhs) => {
                    let rhs = gen_expr(std_objs, rhs);
                    NamedExpr::Obj {
                        id: std_objs.prod.unwrap(),
                        args: [lhs, rhs].into(),
                    }
                }

                None => lhs,
            }
        },

        Rule::expr_lt_type => {
            let mut children = node.into_inner();

            let lhs = gen_expr(std_objs, expect_child(children.next()));

            match children.next() {
                Some(rhs) => {
                    let _rhs = gen_expr(std_objs, rhs);
                    
                    // NamedExpr::LtTy {
                    //     lhs: lhs.boxed(),
                    //     rhs,
                    // }
                    unimplemented!()
                }

                None => lhs,
            }
        },

        Rule::expr_add | Rule::expr_mul => {
            let mut children = node.into_inner();

            let mut expr = gen_expr(std_objs, expect_child(children.next()));

            while let Some(op) = children.next() {
                let (op, negate) = match op.as_str() {
                    "+" => (std_objs.add.unwrap(), false),
                    "-" => (std_objs.add.unwrap(), true),
                    "*" => (std_objs.mul.unwrap(), false),
                    "div" => (std_objs.div.unwrap(), false),
                    "rem" => (std_objs.rem.unwrap(), false),
                    op => panic!("invalid binary operator: {}", op),
                };

                let mut rhs = gen_expr(std_objs, expect_child(children.next()));

                if negate {
                    rhs = NamedExpr::Obj {
                        id: std_objs.neg.unwrap(),
                        args: [rhs].into(),
                    };
                }

                expr = NamedExpr::Obj {
                    id: op,
                    args: [expr, rhs].into(),
                }
            }

            expr
        },

        Rule::expr_app => {
            let mut children = node.into_inner();

            let mut expr = gen_expr(std_objs, expect_child(children.next()));

            for child in children {
                let rhs = gen_expr(std_objs, child).boxed();
                expr = NamedExpr::Jux {
                    lhs: expr.boxed(),
                    rhs,
                }
            }

            expr
        },
        
        Rule::expr_subst => {
            let mut children = node.into_inner();

            let first_child = expect_child(children.next());

            match children.next() {
                Some(bound) => {
                    let bound = gen_expr(std_objs, bound).boxed();

                    let args = first_child;
                    assert_eq!(args.as_rule(), Rule::subst_args);

                    let args = args
                        .into_inner()
                        .map(|node| gen_expr(std_objs, node))
                        .collect();

                    NamedExpr::Subst { bound, args }
                },

                None => {
                    gen_expr(std_objs, first_child)
                },
            }
        },

        Rule::dep => {
            let [var, body] = next_children(&mut node.into_inner()).map(expect_child);
            let var = var.as_str().into();
            let body = gen_expr(std_objs, body).boxed();
            NamedExpr::Bound { var, body }
        },

        Rule::unif_var => {
            let mut children = node.into_inner();
            let name = expect_child(children.next());

            let kind = match children.next().map(|child| child.as_str()) {
                None => UnifVarKind::Any,
                Some("n") => UnifVarKind::Nat,
                Some(kind) => panic!("unexpected unif var kind: `{}`", kind),
            };

            NamedExpr::UnifVar { var: name.as_str().into(), kind }
        },

        Rule::tag => {
            let [steps, body] = next_children(&mut node.into_inner()).map(expect_child);
            let steps = match steps.as_rule() {
                Rule::nat => {
                    let n = steps.as_str().parse::<u64>().expect("invalid natural number");
                    ReductionSteps::Finite(n)
                },
                Rule::reduce_all => ReductionSteps::Infinite,
                rule => panic!("unexpected node type: {:?}", rule),
            };
            let body = gen_expr(std_objs, body).boxed();
            NamedExpr::Tag { steps, body }
        },

        Rule::negation => {
            let body = gen_expr(std_objs, expect_child(node.into_inner().next()));
            NamedExpr::Obj {
                id: std_objs.neg.unwrap(),
                args: [body].into(),
            }
        },

        Rule::abstraction => {
            let [var, body] = next_children(&mut node.into_inner()).map(expect_child);
            let var = var.as_str().into();
            let body = gen_expr(std_objs, body).boxed();
            NamedExpr::Obj {
                id: std_objs.lambda.unwrap(),
                args: [NamedExpr::Bound { var, body }].into(),
            }
        },

        Rule::spread => {
            let [vars, pair, body] = next_children(&mut node.into_inner()).map(expect_child);
            
            let [pair, body] = [pair, body].map(|child| gen_expr(std_objs, child));
            
            let [lhs_var, rhs_var] = next_children(&mut vars.into_inner())
                .map(|child| expect_child(child).as_str().into());
            
            NamedExpr::Obj {
                id: std_objs.spread.unwrap(),
                args: [pair, NamedExpr::Bound {
                    var: lhs_var,
                    body: NamedExpr::Bound {
                        var: rhs_var,
                        body: body.boxed(),
                    }.boxed(),
                }].into(),
            }
        },

        Rule::call_by_value => {
            let [var, val, body] = next_children(&mut node.into_inner()).map(expect_child);
            let [val, body] = [val, body].map(|child| gen_expr(std_objs, child));
            let var = var.as_str().into();
            NamedExpr::Obj {
                id: std_objs.cbv.unwrap(),
                args: [val, NamedExpr::Bound { var, body: body.into() }].into(),
            }
        },

        Rule::decide => {
            let [sum, inl_var, inl_case, inr_var, inr_case] =
                next_children(&mut node.into_inner()).map(expect_child);

            let [sum, inl_case, inr_case] =
                [sum, inl_case, inr_case].map(|child| gen_expr(std_objs, child));

            let [inl_var, inr_var] = [inl_var, inr_var].map(|child| child.as_str().into());

            NamedExpr::Obj {
                id: std_objs.decide.unwrap(),
                args: [
                    sum,
                    NamedExpr::Bound { var: inl_var, body: inl_case.boxed() },
                    NamedExpr::Bound { var: inr_var, body: inr_case.boxed() },
                ].into(),
            }
        },

        Rule::compare => {
            let [lhs, op, rhs, l_case, r_case] =
                next_children(&mut node.into_inner()).map(expect_child);

            let [lhs, rhs, l_case, r_case] =
                [lhs, rhs, l_case, r_case].map(|child| gen_expr(std_objs, child));

            let op = match op.as_str() {
                "=" => std_objs.compare_eq.unwrap(),
                "<" => std_objs.compare_lt.unwrap(),
                op => panic!("invalid comparison operator: {}", op),
            };

            NamedExpr::Obj {
                id: op, 
                args: [lhs, rhs, l_case, r_case].into(),
            }
        },

        Rule::pair => {
            let [lhs, rhs] = next_children(&mut node.into_inner())
                .map(expect_child)
                .map(|child| gen_expr(std_objs, child));

            NamedExpr::Obj {
                id: std_objs.pair.unwrap(),
                args: [lhs, rhs].into(),
            }
        },

        Rule::second_order_var => {
            let [ident, bindings] = next_children(&mut node.into_inner())
                .map(expect_child);
            
            let ident = gen_lib_path(ident);

            let bindings = bindings.into_inner()
                .map(gen_lib_path)
                .collect();

            NamedExpr::SecondOrderVar { name: ident, mapping: bindings }
        },

        Rule::ident_path => {
            let object_path = gen_lib_path(node);
            NamedExpr::Var(object_path)
        },

        Rule::nat => {
            let n = node.as_str().parse().expect("invalid natural number");
            NamedExpr::Nat(n)
        },

        Rule::token => {
            // FIXME: iterate over children & check if they are escaped or not
            let body = expect_child(node.into_inner().next());

            let mut buf = String::new();
            for child in body.into_inner() {
                match child.as_rule() {
                    Rule::escaped_token_char => {
                        let escaped = expect_child(child.into_inner().next());
                        // FIXME: match on escaped to see what to do with it
                        match escaped.as_str() {
                            "n" => buf.push('\n'),
                            "r" => buf.push('\r'),
                            "t" => buf.push('\t'),
                            "0" => buf.push('\0'),
                            escaped => buf.push_str(escaped),
                        }
                    },
                    Rule::token_char => {
                        buf.push_str(child.as_str());
                    },
                    rule => panic!("unexpected node type: {:?}", rule),
                }
            }

            NamedExpr::Tok(buf.into())
        },

        rule => panic!("unexpected node type: {:?}", rule),
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use crate::{load_stdlib, source::{Source, SourceIdGen, SourceModule, SourceKind}, path::path::{CanonLibPathBuf, LibPathBuf}, phase2_nameres::expr::NamedExpr, phase1_parse::parse_expr};

    #[test]
    fn test_parse() {
        let stdlib = load_stdlib();
        let std_objs = stdlib.std_objs();

        let expr_from_str = |s: &'static str| {
            let source = Source::new(
                SourceIdGen::new().next_id(),
                SourceModule::Custom(CanonLibPathBuf::root()),
                SourceKind::NuprlSrc,
                Cow::Borrowed(s.as_bytes())
            ).unwrap();

            let source = source.text_source().unwrap();

            parse_expr(source, std_objs).unwrap()
        };

        assert_eq!(
            expr_from_str("1"),
            NamedExpr::Nat(1)
        );

        assert_eq!(
            expr_from_str("\"hello\""),
            NamedExpr::Tok("hello".into())
        );

        assert_eq!(
            expr_from_str("\"hello\\n\\\"world\\\"\""),
            NamedExpr::Tok("hello\n\"world\"".into())
        );

        assert_eq!(
            expr_from_str("x"),
            NamedExpr::Var(LibPathBuf::new_unitary("x".into()))
        );

        assert_eq!(
            expr_from_str("x. x"),
            NamedExpr::Bound {
                var: "x".into(),
                body: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed(),
            }
        );

        assert_eq!(
            expr_from_str("x. x y"),
            NamedExpr::Bound {
                var: "x".into(),
                body: NamedExpr::Jux {
                    lhs: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed(),
                    rhs: NamedExpr::Var(LibPathBuf::new_unitary("y".into())).boxed(),
                }.boxed(),
            }
        );

        assert_eq!(
            expr_from_str("[y]x"),
            NamedExpr::Subst {
                bound: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("y".into()))
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("[y, z]x"),
            NamedExpr::Subst {
                bound: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("y".into())),
                    NamedExpr::Var(LibPathBuf::new_unitary("z".into()))
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("1 + 2"),
            NamedExpr::Obj {
                id: std_objs.add.unwrap(),
                args: [
                    NamedExpr::Nat(1),
                    NamedExpr::Nat(2),
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("1 + 2 * 3"),
            NamedExpr::Obj {
                id: std_objs.add.unwrap(),
                args: [
                    NamedExpr::Nat(1),
                    NamedExpr::Obj {
                        id: std_objs.mul.unwrap(),
                        args: [
                            NamedExpr::Nat(2),
                            NamedExpr::Nat(3),
                        ].into(),
                    }
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("1 * 2 + 3"),
            NamedExpr::Obj {
                id: std_objs.add.unwrap(),
                args: [
                    NamedExpr::Obj {
                        id: std_objs.mul.unwrap(),
                        args: [
                            NamedExpr::Nat(1),
                            NamedExpr::Nat(2),
                        ].into(),
                    },
                    NamedExpr::Nat(3),
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("1 * (2 + 3)"),
            NamedExpr::Obj {
                id: std_objs.mul.unwrap(),
                args: [
                    NamedExpr::Nat(1),
                    NamedExpr::Obj {
                        id: std_objs.add.unwrap(),
                        args: [
                            NamedExpr::Nat(2),
                            NamedExpr::Nat(3),
                        ].into(),
                    },
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("\\y. y x"),
            NamedExpr::Obj {
                id: std_objs.lambda.unwrap(),
                args: [
                    NamedExpr::Bound {
                        var: "y".into(),
                        body: NamedExpr::Jux {
                            lhs: NamedExpr::Var(LibPathBuf::new_unitary("y".into())).boxed(),
                            rhs: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed(),
                        }.boxed(),
                    },
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("(\\y. y) x"),
            NamedExpr::Jux {
                lhs: NamedExpr::Obj {
                    id: std_objs.lambda.unwrap(),
                    args: [
                        NamedExpr::Bound {
                            var: "y".into(),
                            body: NamedExpr::Var(LibPathBuf::new_unitary("y".into())).boxed(),
                        },
                    ].into(),
                }.boxed(),
                rhs: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed(),
            }
        );

        assert_eq!(
            expr_from_str("<1, 2>"),
            NamedExpr::Obj {
                id: std_objs.pair.unwrap(),
                args: [
                    NamedExpr::Nat(1),
                    NamedExpr::Nat(2),
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("A -> B"),
            NamedExpr::Obj {
                id: std_objs.func.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("A".into())),
                    NamedExpr::Var(LibPathBuf::new_unitary("B".into())),
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("x: A -> B"),
            NamedExpr::Obj {
                id: std_objs.func.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("A".into())),
                    NamedExpr::Bound {
                        var: "x".into(),
                        body: NamedExpr::Var(LibPathBuf::new_unitary("B".into())).boxed(),
                    },
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("A -> B -> C"),
            NamedExpr::Obj {
                id: std_objs.func.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("A".into())),
                    NamedExpr::Obj {
                        id: std_objs.func.unwrap(),
                        args: [
                            NamedExpr::Var(LibPathBuf::new_unitary("B".into())),
                            NamedExpr::Var(LibPathBuf::new_unitary("C".into())),
                        ].into(),
                    },
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("A # B"),
            NamedExpr::Obj {
                id: std_objs.prod.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("A".into())),
                    NamedExpr::Var(LibPathBuf::new_unitary("B".into())),
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("x: A # B"),
            NamedExpr::Obj {
                id: std_objs.prod.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("A".into())),
                    NamedExpr::Bound {
                        var: "x".into(),
                        body: NamedExpr::Var(LibPathBuf::new_unitary("B".into())).boxed(),
                    },
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("A | B"),
            NamedExpr::Obj {
                id: std_objs.sum.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("A".into())),
                    NamedExpr::Var(LibPathBuf::new_unitary("B".into())),
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("x: A & B"),
            NamedExpr::Obj {
                id: std_objs.isect.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("A".into())),
                    NamedExpr::Bound {
                        var: "x".into(),
                        body: NamedExpr::Var(LibPathBuf::new_unitary("B".into())).boxed(),
                    },
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("1 = x in T"),
            NamedExpr::Obj {
                id: std_objs.eq.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("T".into())),
                    NamedExpr::Nat(1),
                    NamedExpr::Var(LibPathBuf::new_unitary("x".into())),
                ].into(),
            }
        );

        assert_eq!(
            expr_from_str("1 + 2 = x + 2 in T"),
            NamedExpr::Obj {
                id: std_objs.eq.unwrap(),
                args: [
                    NamedExpr::Var(LibPathBuf::new_unitary("T".into())),
                    NamedExpr::Obj {
                        id: std_objs.add.unwrap(),
                        args: [
                            NamedExpr::Nat(1),
                            NamedExpr::Nat(2),
                        ].into(),
                    },
                    NamedExpr::Obj {
                        id: std_objs.add.unwrap(),
                        args: [
                            NamedExpr::Var(LibPathBuf::new_unitary("x".into())),
                            NamedExpr::Nat(2),
                        ].into(),
                    },
                ].into(),
            }
        );
    }
}
