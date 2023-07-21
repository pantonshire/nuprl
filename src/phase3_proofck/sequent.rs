use rkyv::{Archive, Serialize, Deserialize};

use super::{hypothesis::{Hypotheses, HypothesisEntryRef}, expr::RcExpr, var_names::NameAssignments, library::Context};

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct Sequent {
    hypotheses: Hypotheses,
    conclusion: RcExpr,
}

impl Sequent {
    pub fn new(hypotheses: Hypotheses, conclusion: RcExpr) -> Self {
        Self { hypotheses, conclusion }
    }

    pub fn seq_ref(&self) -> SequentRef {
        SequentRef::new(&self.hypotheses, &self.conclusion)
    }

    pub fn hys(&self) -> &Hypotheses {
        &self.hypotheses
    }

    pub fn concl(&self) -> &RcExpr {
        &self.conclusion
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SequentRef<'a> {
    hypotheses: &'a Hypotheses,
    conclusion: &'a RcExpr,
}

impl<'a> SequentRef<'a> {
    pub fn new(hypotheses: &'a Hypotheses, conclusion: &'a RcExpr) -> Self {
        Self { hypotheses, conclusion }
    }

    pub fn hys(self) -> &'a Hypotheses {
        self.hypotheses
    }

    pub fn concl(self) -> &'a RcExpr {
        self.conclusion
    }

    pub fn display(&self, ctx: Context) -> DisplaySequent {
        let mut names = NameAssignments::new();
        let mut hypotheses_ser = Vec::new();

        for HypothesisEntryRef { id, hy } in self.hypotheses.iter() {
            let mut ty_buf = String::new();
            hy.ty().format(&mut ty_buf, ctx, &mut names).unwrap();

            hypotheses_ser.push(DisplayHypothesis {
                var: hy.var().as_ref().to_owned(),
                ty: ty_buf,
                hidden: hy.visibility().is_hidden(),
            });

            names.push_hypothesis_name(id, hy.var().clone());
        }

        let mut concl_buf = String::new();
        self.conclusion.format(&mut concl_buf, ctx, &mut names).unwrap();

        DisplaySequent {
            hys: hypotheses_ser,
            concl: concl_buf,
        }
    }
}

#[derive(serde::Serialize, Debug)]
#[serde(rename = "Hypothesis")]
pub struct DisplayHypothesis {
    var: String,
    ty: String,
    hidden: bool,
}

#[derive(serde::Serialize, Debug)]
#[serde(rename = "Sequent")]
pub struct DisplaySequent {
    hys: Vec<DisplayHypothesis>,
    concl: String,
}
