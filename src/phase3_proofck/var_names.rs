use std::{borrow::Cow, rc::Rc};

use crate::de_bruijn::DeBruijnIndex;

use super::{expr::RcExpr, hypothesis::{HypothesisId, Hypotheses}};

#[derive(Clone, Debug)]
pub struct NameAssignments {
    hypotheses: Vec<(HypothesisId, Rc<str>)>,
    variables: Vec<Option<Rc<str>>>,
}

impl NameAssignments {
    pub fn new() -> Self {
        Self {
            hypotheses: Vec::new(),
            variables: Vec::new(),
        }
    }

    pub fn from_hypotheses(hypotheses: &Hypotheses) -> Self {
        let hypotheses = hypotheses
            .iter()
            .map(|hy_entry| (hy_entry.id, hy_entry.hy.var().clone()))
            .collect();

        Self {
            hypotheses,
            variables: Vec::new(),
        }
    }

    pub fn push_hypothesis_name(&mut self, id: HypothesisId, name: Rc<str>) {
        self.hypotheses.push((id, name));
    }

    pub fn push_hypothesis_names<I>(&mut self, names: I)
    where
        I: Iterator<Item = (HypothesisId, Rc<str>)>,
    {
        self.hypotheses.extend(names.into_iter())
    }

    pub fn push_var_name(&mut self, var: Option<Rc<str>>) {
        self.variables.push(var);
    }

    pub fn pop_var_name(&mut self) {
        self.variables.pop();
    }

    pub fn can_use_name(&self, expr: &RcExpr, name: &str) -> bool {
        if self.variables
            .iter()
            .flatten()
            .any(|var| var.as_ref() == name)
        {
            return false;
        }

        if self
            .hypotheses
            .iter()
            .any(|(id, hy)| hy.as_ref() == name && expr.contains_hypothesis(*id))
        {
            return false;
        }

        true
    }

    pub fn find_available_name(
        &self,
        expr: &RcExpr,
        user_chosen_name: Option<Rc<str>>
    ) -> Rc<str>
    {
        if let Some(user_chosen_name) = user_chosen_name {
            if self.can_use_name(expr, &user_chosen_name) {
                return user_chosen_name;
            }
        }

        let mut n = 0usize;

        loop {
            let name = nth_var_name(n);
            if self.can_use_name(expr, &name) {
                return name.into();
            }

            // Panic if we run out of variable names.
            n = n.checked_add(1).unwrap();
        }
    }

    pub fn hypothesis_name(&self, id: HypothesisId) -> Option<&Rc<str>> {
        self.hypotheses
            .iter()
            .find_map(|(named_hy_id, named_hy)| (*named_hy_id == id).then_some(named_hy))
    }

    pub fn var_name(&self, index: DeBruijnIndex) -> Option<&Rc<str>> {
        self.variables
            .len()
            .checked_sub(1)
            .and_then(|i| i.checked_sub(index.get()))
            .and_then(|i| self.variables
                .get(i)
                .map(Option::as_ref)
                .flatten())
    }
}

fn nth_var_name(n: usize) -> Cow<'static, str> {
    match n {
        0 => Cow::Borrowed("x"),
        1 => Cow::Borrowed("y"),
        2 => Cow::Borrowed("z"),
        3 => Cow::Borrowed("w"),
        4 => Cow::Borrowed("p"),
        5 => Cow::Borrowed("q"),
        6 => Cow::Borrowed("r"),
        7 => Cow::Borrowed("s"),
        8 => Cow::Borrowed("t"),
        9 => Cow::Borrowed("i"),
        10 => Cow::Borrowed("j"),
        11 => Cow::Borrowed("k"),
        n => Cow::Owned(format!("var{}", n - 11)),
    }
}
