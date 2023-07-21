use pest::iterators::{Pair, Pairs};

#[derive(pest_derive::Parser)]
#[grammar = "grammar/grammar.pest"]
pub(super) struct NuprlParser;

pub(super) type Node<'i> = Pair<'i, Rule>;

pub(super) type Nodes<'i> = Pairs<'i, Rule>;
