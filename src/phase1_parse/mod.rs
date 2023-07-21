pub mod error;
mod expr;
mod path;
mod pest_parser;
mod statement;

pub use expr::parse_expr;
pub use statement::parse_statements;

use pest_parser::{Node, Nodes};

fn expect_child(child_node: Option<Node>) -> Node {
    child_node.expect("node had fewer children than expected")
}

fn next_children<'i, const N: usize>(children_iter: &mut Nodes<'i>) -> [Option<Node<'i>>; N] {
    const NONE: Option<Node> = None;

    let mut children = [NONE; N];
    for (i, child) in children_iter.take(N).enumerate() {
        children[i] = Some(child);
    }

    children
}
