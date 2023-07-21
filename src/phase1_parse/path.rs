use crate::path::path::{LibPathBuf, LibPathNode};

use super::{pest_parser::{Node, Rule}, expect_child, next_children};

pub(super) fn gen_lib_path(node: Node) -> LibPathBuf {
    assert_eq!(node.as_rule(), Rule::ident_path);
    
    let node = expect_child(node.into_inner().next());

    let (node, absolute) = match node.as_rule() {
        Rule::absolute_ident_path => (expect_child(node.into_inner().next()), true),
        Rule::relative_ident_path => (node, false),
        rule => panic!("unexpected node type: {:?}", rule),
    };

    let nodes = node
        .into_inner()
        .map(gen_lib_path_node)
        .collect();

    LibPathBuf::new(nodes, absolute)
}

fn gen_lib_path_node(node: Node) -> LibPathNode {
    assert_eq!(node.as_rule(), Rule::ident_path_node);

    let [node] = next_children(&mut node.into_inner()).map(expect_child);

    match node.as_rule() {
        Rule::ident_path_node_super => LibPathNode::Super,
        Rule::ident_path_node_module => LibPathNode::Module,
        Rule::ident => LibPathNode::Named(node.as_str().into()),
        rule => panic!("unexpected node type: {:?}", rule),
    }
}
