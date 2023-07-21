use std::{collections::{HashMap, hash_map, HashSet}, rc::Rc, iter, error, fmt};

use rkyv::{Archive, Serialize, Deserialize};

use crate::{utils::ComparePtr, object_id::ObjectId};

use super::path::{CanonLibPathBuf, LibPathBuf, LibPathNode, CanonLibPath};

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
#[archive(bound(serialize = "__S: rkyv::ser::Serializer + rkyv::ser::ScratchSpace + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "__D: rkyv::de::SharedDeserializeRegistry"))]
pub enum NameTree {
    Module {
        #[omit_bounds]
        subtrees: HashMap<Rc<str>, NameTree>,
    },
    Object {
        id: ObjectId,
        params: usize,
    },
    Alias {
        ctx: CanonLibPathBuf,
        path: LibPathBuf,
    },
}

impl NameTree {
    pub fn empty_module() -> Self {
        Self::Module { subtrees: HashMap::new() }
    }

    pub fn reroot(&mut self, new_root: &CanonLibPath) {
        match self {
            Self::Module { subtrees } => {
                for subtree in subtrees.values_mut() {
                    subtree.reroot(new_root);
                }
            },
            Self::Object { id: _, params: _ } => (),
            Self::Alias { ctx, path: _ } => {
                *ctx = ctx.rerooted(new_root);
            },
        }
    }

    pub fn get_obj(&self, ctx: &CanonLibPath, path: &LibPathBuf)
        -> Result<(ObjectId, CanonLibPathBuf, usize), NameTreeError>
    {
        let mut ctx = ctx;
        let mut path = path;
        let mut visited = HashSet::new();

        loop {
            let tree_stack = self.get_subtree_stack(ctx, path)?;

            let subtree = tree_stack
                .last()
                .map(|(_, subtree)| subtree)
                .copied()
                .unwrap_or(self);

            if visited.contains(&ComparePtr(subtree)) {
                let err_path = tree_stack.iter().map(|(node, _)| *node).collect();
                return Err(NameTreeError::Cycle(err_path));
            }

            match subtree {
                Self::Module { subtrees: _ } => {
                    let err_path = tree_stack.iter().map(|(node, _)| *node).collect();
                    return Err(NameTreeError::ExpectedObject(err_path));
                },

                Self::Object { id, params } => {
                    let path = tree_stack.iter().map(|(node, _)| *node).collect();
                    break Ok((*id, path, *params));
                },
                
                Self::Alias { ctx: new_ctx, path: new_path } => {
                    visited.insert(ComparePtr(subtree));
                    ctx = new_ctx;
                    path = new_path;
                },
            }
        }
    }

    pub fn get_subtree_stack<'s>(&'s self, ctx: &CanonLibPath, path: &LibPathBuf)
        -> Result<Vec<(&'s str, &'s Self)>, NameTreeError>
    {
        let mut nodes = path.nodes().iter();

        let mut tree_stack = if path.absolute() {
            Vec::new()
        } else {
            match nodes.next() {
                Some(LibPathNode::Module) => {
                    self.subtrees_for_path(ctx)?
                },
                
                Some(LibPathNode::Super) => {
                    let mut tree_stack = self.subtrees_for_path(ctx)?;
                    tree_stack.pop();
                    tree_stack
                },
                
                Some(LibPathNode::Named(name)) => 'search_named: {
                    // First, see if we can find the name in the current context (`ctx`) module.
                    'search_named_ctx: {
                        let Ok(mut tree_stack) = self.subtrees_for_path(ctx) else {
                            break 'search_named_ctx
                        };
    
                        let NameTree::Module { subtrees: ctx_module } = tree_stack
                            .last()
                            .map(|(_, subtree)| subtree)
                            .copied()
                            .unwrap_or(self)
                        else {
                            break 'search_named_ctx
                        };
    
                        let Some((key, subtree)) = ctx_module.get_key_value(name) else {
                            break 'search_named_ctx
                        };
    
                        tree_stack.push((key.as_ref(), subtree));
    
                        break 'search_named tree_stack;
                    }
    
                    // If the name was not in the context module, check the root module.
                    let NameTree::Module { subtrees: root_module } = self else {
                        return Err(NameTreeError::ExpectedModule(CanonLibPathBuf::root()))
                    };
    
                    let Some((key, subtree)) = root_module.get_key_value(name) else {
                        let err_path = CanonLibPathBuf::from_nodes([name.as_ref()]);
                        return Err(NameTreeError::NotFound(err_path))
                    };
    
                    vec![(key.as_ref(), subtree)]
                },
    
                None => return Ok(Vec::new()),
            }
        };

        for node in nodes {
            match node {
                LibPathNode::Super => {
                    tree_stack.pop();
                },
                
                LibPathNode::Module => (),
                
                LibPathNode::Named(name) => {
                    let NameTree::Module { subtrees: module } = tree_stack
                        .last()
                        .map(|(_, subtree)| subtree)
                        .copied()
                        .unwrap_or(self)
                    else {
                        let err_path = tree_stack.iter().map(|(node, _)| *node).collect();
                        return Err(NameTreeError::ExpectedModule(err_path))
                    };

                    let Some((key, subtree)) = module.get_key_value(name) else {
                        let err_path = tree_stack
                            .iter()
                            .map(|(node, _)| *node)
                            .chain(iter::once(name.as_ref()))
                            .collect();
                        return Err(NameTreeError::NotFound(err_path))
                    };

                    tree_stack.push((key.as_ref(), subtree));
                },
            }
        }

        Ok(tree_stack)
    }

    fn subtrees_for_path<'s>(&'s self, path: &CanonLibPath)
        -> Result<Vec<(&'s str, &'s Self)>, NameTreeError>
    {
        let mut subtree_stack = Vec::new();
        let mut current = self;
        
        for (parent_path, current_path, node) in path.iter() {
            let Self::Module { subtrees } = current else {
                return Err(NameTreeError::ExpectedModule(parent_path.to_owned()))
            };

            let Some((key, subtree)) = subtrees.get_key_value(node) else {
                return Err(NameTreeError::NotFound(current_path.to_owned()))
            };

            current = subtree;
            subtree_stack.push((key.as_ref(), current));
        }

        Ok(subtree_stack)
    }

    pub fn prepare_entry_last_segment<'s>(&'s mut self, path: &CanonLibPath)
        -> Result<(hash_map::VacantEntry<'s, Rc<str>, NameTree>, CanonLibPathBuf), NameTreeError>
    {
        let Self::Module { subtrees: current } = self else {
            return Err(NameTreeError::ExpectedModule(CanonLibPathBuf::root()))
        };

        let mut current = current;

        let mut path_iter = path.iter().peekable();

        while let Some((_, current_path, node)) = path_iter.next() {
            match path_iter.peek() {
                Some(_) => {
                    if !current.contains_key(node) {
                        current.insert(node.into(), NameTree::empty_module());
                    }
        
                    let Some(Self::Module { subtrees: next }) = current.get_mut(node) else {
                        return Err(NameTreeError::ExpectedModule(current_path.to_owned()))
                    };
        
                    current = next;
                },

                None => {
                    match current.entry(node.into()) {
                        hash_map::Entry::Occupied(_) => {
                            return Err(NameTreeError::Duplicate(current_path.to_owned()));
                        },
                        hash_map::Entry::Vacant(entry) => {
                            return Ok((entry, current_path.to_owned()));
                        },
                    }
                },
            }
        }

        Err(NameTreeError::Duplicate(CanonLibPathBuf::root()))
    }

    pub fn prepare_entry<'s>(&'s mut self, parent: &CanonLibPath, name: Rc<str>)
        -> Result<(hash_map::VacantEntry<'s, Rc<str>, NameTree>, CanonLibPathBuf), NameTreeError>
    {
        let Self::Module { subtrees: current } = self else {
            return Err(NameTreeError::ExpectedModule(CanonLibPathBuf::root()))
        };

        let mut current = current;
        
        for (_, current_path, node) in parent.iter() {
            // Get the subtree for the next node of the path, or create one if it doesn't exist.
            // This manual `contains_key` is used rather than the `entry` api to avoid allocating
            // a copy of `node` in the happy path.
            if !current.contains_key(node) {
                current.insert(node.into(), NameTree::empty_module());
            }

            let Some(Self::Module { subtrees: next }) = current.get_mut(node) else {
                return Err(NameTreeError::ExpectedModule(current_path.to_owned()))
            };

            current = next;
        }

        let new_path = {
            let mut path = parent.to_owned();
            path.push(&name);
            path
        };

        match current.entry(name) {
            hash_map::Entry::Occupied(_) => {
                Err(NameTreeError::Duplicate(new_path))
            },
            hash_map::Entry::Vacant(entry) => {
                Ok((entry, new_path))
            },
        }
    }
}

#[derive(Debug)]
pub enum NameTreeError {
    NotFound(CanonLibPathBuf),
    ExpectedObject(CanonLibPathBuf),
    ExpectedModule(CanonLibPathBuf),
    Duplicate(CanonLibPathBuf),
    Cycle(CanonLibPathBuf),
}

impl fmt::Display for NameTreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFound(path) => {
                write!(f, "name `{}` not found", path)
            },
            Self::ExpectedObject(path) => {
                write!(f, "expected `{}` to be an object", path)
            },
            Self::ExpectedModule(path) => {
                write!(f, "expected `{}` to be a module", path)
            },
            Self::Duplicate(path) => {
                write!(f, "duplicate name `{}`", path)
            },
            Self::Cycle(path) => {
                write!(f, "cycle in resolving name `{}`", path)
            },
        }
    }
}

impl error::Error for NameTreeError {}
