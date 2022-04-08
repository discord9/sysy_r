//! Abstract Syntax Tree
//! 
use crate::cst::{SyntaxNode};
use crate::syntax::SyntaxKind as Kind;

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(PartialEq, Eq, Hash)]
        #[repr(transparent)]
        struct $ast(SyntaxNode);
        impl $ast {
            #[allow(unused)]
            fn cast(node: SyntaxNode) -> Option<Self> {
                if node.kind() == $kind {
                    Some(Self(node))
                } else {
                    None
                }
            }
        }
    };
}

struct CompUnit(SyntaxNode);
impl CompUnit{
    #[allow(unused)]
    fn cast(node: SyntaxNode) -> Option<Self> {
        if node.kind() == Kind::CompUnit {
            Some(Self(node))
        } else {
            None
        }
    }
}