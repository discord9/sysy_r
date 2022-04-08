//! Abstract Syntax Tree
//!
#![allow(unused)]
use crate::cst::SyntaxNode;
use crate::syntax::SyntaxKind as Kind;

/// to wrap a SyntaxNode into a AST node

macro_rules! ast_node {
    ($ast:ident, $kind:pat) => {
        #[derive(PartialEq, Eq, Hash)]
        #[repr(transparent)]
        struct $ast(SyntaxNode);
        impl $ast {
            #[allow(unused)]
            fn cast(node: SyntaxNode) -> Option<Self> {
                if let $kind = node.kind() {
                    Some(Self(node))
                } else {
                    None
                }
            }
        }
    };
}

//ast_node!(CompUnit, Kind::CompUnit);
// Decl | FuncDef
enum DeclOrDef{
    Decl(Decl),
    Def(FuncDef),
}
enum BasicType {
    Int,
    Float,
    Void
}
struct Decl {
    is_const: bool,
    btype: BasicType,
    const_def: Vec<ConstDef>,
}
struct ConstDef {
    ident: String,
}
struct FuncDef {

}
struct CompUnit{
    item: Vec<DeclOrDef>
}
