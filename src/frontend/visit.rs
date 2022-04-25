//! AST Walker
//! ref to [https://doc.rust-lang.org/nightly/nightly-rustc/rustc_ast/visit/trait.Visitor.html] for detailed arch
#![allow(unused)]
use super::ast::*;
/// default impl of trait `Visitor` is to call walk_*
/// but for readble not use macro
macro_rules! visit_walk_default {
    ($visit_name: ident, $walk_name: ident, $node_type: ty) => {
            fn $visit_name(&mut self, node: &$node_type){
                $walk_name(self, node);
            }
    }
}

pub trait Visitor: Sized{
    fn visit_comp_unit(&mut self,cu: &CompUnit){
        walk_comp_unit(self, cu);
    }
    fn visit_decl(&mut self,node: &Decl){
        walk_decl(self, node);
    }
    fn visit_basic_type(&mut self,node: &BasicType){
        walk_basic_type(self, node);
    }
    fn visit_def(&mut self,node: &Def){
        walk_def(self, node);
    }
    fn visit_expr(&mut self,node: &Expr){
        walk_expr(self, node);
    }
}

pub fn walk_comp_unit<V: Visitor>(visitor: &mut V,cu: &CompUnit){
    for item in &cu.kind.items{
        match item{
            DeclOrFuncDef::Decl(decl)=>visitor.visit_decl(decl),
            DeclOrFuncDef::FuncDef(func_def)=>(),
        }
    }
}
pub fn walk_decl<V: Visitor>(visitor: &mut V,node: &Decl){
    visitor.visit_basic_type(&node.kind.btype);
    for def in &node.kind.defs{
        visitor.visit_def(def);
    }
}

pub fn walk_def<V: Visitor>(visitor: &mut V,node: &Def){
   // Shape
   for dim in &node.kind.shape{
        visitor.visit_expr(dim);
   }
}
pub fn walk_expr<V: Visitor>(visitor: &mut V,node: &Expr){
    use ExprKind::*;
    match &node.kind{
        Call{id, args} =>{

        }
        _ =>()
    }
}
pub fn walk_basic_type<V: Visitor>(visitor: &mut V,node: &BasicType){
    // A leaf
}