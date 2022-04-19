//! AST Walker
//! ref to [https://doc.rust-lang.org/nightly/nightly-rustc/rustc_ast/visit/trait.Visitor.html] for detailed arch

use super::ast::*;

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
}

pub fn walk_basic_type<V: Visitor>(visitor: &mut V,node: &BasicType){

}