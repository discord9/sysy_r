//! AST Walker
//! ref to [https://doc.rust-lang.org/nightly/nightly-rustc/rustc_ast/visit/trait.Visitor.html] for detailed arch
//! walk in eval order(reverse post order that is, like a=b is walk in the order of `b` `=` `a`)

use crate::frontend::visit;

use super::symbol_table::Symbol;
use super::ast::*;
/// default impl of trait `Visitor` is to call walk_*
/// but for readble not use macro
/*
macro_rules! visit_walk_default {
    ($visit_name: ident, $walk_name: ident, $node_type: ty) => {
        fn $visit_name(&mut self, node: &$node_type) {
            $walk_name(self, node);
        }
    };
}
*/

#[allow(unused)]
pub trait Visitor: Sized {
    fn visit_symbol(&mut self, _node: &Symbol ){
        // do nothing by default
    }
    fn visit_ident(&mut self, node: & Ident){
        walk_ident(self, node);
    }
    fn visit_comp_unit(&mut self, cu: &CompUnit) {
        walk_comp_unit(self, cu);
    }
    fn visit_decl(&mut self, node: &Decl) {
        walk_decl(self, node);
    }
    fn visit_func_def(&mut self, node: &FuncDef) {
        walk_func_def(self, node);
    }
    
    fn visit_def(&mut self, node: &Def) {
        walk_def(self, node);
    }
    fn visit_init_val(&mut self, node: &InitVal){
        walk_init_val(self, node);
    }
    fn visit_basic_type(&mut self, node: &BasicType) {
        walk_basic_type(self, node);
    }
    fn visit_formal_param(&mut self, node: &FuncFParam){
        walk_formal_param(self, node);
    }
    fn visit_block(&mut self, node:&Block){
        walk_block(self, node);
    }
    fn visit_decl_or_stmt(&mut self, node:&DeclOrStatement){
        walk_decl_or_stmt(self, node);
    }
    fn visit_stmt(&mut self, node:&Statement){
        walk_stmt(self, node);
    }
    fn visit_expr(&mut self, node: &Expr) {
        walk_expr(self, node);
    }
}

pub fn walk_ident<V: Visitor>(visitor: &mut V, node: &Ident){
    visitor.visit_symbol(&node.name);
}

pub fn walk_comp_unit<V: Visitor>(visitor: &mut V, cu: &CompUnit) {
    for item in &cu.kind.items {
        match item {
            DeclOrFuncDef::Decl(decl) => visitor.visit_decl(decl),
            DeclOrFuncDef::FuncDef(func_def) => visitor.visit_func_def(func_def)
        }
    }
}
pub fn walk_decl<V: Visitor>(visitor: &mut V, node: &Decl) {
    visitor.visit_basic_type(&node.kind.btype);
    for def in &node.kind.defs {
        visitor.visit_def(def);
    }
}

pub fn walk_func_def<V: Visitor>(visitor: &mut V, node: &FuncDef) {
    // A leaf
    visitor.visit_basic_type(&node.kind.func_type);
    visitor.visit_ident(&node.kind.ident);
    for fp in &node.kind.formal_params{
        visitor.visit_formal_param(fp);
    }
    todo!();
    // visit block
}

pub fn walk_def<V: Visitor>(visitor: &mut V, node: &Def) {
    visitor.visit_ident(&node.kind.ident);
    // Shape
    for dim in &node.kind.shape {
        visitor.visit_expr(dim);
    }
    if let Some(init_val) = &node.kind.init_val{
        visitor.visit_init_val(init_val);
    }
    // initval
}

pub fn walk_init_val<V: Visitor>(visitor: &mut V, node: &InitVal){
    use ExpOrInitValKind::*;
    match &node.kind{
        Exp(e)=>visitor.visit_expr(e),
        InitVals(vs)=>{
            for v in vs{
                visitor.visit_init_val(v);
            }
        }
    }
}

#[allow(unused)]
pub fn walk_basic_type<V: Visitor>(visitor: &mut V, node: &BasicType) {
    // A leaf
}

pub fn walk_formal_param<V: Visitor>(visitor: &mut V, node: &FuncFParam){
    visitor.visit_basic_type(&node.kind.btype);
    visitor.visit_ident(&node.kind.ident);
    if let Some(shape) = &node.kind.array_shape{
        for i in shape{
            visitor.visit_expr(i);
        }
    }
}

pub fn walk_block<V: Visitor>(visitor: &mut V, node: &Block){
    for item in &node.kind.items{
        visitor.visit_decl_or_stmt(item)
    }
}

pub fn walk_decl_or_stmt<V: Visitor>(visitor: &mut V, node: &DeclOrStatement){
    use DeclOrStatement::*;
    match &node{
        Decl(d)=>visitor.visit_decl(d),
        Statement(s)=>todo!()
    }
}

pub fn walk_stmt<V: Visitor>(visitor: &mut V, node: &Statement){
    use StatementKind::*;
    let kind = &node.kind;
    match kind{
        Empty => (),
        // in eval value order `target` = `value`
        Assign { target, value }=>{
            visitor.visit_expr(value);
            visitor.visit_expr(target);
        }
        Expr(e)=>visitor.visit_expr(e),
        Block(b)=>visitor.visit_block(b),
        IfStmt { cond, stmt, else_stmt }=>{
            visitor.visit_expr(cond);
            visitor.visit_stmt(stmt);
            if let Some(stmt) = else_stmt{
                visitor.visit_stmt(stmt);
            }
        }
        WhileStmt { cond, stmt } => {
            visitor.visit_expr(cond);
            visitor.visit_stmt(stmt);
        }
        BreakStmt=>(),
        ContinueStmt=>(),
        ReturnStmt(e)=>{
            if let Some(e) = e{
                visitor.visit_expr(e);
            }
        }
    }
}

pub fn walk_expr<V: Visitor>(visitor: &mut V, node: &Expr) {
    use ExprKind::*;
    match &node.kind {
        Call { id, args } => {
            visitor.visit_ident(id);
            for arg in args{
                visitor.visit_expr(arg);
            }
        }
        BinOp{op: _op, left  ,right}=>{
            visitor.visit_expr(left);
            visitor.visit_expr(right);
        }
        BoolOp { op: _op, args }=>{
            for arg in args{
                visitor.visit_expr(arg)
            }
        }
        UnaryOp { op: _op, val } => {
            visitor.visit_expr(val)
        }
        CmpOp { op: _op, left, comparators } => {
            visitor.visit_expr(left);
            for arg in comparators{
                visitor.visit_expr(arg)
            }
        }
        // do nothing for now
        Constant(_)=>(),
        Name(ident)=>visitor.visit_ident(ident),
        Subscript { value, slice }=>{
            visitor.visit_expr(value);
            visitor.visit_expr(slice);
        }
    }
}


