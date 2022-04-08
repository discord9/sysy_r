//! Abstract Syntax Tree
//!
#![allow(unused)]
use crate::cst::SyntaxNode;
use crate::syntax::SyntaxKind as Kind;
use either::Either;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct CompUnit {
    item: Vec<Either<Decl, FuncDef>>,
}

/// merge ConstDecl and VarDecl together
#[derive(Serialize, Deserialize, Debug)]
struct Decl {
    is_const: bool,
    btype: BasicType,
    def: Vec<Def>,
}
#[derive(Serialize, Deserialize, Debug)]
enum BasicType {
    Int,
    Float,
    Void,
}
#[derive(Serialize, Deserialize, Debug)]
struct Def {
    is_const: bool, // if not const InitVal can be optional
    ident: String,
    exp: Option<Vec<Exp>>,
    init_val: Option<InitVal>, //const_init_val:
}
/// -> Exp | `{` InitVal {`,` InitVal }`}`
#[derive(Serialize, Deserialize, Debug)]
struct InitVal(Either<Exp, Vec<InitVal>>);
#[derive(Serialize, Deserialize, Debug)]
struct FuncDef {
    func_type: BasicType,
    ident: String,
    formal_params: Option<Vec<FuncFParam>>,
}
#[derive(Serialize, Deserialize, Debug)]
struct FuncFParam {
    btype: BasicType,
    ident: String,
    array_shape: Option<Vec<Exp>>, // if not None, default to have `[]` and then zero to multiple `[`Exp`]`
}
#[derive(Serialize, Deserialize, Debug)]
struct Block {
    items: Option<Vec<BlockItem>>,
}
#[derive(Serialize, Deserialize, Debug)]
struct BlockItem(Either<Decl, Statement>);
#[derive(Serialize, Deserialize, Debug)]
enum Statement {
    Assign,
    Exp,
    Block,
    IfStmt {
        cond: Exp,
        stmt: Box<Statement>,
        else_stmt: Box<Statement>,
    },
    WhileStmt {
        cond: Exp,
        stmt: Box<Statement>,
    },
    BreakStmt,
    ContinueStmt,
    ReturnStmt(Option<Exp>),
}
/// merge all *Exp into one. is it wise?NO, but as a enum with all possible variant? YESYES
#[derive(Serialize, Deserialize, Debug)]
enum Exp {
    //?
    BinOp(BinOp),
    UnaryOp(UnaryOp)
}
/// Binary Operator
#[derive(Serialize, Deserialize, Debug)]
struct BinOp{
    op: Kind, // OpAdd OpSub OpMul OpDiv etc.
    left: Box<Exp>,
    right: Box<Exp>
}
/// Unary operator
#[derive(Serialize, Deserialize, Debug)]
struct UnaryOp{
    op: Kind, // OpSub OpAdd OpNot
    val: Box<Exp>
}


#[derive(Serialize, Deserialize, Debug)]
struct FuncRParams(Vec<Exp>);

/// given a Exp in CST, return AST
fn parse_exp() -> Exp {
    unimplemented!()
}
