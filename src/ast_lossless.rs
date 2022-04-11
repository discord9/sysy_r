//! a attempt to build a ast that select few nodes from cst
//!
//! layer AST on top of `SyntaxNode` API.
#![allow(unused)]
use crate::cst::{parse, SyntaxElement, SyntaxNode, SyntaxToken};
use crate::syntax::SyntaxKind as Kind;
use either::Either;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
struct CSTElement(SyntaxElement);

// TODO: impl serialize manually for ASTNode
macro_rules! decl_ast_node {
    ($($ast: ident ),*) => {
        #[derive(Debug)]
        enum ASTNode {
            $(
                $ast ( $ast, SyntaxElement)
            ),*
        }
    }
}

decl_ast_node!(
    CompUnit,
    DeclOrFuncDef,
    Decl,
    FuncDef,
    Def,
    ExpOrInitVal,
    BasicType,
    FuncFParam,
    Block,
    DeclOrStatement,
    Statement,
    IntOrFloat,
    Exp
);

// TODO: write a better iterator for CST
// TODO: write a better state machine for choosing CST node and convert to AST
#[derive(Serialize, Deserialize, Debug)]
struct CompUnit {
    items: Vec<DeclOrFuncDef>,
}

#[derive(Serialize, Deserialize, Debug)]
enum DeclOrFuncDef {
    Decl(Decl),
    FuncDef(FuncDef),
}

#[derive(Serialize, Deserialize, Debug)]
struct Decl {
    is_const: bool,
    btype: BasicType,
    def: Vec<Def>,
}
#[derive(Serialize, Deserialize, Debug)]
struct FuncDef {
    func_type: BasicType,
    ident: String,
    formal_params: Vec<FuncFParam>, // if is_empty() then zero args
    block: Block,
}

/// ConstDef or VarDef
#[derive(Serialize, Deserialize, Debug)]
struct Def {
    is_const: bool, // if not const InitVal can be optional
    ident: String,
    shape: Option<Vec<Exp>>,   // const
    init_val: Option<InitVal>, //const_init_val:
}

#[derive(Serialize, Deserialize, Debug)]
pub enum ExpOrInitVal {
    Exp(Exp),
    InitVals(Vec<InitVal>),
}

type InitVal = ExpOrInitVal;

#[derive(Serialize, Deserialize, Debug)]
enum BasicType {
    Int,
    Float,
    Void,
}

#[derive(Serialize, Deserialize, Debug)]
struct FuncFParam {
    btype: BasicType,
    ident: String,
    array_shape: Option<Vec<Exp>>,
    // if None, then it is a normal var
    // if not None, default to have `[]` and then zero to multiple `[`Exp`]`
}

#[derive(Serialize, Deserialize, Debug)]
struct Block {
    items: Vec<(DeclOrStatement)>,
}

#[derive(Serialize, Deserialize, Debug)]
enum DeclOrStatement {
    Decl(Decl),
    Statement(Statement),
}

#[derive(Serialize, Deserialize, Debug)]
enum Statement {
    Empty, //`;`
    /// LVal '=' Exp ';'
    Assign {
        target: Exp,
        value: Exp,
    },
    Exp(Exp),
    Block(Block),
    IfStmt {
        cond: Exp,
        stmt: Box<Statement>,
        else_stmt: Box<Option<Statement>>,
    },
    WhileStmt {
        cond: Exp,
        stmt: Box<Statement>,
    },
    BreakStmt,
    ContinueStmt,
    ReturnStmt(Option<Exp>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub enum Exp {
    /// Call to function
    ///
    /// `f(args)`
    Call { id: String, args: Vec<Exp> },
    /// Binary Operator. Note: in CST BinOp is a vec of exp, like vec!\[1+2+3\]
    ///
    /// `+` `-` `*` `/` `%`
    BinOp {
        op: Kind, // OpAdd OpSub OpMul OpDiv OpMod
        left: Box<Exp>,
        right: Box<Exp>,
    },
    /// `&&` `||`
    BoolOp {
        op: Kind, // OpAnd OpOr
        args: Vec<Exp>,
    },
    /// Unary operator
    ///
    /// `+1` `-1` `!flag`
    UnaryOp {
        op: Kind, // OpSub OpAdd OpNot
        val: Box<Exp>,
    },
    /// Compare operator can be chain like: 1<2<3
    ///
    /// `<` `>` `<=` `>=` `==` `!=`
    ///
    /// => op: LT,LT;left:1, comparators:[2,3]
    CmpOp {
        op: Vec<Kind>, // OpLT OpGT OpNG OpNL OpEQ OpNE
        left: Box<Exp>,
        comparators: Vec<Exp>,
    },
    /// int or float
    Constant(IntOrFloat),
    /// Ident
    Name(String),
    /// `a[b]`
    Subscript { value: Box<Exp>, slice: Box<Exp> },
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub enum IntOrFloat {
    Int(i32),
    Float(f32),
}
