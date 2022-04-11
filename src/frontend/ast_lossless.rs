//! a attempt to build a ast that select few nodes from cst
//!
//! Refactory AST to
//! ```
//! pub struct $node {
//!     pub id: usize,
//!     pub kind: $node Kind,
//!     pub elem: CSTElement,
//! }
//! ```
//! layer AST on top of `SyntaxNode` API.
#![allow(unused)]
use crate::cst::{parse, SyntaxElement, SyntaxNode, SyntaxToken};
use crate::syntax::SyntaxKind as Kind;
use serde::{Deserialize, Serialize};

/// a wrapper for syntax element
#[derive(Serialize, Deserialize, Debug)]
pub struct Span(
    usize,
    usize, //SyntaxElement
           // TODO ser for SyntaxElement
);

// TODO: impl serialize manually for ASTNode
macro_rules! decl_ast_node {
    ($(($ast: ident, $astkind: ident) ),*) => {
    $(
        #[derive(Serialize, Deserialize, Debug)]
        pub struct $ast {
            pub id: usize,
            pub kind: $astkind,
            pub elem: Span
        }
    )*
    }
}

// TODO: write a better iterator for CST
// TODO: write a better state machine for choosing CST node and convert to AST
#[derive(Serialize, Deserialize, Debug)]
pub struct CompUnitKind {
    items: Vec<DeclOrFuncDef>,
}
decl_ast_node!((CompUnit, CompUnitKind));

#[derive(Serialize, Deserialize, Debug)]
pub enum DeclOrFuncDefKind {
    Decl(Decl),
    FuncDef(FuncDef),
}
decl_ast_node!((DeclOrFuncDef, DeclOrFuncDefKind));

#[derive(Serialize, Deserialize, Debug)]
pub struct DeclKind {
    is_const: bool,
    btype: BasicType,
    def: Vec<Def>,
}
decl_ast_node!((Decl, DeclKind));
#[derive(Serialize, Deserialize, Debug)]
pub struct FuncDefKind {
    func_type: BasicType,
    ident: String,
    formal_params: Vec<FuncFParam>, // if is_empty() then zero args
    block: Block,
}

decl_ast_node!((FuncDef, FuncDefKind));

/// ConstDef or VarDef
#[derive(Serialize, Deserialize, Debug)]
pub struct DefKind {
    is_const: bool, // if not const InitVal can be optional
    ident: String,
    shape: Option<Vec<Expr>>,   // const
    init_val: Option<InitVal>, //const_init_val:
}

decl_ast_node!((Def, DefKind));

#[derive(Serialize, Deserialize, Debug)]
pub enum ExpOrInitValKind {
    Exp(Expr),
    InitVals(Vec<ExpOrInitVal>),
}

decl_ast_node!((ExpOrInitVal, ExpOrInitValKind));

type InitVal = ExpOrInitVal;

#[derive(Serialize, Deserialize, Debug)]
pub enum BasicTypeKind {
    Int,
    Float,
    Void,
}
decl_ast_node!((BasicType, BasicTypeKind));

#[derive(Serialize, Deserialize, Debug)]
pub struct FuncFParamKind {
    btype: BasicType,
    ident: String,
    array_shape: Option<Vec<Expr>>,
    // if None, then it is a normal var
    // if not None, default to have `[]` and then zero to multiple `[`Exp`]`
}
decl_ast_node!((FuncFParam, FuncFParamKind));

#[derive(Serialize, Deserialize, Debug)]
pub struct BlockKind {
    items: Vec<(DeclOrStatement)>,
}
decl_ast_node!((Block, BlockKind));

#[derive(Serialize, Deserialize, Debug)]
pub enum DeclOrStatementKind {
    Decl(Decl),
    Statement(Statement),
}
decl_ast_node!((DeclOrStatement, DeclOrStatementKind));

#[derive(Serialize, Deserialize, Debug)]
pub enum StatementKind {
    Empty, //`;`
    /// LVal '=' Exp ';'
    Assign {
        target: Expr,
        value: Expr,
    },
    Exp(Expr),
    Block(Block),
    IfStmt {
        cond: Expr,
        stmt: Box<Statement>,
        else_stmt: Box<Option<Statement>>,
    },
    WhileStmt {
        cond: Expr,
        stmt: Box<Statement>,
    },
    BreakStmt,
    ContinueStmt,
    ReturnStmt(Option<Expr>),
}

decl_ast_node!((Statement, StatementKind));

#[derive(Serialize, Deserialize, Debug)]
pub enum ExprKind {
    /// Call to function
    ///
    /// `f(args)`
    Call { id: String, args: Vec<Expr> },
    /// Binary Operator. Note: in CST BinOp is a vec of exp, like vec!\[1+2+3\]
    ///
    /// `+` `-` `*` `/` `%`
    BinOp {
        op: Kind, // OpAdd OpSub OpMul OpDiv OpMod
        left: Box<Expr>,
        right: Box<Expr>,
    },
    /// `&&` `||`
    BoolOp {
        op: Kind, // OpAnd OpOr
        args: Vec<Expr>,
    },
    /// Unary operator
    ///
    /// `+1` `-1` `!flag`
    UnaryOp {
        op: Kind, // OpSub OpAdd OpNot
        val: Box<Expr>,
    },
    /// Compare operator can be chain like: 1<2<3
    ///
    /// `<` `>` `<=` `>=` `==` `!=`
    ///
    /// => op: LT,LT;left:1, comparators:[2,3]
    CmpOp {
        op: Vec<Kind>, // OpLT OpGT OpNG OpNL OpEQ OpNE
        left: Box<Expr>,
        comparators: Vec<Expr>,
    },
    /// int or float
    Constant(IntOrFloat),
    /// Ident
    Name(String),
    /// `a[b]`
    Subscript { value: Box<Expr>, slice: Box<Expr> },
}

decl_ast_node!((Expr, ExprKind));

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub enum IntOrFloatKind {
    Int(i32),
    Float(f32),
}

decl_ast_node!((IntOrFloat, IntOrFloatKind));
