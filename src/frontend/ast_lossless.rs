//! a attempt to build a ast that select few nodes from cst
//!
//! Refactory AST to
//! ```
//! pub struct $node {
//!     pub id: NodeId,
//!     pub kind: $node Kind,
//!     pub elem: CSTElement,
//! }
//! ```
//! layer AST on top of `SyntaxNode` API.
#![allow(unused)]
use std::ptr::NonNull;

// TODO: Remove after completed
use crate::cst::{parse, SyntaxElement, SyntaxNode, SyntaxToken};
use crate::syntax::SyntaxKind as Kind;
use rowan::{TextLen, TextRange};
use serde::{Deserialize, Serialize};

/// a wrapper for syntax element
#[derive(Serialize, Deserialize, Debug)]
pub struct Span(usize, usize);

impl From<TextRange> for Span {
    fn from(tr: TextRange) -> Self {
        Self(tr.start().into(), tr.end().into())
    }
}

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
    shape: Option<Vec<Expr>>,  // const
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

type NodeId = usize;
/// Convert CST to AST
pub struct AST {
    first_unalloc_node_id: NodeId,
}
impl AST {
    fn get_syntax_node<'a>(elem: &'a SyntaxElement, kinds: &[Kind]) -> Option<&'a SyntaxNode> {
        match elem {
            SyntaxElement::Node(node) => {
                for kind in kinds {
                    if *kind != node.kind() {
                        return None;
                    }
                }
                Some(node)
            }
            SyntaxElement::Token(token) => None,
        }
    }

    fn get_syntax_token<'a>(elem: &'a SyntaxElement, kinds: &[Kind]) -> Option<&'a SyntaxToken> {
        match elem {
            SyntaxElement::Node(node) => None,
            SyntaxElement::Token(token) => {
                for kind in kinds {
                    if *kind != token.kind() {
                        return None;
                    }
                }
                Some(token)
            }
        }
    }
    /// alloc a node id, return a unique node id
    fn alloc_node_id(&mut self) -> NodeId {
        let ret = self.first_unalloc_node_id;
        self.first_unalloc_node_id += 1;
        ret
    }
    /// get all child elem(Node and token) using flag to selectivelty filter out node or token or ws&cmt
    fn get_child_elem(
        elem: &SyntaxNode,
        skip_ws_cmt: bool,
        take_token: bool,
        take_node: bool,
    ) -> Vec<SyntaxElement> {
        elem.children_with_tokens()
            .map(|child| match child {
                SyntaxElement::Token(ref token) => {
                    if skip_ws_cmt && matches!(token.kind(), Kind::Whitespace | Kind::Comment) {
                        None
                    } else if take_token {
                        Some(child)
                    } else {
                        None
                    }
                }
                SyntaxElement::Node(ref node) => {
                    if take_node {
                        Some(child)
                    } else {
                        None
                    }
                }
            })
            .filter(|x| x.is_some())
            .map(|x| x.unwrap())
            .collect()
    }
    /// get first token 
    /// 
    /// NOTE: skip white space and comment
    fn get_first_skipped_token(node: &SyntaxNode) -> Option<SyntaxToken> {
        Self::get_child_elem(node, true, true, false)
            .get(0)
            .unwrap()
            .as_token()
            .cloned()
    }
    /// Accept a Number compsite node
    pub fn parse_number(&mut self, elem: &SyntaxElement) -> IntOrFloat {
        if let Some(node) = elem.as_node() {
            if !matches!(node.kind(), Kind::Number) {
                panic!("Expect a number node");
            }
            let tok = Self::get_first_skipped_token(node).expect("Expect a number");
            let reskind = match tok.kind() {
                Kind::IntConst => IntOrFloatKind::Int(tok.text().parse::<i32>().unwrap()),
                Kind::FloatConst => IntOrFloatKind::Float(tok.text().parse::<f32>().unwrap()),
                _ => panic!("Expect a float or int"),
            };
            return IntOrFloat {
                id: self.alloc_node_id(),
                kind: reskind,
                elem: tok.text_range().into(),
            };
        }
        panic!("Expect a Number CST Node.")
    }
}
