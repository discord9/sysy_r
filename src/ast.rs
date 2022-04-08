//! Abstract Syntax Tree
//!
#![allow(unused)]
use crate::cst::{SyntaxElement, SyntaxNode, SyntaxToken};
use crate::syntax::SyntaxKind as Kind;
use either::Either;
use serde::{Deserialize, Serialize};

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
    Assign {
        target: Box<Exp>,
        value: Box<Exp>,
    },
    Call {
        id: String,
        args: Vec<Exp>,
    },
    /// Binary Operator. Note: in CST BinOp is a vec of exp, like 1+2+3
    BinOp {
        op: Kind, // OpAdd OpSub OpMul OpDiv OpMod
        left: Box<Exp>,
        right: Box<Exp>,
    },
    /// Unary operator
    UnaryOp {
        op: Kind, // OpSub OpAdd OpNot
        val: Box<Exp>,
    },
    /// Compare operator can be chain like: 1<2<3
    ///
    /// => op: LT,LT;left:1, comparators:[2,3]
    CmpOp {
        op: Vec<Kind>, // OpLT OpGT OpNG OpNL OpEQ OpNE
        left: Box<Exp>,
        comparators: Vec<Exp>,
    },
    /// int or float
    Constant(Either<i32, f32>),
    /// Ident
    Name(String),
    Subscript {
        value: Box<Exp>,
        slice: Box<Exp>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub enum CSTNodeOrToken {
    Node(Kind, Vec<CSTNodeOrToken>),
    Token(Kind, String),
}

/// transform a syntaxNode tree into a rusty object notion style simpler tree
fn into_ron_tree(node: &SyntaxNode, text: &str) -> CSTNodeOrToken {
    let kind = node.kind();
    //let mut ret = CSTNodeOrToken::Node(kind, Vec::new());
    let mut child_elem: Vec<CSTNodeOrToken> = Vec::new();
    node.children_with_tokens()
        .map(|child| {
            match child {
                SyntaxElement::Node(node) => child_elem.push(into_ron_tree(&node, text)),
                SyntaxElement::Token(token) => {
                    let content = text.get(
                        token.text_range().start().into()..token.text_range().end().into()
                    ).unwrap();
                    child_elem.push(CSTNodeOrToken::Token(token.kind(), content.to_string()));
                }
            };
        })
        .count();
    unimplemented!()
}

/// given a Exp in CST, return AST
///
/// `text` is the source code
fn parse_exp(node: SyntaxNode, text: &str) -> Exp {
    use either::{Left, Right};
    let node_kind = node.kind();
    let mut cur_node = node;
    // go all the way deeper until there is a token or there is more than one child
    // for simpler tree
    loop {
        let child_count = cur_node.children_with_tokens().count();
        if child_count != 1 {
            break;
        }
        match cur_node.children_with_tokens().next().unwrap() {
            SyntaxElement::Node(node) => {
                cur_node = node;
            }
            SyntaxElement::Token(token) => {
                // 一脉单传抵达一个token，说明整个树可以简化为一个token
                // for exp, only Ident(LVal), Number is possible to be the leaf of such tree
                let content = text
                    .get(token.text_range().start().into()..token.text_range().end().into())
                    .unwrap();
                match token.kind() {
                    Kind::Ident => {
                        let ret = Exp::Name(content.to_owned());
                        return ret;
                    }
                    Kind::IntConst => {
                        let val = content.parse::<i32>().unwrap();
                        let ret = Exp::Constant(Left(val));
                        return ret;
                    }
                    Kind::FloatConst => {
                        let val = content.parse::<f32>().unwrap();
                        let ret = Exp::Constant(Right(val));
                        return ret;
                    }
                    _ => (),
                }
            }
        }
    }
    match node_kind {
        Kind::IntConst => {
            //let ret = Exp::Constant(Left())
        }
        _ => (),
    }
    unimplemented!()
}
