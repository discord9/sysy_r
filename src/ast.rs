//! Abstract Syntax Tree
//!
//! TODO: Add Range for AST node
#![allow(unused)]
use crate::cst::{SyntaxElement, SyntaxNode, SyntaxToken, parse};
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
    items: Option<Vec<(BlockItem)>>,
}
#[derive(Serialize, Deserialize, Debug)]
struct BlockItem(Either<Decl, Statement>);
#[derive(Serialize, Deserialize, Debug)]
enum Statement {
    Assign {
        target: Box<Exp>,
        value: Box<Exp>,
    },
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
#[derive(Serialize, Deserialize, Debug, PartialEq)]
enum Exp {
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
    Constant(IntOrFloat),
    /// Ident
    Name(String),
    Subscript {
        value: Box<Exp>,
        slice: Box<Exp>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
enum IntOrFloat {
    Int(i32),
    Float(f32),
}
use std::ops::Range;
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub enum CSTNodeOrToken {
    Node(Kind, Vec<CSTNodeOrToken>),
    Token(Kind, String),
}

/// see if it is a whitespace or comment
fn is_ws_cmt(kind: Kind) -> bool {
    kind == Kind::Whitespace || kind == Kind::Comment
}

/// transform a syntaxNode tree into a rusty object notion style simpler tree
fn into_ron_tree(node: &SyntaxNode, text: &str, skip_ws_cmt: bool) -> CSTNodeOrToken {
    let kind = node.kind();
    //let mut ret = CSTNodeOrToken::Node(kind, Vec::new());
    let mut child_elem: Vec<CSTNodeOrToken> = Vec::new();
    node.children_with_tokens()
        .map(|child| {
            match child {
                SyntaxElement::Node(node) => child_elem.push(into_ron_tree(&node, text, true)),
                SyntaxElement::Token(token) => {
                    let content = text
                        .get(token.text_range().start().into()..token.text_range().end().into())
                        .unwrap();
                    // if skip ws then dont push
                    if skip_ws_cmt && is_ws_cmt(token.kind()) {
                        return;
                    }
                    //let _range = token.text_range();
                    //let _range: Range<usize> = (range.start().into()..range.end().into());
                    child_elem.push(CSTNodeOrToken::Token(
                        token.kind(),
                        content.to_string(),
                    ));
                }
            };
        })
        .count();
    //let _range = node.text_range();
    //let _range: Range<usize> = (range.start().into()..range.end().into());
    let ret = CSTNodeOrToken::Node(kind, child_elem);
    ret
}

/// given a Exp in CST, return AST
///
/// `text` is the source code
/// TODO: change it to use simple ron style CST
fn parse_exp(node: &CSTNodeOrToken) -> Exp {
    if let CSTNodeOrToken::Node(node_kind, child_vec) = node {
        let (mut cur_node_kind, mut cur_child_vec) = (node_kind, child_vec);
        loop {
            let child_cnt = cur_child_vec.len();
            if child_cnt != 1 {
                break;
            }
            match cur_child_vec.get(0).unwrap() {
                CSTNodeOrToken::Node(kind, child_elem) => {
                    (cur_node_kind, cur_child_vec) = (kind, child_elem);
                    //cur_child_vec = child_elem;
                }
                CSTNodeOrToken::Token(kind, content) => {
                    // 一脉单传抵达一个token，说明整个树可以简化为一个token
                    // In the case of expression, only Ident(LVal), Number is possible to be the leaf of such tree
                    match kind {
                        Kind::Ident => {
                            let ret = Exp::Name(content.to_owned());
                            return ret;
                        }
                        Kind::IntConst => {
                            let val = content.parse::<i32>().unwrap();
                            let ret = Exp::Constant(IntOrFloat::Int(val));
                            return ret;
                        }
                        Kind::FloatConst => {
                            let val = content.parse::<f32>().unwrap();
                            let ret = Exp::Constant(IntOrFloat::Float(val));
                            return ret;
                        }
                        _ => (),
                    }
                }
            }
        }
        match *cur_node_kind{
            Kind::UnaryExp => {// UnaryOp UnaryExp
                if let CSTNodeOrToken::Token(op, _)  = cur_child_vec.get(0).unwrap(){
                    let val = parse_exp(cur_child_vec.get(1).unwrap());
                    return Exp::UnaryOp { op: *op, val: Box::new(val) }
                }
            },
            _ => ()
        }
    }
    // go all the way deeper until there is a token or there is more than one child
    // for simpler tree
    unimplemented!()
}
use std::fs::File;
use std::path::Path;
fn load_test_cases(path: &Path) -> CSTNodeOrToken {
    let mut file = File::open(path).expect("Fail to open file.");
    use ron::de::from_reader;
    let ret: CSTNodeOrToken = from_reader(file).expect("Wrong format");
    ret
}


#[test]
fn test_unary_exp() {
    use ron::ser::{to_string_pretty, PrettyConfig};
    use ron::de::from_str;
    let res = load_test_cases(Path::new("test_cases/ast/unary_exp.ron"));
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );
    let exp = parse_exp(&res);
    println!("AST:\n{}", to_string_pretty(&exp, pretty.to_owned()).unwrap());
    let res:Exp = from_str("UnaryOp(
        op: OpSub,
        val: Constant(Int(1)),
    )").expect("Wrong format");
    assert_eq!(exp, res);
}

/// test CST -> AST case of AddExp(MulExp(UnaryExp(PrimaryExp(Number(IntConst(1)))))) to Constant(1) function
#[test]
fn test_single_exp() {
    use ron::ser::{to_string_pretty, PrettyConfig};
    let res = load_test_cases(Path::new("test_cases/ast/single_exp.ron"));
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );
    let exp = parse_exp(&res);
    println!("AST:\n{:?}", exp);
    assert_eq!(format!("{:?}", exp), "Constant(Int(1))".trim());
}
#[test]
fn test_integrate() {
    use crate::cst::parse;
    use crate::lex::lex;
    use ron::ser::{to_string_pretty, PrettyConfig};
    let text = "
        int main(){
            -1+2*3;
        }";
    let parse = parse(text);
    let node = parse.syntax();
    let res = into_ron_tree(&node, text, true);
    println!("Errors:{:?}", parse.errors);
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .indentor("  ".to_string())
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );

    //let mut out  = String::new();
    //output_cst(&node, 0, text, &mut out, "│");
    //println!("CST:{}", out);
}
