//! Abstract Syntax Tree
//!
//! TODO: Add Range for AST node
#![allow(unused)]
use crate::cst::{parse, SyntaxElement, SyntaxNode, SyntaxToken};
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
/// is VarDef or ConstDef
#[derive(Serialize, Deserialize, Debug)]
struct Def {
    is_const: bool, // if not const InitVal can be optional
    ident: String,
    shape: Option<Vec<Exp>>,   // const
    init_val: Option<InitVal>, //const_init_val:
}
#[derive(Serialize, Deserialize, Debug)]
enum ExpOrInitVal {
    Exp(Exp),
    InitVals(Vec<InitVal>),
}
/// -> Exp | `{` InitVal {`,` InitVal }`}`
#[derive(Serialize, Deserialize, Debug)]
struct InitVal(ExpOrInitVal);

/// ConstInitVal or InitVal
fn parse_init_val(node: &CST) -> InitVal {
    if let CST::Node(kind, childs) = node {
        if *kind != Kind::ConstInitVal && *kind != Kind::InitVal {
            panic!("Expect Init Val, const or not.");
        }
        let mut args = Vec::new();
        let mut exp = None;
        for elem in childs {
            match elem {
                CST::Token(kind, _) => {
                    if matches!(kind, Kind::LCurly | Kind::RCurly | Kind::Comma) {
                        continue;
                    } else {
                        unreachable!()
                    }
                }
                CST::Node(kind, _) => {
                    if matches!(*kind, Kind::ConstInitVal | Kind::InitVal) {
                        //let ret = parse_init_val(elem);
                        args.push(parse_init_val(elem));
                    }else if matches!(*kind, Kind::ConstExp | Kind::Expression) {
                        exp = Some(parse_exp(elem));
                    }
                }
            }
        }
        if args.is_empty() && exp.is_some(){
            return InitVal(ExpOrInitVal::Exp(exp.unwrap()))
        }else if !args.is_empty() {
            return InitVal(ExpOrInitVal::InitVals(args))
        }else{
            unreachable!()
        }
    }
    unreachable!()
}

fn parse_def(node: &CST, is_const: bool) -> Def {
    match node {
        CST::Node(kind, childs) => {
            if *kind != Kind::ConstDef && *kind != Kind::VarDef {
                panic!("Expect a def from CST!")
            }
            let mut is_first = true;
            let mut ident = String::new();
            let mut shape = Vec::new();
            let mut init_val: Option<InitVal> = None;
            for elem in childs {
                if is_first {
                    is_first = false;
                    if let CST::Token(Kind::Ident, name) = elem {
                        ident = name.to_owned();
                    }
                }
                match elem {
                    CST::Token(Kind::LBracket, _) | CST::Token(Kind::RBracket, _) => (),
                    CST::Node(Kind::Expression, _) => {
                        let res = parse_exp(elem);
                        shape.push(res);
                    }
                    CST::Node(Kind::ConstInitVal, _) | CST::Node(Kind::InitVal, _) => {
                        // parse init val
                        init_val = Some(parse_init_val(elem));
                    }
                    _ => (),
                }
            }
            Def {
                is_const,
                ident,
                shape: Some(shape),
                init_val,
            }
        }
        _ => panic!("Expect a Def"),
    }
}

/// ConstDecl or VarDecl
fn parse_decl(node: &CST) -> Decl {
    match node {
        CST::Node(kind, childs) => {
            // [const] 0:BType 1:VarDef { ',' VarDef } ';'
            let mut is_const = *kind == Kind::ConstDecl;
            if *kind != Kind::ConstDecl && *kind != Kind::VarDecl {
                panic!("Expect a decl from CST!")
            }
            let offset = {
                if is_const {
                    1
                } else {
                    0
                }
            };
            let btype = parse_basic_type(childs.get(offset).unwrap());
            let mut it = childs.iter();
            let mut defs = vec![parse_def(it.next().unwrap(), is_const)];
            while let Some(def) = it.nth(1) {
                defs.push(parse_def(def, is_const));
            }

            return Decl {
                is_const,
                btype,
                def: defs,
            };
        }
        _ => panic!("Expect a Decl"),
    }
    unreachable!()
}

#[derive(Serialize, Deserialize, Debug)]
enum BasicType {
    Int,
    Float,
    Void,
}

fn parse_basic_type(node: &CST) -> BasicType {
    match node {
        CST::Token(Kind::BType, val) => match val.as_str() {
            "int" => BasicType::Int,
            "float" => BasicType::Float,
            "void" => BasicType::Void,
            _ => panic!("Expect int, float or void"),
        },
        _ => panic!("Expect CST Basic Type!"),
    }
}

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
enum DeclOrStatement {
    Decl(Decl),
    Statement(Statement),
}
#[derive(Serialize, Deserialize, Debug)]
struct BlockItem(DeclOrStatement);
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

/// CST: `{` BlockItem `}`
fn parse_block(node: &CST) -> Block {
    match node {
        CST::Node(Kind::Statement, childs) => {
            let mut block_item: Vec<DeclOrStatement> = Vec::new();
            for elem in childs {
                match elem {
                    CST::Token(Kind::LCurly, _) | CST::Token(Kind::RCurly, _) => (),
                    CST::Node(Kind::BlockItem, grandchilds) => {
                        let only_child = grandchilds.get(0).unwrap();
                        match only_child {
                            CST::Node(Kind::Decl, _) => {
                                let res = parse_decl(only_child);
                                block_item.push(DeclOrStatement::Decl(res));
                            }
                            CST::Node(Kind::Statement, _) => {
                                let res = parse_stmt(only_child);
                                block_item.push(DeclOrStatement::Statement(res));
                            }
                            _ => panic!("Expect CST Decl or Statement!"),
                        }
                    }
                    _ => panic!("Expect CST BlockItem or Curly!"),
                }
            }
        }
        _ => panic!("Expect a CST Block!"),
    }
    unreachable!()
}

/// parse statement
fn parse_stmt(node: &CST) -> Statement {
    // first: LeftValue | Exp | Semicolon | Block | ....
    match node {
        CST::Node(Kind::Statement, childs) => {
            // check what is the first elem, to see what type of stmt is this
            if let Some(elem) = childs.get(0) {
                match elem {
                    CST::Node(kind, grandchilds) => {
                        match *kind {
                            Kind::LeftValue => {
                                // 0: LVal 1:= 2:Exp
                                let left_value = parse_exp(childs.get(0).unwrap());
                                let value = parse_exp(childs.get(2).unwrap());
                                return Statement::Assign {
                                    target: left_value,
                                    value,
                                };
                            }
                            Kind::Expression => {
                                let value = parse_exp(childs.get(2).unwrap());
                                return Statement::Exp(value);
                            }
                            Kind::Block => {
                                unimplemented!()
                            }
                            _ => unreachable!(),
                        }
                    }
                    CST::Token(kind, _) => match *kind {
                        Kind::Semicolon => return Statement::Empty,
                        Kind::IfKeyword => {
                            // TODO: maybe check unused tokens?
                            // 0:if 1:( 2:Cond 3:) 4:Stmt Optional:(5:else 6:stmt)
                            let cond = childs.get(2).unwrap();
                            let cond = parse_exp(cond);
                            let stmt = childs.get(4).unwrap();
                            let stmt = parse_stmt(stmt);
                            let mut cst_else_stmt: Option<_> = childs.get(6);
                            let mut ast_else_stmt = None;
                            if let Some(cst_else_stmt) = cst_else_stmt {
                                ast_else_stmt = Some(parse_stmt(cst_else_stmt));
                            }
                            return Statement::IfStmt {
                                cond,
                                stmt: Box::new(stmt),
                                else_stmt: Box::new(ast_else_stmt),
                            };
                        }
                        Kind::WhileKeyword => {
                            // 0:while 1:( 2:Cond 3:) 4:Stmt
                            let cond = childs.get(2).unwrap();
                            let cond = parse_exp(cond);
                            let stmt = childs.get(4).unwrap();
                            let stmt = Box::new(parse_stmt(stmt));
                            return Statement::WhileStmt { cond, stmt };
                        }
                        Kind::BreakKeyword => return Statement::BreakStmt,
                        Kind::ContinueKeyword => return Statement::ContinueStmt,
                        Kind::ReturnKeyword => {
                            // 0: return optional: 1: exp
                            if let Some(exp) = childs.get(1) {
                                let ret = parse_exp(exp);
                                return Statement::ReturnStmt(Some(ret));
                            } else {
                                return Statement::ReturnStmt(None);
                            }
                        }
                        _ => unreachable!(),
                    },
                }
            }
        }
        _ => panic!("Expect a CST Statement!"),
    }
    unimplemented!()
}
/// merge all *Exp into one. is it wise?NO, but as a enum with all possible variant? YESYES
#[derive(Serialize, Deserialize, Debug, PartialEq)]
enum Exp {
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
enum IntOrFloat {
    Int(i32),
    Float(f32),
}
use std::ops::Range;
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub enum CST {
    Node(Kind, Vec<CST>),
    Token(Kind, String),
}

/// see if it is a whitespace or comment
fn is_ws_cmt(kind: Kind) -> bool {
    matches!(kind, Kind::Whitespace | Kind::Comment)
}

fn is_unary_op(kind: Kind) -> bool {
    matches!(kind, Kind::OpAdd | Kind::OpSub | Kind::OpNot)
}

/// +-*/%
fn is_bin_op(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::OpAdd | Kind::OpSub | Kind::OpMul | Kind::OpDiv | Kind::OpMod
    )
}

/// `<` `>` `>=` `<=` `!=` `==`
fn is_cmp_op(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::OpLT | Kind::OpGT | Kind::OpNL | Kind::OpNG | Kind::OpNE | Kind::OpEQ
    )
}

/// transform a syntaxNode tree into a rusty object notion style simpler tree
fn into_ron_tree(node: &SyntaxNode, text: &str, skip_ws_cmt: bool) -> CST {
    let kind = node.kind();
    //let mut ret = CSTNodeOrToken::Node(kind, Vec::new());
    let mut child_elem: Vec<CST> = Vec::new();
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
                    child_elem.push(CST::Token(token.kind(), content.to_string()));
                }
            };
        })
        .count();
    //let _range = node.text_range();
    //let _range: Range<usize> = (range.start().into()..range.end().into());
    let ret = CST::Node(kind, child_elem);
    ret
}

/// args is a CSTNode return Exp
///
/// UnaryExp -> UnaryOp UnaryExp | Ident `(` FuncRParams `)`
fn parse_unary_exp_node(kind: Kind, cur_child_vec: &Vec<CST>) -> Exp {
    // UnaryOp UnaryExp | Ident `(` FuncRParams `)`
    let mut it = cur_child_vec.into_iter();
    if let CST::Token(tok, content) = it.next().unwrap() {
        if is_unary_op(*tok) {
            let val = parse_exp(it.next().unwrap());
            return Exp::UnaryOp {
                op: *tok,
                val: Box::new(val),
            };
        } else if *tok == Kind::Ident {
            let mut args = Vec::new();
            assert_eq!(
                CST::Token(Kind::LParen, "(".to_string()),
                *it.next().unwrap()
            ); // LParen
               // FuncRParams → Exp { ',' Exp }
            let next = it.next().unwrap();
            match next {
                CST::Node(Kind::FuncRParams, grandchilds) => {
                    let mut it = grandchilds.into_iter();
                    for i in it {
                        match i {
                            CST::Node(_, _) => {
                                let val = parse_exp(i);
                                args.push(val);
                            }
                            CST::Token(kind, _) => match *kind {
                                Kind::RParen => break,
                                Kind::Comma => continue,
                                _ => panic!("Expect more Func Real Params."),
                            },
                        }
                    }
                }
                CST::Token(Kind::RParen, content) => (),
                _ => unreachable!(),
            }
            return Exp::Call {
                id: content.into(),
                args,
            };
        }
    }
    unreachable!()
}

/// PrimaryExp → '(' Exp ')'
fn parse_primary_exp_node(kind: Kind, cur_child_vec: &Vec<CST>) -> Exp {
    let mut left_p = false;
    let mut right_p = false;
    for tok in cur_child_vec {
        match tok {
            CST::Node(kind, grandchilds) => return parse_exp(tok),
            CST::Token(kind, content) => match *kind {
                Kind::LParen => {
                    if !left_p && !right_p {
                        left_p = true
                    } else {
                        unreachable!()
                    }
                }
                Kind::RParen => {
                    if !right_p && left_p {
                        right_p = true;
                    } else {
                        unreachable!()
                    }
                }
                _ => unreachable!(),
            },
        }
    }
    unreachable!()
}

/// parse bool exp
fn parse_bool_exp_node(kind: Kind, cur_child_vec: &Vec<CST>) -> Exp {
    let mut op = None;
    let mut args = Vec::new();
    let mut expect_node = true; // ping-pong parse node and op token
    for elem in cur_child_vec {
        match elem {
            CST::Node(kind, grandchilds) => {
                args.push(parse_exp(elem));
                assert_eq!(expect_node, true);
                expect_node = false;
            }
            CST::Token(kind, _) => {
                if op.is_none() {
                    op = Some(*kind);
                } else {
                    assert_eq!(op, Some(*kind));
                }
                assert_eq!(expect_node, false);
                expect_node = true;
            }
        }
    }
    Exp::BoolOp {
        op: op.unwrap(),
        args,
    }
}

/// parse i.e. `a[1][2][3]`
fn parse_subscript_exp_node(kind: Kind, cur_child_vec: &Vec<CST>) -> Exp {
    let mut cur_exp: Option<Exp> = None;
    let mut cnt_pair = 0;
    for elem in cur_child_vec {
        match elem {
            CST::Token(Kind::Ident, content) => {
                if cur_exp.is_none() {
                    cur_exp = Some(Exp::Name(content.to_owned()));
                } else {
                    unreachable!()
                }
            }
            CST::Token(Kind::LBracket, _) => {
                cnt_pair += 1;
                assert_eq!(cnt_pair, 1);
            }
            CST::Token(Kind::RBracket, _) => {
                cnt_pair -= 1;
                assert_eq!(cnt_pair, 0);
            }
            CST::Node(_, _) => {
                let ret = parse_exp(elem);
                cur_exp = Some(Exp::Subscript {
                    value: Box::new(cur_exp.unwrap()),
                    slice: Box::new(ret),
                });
            }
            _ => unreachable!(),
        }
    }
    cur_exp.unwrap()
}
/// parse compare exp
fn parse_compare_exp_node(kind: Kind, cur_child_vec: &Vec<CST>) -> Exp {
    let mut ops = Vec::new();
    let mut left = None;
    let mut comparators = Vec::new();
    let mut expect_node = true; // ping-pong parse node and op token
    for elem in cur_child_vec {
        match elem {
            CST::Node(kind, grandchilds) => {
                if left.is_none() {
                    left = Some(parse_exp(elem));
                } else {
                    comparators.push(parse_exp(elem));
                }
                assert_eq!(expect_node, true);
                expect_node = false;
            }
            CST::Token(kind, _) => {
                ops.push(*kind);
                assert_eq!(expect_node, false);
                expect_node = true;
            }
        }
    }
    Exp::CmpOp {
        op: ops,
        left: Box::new(left.unwrap()),
        comparators,
    }
}

/// parse binary exp in right associativity
fn parse_binary_exp_node(kind: Kind, cur_child_vec: &Vec<CST>) -> Exp {
    let mut left = None;
    let mut op = None;
    for tok in cur_child_vec {
        match tok {
            CST::Node(kind, grandchilds) => {
                if left.is_none() {
                    left = Some(parse_exp(tok));
                } else if op.is_some() {
                    let right = parse_exp(tok);
                    // lfet op right
                    left = Some(Exp::BinOp {
                        op: op.unwrap(),
                        left: Box::new(left.unwrap()),
                        right: Box::new(right),
                    })
                } else {
                    unreachable!()
                }
            }
            CST::Token(kind, _content) => {
                op = Some(*kind);
            }
        }
    }
    return left.unwrap();
}

/// given a Exp in CST, return AST
///
/// `text` is the source code
/// TODO: change it to use simple ron style CST
fn parse_exp(node: &CST) -> Exp {
    if let CST::Node(node_kind, child_vec) = node {
        let (mut cur_node_kind, mut cur_child_vec) = (node_kind, child_vec);
        loop {
            let child_cnt = cur_child_vec.len();
            if child_cnt != 1 {
                break;
            }
            match cur_child_vec.get(0).unwrap() {
                CST::Node(kind, child_elem) => {
                    (cur_node_kind, cur_child_vec) = (kind, child_elem);
                    //cur_child_vec = child_elem;
                }
                CST::Token(kind, content) => {
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
        match *cur_node_kind {
            Kind::PrimaryExp => return parse_primary_exp_node(*cur_node_kind, cur_child_vec),
            Kind::UnaryExp => return parse_unary_exp_node(*cur_node_kind, cur_child_vec),
            // a series of BinOp and LogicOp
            // BinOp CmpOp BoolOp
            // in cst have similar storage pattern:
            // exp op exp op...
            // all deals in different way
            // BinOp: .... to right associtivity
            // TODO: test this arm
            Kind::MulExp | Kind::AddExp => {
                return parse_binary_exp_node(*cur_node_kind, cur_child_vec)
            }

            // CmpOp: a array of op and exp
            // note eq and rel is separate in cst so should be seprarte in ast
            // TODO:test
            Kind::RelationExp | Kind::EqExp => {
                return parse_compare_exp_node(*cur_node_kind, cur_child_vec)
            }
            // BoolOp: a single op and a array of exp
            // TODO: test
            Kind::LogicAndExp | Kind::LogicOrExp => {
                return parse_bool_exp_node(*cur_node_kind, cur_child_vec)
            }
            Kind::LeftValue => {
                // more than one child elems means subscript
                return parse_subscript_exp_node(*cur_node_kind, cur_child_vec);
            }
            _ => (),
        }
    }
    // go all the way deeper until there is a token or there is more than one child
    // for simpler tree
    unreachable!()
}
use std::fs::File;
use std::path::Path;
fn load_test_cases(path: &Path) -> CST {
    let mut file = File::open(path).expect("Fail to open file.");
    use ron::de::from_reader;
    let ret: CST = from_reader(file).expect("Wrong format");
    ret
}

#[test]
fn test_subscript_exp() {
    use ron::de::from_str;
    use ron::ser::{to_string_pretty, PrettyConfig};
    let res = load_test_cases(Path::new("test_cases/ast/subscript.ron"));
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );
    let exp = parse_exp(&res);
    println!(
        "AST:\n{}",
        to_string_pretty(&exp, pretty.to_owned()).unwrap()
    );
    let res: Exp = from_str(
        r#"Subscript(
            value: Subscript(
                value: Name("a"),
                slice: Constant(Int(1)),
            ),
            slice: BinOp(
                op: OpAdd,
                left: Constant(Int(2)),
                right: Constant(Int(3)),
            ),
        )"#,
    )
    .expect("Wrong format");
    assert_eq!(exp, res);
}

#[test]
fn test_logic_exp() {
    use ron::de::from_str;
    use ron::ser::{to_string_pretty, PrettyConfig};
    let res = load_test_cases(Path::new("test_cases/ast/logic_exp.ron"));
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );
    let exp = parse_exp(&res);
    println!(
        "AST:\n{}",
        to_string_pretty(&exp, pretty.to_owned()).unwrap()
    );
    let res: Exp = from_str(
        "BoolOp(
            op: OpOr,
            args: [
                BoolOp(
                    op: OpAnd,
                    args: [
                        Constant(Int(1)),// [0]
                        Constant(Int(2)),
                    ],
                ),// [0]
                BoolOp(
                    op: OpAnd,
                    args: [
                        Constant(Int(3)),// [0]
                        Constant(Int(4)),// [1]
                        Constant(Int(5)),
                    ],
                ),
            ],
        )",
    )
    .expect("Wrong format");
    assert_eq!(exp, res);
}

#[test]
fn test_compare_exp() {
    use ron::de::from_str;
    use ron::ser::{to_string_pretty, PrettyConfig};
    let res = load_test_cases(Path::new("test_cases/ast/cmp_exp.ron"));
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );
    let exp = parse_exp(&res);
    println!(
        "AST:\n{}",
        to_string_pretty(&exp, pretty.to_owned()).unwrap()
    );
    let res: Exp = from_str(
        "CmpOp(
            op: [
                OpLT,// [0]
                OpGT,// [1]
                OpNG,
            ],
            left: Constant(Int(1)),
            comparators: [
                Constant(Int(2)),// [0]
                Constant(Float(1.5)),// [1]
                Constant(Int(4)),
            ],
        )",
    )
    .expect("Wrong format");
    assert_eq!(exp, res);
}

#[test]
fn test_binary_exp() {
    use ron::de::from_str;
    use ron::ser::{to_string_pretty, PrettyConfig};
    let res = load_test_cases(Path::new("test_cases/ast/binary_exp.ron"));
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );
    let exp = parse_exp(&res);
    println!(
        "AST:\n{}",
        to_string_pretty(&exp, pretty.to_owned()).unwrap()
    );
    let res: Exp = from_str(
        "
    BinOp(
        op: OpAdd,
        left: BinOp(
            op: OpAdd,
            left: Constant(Int(1)),
            right: Constant(Int(2)),
        ),
        right: BinOp(
            op: OpMul,
            left: Constant(Int(3)),
            right: Constant(Int(4)),
        ),
    )",
    )
    .expect("Wrong format");
    assert_eq!(exp, res);
}

#[test]
fn test_primary_exp() {
    use ron::de::from_str;
    use ron::ser::{to_string_pretty, PrettyConfig};
    let res = load_test_cases(Path::new("test_cases/ast/primary_exp.ron"));
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );
    let exp = parse_exp(&res);
    println!(
        "AST:\n{}",
        to_string_pretty(&exp, pretty.to_owned()).unwrap()
    );
    let res: Exp = from_str("Constant(Int(1))").expect("Wrong format");
    assert_eq!(exp, res);
}

#[test]
fn test_unary_exp() {
    use ron::de::from_str;
    use ron::ser::{to_string_pretty, PrettyConfig};
    let res = load_test_cases(Path::new("test_cases/ast/unary_exp.ron"));
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );
    let exp = parse_exp(&res);
    println!(
        "AST:\n{}",
        to_string_pretty(&exp, pretty.to_owned()).unwrap()
    );
    let res: Exp = from_str(
        "UnaryOp(
        op: OpSub,
        val: Constant(Int(1)),
    )",
    )
    .expect("Wrong format");
    //assert_eq!(exp, res);
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
            a[1][2+3];
        }";
    let parse = parse(text);
    let node = parse.syntax();
    let res = into_ron_tree(&node, text, true);
    println!("Errors:{:?}", parse.errors);
    let pretty = PrettyConfig::new()
        .separate_tuple_members(false)
        //.indentor("  ".to_string())
        .enumerate_arrays(true);
    println!(
        "Ron Tree:\n{}",
        to_string_pretty(&res, pretty.to_owned()).unwrap()
    );

    //let mut out  = String::new();
    //output_cst(&node, 0, text, &mut out, "│");
    //println!("CST:{}", out);
}
