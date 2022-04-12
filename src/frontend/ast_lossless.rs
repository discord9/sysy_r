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
            pub span: Span
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
    defs: Vec<Def>,
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
        if let Some(node) = elem.as_node() {
            for kind in kinds {
                if *kind != node.kind() {
                    return None;
                }
            }
            return Some(node);
        } else {
            return None;
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
    fn get_first_token_skip_ws_cmt(node: &SyntaxNode) -> Option<SyntaxToken> {
        Self::get_child_elem(node, true, true, false)
            .get(0)
            .unwrap()
            .as_token()
            .cloned()
    }

    pub fn parse_def(&mut self, node: &SyntaxNode) -> Def {
        todo!()
    }
    pub fn parse_btype_token(&mut self, token: &SyntaxToken) -> BasicType {
        assert_eq!(token.kind(), Kind::BType);
        let reskind = match token.text() {
            "void" => BasicTypeKind::Void,
            "int" => BasicTypeKind::Int,
            "float" => BasicTypeKind::Float,
            _ => unreachable!(),
        };
        BasicType {
            id: self.alloc_node_id(),
            kind: reskind,
            span: token.text_range().into(),
        }
    }
    pub fn parse_decl(&mut self, node: &SyntaxNode) -> Decl {
        let childs = Self::get_child_elem(node, true, true, false);
        let mut it_token = childs.iter();
        let mut cur_token = it_token.next().unwrap().as_token().unwrap();
        let is_const = cur_token.kind() == Kind::ConstKeyword;
        let btype = {
            let btype_cst = {
                if is_const {
                    it_token.next().unwrap().as_token().unwrap()
                } else {
                    cur_token
                }
            };
            self.parse_btype_token(btype_cst)
        };
        let it = node.children();
        let mut defs: Vec<Def> = Vec::new();
        for def_cst in it {
            defs.push(self.parse_def(&def_cst));
        }
        let reskind = DeclKind {
            is_const,
            btype,
            defs,
        };
        Decl {
            id: self.alloc_node_id(),
            kind: reskind,
            span: node.text_range().into(),
        }
    }

    /// Vec<DeclOrStatement>
    pub fn parse_block(&mut self, node: &SyntaxNode) -> Block {
        let block_items: Vec<_> = Self::get_child_elem(node, true, false, true)
            .iter()
            .map(|x| x.as_node().unwrap().clone())
            .collect();
        let mut lines: Vec<DeclOrStatement> = Vec::new();
        for block_item in block_items {
            let child_node = block_item.first_child().unwrap();
            match child_node.kind() {
                Kind::Decl => {
                    let decl = self.parse_decl(&child_node);
                    let line = DeclOrStatement {
                        id: self.alloc_node_id(),
                        kind: DeclOrStatementKind::Decl(decl),
                        span: child_node.text_range().into(),
                    };
                    lines.push(line);
                }
                Kind::Statement => {
                    let stmt = self.parse_stmt(&child_node);
                    let line = DeclOrStatement {
                        id: self.alloc_node_id(),
                        kind: DeclOrStatementKind::Statement(stmt),
                        span: child_node.text_range().into(),
                    };
                    lines.push(line);
                }
                _ => (),
            }
        }
        let reskind = BlockKind { items: lines };
        return Block {
            id: self.alloc_node_id(),
            kind: reskind,
            span: node.text_range().into(),
        };
    }

    /// all of the if while etc.
    pub fn parse_stmt(&mut self, node: &SyntaxNode) -> Statement {
        assert_eq!(node.kind(), Kind::Statement);
        let first = Self::get_first_token_skip_ws_cmt(node).unwrap();
        let mut it = node.children();
        match first.kind() {
            Kind::OpAsg => {
                let lval = self.parse_subscript_exp(&it.next().unwrap());
                let exp = self.parse_expr(&it.next().unwrap());
                let reskind = StatementKind::Assign {
                    target: lval,
                    value: exp,
                };
                return Statement {
                    id: self.alloc_node_id(),
                    kind: reskind,
                    span: node.text_range().into(),
                };
            }
            Kind::LCurly => {
                let block = self.parse_block(node);
                // parse block
                return Statement {
                    id: self.alloc_node_id(),
                    kind: StatementKind::Block(block),
                    span: node.text_range().into(),
                };
            }
            Kind::IfKeyword => {
                let cond = self.parse_expr(&it.next().unwrap());
                let stmt = self.parse_stmt(&it.next().unwrap());
                let else_stmt = {
                    if let Some(stmt) = it.next() {
                        Some(self.parse_stmt(&stmt))
                    } else {
                        None
                    }
                };
                let reskind = StatementKind::IfStmt {
                    cond: cond,
                    stmt: Box::new(stmt),
                    else_stmt: Box::new(else_stmt),
                };
                return Statement {
                    id: self.alloc_node_id(),
                    kind: reskind,
                    span: node.text_range().into(),
                };
            }
            Kind::WhileKeyword => {
                let cond = self.parse_expr(&it.next().unwrap());
                let stmt = self.parse_stmt(&it.next().unwrap());
                let reskind = StatementKind::WhileStmt {
                    cond,
                    stmt: Box::new(stmt),
                };
                return Statement {
                    id: self.alloc_node_id(),
                    kind: reskind,
                    span: node.text_range().into(),
                };
            }
            Kind::BreakKeyword => {
                return Statement {
                    id: self.alloc_node_id(),
                    kind: StatementKind::BreakStmt,
                    span: node.text_range().into(),
                }
            }
            Kind::ContinueKeyword => {
                return Statement {
                    id: self.alloc_node_id(),
                    kind: StatementKind::ContinueStmt,
                    span: node.text_range().into(),
                }
            }
            Kind::ReturnKeyword => {
                let exp_opt = {
                    if let Some(exp_cst) = it.next() {
                        Some(self.parse_expr(&exp_cst))
                    } else {
                        None
                    }
                };
                return Statement {
                    id: self.alloc_node_id(),
                    kind: StatementKind::ReturnStmt(exp_opt),
                    span: node.text_range().into(),
                };
            }
            _ => panic!("Expect statement CST node"),
        }
    }

    /// UnaryExp -> UnaryOp UnaryExp
    ///
    /// | Ident `(` FuncRParams `)`
    pub fn parse_unary_exp(&mut self, node: &SyntaxNode) -> Expr {
        let first = Self::get_first_token_skip_ws_cmt(&node);
        if let Some(token) = first {
            // UnaryExp -> UnaryOp UnaryExp
            // UnaryOp -> `+` | `-` | `!`
            if matches!(token.kind(), Kind::OpAdd | Kind::OpSub | Kind::OpNot) {
                let val = self.parse_expr(&node.first_child().unwrap());
                let reskind = ExprKind::UnaryOp {
                    op: token.kind(),
                    val: Box::new(val),
                };
                return Expr {
                    id: self.alloc_node_id(),
                    kind: reskind,
                    span: node.text_range().into(),
                };
            } else if matches!(token.kind(), Kind::Ident) {
                // UnaryExp -> Ident `(` FuncRParams `)`
                // FuncRParams → Exp { ',' Exp }
                let id = Self::get_first_token_skip_ws_cmt(&node).unwrap();
                let func_real_params = node.first_child().unwrap();
                let mut args = Vec::new();
                for exp_cst in func_real_params.children() {
                    args.push(self.parse_expr(&exp_cst));
                }
                let reskind = ExprKind::Call {
                    id: id.text().to_string(),
                    args: args,
                };
                return Expr {
                    id: self.alloc_node_id(),
                    kind: reskind,
                    span: node.text_range().into(),
                };
            } else {
                unreachable!()
            }
        };
        unreachable!()
    }

    /// PrimaryExp → '(' Exp ')'
    pub fn parse_primary_exp(&mut self, node: &SyntaxNode) -> Expr {
        return self.parse_expr(&node.first_child().unwrap());
    }

    /// parse bool exp
    ///
    /// exp op exp op exp ....
    ///
    /// op -> `&&` | `||`
    pub fn parse_bool_exp(&mut self, node: &SyntaxNode) -> Expr {
        let op = node.first_token().unwrap();
        let mut args = Vec::new();
        for exp_cst in node.children() {
            args.push(self.parse_expr(&exp_cst));
        }
        let reskind = ExprKind::BoolOp {
            op: op.kind(),
            args,
        };
        Expr {
            id: self.alloc_node_id(),
            kind: reskind,
            span: node.text_range().into(),
        }
    }

    /// parse binary exp in left associativity
    /// exp0 -> exp + exp - exp
    ///  (-, (+, exp,exp), exp)
    pub fn parse_binary_exp(&mut self, node: &SyntaxNode) -> Expr {
        let childs = Self::get_child_elem(node, true, true, true);
        let start_loc: usize = childs.get(0).unwrap().text_range().start().into();
        /// mark the range of end and start for span
        let mut end_loc = start_loc;
        let mut it = childs.iter();
        let first = it.next().unwrap().as_node().unwrap();
        end_loc = first.text_range().end().into();
        let mut left = self.parse_expr(first);

        while let Some(next) = it.next() {
            let op = next.as_token().unwrap().kind();
            let next = it.next().unwrap().as_node().unwrap();
            end_loc = next.text_range().end().into();
            let right = self.parse_expr(next);
            let reskind = ExprKind::BinOp {
                op: op,
                left: Box::new(left),
                right: Box::new(right),
            };
            left = Expr {
                id: self.alloc_node_id(),
                kind: reskind,
                span: Span(start_loc, end_loc),
            };
        }
        left
    }

    /// parse 1<2<3 to {op:[`<`,`<`],left:1, comparators:[2,3]}
    pub fn parse_compare_exp(&mut self, node: &SyntaxNode) -> Expr {
        let childs = Self::get_child_elem(node, true, true, true);
        let mut it = childs.iter();
        let first = it.next().unwrap().as_node().unwrap();
        let mut left = self.parse_expr(first);
        let mut ops = Vec::new();
        let mut comparators = Vec::new();
        while let Some(next) = it.next() {
            let op = next.as_token().unwrap().kind();
            ops.push(op);
            let next = it.next().unwrap().as_node().unwrap();
            let right = self.parse_expr(next);
            comparators.push(right);
        }
        let reskind = ExprKind::CmpOp {
            op: ops,
            left: Box::new(left),
            comparators,
        };
        Expr {
            id: self.alloc_node_id(),
            kind: reskind,
            span: node.text_range().into(),
        }
    }

    /// a[1][2][3] to sub(sub(sub(a,1),2),3)
    pub fn parse_subscript_exp(&mut self, node: &SyntaxNode) -> Expr {
        assert_eq!(node.kind(), Kind::LeftValue);

        let ident = Self::get_first_token_skip_ws_cmt(node).unwrap();
        let mut it = node.children();
        let mut sub_exp = Expr {
            id: self.alloc_node_id(),
            kind: ExprKind::Name(ident.text().to_string()),
            span: ident.text_range().into(),
        };
        let (mut start_loc, mut end_loc): (usize, usize) = (
            ident.text_range().start().into(),
            ident.text_range().end().into(),
        );
        while let Some(exp_cst) = it.next() {
            end_loc = exp_cst.text_range().end().into();
            let slice = self.parse_expr(&exp_cst);
            let reskind = ExprKind::Subscript {
                value: Box::new(sub_exp),
                slice: Box::new(slice),
            };
            sub_exp = Expr {
                id: self.alloc_node_id(),
                kind: reskind,
                span: Span(start_loc, end_loc),
            };
        }
        sub_exp
    }

    /// go over the single child tree until find a node that is:
    ///
    /// 1. have more than one childs
    ///
    /// or
    /// 2. have only one child but the child is a token
    pub fn parse_expr(&mut self, node: &SyntaxNode) -> Expr {
        {
            let mut node = node.clone();
            let mut childs = Self::get_child_elem(&node, true, true, true);

            while childs.len() == 1 {
                if let Some(child_node) = node.first_child() {
                    node = child_node;
                    childs = Self::get_child_elem(&node, true, true, true);
                } else {
                    break;
                }
            }

            if childs.len() == 1 {
                // only two possible: 1. a LVAL(ident) 2. a number
                let cur_node = node;
                match cur_node.kind() {
                    Kind::LeftValue => {
                        let ident = Self::get_first_token_skip_ws_cmt(&cur_node).unwrap();
                        let reskind = ExprKind::Name(ident.text().to_string());
                        return Expr {
                            id: self.alloc_node_id(),
                            kind: reskind,
                            span: ident.text_range().into(),
                        };
                    }
                    Kind::Number => {
                        return self.parse_expr(&cur_node);
                    }
                    _ => (),
                }
            } else {
                // other possibility of Expr
                //let first = Self::get_first_token_skip_ws_cmt(&node).unwrap();
                match node.kind() {
                    Kind::PrimaryExp => return self.parse_primary_exp(&node),
                    Kind::UnaryExp => return self.parse_unary_exp(&node),
                    /// binary op
                    Kind::MulExp | Kind::AddExp => return self.parse_binary_exp(&node),
                    // compare exp, can chain together for compare
                    Kind::RelationExp | Kind::EqExp => return self.parse_compare_exp(&node),
                    /// Bool exp, chain together with same BoolOp, for short circuit
                    Kind::LogicAndExp | Kind::LogicOrExp => return self.parse_bool_exp(&node),
                    // more than one child elems means subscript
                    Kind::LeftValue => return self.parse_subscript_exp(&node),
                    _ => panic!("Expect one type of *Exp CST Node"),
                }
                todo!()
            }
        }
        //panic!("Expect a node");

        unreachable!()
    }

    /// Accept a Number compsite node
    pub fn parse_number(&mut self, elem: &SyntaxElement) -> IntOrFloat {
        if let Some(node) = elem.as_node() {
            if !matches!(node.kind(), Kind::Number) {
                panic!("Expect a number node");
            }
            let tok = Self::get_first_token_skip_ws_cmt(node).expect("Expect a number");
            let reskind = match tok.kind() {
                Kind::IntConst => IntOrFloatKind::Int(tok.text().parse::<i32>().unwrap()),
                Kind::FloatConst => IntOrFloatKind::Float(tok.text().parse::<f32>().unwrap()),
                _ => panic!("Expect a float or int"),
            };
            return IntOrFloat {
                id: self.alloc_node_id(),
                kind: reskind,
                span: tok.text_range().into(),
            };
        }
        panic!("Expect a Number CST Node.")
    }
}
