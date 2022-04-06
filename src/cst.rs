//! Concrete Synatx Tree
use crate::syntax::{Lang, SyntaxKind};

use rowan::GreenNode;

use rowan::GreenNodeBuilder;

pub struct Parse {
    green_node: GreenNode,
    #[allow(unused)]
    errors: Vec<String>,
}

/// To work with the parse results we need a view into the
/// green tree - the Syntax tree.
/// It is also immutable, like a GreenNode,
/// but it contains parent pointers, offsets, and
/// has identity semantics.

type SyntaxNode = rowan::SyntaxNode<Lang>;
#[allow(unused)]
type SyntaxToken = rowan::SyntaxToken<Lang>;
#[allow(unused)]
type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;

impl Parse {
    /// view from SyntaxNode root
    fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green_node.clone())
    }
}

pub struct Parser {
    /// input tokens, including whitespace and comment
    tokens: Vec<(SyntaxKind, String)>,
    /// the in-progress tree.
    builder: GreenNodeBuilder<'static>,
    /// the list of syntax errors we've accumulated
    /// so far.
    errors: Vec<String>,
}
use SyntaxKind as Kind;

/// macro use to quickly gen code for exp0 => exp1 | exp1 op exp0
/// `cur` is self
///
/// `child` calling method for exp1
///
/// multiple concat_op for pattern match
macro_rules! ConcatExp {
    ($cur: ident,$child: ident ,$($concat_op:pat ),*) => {
        $cur.$child();
        loop{
            match $cur.current(){
                $(
                Some($concat_op))|* => {
                    $cur.bump();
                    $cur.$child();
                },
                _ => break
            }
        };
    }
}
impl Parser {
    fn new(mut tokens: Vec<(SyntaxKind, String)>) -> Self {
        tokens.reverse();
        Parser {
            tokens: tokens,
            builder: GreenNodeBuilder::new(),
            errors: Vec::new(),
        }
    }
    /// start parsing
    fn parse(mut self) -> Parse {
        unimplemented!()
    }
    /// Advance one token, adding it to the current branch of the tree builder.
    fn bump(&mut self) {
        self.skip_ws_cmt();
        let (mut kind, mut text) = self.tokens.pop().unwrap();
        self.builder.token(kind.into(), text.as_str());
    }
    /// bump expected token or push a error node with given error message
    fn bump_expect(&mut self, expected: Kind, err_msg: &str) {
        self.skip_ws_cmt();
        match self.current() {
            Some(out) => {
                if expected == out {
                    self.bump()
                } else {
                    let mut std_err_msg = format!(
                        "Expect {}, found {}. ",
                        String::from(expected),
                        String::from(out)
                    );
                    std_err_msg.push_str(&err_msg);
                    self.push_err(std_err_msg.as_str());
                }
            }
            _ => self.push_err(err_msg),
        }
    }
    /// Push a error node(BUG!)
    fn push_err(&mut self, err_msg: &str) {
        self.builder.start_node(SyntaxKind::Error.into());
        self.errors.push(err_msg.to_string());
        if !self.tokens.is_empty() {
            self.bump();
        }
        self.builder.finish_node();
    }
    /// Peek at the first unprocessed token
    fn current(&self) -> Option<SyntaxKind> {
        self.tokens.last().map(|(kind, _)| *kind)
    }
    /// Peek ahead
    ///
    /// `peek(0) == current()`
    fn peek(&self, ahead: usize) -> Option<SyntaxKind> {
        if self.tokens.len() < 1 + ahead {
            return None;
        };
        if let Some((kind, _)) = self.tokens.get(self.tokens.len() - 1 - ahead) {
            Some(*kind)
        } else {
            None
        }
    }
    /// skip whitespace and comment
    fn skip_ws_cmt(&mut self) {
        use SyntaxKind::{Comment, Whitespace};
        while self.current() == Some(Whitespace) || self.current() == Some(Comment) {
            // skip all whitespace and push them into current node
            let (mut kind, mut text) = self.tokens.pop().unwrap();
            self.builder.token(kind.into(), text.as_str());
        }
    }
    /// CompUnit -> (Decl | FuncDef) +
    ///
    /// TODO: uncomplete
    fn comp_unit(&mut self) {
        self.builder.start_node(SyntaxKind::CompUnit.into());
        loop {
            match self.peek(0) {
                Some(SyntaxKind::ConstKeyword) => {
                    self.const_decl();
                }
                Some(Kind::BType) => {
                    // determine if it's a VarDec or a FuncDef
                    match self.peek(2) {
                        Some(Kind::LParen) => {
                            unimplemented!()
                        }
                        _ => self.decl(),
                    }
                }
                _ => break,
            }
        }
        self.builder.finish_node();
    }
    /// FuncDef → FuncType Ident '(' \[FuncFParams\] ')' Block
    fn func_def(&mut self) {
        self.builder.start_node(SyntaxKind::FuncDef.into());
        let expected = [Kind::BType, Kind::Ident, Kind::LParen];
        for e in expected {
            self.bump_expect(e, format!("Expect {}", String::from(e)).as_str());
        }
        self.func_formal_params();
        self.bump_expect(Kind::RParen, "Expect `)`");
        self.block();
        self.builder.finish_node();
    }
    /// FuncFParam { ',' FuncFParam }
    fn func_formal_params(&mut self) {
        self.builder.start_node(SyntaxKind::FuncFParams.into());
        ConcatExp!(self, func_formal_param, Kind::Comma);
        self.builder.finish_node();
    }
    /// FuncFParam → BType Ident ['[' ']' { '[' Exp ']' }]
    fn func_formal_param(&mut self) {
        self.builder.start_node(SyntaxKind::FuncFParam.into());
        self.bump_expect(
            Kind::BType,
            format!("Expect {}.", String::from(Kind::BType)).as_str(),
        );
        self.bump_expect(
            Kind::Ident,
            format!("Expect {}.", String::from(Kind::Ident)).as_str(),
        );
        if let Some(Kind::LBracket) = self.current() {
            self.bump();
            self.bump_expect(
                Kind::RBracket,
                format!("Expect {}.", String::from(Kind::RBracket)).as_str(),
            );
            while let Some(Kind::LBracket) = self.current() {
                self.bump();
                self.exp();
                self.bump_expect(
                    Kind::RBracket,
                    format!("Expect {}.", String::from(Kind::RBracket)).as_str(),
                );
            }
        }
        self.builder.finish_node();
    }
    /// Block → '{' { BlockItem } '}'
    fn block(&mut self) {
        self.builder.start_node(SyntaxKind::Block.into());
        self.bump_expect(Kind::LCurly, "");
        if Some(Kind::RCurly) != self.current(){
            self.block_item();
        }
        self.bump_expect(Kind::RCurly, "");
        self.builder.finish_node();
    }

    /// BlockItem → Decl | Stmt
    fn block_item(&mut self) {
        self.builder.start_node(SyntaxKind::BlockItem.into());
        match self.current() {
            Some(Kind::ConstKeyword) | Some(Kind::BType) => self.decl(),
            _ => self.stmt(),
        }
        self.builder.finish_node();
    }
    /// Stmt → LVal '=' Exp ';' | \[Exp\] ';' | Block
    ///
    /// | 'if' '( Cond ')' Stmt \[ 'else' Stmt \]
    ///
    /// | 'while' '(' Cond ')' Stmt
    ///
    /// | 'break' ';' | 'continue' ';'
    ///
    /// | 'return' \[Exp\] ';'
    fn stmt(&mut self) {
        use Kind::{
            BreakKeyword, ContinueKeyword, ElseKeyword, Ident, IfKeyword, LCurly, LParen,
            OpAsg, RParen, ReturnKeyword, Semicolon, WhileKeyword,
        };
        self.builder.start_node(SyntaxKind::Statement.into());
        match self.current() {
            Some(Ident) => {
                // Stmt → LVal '=' Exp ';' | \[Exp\] ';'
                // check ahead to see if a `=` exist in this line of code
                let mut flag = false;
                let mut ahead = 0;
                // TODO: better predicate
                while self.peek(ahead) != Some(Semicolon) {
                    match self.peek(ahead) {
                        Some(OpAsg) => {
                            flag = true;
                            break;
                        }
                        _ => (),
                    }
                    ahead += 1;
                }
                if flag {
                    self.left_value();
                    self.bump_expect(OpAsg, "");
                    self.exp();
                } else {
                    self.exp();
                }
                self.bump_expect(Semicolon, "");
            }
            Some(Semicolon) => self.bump(),
            Some(LCurly) => self.block(),
            Some(IfKeyword) => {
                self.bump();
                self.bump_expect(LParen, "");
                self.cond();
                self.bump_expect(RParen, "");
                self.stmt();
                if let Some(ElseKeyword) = self.current() {
                    self.bump();
                    self.stmt();
                }
            }
            Some(WhileKeyword) => {
                self.bump();
                self.bump_expect(LParen, "");
                self.cond();
                self.bump_expect(RParen, "");
                self.stmt();
            }
            Some(BreakKeyword) | Some(ContinueKeyword) => {
                self.bump();
                self.bump_expect(Semicolon, "");
            }
            Some(ReturnKeyword) => {
                self.bump();
                if Some(Semicolon) != self.current() {
                    self.exp();
                }
                self.bump_expect(Semicolon, "");
            }

            _ => {
                if Some(Semicolon) != self.current() {
                    self.exp();
                }
                self.bump_expect(Semicolon, "");
            }
        }
        self.builder.finish_node();
    }
    fn cond(&mut self) {
        self.builder.start_node(SyntaxKind::Condition.into());
        self.logic_or_exp();
        self.builder.finish_node();
    }
    /// Decl -> ConstDecl | VarDecl
    fn decl(&mut self) {
        self.builder.start_node(SyntaxKind::Decl.into());
        match self.current() {
            Some(Kind::ConstKeyword) => self.const_decl(),
            _ => self.var_decl(),
        }
        self.builder.finish_node();
    }
    fn var_decl(&mut self) {
        self.builder.start_node(SyntaxKind::VarDecl.into());
        self.b_type();
        self.var_def();
        while let Some(Kind::Comma) = self.current() {
            self.bump();
            self.var_def();
        }
        self.builder.finish_node();
    }
    /// VarDef -> Ident { '\[' ConstExp '\]' }
    ///
    /// | Ident { '\[' ConstExp '\]' } '=' InitVal
    fn var_def(&mut self) {
        self.builder.start_node(SyntaxKind::VarDef.into());
        self.bump_expect(Kind::Ident, "expect a identifier");
        // { '\[' ConstExp '\]' }
        if Some(Kind::LBracket) == self.current() {
            while let Some(Kind::LBracket) = self.current() {
                self.bump(); //[
                self.const_exp();
                self.bump_expect(Kind::RBracket, "Expect `]`");
            }
        }
        // '=' InitVal
        match self.current() {
            Some(Kind::OpAsg) => {
                self.bump();
                self.init_val();
            }
            _ => self.push_err("Expect `=`"),
        }
        self.builder.finish_node();
    }
    /// Exp | '{' \[ InitVal { ',' InitVal } \] '}'
    fn init_val(&mut self) {
        self.builder.start_node(SyntaxKind::InitVal.into());
        match self.current() {
            Some(Kind::LCurly) => {
                self.bump();
                if Some(Kind::RCurly) != self.current() {
                    self.init_val();
                    while let Some(Kind::Comma) = self.current() {
                        self.bump();
                        self.init_val();
                    }
                }
                self.bump_expect(Kind::RCurly, "Expect `}`");
            }
            _ => self.exp(),
        }
        self.builder.finish_node();
    }
    /// ConstDecl -> `const` BType ConstDef {`,` ConstDef }`;`
    fn const_decl(&mut self) {
        self.builder.start_node(SyntaxKind::ConstDecl.into());
        match self.current() {
            Some(Kind::ConstKeyword) => {
                self.bump(); // eat `const`
                self.b_type();
                loop {
                    match self.current() {
                        Some(Kind::Comma) => {
                            self.bump();
                            self.const_def();
                        }
                        Some(Kind::Semicolon) => {
                            self.bump();
                            break;
                        }
                        _ => self.push_err("Expect `,` or `;`."),
                    }
                }
            }
            _ => {
                self.push_err("Expect `const`");
            }
        };
        self.builder.finish_node();
    }
    /// ConstDef -> Ident {`[` ConstExp `]` } `=` ConstInitVal
    fn const_def(&mut self) {
        self.builder.start_node(SyntaxKind::ConstDef.into());
        match self.current() {
            Some(Kind::Ident) => {
                self.bump();
                while let Some(Kind::LBracket) = self.current() {
                    self.bump();
                    self.const_exp();
                    self.bump_expect(Kind::RBracket, "Expect `]`");
                }
                self.bump_expect(Kind::OpAsg, "Expect `=`");
                self.const_init_val();
            }
            _ => self.push_err("Expect a identifier."),
        }
        self.builder.finish_node();
    }
    /// COnstInitVal => ConstExp | `{` [ ConstInitVal { `,`ConstInitVal } ] `}`
    fn const_init_val(&mut self) {
        self.builder.start_node(SyntaxKind::ConstInitVal.into());
        match self.current() {
            Some(Kind::LCurly) => {
                self.bump();
                if self.current() != Some(Kind::RCurly) {
                    self.const_init_val();
                    while let Some(Kind::Comma) = self.current() {
                        self.bump();
                        self.const_init_val();
                    }
                }
                self.bump_expect(Kind::RCurly, "Expect `}`");
            }
            _ => self.const_exp(),
        }
        self.builder.finish_node();
    }
    fn const_exp(&mut self) {
        self.builder.start_node(SyntaxKind::ConstExp.into());
        self.add_exp();
        self.builder.finish_node();
    }
    /// BType -> `int` | `float`
    fn b_type(&mut self) {
        self.builder.start_node(Kind::BType.into());
        self.bump_expect(Kind::BType, "Expect `int` or `float`");
        self.builder.finish_node();
    }

    /// Expression -> AddExp
    fn exp(&mut self) {
        self.builder.start_node(Kind::Expression.into());
        self.add_exp();
        self.builder.finish_node();
    }
    /// LVal -> Ident { `[` Exp `]` }
    fn left_value(&mut self) {
        self.builder.start_node(Kind::LeftValue.into());
        if let Some(Kind::Ident) = self.current() {
            self.bump();
            while let Some(Kind::LBracket) = self.current() {
                self.bump();
                self.exp();
                self.bump_expect(Kind::RBracket, "Expect `]`");
            }
        }
        self.builder.finish_node();
    }
    /// PrimaryExp -> `(` Exp `)` | LVal | Number
    fn primary_exp(&mut self) {
        self.builder.start_node(Kind::PrimaryExp.into());
        match self.current() {
            Some(Kind::LParen) => {
                self.bump();
                self.exp();
                self.bump_expect(Kind::RParen, "Expect `)`.");
            }
            Some(Kind::Ident) => self.left_value(),
            Some(Kind::IntConst) | Some(Kind::FloatConst) => self.number(),
            _ => {
                self.push_err("Expect Left parthness or left value or a number.");
            }
        }
        self.builder.finish_node();
    }

    /// Number -> IntConst | FloatConst
    fn number(&mut self) {
        self.builder.start_node(Kind::Number.into());
        match self.current() {
            Some(Kind::IntConst) | Some(Kind::FloatConst) => self.bump(),
            _ => self.push_err("Expect int number or floating number."),
        }
        self.builder.finish_node();
    }
    /// UnaryExp -> PrimaryExp | Ident `(`\[ FuncRParams \]`)` | UnaryOp UnaryExp
    fn unary_exp(&mut self) {
        self.builder.start_node(Kind::UnaryExp.into());
        match (self.current(), self.peek(1)) {
            (Some(Kind::Ident), Some(Kind::LParen)) => {
                self.bump(); // ident
                self.bump_expect(Kind::LParen, "Expect `(`.");
                if self.current() != Some(Kind::RParen) {
                    self.func_real_params();
                }
                self.bump_expect(Kind::RParen, "Expect `)`.");
            }
            //(Some(Kind::Ident), _) => self.primary_exp(),
            (Some(Kind::OpAdd), _) | (Some(Kind::OpSub), _) | (Some(Kind::OpNot), _) => {
                self.bump();
                self.unary_exp();
            }
            _ => self.primary_exp(), //self.push_err("Expect primary exp or f(..) or unary exp like -1"),
        }
        self.builder.finish_node();
    }
    /// FuncRParams -> Exp {`,` Exp}
    fn func_real_params(&mut self) {
        self.builder.start_node(Kind::FuncRParams.into());
        ConcatExp!(self, exp, Kind::Comma);
        self.builder.finish_node();
    }

    /// MulExp -> UnaryExp | UnaryExp (`*`|`/`|`%`) MulExp
    fn mul_exp(&mut self) {
        self.builder.start_node(Kind::MulExp.into());
        ConcatExp!(self, unary_exp, Kind::OpMul, Kind::OpDiv, Kind::OpMod);
        self.builder.finish_node();
    }
    /// AddExp -> MulExp | MulExp (`+`|`-`) AddExp
    fn add_exp(&mut self) {
        self.builder.start_node(Kind::AddExp.into());
        ConcatExp!(self, mul_exp, Kind::OpAdd, Kind::OpSub);
        self.builder.finish_node();
    }
    /// RelExp -> AddExp | RelExp (`<`|`>`|`<=`|`>=`)AddExp
    fn rel_exp(&mut self) {
        self.builder.start_node(Kind::RelationExp.into());
        ConcatExp!(
            self,
            add_exp,
            Kind::OpLT,
            Kind::OpGT,
            Kind::OpNG,
            Kind::OpNL
        );
        self.builder.finish_node();
    }
    /// EqExp -> RelExp | EqExp(`==`|`!=`)RelExp
    fn eq_exp(&mut self) {
        self.builder.start_node(Kind::EqExp.into());
        ConcatExp!(self, rel_exp, Kind::OpEQ, Kind::OpNE);
        self.builder.finish_node();
    }
    /// LogicAndExp -> EqExp | LogicAndExp `&&`EqExp
    fn logic_and_exp(&mut self) {
        self.builder.start_node(Kind::LogicAndExp.into());
        ConcatExp!(self, eq_exp, Kind::OpAnd);
        self.builder.finish_node();
    }
    // LogicOrExp -> LAndExp | LOrExp `||` LAndExp
    fn logic_or_exp(&mut self) {
        self.builder.start_node(Kind::LogicOrExp.into());
        ConcatExp!(self, logic_and_exp, Kind::OpOr);
        self.builder.finish_node();
    }
}

pub fn parse(text: &str) -> Parse {
    use crate::lex::lex;
    let text = r"hello=world";
    let tokens: Vec<(SyntaxKind, String)> = lex(text)
        .into_iter()
        .map(|tok| {
            (
                tok.1,
                text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap().to_owned(),
            )
        })
        .collect();
    Parser::new(tokens).parse()
}

#[cfg(test)]
mod tests {
    use super::{Parse, Parser, SyntaxElement, SyntaxNode};
    use crate::lex::lex;
    use crate::syntax::SyntaxKind as Kind;
    fn lex_into_tokens(text: &str) -> Vec<(Kind, String)> {
        let tokens: Vec<(Kind, String)> = lex(text)
            .into_iter()
            .map(|tok| {
                (
                    tok.1,
                    text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap().to_owned(),
                )
            })
            .collect();
        tokens
    }
    /// output cst into a string.
    ///
    /// `tab` is spacing for child node
    fn output_cst(node: &SyntaxNode, depth: usize, text: &str, output: &mut String, tab: &str) {
        //let tab = "    ";
        let child_spaces: String = (0..depth + 1).map(|_| tab).collect();
        let spaces: String = (0..depth).map(|_| tab).collect();
        let dis_node = format!("{}{:?}\n", spaces, node);
        output.push_str(&dis_node);
        //print!("{}",dis_node);
        let _ = node
            .children_with_tokens()
            .map(|child| {
                match child {
                    SyntaxElement::Node(node) => {
                        output_cst(&node, depth + 1, text, output, tab);
                    }
                    SyntaxElement::Token(token) => {
                        let res = format!(
                            "{}{:?}@{:?} \"{}\"\n",
                            child_spaces,
                            token.kind(),
                            token.text_range(),
                            text.get(
                                token.text_range().start().into()..token.text_range().end().into()
                            )
                            .unwrap()
                        );
                        //print!("{}", res);
                        output.push_str(&res);
                    }
                }
            })
            .count();
    }
    fn print_cst(node: &SyntaxNode, depth: usize, text: &str) {
        //let node = tree.syntax();
        let child_spaces: String = (0..depth + 1).map(|_| ' ').collect();
        let spaces = child_spaces.get(0..depth).unwrap();
        println!("{}{:?}", spaces, node);
        let _ = node
            .children_with_tokens()
            .map(|child| match child {
                SyntaxElement::Node(node) => {
                    print_cst(&node, depth + 1, text);
                }
                SyntaxElement::Token(token) => {
                    println!(
                        "{}{:?}@{:?} \"{}\"",
                        child_spaces,
                        token.kind(),
                        token.text_range(),
                        text.get(
                            token.text_range().start().into()..token.text_range().end().into()
                        )
                        .unwrap()
                    )
                }
            })
            .count();
    }
    /// standard operation producure for test parser
    ///
    /// take input `text` and a top-down parse function `f`
    fn test_sop<F>(text: &str, f: F, tab: &str) -> String
    where
        F: Fn(&mut Parser),
    {
        let tokens: Vec<(Kind, String)> = lex_into_tokens(text);
        println!("Tokens: {:?}", tokens);
        let mut parser = Parser::new(tokens);
        f(&mut parser);
        let res = Parse {
            green_node: parser.builder.finish(),
            errors: parser.errors,
        };
        let node = res.syntax();
        if !res.errors.is_empty() {
            println!("{:?}", res.errors);
        }
        let mut res = String::new();
        output_cst(&node, 0, text, &mut res, tab);
        print!("CST:\n{}\n", res);
        res
    }
    #[test]
    fn test_func_def(){
        {
            println!("Test 1");
            // test LeftValue-> Ident
            let text = "void main(int args, int argv[]){}";
            let res = test_sop(text, Parser::func_def, "|");
            
        }
    }
    #[test]
    fn test_stmt() {
        {
            println!("Test 1");
            // test LeftValue-> Ident
            let text = "a[0]=b[1];";
            let res = test_sop(text, Parser::stmt, "-");
            assert_eq!(
                r#"
Statement@0..10
-LeftValue@0..4
--Ident@0..1 "a"
--LBracket@1..2 "["
--Expression@2..3
---AddExp@2..3
----MulExp@2..3
-----UnaryExp@2..3
------PrimaryExp@2..3
-------Number@2..3
--------IntConst@2..3 "0"
--RBracket@3..4 "]"
-OpAsg@4..5 "="
-Expression@5..9
--AddExp@5..9
---MulExp@5..9
----UnaryExp@5..9
-----PrimaryExp@5..9
------LeftValue@5..9
-------Ident@5..6 "b"
-------LBracket@6..7 "["
-------Expression@7..8
--------AddExp@7..8
---------MulExp@7..8
----------UnaryExp@7..8
-----------PrimaryExp@7..8
------------Number@7..8
-------------IntConst@7..8 "1"
-------RBracket@8..9 "]"
-Semicolon@9..10 ";""#
                    .trim(),
                res.trim()
            );
        }
        {
            println!("Test 2");
            // test LeftValue-> Ident
            let text = "b[1];";
            let res = test_sop(text, Parser::stmt, "-");
            assert_eq!(
                r#"
Statement@0..5
-Expression@0..4
--AddExp@0..4
---MulExp@0..4
----UnaryExp@0..4
-----PrimaryExp@0..4
------LeftValue@0..4
-------Ident@0..1 "b"
-------LBracket@1..2 "["
-------Expression@2..3
--------AddExp@2..3
---------MulExp@2..3
----------UnaryExp@2..3
-----------PrimaryExp@2..3
------------Number@2..3
-------------IntConst@2..3 "1"
-------RBracket@3..4 "]"
-Semicolon@4..5 ";"
                "#
                .trim(),
                res.trim()
            );
        }
    }
    #[test]
    fn test_exp() {
        {
            println!("Test 1");
            // test LeftValue-> Ident
            let text = "abc123";
            let res = test_sop(text, Parser::left_value, "    ");
            assert_eq!(
                r#"LeftValue@0..6
    Ident@0..6 "abc123"
"#
                .trim(),
                res.trim()
            );
        }
        {
            println!("Test 2");
            // test PrimaryExp -> LVal|Number
            let text = "abc123";
            let res = test_sop(text, Parser::primary_exp, "    ");
            assert_eq!(
                r#"PrimaryExp@0..6
    LeftValue@0..6
        Ident@0..6 "abc123"
"#
                .trim(),
                res.trim()
            );
        }
        {
            println!("Test 3");
            // UnaryExp -> PrimaryExp
            let text = "abc123";
            let res = test_sop(text, Parser::unary_exp, "    ");
            assert_eq!(
                r#"UnaryExp@0..6
    PrimaryExp@0..6
        LeftValue@0..6
            Ident@0..6 "abc123"
"#
                .trim(),
                res.trim()
            );
        }
        {
            println!("Test 4");
            let text = "abc123()";
            let res = test_sop(text, Parser::unary_exp, "    ");
            // UnaryExp ->  Ident (FuncRParams)
            assert_eq!(
                r#"UnaryExp@0..8
    Ident@0..6 "abc123"
    LParen@6..7 "("
    RParen@7..8 ")"
"#
                .trim(),
                res.trim()
            );
        }
        {
            println!("Test 5");
            let text = "-+!1";
            let res = test_sop(text, Parser::unary_exp, "    ");
            // UnaryExp ->  UnaryOp UnaryExp
            assert_eq!(
                r#"
UnaryExp@0..4
    OpSub@0..1 "-"
    UnaryExp@1..4
        OpAdd@1..2 "+"
        UnaryExp@2..4
            OpNot@2..3 "!"
            UnaryExp@3..4
                PrimaryExp@3..4
                    Number@3..4
                        IntConst@3..4 "1"
"#
                .trim(),
                res.trim()
            );
        }
        {
            println!("Test 6");
            let text = "1*2*3";
            let res = test_sop(text, Parser::mul_exp, "    ");
            // UnaryExp ->  UnaryOp UnaryExp
            assert_eq!(
                r#"
MulExp@0..5
    UnaryExp@0..1
        PrimaryExp@0..1
            Number@0..1
                IntConst@0..1 "1"
    OpMul@1..2 "*"
    UnaryExp@2..3
        PrimaryExp@2..3
            Number@2..3
                IntConst@2..3 "2"
    OpMul@3..4 "*"
    UnaryExp@4..5
        PrimaryExp@4..5
            Number@4..5
                IntConst@4..5 "3"
"#
                .trim(),
                res.trim()
            );
        }
        {
            println!("Test 7");
            let text = "-1*0+1<2==1<3&&2||3&&4";
            let res = test_sop(text, Parser::logic_or_exp, "-");
            assert_eq!(
                r#"
LogicOrExp@0..22
-LogicAndExp@0..16
--EqExp@0..13
---RelationExp@0..8
----AddExp@0..6
-----MulExp@0..4
------UnaryExp@0..2
-------OpSub@0..1 "-"
-------UnaryExp@1..2
--------PrimaryExp@1..2
---------Number@1..2
----------IntConst@1..2 "1"
------OpMul@2..3 "*"
------UnaryExp@3..4
-------PrimaryExp@3..4
--------Number@3..4
---------IntConst@3..4 "0"
-----OpAdd@4..5 "+"
-----MulExp@5..6
------UnaryExp@5..6
-------PrimaryExp@5..6
--------Number@5..6
---------IntConst@5..6 "1"
----OpLT@6..7 "<"
----AddExp@7..8
-----MulExp@7..8
------UnaryExp@7..8
-------PrimaryExp@7..8
--------Number@7..8
---------IntConst@7..8 "2"
---OpEQ@8..10 "=="
---RelationExp@10..13
----AddExp@10..11
-----MulExp@10..11
------UnaryExp@10..11
-------PrimaryExp@10..11
--------Number@10..11
---------IntConst@10..11 "1"
----OpLT@11..12 "<"
----AddExp@12..13
-----MulExp@12..13
------UnaryExp@12..13
-------PrimaryExp@12..13
--------Number@12..13
---------IntConst@12..13 "3"
--OpAnd@13..15 "&&"
--EqExp@15..16
---RelationExp@15..16
----AddExp@15..16
-----MulExp@15..16
------UnaryExp@15..16
-------PrimaryExp@15..16
--------Number@15..16
---------IntConst@15..16 "2"
-OpOr@16..18 "||"
-LogicAndExp@18..22
--EqExp@18..19
---RelationExp@18..19
----AddExp@18..19
-----MulExp@18..19
------UnaryExp@18..19
-------PrimaryExp@18..19
--------Number@18..19
---------IntConst@18..19 "3"
--OpAnd@19..21 "&&"
--EqExp@21..22
---RelationExp@21..22
----AddExp@21..22
-----MulExp@21..22
------UnaryExp@21..22
-------PrimaryExp@21..22
--------Number@21..22
---------IntConst@21..22 "4""#
                    .trim(),
                res.trim()
            );
        }
    }
    #[test]
    fn test_number() {
        use super::{Parse, Parser};
        use crate::lex::lex;
        use crate::syntax::SyntaxKind as Kind;
        let text = r"42.3";
        let tokens: Vec<(Kind, String)> = lex_into_tokens(text);
        println!("Tokens: {:?}", tokens);
        let mut parser = Parser::new(tokens);
        parser.number();
        let res = Parse {
            green_node: parser.builder.finish(),
            errors: parser.errors,
        };
        let node = res.syntax();
        let mut res = String::new();
        output_cst(&node, 0, text, &mut res, "    ");
        print!("CST:\n{}\n", res);
        assert_eq!(
            res,
            r#"Number@0..4
    FloatConst@0..4 "42.3"
"#, // root node, spanning 4 bytes
        );
        //assert_eq!(node.children().count(), 1);
    }
}
