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
        let (kind, text) = self.tokens.pop().unwrap();
        self.builder.token(kind.into(), text.as_str());
    }
    /// bump expected token or push a error node with given error message
    fn bump_expect(&mut self, expected: Kind, err_msg: &str) {
        match self.current() {
            Some(out) => {
                if expected == out {
                    self.bump()
                } else {
                    self.push_err(err_msg);
                }
            }
            _ => self.push_err(err_msg),
        }
    }
    /// Push a error node(BUG!)
    fn push_err(&mut self, err_msg: &str) {
        self.builder.start_node(SyntaxKind::Error.into());
        self.errors.push(err_msg.to_string());
        if !self.tokens.is_empty(){
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
            self.bump()
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
                    unimplemented!()
                }
                Some(Kind::BType) => {
                    unimplemented!()
                }
                _ => break,
            }
        }
        self.builder.finish_node();
    }
    /// Decl -> ConstDecl | VarDecl
    fn decl(&mut self) {}
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
    /// ConstDef -> Ident {`[` ConstExp `]` `=` ConstInitVal}
    fn const_def(&mut self) {
        unimplemented!()
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
            while let Some(Kind::LSquare) = self.current() {
                self.bump();
                self.exp();
                self.bump_expect(Kind::RSquare, "Expect `]`");
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
                if self.current()!=Some(Kind::RParen){
                    self.func_real_params();
                }
                self.bump_expect(Kind::RParen, "Expect `)`.");
            }
            (Some(Kind::Ident), _) => self.primary_exp(),
            (Some(Kind::OpAdd), _) | (Some(Kind::OpSub), _) | (Some(Kind::OpNot), _) => {
                self.bump();
                self.unary_exp();
            }
            _ => self.primary_exp()//self.push_err("Expect primary exp or f(..) or unary exp like -1"),
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
        self.builder.start_node(Kind::LogicAndExp.into());
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
    fn test_sop<F>(text: &str, f: F) -> String
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
        if !res.errors.is_empty(){
            println!("{:?}", res.errors);
        }
        let mut res = String::new();
        output_cst(&node, 0, text, &mut res, "    ");
        print!("CST:\n{}\n", res);
        res
    }
    #[test]
    fn test_exp() {
        {
            println!("Test 1");
            // test LeftValue-> Ident
            let text = "abc123";
            let res = test_sop(text, Parser::left_value);
            assert_eq!(
                r#"LeftValue@0..6
    Ident@0..6 "abc123"
"#,
                res
            );
        }
        {
            println!("Test 2");
            // test PrimaryExp -> LVal|Number
            let text = "abc123";
            let res = test_sop(text, Parser::primary_exp);
            assert_eq!(
                r#"PrimaryExp@0..6
    LeftValue@0..6
        Ident@0..6 "abc123"
"#,
                res
            );
        }
        {
            println!("Test 3");
            // UnaryExp -> PrimaryExp 
            let text = "abc123";
            let res = test_sop(text, Parser::unary_exp);
            assert_eq!(
                r#"UnaryExp@0..6
    PrimaryExp@0..6
        LeftValue@0..6
            Ident@0..6 "abc123"
"#,
                res
            );
        }
        {
            println!("Test 4");
            let text = "abc123()";
            let res = test_sop(text, Parser::unary_exp);
            // UnaryExp ->  Ident (FuncRParams)
            assert_eq!(
                r#"UnaryExp@0..8
    Ident@0..6 "abc123"
    LParen@6..7 "("
    RParen@7..8 ")"
"#.trim(),
                res.trim()
            );
        }
        {
            println!("Test 5");
            let text = "-+!1";
            let res = test_sop(text, Parser::unary_exp);
            // UnaryExp ->  UnaryOp UnaryExp
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
