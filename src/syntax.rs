/// define all possible tokens and nodes' type tag that may appear in sysY language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//#[allow(non_camel_case_types)]
#[repr(u16)]
#[allow(unused)] //to be REMOVE!
pub enum SyntaxKind {
    BType = 0, // basic type like 'int' | 'float' | 'void'
    Ident,     // [a-zA-Z][a-zA-Z0-9]*
    // keywords
    ConstKeyword, // 'const'
    IfKeyword,
    ElseKeyword,
    WhileKeyword,
    BreakKeyword,
    ContinueKeyword,
    ReturnKeyword,
    // punctuation
    Comma,     // ,
    Semicolon, // ;
    LParen,    // (
    RParen,    // )
    LCurly,    // {
    RCurly,    // }
    LSquare,   // [
    RSquare,   // ]
    // Operator
    // unary op '+' '-' '!', '!' only appear in Cond
    Operator, // * / % + - < > <= >= == != && || =
    OpAdd,
    OpSub,
    OpNot,
    OpMul,
    OpDiv,
    OpMod,
    OpLT,
    OpGT,
    OpNG,
    OpNL,
    OpEQ,
    OpNE,
    OpAnd,
    OpOr,
    OpAsg,
    // literal const
    IntConst,
    FloatConst,
    Number,
    // whitespace and comment
    Comment, // one line or multiline
    Whitespace,
    Error,

    // composite nodes
    CompUnit,
    Decl,
    ConstDecl,
    ConstDef,
    ConstInitVal,
    VarDecl,
    VarDef,
    InitVal,
    FuncDef,
    FuncType,
    FuncFParams,
    FuncFParam,
    Block,
    BLockItem,
    Statement,
    Expression,
    Condition,
    LeftValue,
    PrimaryExp,
    UnaryExp,
    FuncRParams,
    MulExp,
    AddExp,
    RelationExp,
    EqExp,
    LogicAndExp,
    LogicOrExp,
    ConstExp,
    // end here
    EndMark, // shoud not appear in token stream, purely use as a end mark
}

/// Some boilerplate is needed, as rowan settled on using its own
/// `struct SyntaxKind(u16)` internally, instead of accepting the
/// user's `enum SyntaxKind` as a type parameter.
///
/// First, to easily pass the enum variants into rowan via `.into()`:
impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

/// Second, implementing the `Language` trait teaches rowan to convert between
/// these two SyntaxKind types, allowing for a nicer SyntaxNode API where
/// "kinds" are values from our `enum SyntaxKind`, instead of plain u16 values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lang {}
impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        assert!(raw.0 < SyntaxKind::EndMark as u16);
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

use rowan::GreenNode;

use rowan::GreenNodeBuilder;

struct Parse {
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
macro_rules! ConcatExp {
    ($cur: ident,$child: ident $( ,$concat_op:tt )*) => {
        $cur.$child();
        loop{
            match $cur.current(){
                $(
                Some($concat_op) => {
                    $cur.bump();
                    $cur.$child();
                },
                )*
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
            Some(expected) => self.bump(),
            _ => self.push_err(err_msg),
        }
    }
    /// Push a error node
    fn push_err(&mut self, err_msg: &str) {
        self.builder.start_node(SyntaxKind::Error.into());
        self.errors.push(err_msg.to_string());
        self.bump();
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
        self.tokens
            .get(self.tokens.len() - 1 - ahead)
            .map(|(kind, _)| *kind)
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
        self.add_exp()
    }
    /// LVal -> Ident { `[` Exp `]` }
    fn left_value(&mut self) {
        self.builder.start_node(Kind::LeftValue.into());
        if let Some(Kind::Ident) = self.current() {
            self.bump();
            loop {
                if let Some(Kind::LSquare) = self.current() {
                    self.bump();
                    self.exp();
                    self.bump_expect(Kind::RSquare, "Expect `]`");
                } else {
                    break;
                }
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
    /// UnaryExp -> PrimaryExp | Ident `(`[FuncRParams]`)` | UnaryOp UnaryExp
    fn unary_exp(&mut self) {
        self.builder.start_node(Kind::UnaryExp.into());
        match self.current() {
            Some(Kind::Ident) => {
                self.bump_expect(Kind::Ident, "Expect identifier.");
                self.bump_expect(Kind::LParen, "Expect `(`.");
                self.func_real_params();
                self.bump_expect(Kind::RParen, "Expect `)`.");
            },
            Some(Kind::OpAdd) | Some(Kind::OpSub) | Some(Kind::OpNot) => {
                self.bump();
                self.unary_exp();
            }
            _ => self.primary_exp(),
        }
        self.builder.finish_node();
    }
    /// FuncRParams -> Exp {`,` Exp}
    fn func_real_params(&mut self){
        self.builder.start_node(Kind::FuncRParams.into());
        self.exp();
        loop{
            match self.current(){
                Some(Kind::Comma)=>{
                    self.bump();
                    self.exp();
                },
                _ => break
            }
        }
        self.builder.finish_node();
    }

    /// MulExp -> UnaryExp | UnaryExp (`*`|`/`|`%`) MulExp
    fn mul_exp(&mut self){
        self.builder.start_node(Kind::MulExp.into());
        ConcatExp!(self, unary_exp, (Kind::OpMul), (Kind::OpDiv), (Kind::OpMod));
        self.unary_exp();
        let _r = Some((Kind::OpMul));
        loop{
            match self.current(){
                Some(Kind::OpMul) | Some(Kind::OpDiv) | Some(Kind::OpMod) => {
                    self.bump();
                    self.unary_exp();
                },
                _ => break
            }
        }
        self.builder.finish_node();
    }
    /// AddExp -> MulExp | MulExp (`+`|`-`) AddExp
    fn add_exp(&mut self){
        self.builder.start_node(Kind::AddExp.into());
        self.mul_exp();
        loop{
            match self.current(){
                Some(Kind::OpAdd) | Some(Kind::OpSub) => {
                    self.bump();
                    self.mul_exp();
                },
                _ => break
            }
        }
        self.builder.finish_node();
    }
    /// RelExp -> AddExp | RelExp (`<`|`>`|`<=`|`>=`)AddExp
    fn rel_exp(&mut self){
        self.builder.start_node(Kind::RelationExp.into());
        self.add_exp();
        loop{
            match self.current(){
                Some(Kind::OpLT) | Some(Kind::OpGT) | Some(Kind::OpNG) | Some(Kind::OpNL) => {
                    self.bump();
                    self.add_exp();
                },
                _ => break
            }
        }
        self.builder.finish_node();
    }
    /// EqExp -> RelExp | EqExp(`==`|`!=`)RelExp
    fn eq_exp(&mut self){
        self.builder.start_node(Kind::EqExp.into());
        self.rel_exp();
        loop{
            match self.current(){
                Some(Kind::OpLT) | Some(Kind::OpGT) | Some(Kind::OpNG) | Some(Kind::OpNL) => {
                    self.bump();
                    self.rel_exp();
                },
                _ => break
            }
        }
        self.builder.finish_node();
    }
    /// LogicAndExp -> EqExp | LogicAndExp `&&`EqExp
    fn logic_and_exp(&mut self){
        self.builder.start_node(Kind::LogicAndExp.into());
        self.eq_exp();
        loop{
            match self.current(){
                Some(Kind::OpAnd) => {
                    self.bump();
                    self.eq_exp();
                },
                _ => break
            }
        }
        self.builder.finish_node();
    }
}

fn parse(text: &str) -> Parse {
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
    #[test]
    fn test_number() {
        use crate::lex::lex;
        use crate::syntax::{Kind, Parse, Parser};
        let text = r"42.3";
        let tokens: Vec<(Kind, String)> = lex(text)
            .into_iter()
            .map(|tok| {
                (
                    tok.1,
                    text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap().to_owned(),
                )
            })
            .collect();
        println!("Tokens: {:?}", tokens);
        let mut parser = Parser::new(tokens);
        parser.number();
        let res = Parse {
            green_node: parser.builder.finish(),
            errors: parser.errors,
        };
        let node = res.syntax();
        println!("{:?}", node);
        assert_eq!(
            format!("{:?}", node),
            "Number@0..4", // root node, spanning 15 bytes
        );
        //println!("{:?}", node.children_with_tokens());
        let list = node
            .children_with_tokens()
            .map(|child| {
                format!(
                    "{:?}@{:?} \"{}\"",
                    child.kind(),
                    child.text_range(),
                    text.get(child.text_range().start().into()..child.text_range().end().into())
                        .unwrap()
                )
            })
            .collect::<Vec<_>>();
        for line in &list {
            println!("  {}", line);
        }
        assert_eq!(list, vec!["FloatConst@0..4 \"42.3\"".to_string()]);
        //assert_eq!(node.children().count(), 1);
    }
}
