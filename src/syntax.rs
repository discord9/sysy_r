/// define all possible tokens and nodes' type tag that may appear in sysY language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//#[allow(non_camel_case_types)]
#[repr(u16)]
#[allow(unused)]//to be REMOVE!
pub enum SyntaxKind{
    BType = 0, // basic type like 'int' | 'float' | 'void'
    Ident, // [a-zA-Z][a-zA-Z0-9]*
    // keywords
    ConstKeyword, // 'const'
    IfKeyword,
    ElseKeyword,
    WhileKeyword,
    BreakKeyword,
    ContinueKeyword,
    ReturnKeyword,
    // punctuation
    Comma,// ,
    Semicolon,// ;
    LParen,// (
    RParen,// )
    LCurly,// {
    RCurly,// }
    LSquare,// [
    RSquare,// ]
    // Operator
    // unary op '+' '-' '!', '!' only appear in Cond
    Operator,// * / % + - < > <= >= == != && ||
    // literal const
    IntConst,
    FloatConst,
    Number,
    // whitespace and comment
    Comment,// one line or multiline
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
    EndMark,// shoud not appear in token stream, purely use as a end mark
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
enum Lang {}
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

struct Parser {
    /// input tokens, including whitespace and comment
    tokens: Vec<(SyntaxKind, String)>,
    /// the in-progress tree.
    builder: GreenNodeBuilder<'static>,
    /// the list of syntax errors we've accumulated
    /// so far.
    errors: Vec<String>,
}

impl Parser{
    fn new(mut tokens: Vec<(SyntaxKind, String)>)->Self{
        tokens.reverse();
        Parser { 
            tokens: tokens, 
            builder: GreenNodeBuilder::new(), 
            errors: Vec::new()
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
    /// Peek at the first unprocessed token
    fn current(&self) -> Option<SyntaxKind> {
        self.tokens.last().map(|(kind, _)| *kind)
    }
    /// Peek ahead 
    /// 
    /// `peek(0) == current()`
    fn peek(&self, ahead: usize) -> Option<SyntaxKind> {
        self.tokens.get(self.tokens.len() - 1 - ahead)
        .map(|(kind, _)| *kind)
    }
    /// skip whitespace and comment
    fn skip_ws_cmt(&mut self) {
        use SyntaxKind::{Whitespace, Comment};
        while self.current() == Some(Whitespace) 
           || self.current() == Some(Comment) {
            self.bump()
        }
    }
    /// CompUnit -> (Decl | FuncDef) +
    fn comp_unit(&mut self){
        loop{
            self.builder.start_node(SyntaxKind::CompUnit.into());
            match self.peek(2){
                Some(SyntaxKind::LParen)=>{

                },
                _ => ()
            }
            
        };
    }
}

fn parse(text: &str) -> Parse {
    use crate::lex::lex;
    let text = r"hello=world";
    let tokens: Vec<(SyntaxKind, String)> = lex(text)
    .into_iter()
    .map(|tok|{
        (tok.1, text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap().to_owned())
    })
    .collect();
    Parser::new(tokens).parse()
}