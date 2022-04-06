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
    LBracket,   // [
    RBracket,   // ]
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
    BlockItem,
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

impl From<SyntaxKind> for String {
    fn from(kind: SyntaxKind) -> Self {
        use SyntaxKind as Kind;
        use Kind::{BType, LParen, RParen,LBracket, RBracket ,Ident, OpAsg};
        let r = match kind{
            BType => "Basic Type",
            LParen => "(",
            RParen => ")",
            LBracket => "[",
            RBracket => "]",
            Ident => "Identifier",
            OpAsg => "=",
            _ => "Node"
        };
        r.to_string()
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