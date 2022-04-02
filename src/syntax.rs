/// define all possible tokens that may appear in sysY language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//#[allow(non_camel_case_types)]
#[repr(u16)]
#[allow(unused)]//to be REMOVE!
pub enum SyntaxKind{
    BType = 0, // 'int' | 'float' | 'void'
    Ident, // [a-zA-Z][a-zA-Z0-9]*
    // keywords
    ConstKeyword, // 'const'
    IFKeyword,
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
    // operator
    UnaryOP,// unary op '+' '-' '!', '!' only appear in Cond
    BinaryOP,// * / % + - < > <= >= == != && ||
    // literal const
    IntConst,
    FloatConst,
    Number,
    // whitespace and comment
    Coment,// one line or multiline
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
    EndMark,
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
