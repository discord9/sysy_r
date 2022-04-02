use crate::syntax::SyntaxKind;
use lexgen::lexer;
use lexgen_util::Loc;
/// Split the input string into a flat list of tokens
/// (such as L_PAREN, WORD, and WHITESPACE)
fn lex(text: &str) -> Vec<(Loc, SyntaxKind, Loc)> {
    lexer! {
        Lexer -> SyntaxKind;

        let whitespace = [' ' '\t' '\n'] | "\r\n";
        let ident_init = ['a'-'z'];
        let ident_subseq = $ident_init | ['A'-'Z' '0'-'9' '-' '_'];
        let digit = ['0' - '9'];
        let hex_digit = ['a'-'f' 'A'-'F' '0'-'9'];
        let hex_prefix = "0x" | "0X";

        let int_const =  ['1'-'9']['0'-'9']+ | 'o'['0'-'7']+ | $hex_prefix ['0' - '9' 'a' - 'f' 'A' - 'F']+;

        let frac_const = $digit* '.' $digit+ | $digit+ '.';
        let sign = '+' | '-';
        let exp_part = 'e'$sign? $digit+ | 'E'$sign? $digit+;
        let dec_float_const = $frac_const $exp_part | $digit+ $exp_part;

        "int" | "float" | "void" => |lexer| {
            lexer.return_(SyntaxKind::BType)
        },
        "const" | "if" | "else"| "while"| "break"| "continue"| "return" => |lexer| {
            let ret = match lexer.match_(){
                "const" => SyntaxKind::ConstKeyword,
                "if" => SyntaxKind::IfKeyword,
                "else" => SyntaxKind::ElseKeyword,
                "while" => SyntaxKind::WhileKeyword,
                "break" => SyntaxKind::BreakKeyword,
                "continue" => SyntaxKind::ContinueKeyword,
                "return" => SyntaxKind::ContinueKeyword,
                _ => SyntaxKind::Error
            };
            lexer.return_(ret)
        },

        "," | ";" | "(" | ")" | "{" | "}" | "[" | "]" => |lexer| {
            let ret = match lexer.match_(){
                "," => SyntaxKind::Comma,
                ";" => SyntaxKind::Semicolon,
                "(" => SyntaxKind::LParen,
                ")" => SyntaxKind::RParen,
                "{" => SyntaxKind::LCurly,
                "}" => SyntaxKind::RCurly,
                "[" => SyntaxKind::LSquare,
                "]" => SyntaxKind::RSquare,
                _ => SyntaxKind::Error
            };
            lexer.return_(ret)
        },
        "!" | "+" | "-" | "*" | "/" | "%" | "<" | ">" | "<=" | ">=" | "==" | "!=" | "&&" | "||"   => |lexer| {
            // "!" | "+" | "-" | "*" | "/" | "%" | "<" | ">" | "<=" | ">=" | "==" | "!=" | "&&" | "||" 
            lexer.return_(SyntaxKind::Operator)
        },
        // for literal const
        $dec_float_const = SyntaxKind::FloatConst,
        $int_const = SyntaxKind::IntConst,

        $ident_init $ident_subseq* => |lexer| {
            lexer.return_(SyntaxKind::Ident)
        },
    };
    Lexer::new(text)
    .into_iter()
    .map(|tok|{tok.unwrap()}).collect()
}

#[test]
fn test_lex(){
    let res = lex("123.456e4");
    println!("{:?}",res);

}