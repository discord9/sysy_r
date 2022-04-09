use crate::syntax::SyntaxKind;
use lexgen::lexer;
use lexgen_util::Loc;
/// Split the input string into a flat list of tokens
/// (such as L_PAREN, WORD, and WHITESPACE)
/// 
/// multiline comment come from [stackoverflow: Regex to match a C-style multiline comment](https://stackoverflow.com/questions/13014947/regex-to-match-a-c-style-multiline-comment?msclkid=06d711cbb5bf11ec800ef20a541c0df9)
pub fn lex(text: &str) -> Vec<(Loc, SyntaxKind, Loc)> {
    lexer! {
        Lexer -> SyntaxKind;

        let whitespace = [' ' '\t' '\n'] | "\r\n";
        let comment_oneline = "//" (_ # ['\r' '\n'])*;
        // from [Regex to match a C-style multiline comment](https://stackoverflow.com/questions/13014947/regex-to-match-a-c-style-multiline-comment?msclkid=06d711cbb5bf11ec800ef20a541c0df9)
        let comment_multiline = "/*" (_ # ['*'])* '*'+ ((_ # ['/' '*' ])(_ # '*')* '*'+)* "/";
        let ident_init = ['a'-'z' 'A'-'Z'];
        let ident_subseq = $ident_init | ['a'-'z' 'A'-'Z' '0'-'9' '-' '_'];
        let digit = ['0' - '9'];
        let hex_digit = ['a'-'f' 'A'-'F' '0'-'9'];
        let hex_prefix = "0x" | "0X";
        // original iso not include zero????
        let sign = '+' | '-';
        let int_const =  ('0') |  ( ['1'-'9']['0'-'9']*) | 'o'['0'-'7']+ | $hex_prefix ['0' - '9' 'a' - 'f' 'A' - 'F']+;

        let frac_const = $digit* '.' $digit+ | $digit+ '.';
        
        let exp_part = 'e'$sign? $digit+ | 'E'$sign? $digit+;
        let dec_float_const = $frac_const $exp_part? | $digit+ $exp_part;

        rule Init{
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
                "return" => SyntaxKind::ReturnKeyword,
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
                "[" => SyntaxKind::LBracket,
                "]" => SyntaxKind::RBracket,
                _ => SyntaxKind::Error
            };
            lexer.return_(ret)
        },
        "!" | "+" | "-" | "*" | "/" | "%" | "<" | ">" | "<=" | ">=" | "==" | "!=" | "&&" | "||" | "="   => |lexer| {
            // "!" | "+" | "-" | "*" | "/" | "%" | "<" | ">" | "<=" | ">=" | "==" | "!=" | "&&" | "||"
            use SyntaxKind as Kind;
            let ret = match lexer.match_(){
                "!" => Kind::OpNot,
                "+" => Kind::OpAdd,
                "-" => Kind::OpSub,
                "*" => Kind::OpMul,
                "/" => Kind::OpDiv,
                "%" => Kind::OpMod,
                "<" => Kind::OpLT,
                ">" => Kind::OpGT,
                "<=" => Kind::OpNG,
                ">=" => Kind::OpNL,
                "==" => Kind::OpEQ,
                "!=" => Kind::OpNE,
                "&&" => Kind::OpAnd,
                "||" => Kind::OpOr,
                "=" => Kind::OpAsg,
                _ => Kind::Error
            };
            lexer.return_(ret)
        },
        // for literal const
        $dec_float_const = SyntaxKind::FloatConst,
        $int_const = SyntaxKind::IntConst,

        $ident_init $ident_subseq* => |lexer| {
            lexer.return_(SyntaxKind::Ident)
        },
        $whitespace* = SyntaxKind::Whitespace,
        $comment_oneline | $comment_multiline = {
            SyntaxKind::Comment
        },
        _ = SyntaxKind::Error,
    }
    };
    Lexer::new(text)
        .into_iter()
        .map(|tok| match tok {
            Ok(tok) => tok,
            Err(tok) => (tok.location, SyntaxKind::Error, tok.location),
        })
        .collect()
}

#[test]
fn test_integrate() {
    {
        let text = r"
        // one line 
        fn main(){
            print(42);
            /* test
            of 
            multiple
            line */
        }
        ";
        let res = lex(text);
        for tok in res {
            let src = text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap();
            println!("\'{}\'=>{:?} ", src, tok.1);
        }
    }
    {
        let text = r"
        // one line 
        /* test
        of 
        multiple
        line */
        ";
        let res = lex(text);
        println!("Test 2:");
        for &tok in &res {
            let src = text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap();
            println!("\'{}\'=>{:?} ", src, tok.1);
        }
        assert_eq!(res.get(1).to_owned().unwrap().1, SyntaxKind::Comment);
        assert_eq!(res.get(3).to_owned().unwrap().1, SyntaxKind::Comment);
    }
}

#[cfg(test)]
mod test {
    use crate::lex::{lex, SyntaxKind};
    use proptest::{proptest, prop_assert_eq};
    proptest!{
        #[test]
        fn fuzz_comment(text in r"/\*[^*]*\*+(?:[^/*][^*]*\*+)*/"){
            let res = lex(text.as_str());
            prop_assert_eq!(res.len(), 1);
            prop_assert_eq!(res.get(0).unwrap().1, SyntaxKind::Comment);
            prop_assert_eq!(res.get(0).unwrap().0.byte_idx, 0);
            prop_assert_eq!(res.get(0).unwrap().2.byte_idx, text.len());
        }
    }
    #[test]
    fn test_comment(){
        let text = "/**/";
        let res = lex(text);
        for tok in res {
            let src = text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap();
            println!("{:?}@{}..{} \'{}\'", tok.1,tok.0.byte_idx,tok.2.byte_idx, src);
        }
    }
    #[test]
    fn test_number(){
        use crate::syntax::SyntaxKind as Kind;
        let text = "123 456.789 456e3";
        let res = lex(text);
        //println!("{:?}", res);
        for &_tok in &res {
            //let src = text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap();
            //println!("\'{}\'=>{:?} ", src, tok.1);
        }
        let token_only: Vec<Kind> = res.into_iter().map(|tok|{
            tok.1
        }).collect();
        assert_eq!(token_only,
            [Kind::IntConst, Kind::Whitespace, 
            Kind::FloatConst, Kind::Whitespace, 
            Kind::FloatConst]);
    }
    #[test]
    fn test_operator_lex(){
        let text = "* / % + - < > <= >= == != && || =";
        let res = lex(text);
        for tok in res {
            let src = text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap();
            println!("\'{}\'=>{:?} ", src, tok.1);
        }
    }
    #[test]
    fn test_long_text() {
        let res = lex("123.456e4");
        println!("{:?}", res);
        let res = lex("//hello world");
        println!("{:?}", res);
        let long_text = r"
            int main(){
                for(int i=0; i < 5;i=i+1){
                    print(1,2,3);
                    if(i == 4 && !i%4=0){
                        break;
                    }else{//one line comment
                        continue;
                    }/*
                    a
                    b
                    c */
                }
            }
                ";
        let res = lex(long_text);
        for tok in res {
            let src = long_text.get(tok.0.byte_idx..tok.2.byte_idx).unwrap();
            println!("\'{}\'=>{:?} ", src, tok.1);
        }
        //println!("{:?}",res);
    }
}
