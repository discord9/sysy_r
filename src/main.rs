mod syntax;
mod lex;
use syntax::SyntaxKind;


#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum AstNode {
    Ident(String)
}

fn main() {
    println!("Hello, world!");
}
