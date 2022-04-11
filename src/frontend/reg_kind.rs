//! helper function(iterator?) to match childs of a SyntaxNode and return SyntaxElement
//! 
#![allow(unused)]
// TODO: remove after completed
use crate::syntax::SyntaxKind as Kind;
#[derive(Debug)]
pub enum RegPat{
    Rep {
        pat: Vec<RegPat>,
        op: MetaCh
    },
    Pat (
        Vec<Kind>
    )
}

impl RegPat{
    pub fn pat(pats: &[Kind])-> Self{
        Self::Pattern(Vec::from(pats))
    }
    pub fn rep(pat: Vec<Self>, op: MetaCh) -> Self {
        Self::Rep { pat: pat, op }
    }
}
#[derive(Debug)]
pub enum MetaCh{
    Opt,
    ZeroOrMore,
    OneOrMore,
    Or
}

#[test]
fn test_reg() {
    use Kind::{Decl, FuncDef};
    let a = RegPat::pat(&vec![Decl]);
    let b = RegPat::pat(&vec![FuncDef]);
    let c = RegPat::rep(vec![a,b], MetaCh::Or);
    println!("{:?}", c);
}