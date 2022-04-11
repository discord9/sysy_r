//! Valid certain attribute in the CST
//! Function in this module
//!
//! i.e. ConstExp, ConstInitVal etc.
//!
#![allow(unused)]
// TODO: remove after completed
use std::collections::{BTreeMap};

use crate::cst::{
    SyntaxElement,
    SyntaxNode,
    SyntaxToken
};
use crate::ast::{into_ron_tree, parse_exp, Exp, InitVal};

/// Context containing all var and const currently defined
struct Context {
    global_const: BTreeMap<String, InitVal>,
    global_var: BTreeMap<String, InitVal>,
    local_var: BTreeMap<String, InitVal>
}

/// eval a const exp
fn eval_exp(exp: Exp, context: Context) {

}


/// problem with design valider, how?
fn cst_walker(node: &SyntaxNode, text: &str, context: Context) {
    let _ = node.children_with_tokens().map(|child| {
        match child {
            SyntaxElement::Node(node) => {

            }
            SyntaxElement::Token(token) => {

            }
        }
    }).count();
}
