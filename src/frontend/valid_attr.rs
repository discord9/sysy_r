//! 1. Const-folding
//!
//! 2. InitVal check and folding
use std::collections::HashMap;

use crate::frontend::ast::{CompUnit, Expr, NodeId};

pub struct ConstArray{
    shape: Vec<usize>,
    cols: Vec<usize>,// one cols of n-th dimension
    content: ArrayContent
}
impl ConstArray {
    fn init_with(shape: &[usize],num: NumberValue)->Self{
        let tot_len = shape.iter().fold(1, |acc, x|acc*x);
        Self{
            shape: shape.to_vec(),
            cols: shape.iter().rev().scan(1,|state, &x|{
                let ret = *state;
                *state *= x;
                Some(ret)
            }).collect(),
            content: match num{
                NumberValue::Float(num)=>ArrayContent::Float(vec![num;tot_len]),
                NumberValue::Int(num)=>ArrayContent::Int(vec![num;tot_len])
            }
        }
    }
    fn get(&self,index: &[usize])->Option<NumberValue>{
        if index.len()!= self.shape.len(){return None}
        for (i, s) in index.iter().zip(self.shape.iter()){
            if i>=s{return None}
        }
        // manually sim multidimension array
        let offset = self.cols.iter().zip(index.iter()).fold(0,|acc,(&col, &idx)|acc + col * idx);
        self.content.get(offset)
    }
}
pub enum ArrayContent {
    Int(Vec<i32>),
    Float(Vec<f32>)
}
impl ArrayContent{
    fn get(&self, idx: usize)->Option<NumberValue>{
        use NumberValue::*;
        match self{
            ArrayContent::Float(v)=>
                {
                    match v.get(idx){
                        Some(i) => Some(Float(*i)),
                        None => None
                    }
                },
            ArrayContent::Int(v)=>{
                match v.get(idx){
                    Some(i) => Some(Int(*i)),
                    None => None
                }
            }
        }
    }
}

/// const
pub struct ScopeAnalysis {
    /// actual var value is on `NodeId` Node
    variables: HashMap<String, NodeId>,
    /// constant value, being fold in constant folding
    constants: HashMap<String, NodeId>
}

pub struct SemanticAnalysis {
    /// The result of Const Folding of ast node, NodeId should belong to a `Expr`.
    const_exp: HashMap<NodeId, NumberValue>,
    /// Constant Array of arbitrary dimension, as a result of Const folding, point to a ast node of `InitVals`
    const_array: HashMap<NodeId, ConstArray>,
    comp_unit: CompUnit,
    // Context?
}
impl SemanticAnalysis {
    fn folding_const(&mut self, cu: &CompUnit) {
        for decl_or_func_def in &cu.kind.items{

        }
        //let ret = self.eval_expr(expr);
        //self.const_exp.insert(expr.id, ret);
    }
    fn eval_expr(&mut self, expr: &Expr) -> NumberValue {
        use crate::frontend::ast::{ExprKind::*, IntOrFloat, IntOrFloatKind};
        use crate::syntax::SyntaxKind as Kind;
        use Kind::*;
        use NumberValue::*;
        match &expr.kind {
            Call { id, args } => {
                todo!()
                // TODO: Context related
            }
            BinOp { op, left, right } => {
                let left = self.eval_expr(left);
                let right = self.eval_expr(right);
                if left.as_float().is_some() || right.as_float().is_some() {
                    let l = left.to_float();
                    let r = right.to_float();
                    let ret = {
                        match op {
                            OpAdd => l + r,
                            OpSub => l - r,
                            OpMul => l * r,
                            OpDiv => l / r,
                            OpMod => l % r,
                            _ => unreachable!(),
                        }
                    };
                    return NumberValue::Float(ret);
                } else {
                    let l = left.to_int();
                    let r = right.to_int();
                    let ret = {
                        match op {
                            OpAdd => l + r,
                            OpSub => l - r,
                            OpMul => l * r,
                            OpDiv => l / r,
                            OpMod => l % r,
                            _ => unreachable!(),
                        }
                    };
                    return NumberValue::Int(ret);
                }
            }
            BoolOp { op, args } => {
                // all predicts should be int
                // need for short circuit here
                match op {
                    OpAnd => {
                        // short circuit
                        for exp in args {
                            let predicate = self
                                .eval_expr(exp)
                                .as_int()
                                .expect("All predicates should be integer!");
                            if predicate == 0 {
                                return Int(0);
                            }
                        }
                        return Int(1);
                    }
                    OpOr => {
                        // short circuit
                        for exp in args {
                            let predicate = self
                                .eval_expr(exp)
                                .as_int()
                                .expect("All predicates should be integer!");
                            if predicate != 0 {
                                return Int(1);
                            }
                        }
                        return Int(0);
                    }
                    _ => unreachable!(),
                }
            }
            UnaryOp { op, val } => {
                let val = self.eval_expr(val);
                return match op {
                    OpAdd => val,
                    OpSub => match val {
                        Int(num) => Int(-num),
                        Float(num) => Float(-num),
                    },
                    OpNot => {
                        // only appear in cond
                        if let Int(0) = val {
                            Int(1)
                        } else if let Int(_) = val {
                            Int(0)
                        } else {
                            unreachable!()
                        }
                    }
                    _ => unreachable!(),
                };
            }
            CmpOp {
                op,
                left,
                comparators,
            } => {
                let mut l = self.eval_expr(left);
                for (op, com) in op.iter().zip(comparators.iter()) {
                    let r = self.eval_expr(com);
                    let res = match op {
                        OpLT => l < r,
                        OpGT => l > r,
                        OpNG => l <= r,
                        OpNL => l >= r,
                        OpEQ => l == r,
                        OpNE => l != r,
                        _ => unreachable!(),
                    };
                    if !res {
                        return Int(0);
                    }
                }
                return Int(1);
            }
            Constant(num) => {
                match num.kind{
                    IntOrFloatKind::Float(num) => return NumberValue::Float(num),
                    IntOrFloatKind::Int(num) => return NumberValue::Int(num)
                }
            }
            Name(name) => {
                // Context related
            }
            Subscript { value, slice } => {
                // Context related
                todo!()
            }
            _ => (),
        }
        todo!()
    }
}
#[derive(Debug)]
pub enum NumberValue {
    Int(i32),
    Float(f32),
}
use std::cmp::Ordering;
impl PartialOrd for NumberValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use NumberValue::*;
        match (self, other) {
            (Int(l), Int(r)) => return Some(l.cmp(r)),
            _ => (),
        };
        return self.to_float().partial_cmp(&other.to_float());
    }
}
impl PartialEq for NumberValue {
    fn eq(&self, other: &Self) -> bool {
        use NumberValue::*;
        match (self, other) {
            (Int(l), Int(r)) => return l == r,
            _ => (),
        };
        self.to_float() == other.to_float()
    }
}

impl NumberValue {
    /// if is type int return num else none
    fn as_int(&self) -> Option<i32> {
        use NumberValue::*;
        match self {
            Int(num) => Some(*num),
            _ => None,
        }
    }
    /// if is type float return num else none
    fn as_float(&self) -> Option<f32> {
        use NumberValue::*;
        match self {
            Float(num) => Some(*num),
            _ => None,
        }
    }
    fn to_float(&self) -> f32 {
        use NumberValue::*;
        match self {
            Float(num) => *num,
            Int(num) => *num as f32,
        }
    }
    fn to_int(&self) -> i32 {
        use NumberValue::*;
        match self {
            Float(num) => *num as i32,
            Int(num) => *num,
        }
    }
}

#[test]
fn cmp_number() {
    let a = NumberValue::Float(0.0);
    let b = NumberValue::Int(1);
    assert!(a < b);
}

#[test]
fn test_const_folding_no_context() {
    use crate::frontend::ast::text2ast;
}