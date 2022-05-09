/// using different backend
use std::collections::HashMap;

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{FloatType, IntType};
//use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, BasicValueEnum, FloatValue, FunctionValue, IntValue,
    PointerValue,
};
//use inkwell::{FloatPredicate, OptimizationLevel};

use crate::frontend::ast::{FuncDef, AST};

/// Defines the `Expr` compiler.
#[derive(Debug)]
pub struct Compiler<'a, 'ctx> {
    pub ast: &'ctx AST,
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub fpm: &'a PassManager<FunctionValue<'ctx>>,
    pub module: &'a Module<'ctx>,
    pub function: &'a FuncDef,

    f32_type: FloatType<'ctx>,
    i32_type: IntType<'ctx>,
    variables: HashMap<String, PointerValue<'ctx>>,
    fn_value_opt: Option<FunctionValue<'ctx>>,
}

#[derive(Debug)]
pub enum CompileError {
    TypeError(String),
    InvalidCall(String),
    UnknownFunc(String),
    UndefinedBinOp(String),
}

use crate::frontend::ast::Expr;
impl<'a, 'ctx> Compiler<'a, 'ctx> {
    
    #[inline]
    fn f32_type(&self) -> FloatType<'ctx> {
        self.context.f32_type()
    }
    #[inline]
    fn i32_type(&self) -> IntType<'ctx> {
        self.context.i32_type()
    }
    /// Gets a defined function given its name.
    #[inline]
    fn get_function(&self, name: &str) -> Option<FunctionValue<'ctx>> {
        self.module.get_function(name)
    }

    /// cast a `i32` to `f32` using `SIToFP` instr, or directly return `FloatValue` if already is a `BasicValueEnum::FloatValue`, if type is none above, return `None`
    fn force_cast_f32(&self, val: BasicValueEnum<'ctx>) -> Option<FloatValue<'ctx>> {
        match val {
            BasicValueEnum::IntValue(vi) => {
                let res = self
                    .builder
                    .build_cast(
                        inkwell::values::InstructionOpcode::SIToFP,
                        vi,
                        self.f32_type(),
                        "cast",
                    )
                    .try_into()
                    .unwrap();
                Some(res)
            }
            BasicValueEnum::FloatValue(v) => Some(v),
            _ => None,
        }
    }

    fn force_cast_i32(&self, val: BasicValueEnum<'ctx>) -> Option<IntValue<'ctx>>{
        match val{
            BasicValueEnum::FloatValue(v)=>{
                Some(self.builder.build_float_to_signed_int(v, self.i32_type(), "forced_int"))
            }
            BasicValueEnum::IntValue(v)=>Some(v),
            _=>None
        }
    }
    /// Returns the `FunctionValue` representing the function being compiled.

    #[inline]
    fn fn_value(&self) -> FunctionValue<'ctx> {
        self.fn_value_opt.unwrap()
    }

    /// Creates a new stack allocation instruction in the entry block of the function.

    fn create_entry_block_alloca(&self, name: &str) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = self.fn_value().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),

            None => builder.position_at_end(entry),
        }

        builder.build_alloca(self.context.f64_type(), name)
    }

    /// for Expr can be of int or float

    /// TODO: need to add dtype for expr

    /*fn compile_expr<T>(&mut self, expr: &Expr) -> Result<T, CompileError> {
        use crate::frontend::ast::ExprKind::*;

        use crate::syntax::SyntaxKind as Kind;

        use Kind::*;

        match &expr.kind {
            BinOp{op, left, right} => {
                let left = self.compile_expr(left)?;

                let right = self.compile_expr(right)?;

                match op {
                    OpAdd => {}

                    OpSub => (),

                    OpMul => (),

                    OpDiv => (),

                    OpMod => (),
                    _ => {}
                }
            }
            _ => ()
        }

        todo!()
    }
    */
    fn compile_expr(&mut self, node: &Expr) -> Result<BasicValueEnum<'ctx>, CompileError> {
        use crate::frontend::ast::ExprKind;
        match &node.kind {
            ExprKind::Call { id, args } => {
                match self.get_function(self.ast.get_name2symbol(&id.name).unwrap().as_str()) {
                    Some(func) => {
                        let comp_args: Vec<BasicMetadataValueEnum> = args
                            .iter()
                            .map(|x| self.compile_expr(x).unwrap().into())
                            .collect();
                        match self
                            .builder
                            .build_call(func, comp_args.as_slice(), "tmp")
                            .try_as_basic_value()
                            .left()
                        {
                            Some(value) => Ok(value),
                            None => Err(CompileError::InvalidCall(format!("{:?}", node))),
                        }
                    }
                    None => Err(CompileError::UnknownFunc(
                        self.ast.get_name2symbol(&id.name).unwrap().to_owned(),
                    )),
                }
                //https://github.com/TheDan64/inkwell/blob/bff378bee02bcbb5bed35f47e9ed69e6642e9188/examples/kaleidoscope/main.rs#L977
            }
            ExprKind::BinOp { op, left, right } => {
                let lhs = self.compile_expr(left)?;
                let rhs = self.compile_expr(right)?;

                let use_float = {
                    use BasicValueEnum::*;
                    match (lhs, rhs) {
                        (IntValue(_), IntValue(_)) => false,
                        (FloatValue(_), FloatValue(_))
                        | (IntValue(_), FloatValue(_))
                        | (FloatValue(_), IntValue(_)) => true,
                        _ => {
                            return Err(CompileError::TypeError(
                                "Impossible type in expression!".to_string(),
                            ))
                        }
                    }
                };
                use crate::syntax::SyntaxKind;
                //use inkwell::values::{FloatMathValue, FloatValue, IntMathValue, IntValue};
                if use_float {
                    // use float cast!
                    let lhs: FloatValue = self.force_cast_f32(lhs).unwrap();
                    let rhs: FloatValue = self.force_cast_f32(rhs).unwrap();
                    match *op {
                        SyntaxKind::OpAdd => {
                            Ok(self.builder.build_float_add(lhs, rhs, "tmpadd").into())
                        }
                        SyntaxKind::OpSub => {
                            Ok(self.builder.build_float_sub(lhs, rhs, "tmpadd").into())
                        }
                        SyntaxKind::OpMul => {
                            Ok(self.builder.build_float_mul(lhs, rhs, "tmpmul").into())
                        }
                        SyntaxKind::OpDiv => {
                            Ok(self.builder.build_float_div(lhs, rhs, "tmpdiv").into())
                        }
                        SyntaxKind::OpMod => {
                            Ok(self.builder.build_float_rem(lhs, rhs, "tmpdiv").into())
                        }
                        _ => Err(CompileError::UndefinedBinOp(format!("{:?}", op))),
                    }
                } else {
                    let lhs: IntValue = lhs.try_into().unwrap();
                    let rhs: IntValue = rhs.try_into().unwrap();
                    match *op {
                        SyntaxKind::OpAdd => {
                            Ok(self.builder.build_int_add(lhs, rhs, "tmpadd").into())
                        }
                        SyntaxKind::OpSub => {
                            Ok(self.builder.build_int_sub(lhs, rhs, "tmpadd").into())
                        }
                        SyntaxKind::OpMul => {
                            Ok(self.builder.build_int_mul(lhs, rhs, "tmpmul").into())
                        }
                        SyntaxKind::OpDiv => {
                            Ok(self.builder.build_int_signed_div(lhs, rhs, "tmpdiv").into())
                        }
                        SyntaxKind::OpMod => {
                            Ok(self.builder.build_int_signed_rem(lhs, rhs, "tmpdiv").into())
                        }
                        _ => Err(CompileError::UndefinedBinOp(format!("{:?}", op))),
                    }
                }
            }
            ExprKind::BoolOp { op, args } => {
                use inkwell::IntPredicate;
                use crate::syntax::SyntaxKind;
                match *op{
                    SyntaxKind::OpAnd =>{
                        let parent = self.fn_value();
                        let mut and_chain = Vec::new();
                        and_chain.push(self.context.append_basic_block(parent, "and"));
                        let cont_bb = self.context.append_basic_block(parent, "cont");
                        self.builder.position_at_end(and_chain[0]);
                        let mut cond = self.context.bool_type().const_int(0, false);
                        let zero = self.context.bool_type().const_int(0, false);
                        for arg in args{
                            // Short circuit(difficult!)
                            let val = self.compile_expr(arg)?;
                            let val = self.force_cast_i32(val).unwrap();
                            cond = self.builder.build_int_compare(IntPredicate::NE, val, zero, "and");
                            let and_bb = and_chain.last().unwrap().to_owned();
                            let append_bb = self.context.append_basic_block(parent, "and");
                            and_chain.push(append_bb);
                            self.builder.position_at_end(and_bb);
                            self.builder.build_conditional_branch(cond, append_bb, cont_bb);
                            self.builder.position_at_end(append_bb);
                        }
        
                        // emit merge block
                        self.builder.position_at_end(cont_bb);
                        let phi = self.builder.build_phi(self.context.bool_type(), "andtmp");
                        let mut is_last = true;
                        for and_bb in and_chain.iter().rev(){
                            if is_last{
                                phi.add_incoming(&[(&cond, *and_bb)])
                            }else{
                                phi.add_incoming(&[(&zero, *and_bb)])
                            }
                        }
                        Ok(phi.as_basic_value())
                    }
                    SyntaxKind::OpOr => {
                        let parent = self.fn_value();
                        let mut or_chain = Vec::new();
                        let or_bb = self.context.append_basic_block(parent, "or");
                        or_chain.push(or_bb);
                        let cont_bb = self.context.append_basic_block(parent, "cont");
                        self.builder.position_at_end(or_bb);
                        let mut cond = self.context.bool_type().const_int(0, false);
                        let zero = self.context.bool_type().const_int(0, false);
                        for arg in args{
                            // Short circuit(difficult!)
                            let val = self.compile_expr(arg)?;
                            let val = self.force_cast_i32(val).unwrap();
                            cond = self.builder.build_int_compare(IntPredicate::NE, val, zero, "or");
                            let or_bb = or_chain.last().unwrap().to_owned();
                            let append_bb = self.context.append_basic_block(parent, "or");
                            or_chain.push(append_bb);
                            self.builder.position_at_end(or_bb);
                            self.builder.build_conditional_branch(cond, cont_bb, append_bb);
                            self.builder.position_at_end(append_bb);
                        }
        
                        // emit merge block
                        self.builder.position_at_end(cont_bb);
                        let phi = self.builder.build_phi(self.context.bool_type(), "ortmp");
                        let mut is_last = true;
                        let one = self.context.bool_type().const_int(1, false);
                        for or_bb in or_chain.iter().rev(){
                            if is_last{
                                phi.add_incoming(&[(&cond, *or_bb)])
                            }else{
                                phi.add_incoming(&[(&one, *or_bb)])
                            }
                        }
                        Ok(phi.as_basic_value())
                    }
                    _ => unreachable!()
                }
            }
            _ => unreachable!(),
        }
    }
}
use crate::frontend::visit::Visitor;
impl<'a, 'ctx> Visitor for Compiler<'a, 'ctx> {
    /// emit LLVM IR for expr
    fn visit_expr(&mut self, node: &Expr) {
        self.compile_expr(node);
    }
}
