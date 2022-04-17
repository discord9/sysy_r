/// using different backend
use std::collections::HashMap;

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, FloatValue, FunctionValue, PointerValue,
};
use inkwell::{FloatPredicate, OptimizationLevel};

use crate::frontend::ast::FuncDef;

/// Defines the `Expr` compiler.
pub struct Compiler<'a, 'ctx> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub fpm: &'a PassManager<FunctionValue<'ctx>>,
    pub module: &'a Module<'ctx>,
    pub function: &'a FuncDef,

    variables: HashMap<String, PointerValue<'ctx>>,
    fn_value_opt: Option<FunctionValue<'ctx>>,
}

pub enum CompileError {
    TypeError(String),
}

use crate::frontend::ast::Expr;
impl<'a, 'ctx> Compiler<'a, 'ctx> {
    /// Gets a defined function given its name.

    #[inline]

    fn get_function(&self, name: &str) -> Option<FunctionValue<'ctx>> {
        self.module.get_function(name)
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

    fn compile_expr<T>(&mut self, expr: &Expr) -> Result<T, CompileError> {
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
}
