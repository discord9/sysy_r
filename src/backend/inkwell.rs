/// using different backend
use self::inkwell::builder::Builder;
use self::inkwell::context::Context;
use self::inkwell::module::Module;
use self::inkwell::passes::PassManager;
use self::inkwell::types::BasicMetadataTypeEnum;
use self::inkwell::values::{BasicValue, BasicMetadataValueEnum, FloatValue, FunctionValue, PointerValue};
use self::inkwell::{OptimizationLevel, FloatPredicate};

/// Defines the `Expr` compiler.
pub struct Compiler<'a, 'ctx> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub fpm: &'a PassManager<FunctionValue<'ctx>>,
    pub module: &'a Module<'ctx>,
    pub function: &'a Function,

    variables: HashMap<String, PointerValue<'ctx>>,
    fn_value_opt: Option<FunctionValue<'ctx>>
}