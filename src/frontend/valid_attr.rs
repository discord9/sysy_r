//! 1. Const-folding
//!
//! 2. InitVal check and folding

struct array_const {
    raw_values: IntOrFloatArray,
    shape: (usize, usize),
    dtype: TypeConst,
}

impl array_const {
    fn zeros(h: usize, w: usize, dtype: TypeConst) -> Self {
        let raw_values = match dtype {
            TypeConst::Int => IntOrFloatArray::IntArray(Vec::with_capacity(h * w)),
            TypeConst::Float => IntOrFloatArray::FloatArray(Vec::with_capacity(h * w)),
        };
        Self {
            raw_values,
            shape: (h, w),
            dtype
        }
    }
}

enum TypeConst {
    Int,
    Float,
}

enum IntOrFloatArray {
    IntArray(Vec<i32>),
    FloatArray(Vec<f32>),
}
