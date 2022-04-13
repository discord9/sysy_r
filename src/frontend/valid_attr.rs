//! 1. Const-folding
//! 
//! 2. InitVal check and folding


struct array_const {
    raw_values: ArrayIntOrFloat,
    shape: (usize, usize),
    dtype: 
}

enum IntOrFloatArray {
    IntArray(Vec<i32>),
    FloatArray(Vec<f32>)
}