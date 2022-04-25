use super::ast::{AST, BasicTypeKind, NodeId, Span};
use serde::{Serialize, Deserialize};
use std::collections::HashMap;

/// a index of symbol table
#[derive(Serialize, Deserialize, Debug)]
pub struct Symbol(SymbolIndex);
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct SymbolIndex(u32);

/// Symbol Table genearte by ast
#[derive(Serialize, Deserialize, Debug)]
pub struct SymbolTable {
    table: HashMap<SymbolIndex, SymbolDesc>,
    cnt_sym: SymbolIndex,
}
impl SymbolTable {
    pub fn new() -> Self {
        Self {
            table: HashMap::new(),
            cnt_sym: SymbolIndex(0),
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub enum FuncOrVarKind {
    Func,
    Var,
}
#[derive(Serialize, Deserialize, Debug)]
pub struct SymbolDesc {
    name: String,
    kind: (FuncOrVarKind, BasicTypeKind),
    scope: Scope,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum ScopeType {
    Extern,
    FuncParam,  // as a formal param
    Global,     // In CompUnit
    BlockLocal, // In a block
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Scope {
    ast_node: NodeId, // the scope is either entire or partial of that ast_node
    scope_type: ScopeType,
    span: Span, // indicate scope start from where in a Block or a CompUnit and end by default is the end of Block or CompUnit
}
impl AST{
        /// TODO:Test enter/exit scope and insert symbol
        pub fn enter_scope(&mut self) {
            self.sym_in_scopes.append(&mut Vec::new())
        }
        pub fn insert_symbol(
            &mut self,
            name: String,
            kind: (FuncOrVarKind, BasicTypeKind),
            scope: Scope,
        ) {
            let id = self.symbol_table.cnt_sym;
            self.symbol_table.table.insert(id, SymbolDesc{
                name,kind,scope
            });
        }
        pub fn exit_scope(&mut self) {
            let exiting = self
                .sym_in_scopes
                .pop()
                .expect("Expect a scope to exit from!");
            for idx in exiting {
                let desc = self
                    .symbol_table
                    .table
                    .get(&idx)
                    .expect(format!("Can't found entry for {:?}", idx).as_str());
                let name = &desc.name;
                // remove idx from name2index reverse table
                let arr_idx = self
                    .name2index
                    .get_mut(name)
                    .expect(format!("Can't found entry for {}", name).as_str());
                assert_eq!(idx, *arr_idx.last().expect("Expect non empty vecs"));
                let _last = arr_idx.pop().unwrap();
            }
        }
}