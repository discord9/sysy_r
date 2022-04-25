use super::ast::{BasicTypeKind, NodeId, Span, AST};
use serde::{Deserialize, Serialize};
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
    scope: ScopeType,
}

/// store all `SymbolIndex` in this scope and record scope type
#[derive(Serialize, Deserialize, Debug)]
pub struct ScopeContent {
    /// `SymbolIndex` in this scope
    symbol_indexs: Vec<SymbolIndex>,
    scope_type: ScopeType,
}
impl ScopeContent {
    pub fn new_empty(scope_type: ScopeType) -> Self {
        Self {
            symbol_indexs: Vec::new(),
            scope_type,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Copy, Clone)]
pub enum ScopeType {
    /// like a ad hoc extern std func
    Extern,
    /// as a formal param
    FuncParam,
    /// In `CompUnit`
    Global,
    /// In a `Block`
    BlockLocal,
    /// In a FuncDef
    Func,
}

// store
// #[derive(Serialize, Deserialize, Debug)]
// pub struct SymbolScope(ScopeType);
//ast_node: NodeId, // the scope is either entire or partial of that ast_node

impl AST {
    /// TODO:Test enter/exit scope and insert symbol
    pub fn enter_scope(&mut self, scope_type: ScopeType) {
        let scope = ScopeContent {
            symbol_indexs: Vec::new(),
            scope_type,
        };
        self.sym_in_scopes.push(scope);
    }
    pub fn exit_expect_scope(&mut self, scope_type: ScopeType) {
        assert_eq!(self.get_current_scope(), scope_type);
        self.exit_scope();
    }
    pub fn exit_scope(&mut self) {
        let exiting = self
            .sym_in_scopes
            .pop()
            .expect("Expect a scope to exit from!");
        for idx in exiting.symbol_indexs {
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

    /// Return current scope
    pub fn get_current_scope(&mut self) -> ScopeType {
        self.sym_in_scopes
            .last()
            .expect("At least Global scope exist.")
            .scope_type
    }
    /// insert a symbol into symbol table
    pub fn insert_symbol(
        &mut self,
        name: String,
        kind: (FuncOrVarKind, BasicTypeKind),
        scope_type: ScopeType,
    ) -> Symbol {
        let id = self.symbol_table.cnt_sym;
        self.symbol_table.cnt_sym.0 += 1;
        self.symbol_table.table.insert(
            id,
            SymbolDesc {
                name: name.clone(),
                kind,
                scope: scope_type,
            },
        );
        // add this new symbol to current scope
        assert_eq!(
            self.sym_in_scopes.last_mut().unwrap().scope_type,
            scope_type
        );
        self.sym_in_scopes
            .last_mut()
            .unwrap()
            .symbol_indexs
            .push(id);
        match self.name2index.get_mut(&name) {
            Some(v) => {
                v.push(id);
            }
            None => {
                self.name2index.insert(name, vec![id]);
            }
        }
        Symbol(id)
    }

    /// search sym_in_scope field to find the actual symbol
    pub fn get_symbol(&self, name: &String) -> Option<Symbol> {
        Some(Symbol(
            *(self.name2index.get(name).unwrap()).last().unwrap(),
        ))
    }
}
