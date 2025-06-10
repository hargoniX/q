use std::hash::{DefaultHasher, Hash, Hasher};

use crate::term_manager::{HashConsed, Table};

// Based on: https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-IWIL-2025.pdf

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionInformation {
    pub name: String,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableInformation {
    pub name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionIdentifier(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VariableIdentifier(u32);

#[derive(Debug, PartialEq, Eq)]
pub struct TermData {
    hash: u64,
    ground: bool,
}

impl TermData {
    fn new(hash: u64, ground: bool) -> Self {
        Self { hash, ground }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum RawTerm {
    Var {
        id: VariableIdentifier,
        data: TermData,
    },
    App {
        id: FunctionIdentifier,
        args: Vec<Term>,
        data: TermData,
    },
}

pub type Term = HashConsed<RawTerm>;

impl Hash for RawTerm {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.get_data().hash);
    }
}

impl RawTerm {
    fn get_data(&self) -> &TermData {
        match self {
            RawTerm::Var { data, .. } | RawTerm::App { data, .. } => data,
        }
    }

    pub fn is_ground(&self) -> bool {
        self.get_data().ground
    }
}

#[derive(Debug)]
pub struct TermBank {
    hash_cons_table: Table<RawTerm>,
    variable_bank: Vec<VariableInformation>,
    function_bank: Vec<FunctionInformation>,
}

impl TermBank {
    pub fn new() -> Self {
        Self {
            hash_cons_table: Table::new(),
            variable_bank: Vec::new(),
            function_bank: Vec::new(),
        }
    }

    pub fn add_variable(&mut self, info: VariableInformation) -> VariableIdentifier {
        let size = self.variable_bank.len();
        self.variable_bank.push(info);
        VariableIdentifier(size.try_into().unwrap())
    }

    pub fn add_function(&mut self, info: FunctionInformation) -> FunctionIdentifier {
        let size = self.function_bank.len();
        self.function_bank.push(info);
        FunctionIdentifier(size.try_into().unwrap())
    }

    pub fn get_variable_info(&self, id: VariableIdentifier) -> &VariableInformation {
        &self.variable_bank[id.0 as usize]
    }

    pub fn get_function_info(&self, id: FunctionIdentifier) -> &FunctionInformation {
        &self.function_bank[id.0 as usize]
    }

    pub fn gc(&self) {
        self.hash_cons_table.gc();
    }

    pub fn mk_variable(&self, id: VariableIdentifier) -> Term {
        let mut hasher = DefaultHasher::new();
        hasher.write_u32(id.0);
        let var = RawTerm::Var {
            id,
            data: TermData::new(hasher.finish(), false),
        };
        self.hash_cons_table.hashcons(var)
    }

    pub fn mk_fresh_variable(&mut self, info: VariableInformation) -> Term {
        let id = self.add_variable(info);
        self.mk_variable(id)
    }

    pub fn mk_app(&self, id: FunctionIdentifier, args: Vec<Term>) -> Term {
        let mut hasher = DefaultHasher::new();
        hasher.write_u32(id.0);
        args.iter().for_each(|arg| arg.hash(&mut hasher));
        let hash = hasher.finish();
        let ground = args.iter().fold(true, |acc, arg| acc && arg.is_ground());
        debug_assert_eq!(self.get_function_info(id).arity, args.len());
        let app = RawTerm::App {
            id,
            args,
            data: TermData::new(hash, ground),
        };
        self.hash_cons_table.hashcons(app)
    }

    pub fn mk_const(&self, id: FunctionIdentifier) -> Term {
        self.mk_app(id, vec![])
    }
}
