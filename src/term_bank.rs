use std::{
    collections::HashSet,
    hash::{DefaultHasher, Hash, Hasher},
};

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
    var_bloom_filter: u64,
}

impl TermData {
    fn new(hash: u64, var_bloom_filter: u64) -> Self {
        Self { hash, var_bloom_filter }
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

impl VariableIdentifier {
    fn to_bloom_filter(&self) -> u64 {
        1 << (self.0 % 64) as u64
    }

    pub fn occurs_in(&self, term: &Term) -> bool {
        let mut visited = HashSet::new();
        let mut worklist = vec![term];
        let bloom_id = self.to_bloom_filter();

        while let Some(term) = worklist.pop() {
            if term.get_data().var_bloom_filter & bloom_id == 0 || visited.contains(term) {
                continue;
            } else {
                match term.as_ref() {
                    RawTerm::Var { id, .. } => {
                        if id == self {
                            return true;
                        }
                    }
                    RawTerm::App { args, .. } => args.iter().for_each(|arg| {
                        visited.insert(arg);
                    }),
                }
                visited.insert(term);
            }
        }
        false
    }
}

impl RawTerm {
    fn get_data(&self) -> &TermData {
        match self {
            RawTerm::Var { data, .. } | RawTerm::App { data, .. } => data,
        }
    }

    pub fn is_ground(&self) -> bool {
        self.get_data().var_bloom_filter == 0
    }

    pub fn get_variable_id(&self) -> Option<VariableIdentifier> {
        match self {
            RawTerm::Var { id, .. } => Some(*id),
            RawTerm::App { .. } => None,
        }
    }

    pub fn get_function_id(&self) -> Option<FunctionIdentifier> {
        match self {
            RawTerm::Var { .. } => None,
            RawTerm::App { id, .. } => Some(*id),
        }
    }

    pub fn get_function_args(&self) -> Option<&Vec<Term>> {
        match self {
            RawTerm::Var { .. } => None,
            RawTerm::App { args, .. } => Some(args),
        }
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
            data: TermData::new(hasher.finish(), id.to_bloom_filter()),
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
        let ground = args.iter().fold(0, |acc, arg| acc | arg.get_data().var_bloom_filter);
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

    fn pretty_print_aux(&self, term: &Term, acc: &mut String) {
        match &**term {
            RawTerm::Var { id, .. } => acc.push_str(&self.get_variable_info(*id).name),
            RawTerm::App { id, args, .. } => {
                let info = self.get_function_info(*id);
                acc.push_str(&info.name);
                if info.arity > 0 {
                    acc.push_str("(");
                    args.iter().for_each(|arg| {
                        self.pretty_print_aux(arg, acc);
                        acc.push_str(", ");
                    });
                    acc.push_str(")");
                }
            }
        }
    }

    pub fn pretty_print(&self, term: &Term) -> String {
        let mut str = String::new();
        self.pretty_print_aux(term, &mut str);
        str
    }
}
