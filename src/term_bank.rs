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
    var_count: u32,
    function_count: u32,
    weight: u32,
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
                        worklist.push(arg);
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

    pub fn variable_id(&self) -> Option<VariableIdentifier> {
        match self {
            RawTerm::Var { id, .. } => Some(*id),
            RawTerm::App { .. } => None,
        }
    }

    pub fn function_id(&self) -> Option<FunctionIdentifier> {
        match self {
            RawTerm::Var { .. } => None,
            RawTerm::App { id, .. } => Some(*id),
        }
    }

    pub fn function_args(&self) -> Option<&Vec<Term>> {
        match self {
            RawTerm::Var { .. } => None,
            RawTerm::App { args, .. } => Some(args),
        }
    }

    pub fn weight(&self) -> u32 {
        self.get_data().weight
    }
}

impl HashConsed<RawTerm> {
    pub fn collect_vars_into(&self, acc: &mut HashSet<VariableIdentifier>) {
        let mut visited = HashSet::new();
        let mut front = vec![self];
        while let Some(term) = front.pop() {
            match &**term {
                RawTerm::Var { id, .. } => {
                    acc.insert(*id);
                }
                RawTerm::App { args, .. } => {
                    for arg in args.iter() {
                        if !(arg.is_ground() && visited.contains(arg)) {
                            front.push(arg);
                        }
                        visited.insert(term);
                    }
                }
            }
        }
    }

    pub fn collect_vars(&self) -> HashSet<VariableIdentifier> {
        let mut set = HashSet::new();
        self.collect_vars_into(&mut set);
        set
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

    fn weight_heuristic(var_count: u32, function_count: u32) -> u32 {
        2 * function_count + var_count
    }

    pub fn mk_variable(&self, id: VariableIdentifier) -> Term {
        let mut hasher = DefaultHasher::new();
        hasher.write_u32(id.0);
        let var = RawTerm::Var {
            id,
            data: TermData {
                hash: hasher.finish(),
                var_bloom_filter: id.to_bloom_filter(),
                var_count: 1,
                function_count: 0,
                weight: Self::weight_heuristic(1, 0),
            },
        };
        self.hash_cons_table.hashcons(var)
    }

    pub fn mk_fresh_variable(&mut self, info: VariableInformation) -> Term {
        let id = self.add_variable(info);
        self.mk_variable(id)
    }

    pub fn mk_replacement_variable(&mut self, old_id: VariableIdentifier) -> Term {
        let mut info = self.get_variable_info(old_id).clone();
        info.name.push_str("_rep");
        self.mk_fresh_variable(info)
    }

    pub fn mk_app(&self, id: FunctionIdentifier, args: Vec<Term>) -> Term {
        let mut hasher = DefaultHasher::new();
        hasher.write_u32(id.0);
        args.iter().for_each(|arg| arg.hash(&mut hasher));
        let hash = hasher.finish();
        let var_bloom_filter = args
            .iter()
            .fold(0, |acc, arg| acc | arg.get_data().var_bloom_filter);
        let var_count = args.iter().map(|a| a.get_data().var_count).sum();
        let function_count = args
            .iter()
            .map(|a| a.get_data().function_count)
            .sum::<u32>()
            + 1;
        debug_assert_eq!(self.get_function_info(id).arity, args.len());
        let data = TermData {
            hash,
            var_bloom_filter,
            var_count,
            function_count,
            weight: Self::weight_heuristic(var_count, function_count),
        };
        let app = RawTerm::App { id, args, data };
        self.hash_cons_table.hashcons(app)
    }

    pub fn mk_const(&self, id: FunctionIdentifier) -> Term {
        self.mk_app(id, vec![])
    }

    pub fn get_variable_index(&self, ident: VariableIdentifier) -> u32 {
        ident.0
    }

    pub fn get_function_index(&self, ident: FunctionIdentifier) -> u32 {
        ident.0
    }

    pub fn get_variable_count(&self) -> usize {
        self.variable_bank.len()
    }
}
