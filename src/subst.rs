use std::collections::HashMap;

use crate::term_bank::{
    RawTerm::{App, Var},
    Term, TermBank, VariableIdentifier,
};

#[derive(Debug)]
pub struct Substitution {
    map: HashMap<VariableIdentifier, Term>,
}

impl Substitution {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    pub fn insert(&mut self, var: VariableIdentifier, term: Term) {
        self.map.insert(var, term);
    }

    pub fn get(&self, var: VariableIdentifier) -> Option<Term> {
        self.map.get(&var).cloned()
    }

    pub fn apply_term(&self, term: Term, term_bank: &TermBank) -> Term {
        if term.is_ground() {
            return term;
        }

        match term.as_ref() {
            Var { id, .. } => self.get(*id).unwrap_or(term),
            App { id, args, .. } => {
                let new_args = args
                    .iter()
                    .map(|arg| self.apply_term(arg.clone(), term_bank))
                    .collect();
                term_bank.mk_app(*id, new_args)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::term_bank::{FunctionInformation, TermBank, VariableInformation};

    use super::Substitution;

    #[test]
    fn basic_test() {
        let mut term_bank = TermBank::new();
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 2,
        });
        let g = term_bank.add_function(FunctionInformation {
            name: "g".to_string(),
            arity: 1,
        });
        let a = term_bank.add_function(FunctionInformation {
            name: "a".to_string(),
            arity: 0,
        });
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
        });
        let x_ident = term_bank.add_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y_ident = term_bank.add_variable(VariableInformation {
            name: "y".to_string(),
        });
        let x = term_bank.mk_variable(x_ident);
        let y = term_bank.mk_variable(y_ident);

        let t1 = term_bank.mk_app(f, vec![x.clone(), term_bank.mk_app(g, vec![y.clone()])]);
        let t2 = term_bank.mk_const(a);
        let t3 = term_bank.mk_const(b);
        let t4 = term_bank.mk_app(f, vec![t2.clone(), term_bank.mk_app(g, vec![t2.clone()])]);
        let t5 = term_bank.mk_app(f, vec![t2.clone(), term_bank.mk_app(g, vec![t3.clone()])]);
        let mut sigma1 = Substitution::new();
        sigma1.insert(x_ident, t2.clone());
        sigma1.insert(y_ident, t2.clone());
        assert_eq!(sigma1.apply_term(t1.clone(), &term_bank), t4);

        let mut sigma2 = Substitution::new();
        sigma2.insert(x_ident, t2.clone());
        sigma2.insert(y_ident, t3.clone());
        assert_eq!(sigma2.apply_term(t1.clone(), &term_bank), t5);
    }
}
