//! ## Substitutions
//! This module contains an implementation of substitutions on first order constructs, the key
//! things exposed are:
//! - [Substitution] which is the representation of a substitution, mapping some variables to new
//!   terms to replace them with.
//! - [Substitutable] which may be implemented for types that have some notion of substitution.

use std::collections::HashMap;

use crate::term_bank::{
    RawTerm::{App, Var},
    Term, TermBank, VariableIdentifier,
};

/// A first order substitution, mapping variables to terms to replace them with.
#[derive(Debug, Clone)]
pub struct Substitution {
    map: HashMap<VariableIdentifier, Term>,
}

impl Substitution {
    /// Create a new empty substitution.
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Associate `var` with `term` in the substitution.
    pub fn insert(&mut self, var: VariableIdentifier, term: Term) {
        self.map.insert(var, term);
    }

    /// Obtain the term associated with `var` if it exists.
    pub fn get(&self, var: VariableIdentifier) -> Option<Term> {
        self.map.get(&var).cloned()
    }

    /// Return `true` if the substitution is an identity substitution.
    pub fn is_nop(&self) -> bool {
        self.map.is_empty()
    }

    /// Compose the current substitution with `{ var_id |-> term }`.
    pub fn compose_binding(
        &mut self,
        var_id: VariableIdentifier,
        term: Term,
        term_bank: &TermBank,
    ) {
        let mut new_subst = Substitution::new();
        new_subst.insert(var_id, term.clone());
        for (_, value) in self.map.iter_mut() {
            *value = value.clone().subst_with(&new_subst, &term_bank);
        }
        self.map.entry(var_id).or_insert_with(|| term);
    }
}

/// A type that has a substitution operation on itself.
pub trait Substitutable {
    /// Apply `subst` to `self`, hash consing terms using `term_bank`.
    fn subst_with(self, subst: &Substitution, term_bank: &TermBank) -> Self;
}

impl Term {
    fn subst_with_aux(
        self,
        subst: &Substitution,
        term_bank: &TermBank,
        cache: &mut HashMap<Term, Term>,
    ) -> Term {
        if self.is_ground() {
            self
        } else if let Some(hit) = cache.get(&self) {
            hit.clone()
        } else {
            let substituted = match self.as_ref() {
                Var { id, .. } => subst.get(*id).unwrap_or(self.clone()),
                App { id, args, .. } => {
                    let new_args = args
                        .iter()
                        .map(|arg| arg.clone().subst_with_aux(subst, term_bank, cache))
                        .collect();
                    term_bank.mk_app(*id, new_args)
                }
            };
            cache.insert(self, substituted.clone());
            substituted
        }
    }
}

impl Substitutable for Term {
    /// Apply `subst` to this term, if the substitution fulfills [Substitution::is_nop] or the term
    /// is ground this is constant time, otherwise up to `O(dag_size(term))`.
    fn subst_with(self, subst: &Substitution, term_bank: &TermBank) -> Self {
        if subst.is_nop() {
            self
        } else {
            let mut cache = HashMap::new();
            self.subst_with_aux(subst, term_bank, &mut cache)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        subst::Substitutable,
        term_bank::{FunctionInformation, TermBank, VariableInformation},
    };

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
        assert_eq!(t1.clone().subst_with(&sigma1, &term_bank), t4);

        let mut sigma2 = Substitution::new();
        sigma2.insert(x_ident, t2.clone());
        sigma2.insert(y_ident, t3.clone());
        assert_eq!(t1.clone().subst_with(&sigma2, &term_bank), t5);
    }

    #[test]
    fn subterm_test() {
        let mut term_bank = TermBank::new();
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 2,
        });
        let x_ident = term_bank.add_variable(VariableInformation {
            name: "x".to_string(),
        });
        let x = term_bank.mk_variable(x_ident);
        let y_ident = term_bank.add_variable(VariableInformation {
            name: "y".to_string(),
        });
        let y = term_bank.mk_variable(y_ident);

        let t1 = term_bank.mk_app(
            f,
            vec![
                term_bank.mk_app(f, vec![x.clone(), x.clone()]),
                term_bank.mk_app(f, vec![x.clone(), x.clone()]),
            ],
        );
        let t2 = term_bank.mk_app(
            f,
            vec![
                term_bank.mk_app(f, vec![y.clone(), y.clone()]),
                term_bank.mk_app(f, vec![y.clone(), y.clone()]),
            ],
        );
        let mut sigma = Substitution::new();
        sigma.insert(x_ident, y.clone());
        assert_eq!(t1.subst_with(&sigma, &term_bank), t2);
    }
}
