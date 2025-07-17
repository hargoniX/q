//! ## Substitutions
//! This module contains an implementation of substitutions on first order constructs, the key
//! things exposed are:
//! - [Substitution] providing a general notion of substitutions
//! - [BacktrackSubst] implementing a backtrackable substitution as a persistent data structure
//! - [HashSubstitution] implementing a substitution as a hash map
//! - [Substitutable] which may be implemented for types that have some notion of substitution.

use rpds::HashTrieMap;
use rustc_hash::FxHashMap;

use crate::term_bank::{
    RawTerm::{App, Var},
    Term, TermBank, VarBloomFilter, VariableIdentifier,
};

pub trait Substitution {
    /// Create a new empty substitution.
    fn new() -> Self;
    /// Associate `var` with `term` in the substitution.
    fn insert(&mut self, var: VariableIdentifier, term: Term);
    /// Obtain the term associated with `var` if it exists.
    fn get(&self, var: VariableIdentifier) -> Option<Term>;
    /// Return `true` if the substitution is an identity substitution.
    fn is_nop(&self) -> bool;
    /// Whether the substitution may apply to `term`, if this returns false
    /// it is guaranteed that no variable from the substitution is contained in
    /// the term.
    fn may_apply(&self, term: &Term) -> bool;
}

// TODO: check hash function

/// A first order substitution, mapping variables to terms to replace them with, implemented as a
/// hash array mapped trie to allow for cheap copies.
#[derive(Debug, Clone)]
pub struct BacktrackSubst {
    /// The map that is the substitution itself.
    map: HashTrieMap<VariableIdentifier, Term>,
    /// A var bloom filter for the variables the substitution maps s.t. we can quickly see if a
    /// term we are called for is irrelevant.
    filter: VarBloomFilter
}

impl Substitution for BacktrackSubst {
    fn new() -> Self {
        Self {
            map: HashTrieMap::new(),
            filter: VarBloomFilter::new(),
        }
    }

    fn insert(&mut self, var: VariableIdentifier, term: Term) {
        self.map = self.map.insert(var, term);
        self.filter |= var.to_bloom_filter();
    }

    fn get(&self, var: VariableIdentifier) -> Option<Term> {
        self.map.get(&var).cloned()
    }

    fn is_nop(&self) -> bool {
        self.filter.is_empty()
    }

    fn may_apply(&self, term: &Term) -> bool {
        !(term.var_bloom_filter() & self.filter).is_empty()
    }
}

/// A first order substitution, mapping variables to terms to replace them with, implemented as a
/// hashmap for highest insert and lookup performance.
#[derive(Debug, Clone)]
pub struct HashSubstitution {
    /// The map that is the substitution itself.
    map: FxHashMap<VariableIdentifier, Term>,
    /// A var bloom filter for the variables the substitution maps s.t. we can quickly see if a
    /// term we are called for is irrelevant.
    filter: VarBloomFilter,
}

impl HashSubstitution {
    /// Compose the current substitution with `{ var_id |-> term }`.
    pub fn compose_binding(
        &mut self,
        var_id: VariableIdentifier,
        term: Term,
        term_bank: &TermBank,
    ) {
        let mut new_subst = HashSubstitution::new();
        new_subst.insert(var_id, term.clone());
        for (_, value) in self.map.iter_mut() {
            *value = value.clone().subst_with(&new_subst, term_bank);
        }
        self.map.entry(var_id).or_insert_with(|| term);
        self.filter |= var_id.to_bloom_filter();
    }
}

impl Substitution for HashSubstitution {
    fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            filter: VarBloomFilter::new(),
        }
    }

    fn insert(&mut self, var: VariableIdentifier, term: Term) {
        self.map.insert(var, term);
        self.filter |= var.to_bloom_filter();
    }

    fn get(&self, var: VariableIdentifier) -> Option<Term> {
        self.map.get(&var).cloned()
    }

    fn is_nop(&self) -> bool {
        self.filter.is_empty()
    }

    fn may_apply(&self, term: &Term) -> bool {
        !(term.var_bloom_filter() & self.filter).is_empty()
    }
}

/// A type that has a substitution operation on itself.
pub trait Substitutable {
    /// Apply `subst` to `self`, hash consing terms using `term_bank`.
    fn subst_with<S: Substitution>(self, subst: &S, term_bank: &TermBank) -> Self;
}

impl Term {
    fn subst_with_aux<S: Substitution>(
        self,
        subst: &S,
        term_bank: &TermBank,
        cache: &mut FxHashMap<Term, Term>,
    ) -> Term {
        if !subst.may_apply(&self) {
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
    fn subst_with<S: Substitution>(self, subst: &S, term_bank: &TermBank) -> Self {
        if subst.is_nop() {
            self
        } else {
            let mut cache = FxHashMap::default();
            self.subst_with_aux(subst, term_bank, &mut cache)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::subst::Substitution;
    use crate::{
        subst::Substitutable,
        term_bank::{FunctionInformation, TermBank, VariableInformation},
    };

    use super::HashSubstitution;

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
        let mut sigma1 = HashSubstitution::new();
        sigma1.insert(x_ident, t2.clone());
        sigma1.insert(y_ident, t2.clone());
        assert_eq!(t1.clone().subst_with(&sigma1, &term_bank), t4);

        let mut sigma2 = HashSubstitution::new();
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
        let mut sigma = HashSubstitution::new();
        sigma.insert(x_ident, y.clone());
        assert_eq!(t1.subst_with(&sigma, &term_bank), t2);
    }
}
