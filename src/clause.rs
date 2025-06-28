//! ## Clauses
//! This module provides an implementation of superposition literals and CNF clauses as well as sets
//! of clauses. The key exported data structures are:
//! - [Literal] for representing equalities and disequalities
//! - [Clause] for representing disjunctions of literals
//! - [ClauseSet] for representing sets of clauses

use std::{
    collections::{BTreeMap, HashSet},
    hash::Hash,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{
    pretty_print::BankPrettyPrint,
    subst::{Substitutable, Substitution},
    term_bank::{Term, TermBank},
};

/// Whether a literal is `=` or `!=`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Polarity {
    /// The literal is `=`.
    Eq,
    /// The literal is `!=`.
    Ne,
}

impl Polarity {
    /// Flip the polarity to the other one.
    fn negate(&self) -> Polarity {
        match self {
            Polarity::Eq => Polarity::Ne,
            Polarity::Ne => Polarity::Eq,
        }
    }
}

/// A literal represents either an equality or a disequality between two [Term].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    lhs: Term,
    rhs: Term,
    kind: Polarity,
}

impl Literal {
    /// Create a new literal with `lhs = rhs` or `lhs != rhs` depending on `kind`, note that the
    /// literal will internally choose some canonical sorting of `lhs` and `rhs` such that
    /// `get_lhs()` can actually return what was submitted as `lhs` here.
    pub fn new(lhs: Term, rhs: Term, kind: Polarity) -> Self {
        // As terms are globally shared this should ensure that literals generated with the same
        // terms (regardless of symmetry) end up being represented as the same datastructure
        // underneath.
        let (lhs, rhs) = if (lhs.as_ptr() as usize) < (rhs.as_ptr() as usize) {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        Self { lhs, rhs, kind }
    }

    /// Create a new literal with `lhs = rhs`.
    pub fn mk_eq(lhs: Term, rhs: Term) -> Self {
        Self::new(lhs, rhs, Polarity::Eq)
    }

    /// Create a new literal with `lhs != rhs`.
    pub fn mk_ne(lhs: Term, rhs: Term) -> Self {
        Self::new(lhs, rhs, Polarity::Ne)
    }

    /// Get the left hand side of the literal.
    pub fn get_lhs(&self) -> &Term {
        &self.lhs
    }

    /// Get the right hand side of the literal.
    pub fn get_rhs(&self) -> &Term {
        &self.rhs
    }

    /// Get the polarity of the literal.
    pub fn get_pol(&self) -> Polarity {
        self.kind
    }

    /// Check up to symmetry whether `other` is the negation of `self`.
    pub fn is_negation_of(&self, other: &Self) -> bool {
        self.get_pol() == other.get_pol().negate()
            && self.get_lhs() == other.get_lhs()
            && self.get_rhs() == other.get_rhs()
    }

    /// Check whether the literal is a disequality.
    pub fn is_ne(&self) -> bool {
        self.kind == Polarity::Ne
    }

    /// Check whether the literal is an equality.
    pub fn is_eq(&self) -> bool {
        self.kind == Polarity::Eq
    }

    /// Flip the polarity of the literal.
    pub fn negate(self) -> Self {
        Self {
            lhs: self.lhs,
            rhs: self.rhs,
            kind: self.kind.negate(),
        }
    }

    /// Compute the default weight of the literal for the clause queue.
    pub fn weight(&self) -> u32 {
        self.lhs.weight() + self.rhs.weight()
    }

    /// Iterator over both symmetries of a literal.
    pub fn symm_term_iter(&self) -> SymmLitIterator<'_> {
        SymmLitIterator { lit: self, idx: 0 }
    }
}

impl Substitutable for Literal {
    /// Apply `subst` to the literal, this is constant time if the substitution is a nop
    /// or lhs and rhs are ground, otherwise the worst case complexity is
    /// `O(dag_size(lhs) + dag_size(rhs))`.
    fn subst_with(self, subst: &Substitution, term_bank: &TermBank) -> Self {
        let new_lhs = self.lhs.subst_with(subst, term_bank);
        let new_rhs = self.rhs.subst_with(subst, term_bank);
        Self {
            lhs: new_lhs,
            rhs: new_rhs,
            kind: self.kind,
        }
    }
}

/// Iterator over both symmetries of a literal.
pub struct SymmLitIterator<'a> {
    lit: &'a Literal,
    idx: u8,
}

impl<'a> Iterator for SymmLitIterator<'a> {
    type Item = (Term, Term);

    fn next(&mut self) -> Option<Self::Item> {
        match self.idx {
            0 => {
                self.idx += 1;
                Some((self.lit.get_lhs().clone(), self.lit.get_rhs().clone()))
            }
            1 => {
                self.idx += 1;
                Some((self.lit.get_rhs().clone(), self.lit.get_lhs().clone()))
            }
            2 => None,
            _ => unreachable!(),
        }
    }
}

/// A unique identifier for a literal within a clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LiteralId(usize);

// We want to maintain unique clause identifiers for ease of indexing in a [ClauseSet], this
// counter provides us with these identifiers.
static CLAUSE_ID_COUNT: AtomicUsize = AtomicUsize::new(0);

/// A unique identifier for clauses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId(usize);

fn next_clause_id() -> ClauseId {
    ClauseId(CLAUSE_ID_COUNT.fetch_add(1, Ordering::SeqCst))
}

/// Uniquely identifiable clauses consisting of a multiset of [Literal].
#[derive(Debug, Clone)]
pub struct Clause {
    id: ClauseId,
    pub(crate) literals: Vec<Literal>,
}

impl Clause {
    /// Create a new clause containing the literals from `vec`.
    pub fn new(vec: Vec<Literal>) -> Self {
        Self {
            id: next_clause_id(),
            literals: vec,
        }
    }

    /// Get how many literals are in the clause, counting duplicates, this operation is `O(1)`.
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Check if the clause is empty, this operation is `O(1)`.
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Check if the clause is unit, this operation is `O(1)`.
    pub fn is_unit(&self) -> bool {
        self.len() == 1
    }

    /// Get the default clause weight for the clause queue.
    pub fn weight(&self) -> u32 {
        self.literals.iter().map(Literal::weight).sum()
    }

    /// Obtain a literal from the clause by index.
    pub fn get_literal(&self, literal_id: LiteralId) -> &Literal {
        &self.literals[literal_id.0]
    }

    /// Obtain the unique identifier of this clause.
    pub fn get_id(&self) -> ClauseId {
        self.id
    }

    /// Obtain an iterator over the literals in the clause.
    pub fn iter(&self) -> impl Iterator<Item = (LiteralId, &Literal)> {
        (0..self.len()).map(|idx| {
            let id = LiteralId(idx);
            (id, self.get_literal(id))
        })
    }

    /// Obtain an iterator over the literals after `id` in the clause.
    pub fn iter_after(&self, id: LiteralId) -> impl Iterator<Item = (LiteralId, &Literal)> {
        ((id.0 + 1)..self.len()).map(|idx| {
            let id = LiteralId(idx);
            (id, self.get_literal(id))
        })
    }

    /// Clone the clause and substitute all of its variables with fresh ones to obtain a clause
    /// with unique variables. For ground clauses this is a very cheap `O(clause.len())`, otherwise
    /// worst case `O(clause.len() * max(dag_size(lit_i)))`.
    pub fn fresh_variable_clone(&self, term_bank: &mut TermBank) -> Clause {
        let mut set = HashSet::new();
        for lit in self.literals.iter() {
            lit.get_lhs().collect_vars_into(&mut set);
            lit.get_rhs().collect_vars_into(&mut set);
        }

        if set.is_empty() {
            self.clone()
        } else {
            let mut subst = Substitution::new();
            for old_var in set.iter() {
                subst.insert(*old_var, term_bank.mk_replacement_variable(*old_var));
            }

            self.clone().subst_with(&subst, term_bank)
        }
    }
}

impl PartialEq for Clause {
    /// Clauses are compared by their unique id so comparison is always `O(1)`
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id)
    }
}

impl Eq for Clause {}

impl PartialOrd for Clause {
    /// Clauses are compared by their unique id so comparison is always `O(1)`
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.id.partial_cmp(&other.id)
    }
}

impl Ord for Clause {
    /// Clauses are compared by their unique id so comparison is always `O(1)`
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl Hash for Clause {
    /// Clauses are hashed by their unique id so hashing is always `O(1)`
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Hash::hash(&self.id, state);
    }
}

impl Substitutable for Clause {
    fn subst_with(self, subst: &Substitution, term_bank: &TermBank) -> Self {
        let new_lits = self
            .literals
            .into_iter()
            .map(|lit| lit.subst_with(subst, term_bank))
            .collect();
        Self {
            id: next_clause_id(),
            literals: new_lits,
        }
    }
}

impl BankPrettyPrint for Clause {
    fn print_into(&self, term_bank: &TermBank, acc: &mut String) {
        if self.is_empty() {
            acc.push_str("⊥");
        } else {
            for lit_idx in 0..(self.len() - 1) {
                let lit = self.get_literal(LiteralId(lit_idx));
                acc.push_str("(");
                lit.print_into(term_bank, acc);
                acc.push_str(") ∨ ");
            }
            let lit = self.get_literal(LiteralId(self.len() - 1));
            acc.push_str("(");
            lit.print_into(term_bank, acc);
            acc.push_str(")");
        }
    }
}

/// A set of clauses indexed by unique clause identifiers.
pub struct ClauseSet {
    map: BTreeMap<ClauseId, Clause>,
}

impl ClauseSet {
    /// Create an empty clause set.
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    /// Insert a new clause into the set.
    pub fn insert(&mut self, clause: Clause) {
        self.map.insert(clause.id, clause);
    }

    /// Get clause by its unique identifier.
    pub fn get_by_id(&self, id: ClauseId) -> Option<&Clause> {
        self.map.get(&id)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Clause> {
        self.map.iter().map(|(_, clause)| clause)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        clause::Clause,
        subst::{Substitutable, Substitution},
        term_bank::{FunctionInformation, TermBank, VariableInformation},
    };

    use super::Literal;

    #[test]
    fn basic_literal_test() {
        let mut term_bank = TermBank::new();
        let x_id = term_bank.add_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y_id = term_bank.add_variable(VariableInformation {
            name: "y".to_string(),
        });
        let x = term_bank.mk_variable(x_id);
        let y = term_bank.mk_variable(y_id);

        let l1 = Literal::mk_eq(x.clone(), y.clone());
        let mut l2 = Literal::mk_ne(x.clone(), y.clone());

        assert_eq!(l1.get_lhs(), &x);
        assert_eq!(l1.get_rhs(), &y);
        assert!(l1.is_eq());
        assert!(!l1.is_ne());
        assert!(l2.is_ne());
        assert!(!l2.is_eq());
        assert_ne!(l1, l2);

        l2 = l2.negate();
        assert_eq!(l1, l2);
        assert!(l2.is_eq());

        let c1_id = term_bank.add_function(FunctionInformation {
            name: "c1".to_string(),
            arity: 0,
        });
        let c2_id = term_bank.add_function(FunctionInformation {
            name: "c2".to_string(),
            arity: 0,
        });

        let c1 = term_bank.mk_const(c1_id);
        let c2 = term_bank.mk_const(c2_id);

        let mut subst = Substitution::new();
        subst.insert(x_id, c1);
        subst.insert(y_id, c2);
        assert_eq!(
            l1.subst_with(&subst, &term_bank),
            l2.subst_with(&subst, &term_bank)
        );
    }

    #[test]
    fn basic_clause_test() {
        let mut term_bank = TermBank::new();
        let x_id = term_bank.add_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y_id = term_bank.add_variable(VariableInformation {
            name: "y".to_string(),
        });
        let z_id = term_bank.add_variable(VariableInformation {
            name: "z".to_string(),
        });

        let x = term_bank.mk_variable(x_id);
        let y = term_bank.mk_variable(y_id);
        let z = term_bank.mk_variable(z_id);

        let clause = Clause::new(vec![]);
        assert_eq!(clause.len(), 0);
        assert!(clause.is_empty());
        assert!(!clause.is_unit());

        let lit1 = Literal::mk_eq(x.clone(), y.clone());
        let clause = Clause::new(vec![lit1.clone()]);
        assert_eq!(clause.len(), 1);
        assert!(!clause.is_empty());
        assert!(clause.is_unit());

        let lit2 = Literal::mk_ne(y.clone(), z.clone());
        let clause = Clause::new(vec![lit1.clone(), lit2.clone()]);
        assert_eq!(clause.len(), 2);
        assert!(!clause.is_empty());
        assert!(!clause.is_unit());

        let clause = Clause::new(vec![lit1.clone(), lit2.clone(), lit1.clone()]);
        assert_eq!(clause.len(), 3);
    }
}
