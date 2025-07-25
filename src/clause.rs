//! ## Clauses
//! This module provides an implementation of superposition literals and CNF clauses as well as sets
//! of clauses. The key exported data structures are:
//! - [Literal] for representing equalities and disequalities
//! - [Clause] for representing disjunctions of literals
//! - [ClauseSet] for representing sets of clauses

use std::{cell::OnceCell, cmp::Ordering, hash::Hash, rc::Rc, sync::atomic::AtomicUsize};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    kbo::KboOrd,
    pretty_print::{BankPrettyPrint, pretty_print},
    subst::{Substitutable, Substitution},
    term_bank::{Sort, Term, TermBank},
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

/// The orientation of a literal (if available)
#[derive(Debug, Clone, Copy)]
pub enum Orientation {
    /// The literal is oriented lhs -> rhs
    Natural,
    /// The literal is oriented rhs -> lhs
    Flipped,
    /// The literal can never be oriented
    Impossible,
}

/// A literal represents either an equality or a disequality between two [Term].
#[derive(Debug, Clone)]
pub struct Literal {
    lhs: Term,
    rhs: Term,
    pol: Polarity,
    orientation: Rc<OnceCell<Option<Orientation>>>,
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        self.pol == other.pol
            && ((self.lhs == other.lhs && self.rhs == other.rhs)
                || (self.lhs == other.rhs && self.rhs == other.lhs))
    }
}

impl Eq for Literal {}

impl Hash for Literal {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // To ensure same hash code for equal literals normalize using pointer values.
        let (lhs, rhs) = if (self.lhs.as_ptr() as usize) < (self.rhs.as_ptr() as usize) {
            (&self.lhs, &self.rhs)
        } else {
            (&self.rhs, &self.lhs)
        };
        lhs.hash(state);
        rhs.hash(state);
        self.pol.hash(state);
    }
}

impl Literal {
    pub fn new(lhs: Term, rhs: Term, kind: Polarity) -> Self {
        Self {
            lhs,
            rhs,
            pol: kind,
            orientation: Rc::new(OnceCell::new()),
        }
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
        self.pol
    }

    /// Check up to symmetry whether `other` is the negation of `self`.
    pub fn is_negation_of(&self, other: &Self) -> bool {
        self.pol == other.pol.negate()
            && ((self.lhs == other.lhs && self.rhs == other.rhs)
                || (self.lhs == other.rhs && self.rhs == other.lhs))
    }

    /// Check whether the literal is a disequality.
    pub fn is_ne(&self) -> bool {
        self.pol == Polarity::Ne
    }

    /// Check whether the literal is an equality.
    pub fn is_eq(&self) -> bool {
        self.pol == Polarity::Eq
    }

    /// Flip the polarity of the literal.
    pub fn negate(self) -> Self {
        Self {
            lhs: self.lhs,
            rhs: self.rhs,
            pol: self.pol.negate(),
            orientation: self.orientation,
        }
    }

    /// Iterator over both symmetries of a literal.
    pub fn symm_term_iter(&self) -> SymmLitIterator<'_> {
        SymmLitIterator { lit: self, idx: 0 }
    }

    /// Iterator over the symmetries of a literal permitted by its orientation.
    pub fn oriented_symm_term_iter(&self, term_bank: &TermBank) -> OrientedSymmLitIterator<'_> {
        OrientedSymmLitIterator {
            lit: self,
            idx: 0,
            orientation: self.get_orientation(term_bank),
        }
    }

    pub fn is_ground(&self) -> bool {
        self.lhs.is_ground() && self.rhs.is_ground()
    }

    /// `O(1)` computation for how many function symbols (including constants) occur in the term.
    pub fn function_symbol_count(&self) -> u32 {
        self.get_lhs().function_symbol_count() + self.get_rhs().function_symbol_count()
    }

    /// Obtain the orientation of the literal (if possible), note that this function will
    /// cache the orientation value after first computation.
    pub fn get_orientation(&self, term_bank: &TermBank) -> Option<Orientation> {
        *self
            .orientation
            .get_or_init(|| match self.lhs.kbo(&self.rhs, term_bank) {
                Some(Ordering::Equal) => Some(Orientation::Impossible),
                Some(Ordering::Greater) => Some(Orientation::Natural),
                Some(Ordering::Less) => Some(Orientation::Flipped),
                None => None,
            })
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
            pol: self.pol,
            orientation: Rc::new(OnceCell::new()),
        }
    }
}

/// Iterator over both symmetries of a literal.
pub struct SymmLitIterator<'a> {
    lit: &'a Literal,
    idx: u8,
}

impl Iterator for SymmLitIterator<'_> {
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

/// Iterator over the symmetries of a literal permitted by its orientation.
pub struct OrientedSymmLitIterator<'a> {
    lit: &'a Literal,
    idx: u8,
    orientation: Option<Orientation>,
}

impl Iterator for OrientedSymmLitIterator<'_> {
    type Item = (Term, Term);

    fn next(&mut self) -> Option<Self::Item> {
        match self.orientation {
            Some(Orientation::Impossible) => None,
            Some(Orientation::Natural) => match self.idx {
                0 => {
                    self.idx += 1;
                    Some((self.lit.get_lhs().clone(), self.lit.get_rhs().clone()))
                }
                1 => None,
                _ => unreachable!(),
            },
            Some(Orientation::Flipped) => match self.idx {
                0 => {
                    self.idx += 1;
                    Some((self.lit.get_rhs().clone(), self.lit.get_lhs().clone()))
                }
                1 => None,
                _ => unreachable!(),
            },
            None => match self.idx {
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
            },
        }
    }
}

/// A unique identifier for a literal within a clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LiteralId(pub(crate) usize);

// We want to maintain unique clause identifiers for ease of indexing in a [ClauseSet], this
// counter provides us with these identifiers.
static CLAUSE_ID_COUNT: AtomicUsize = AtomicUsize::new(0);

/// A unique identifier for clauses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId(pub(crate) usize);

fn next_clause_id() -> ClauseId {
    ClauseId(CLAUSE_ID_COUNT.fetch_add(1, std::sync::atomic::Ordering::SeqCst))
}

#[derive(Debug, Clone)]
struct ClauseInfo {
    /// The clause was generated from the initial problem and is not derived via other means.
    is_initial: bool,
}

/// Uniquely identifiable clauses consisting of a multiset of [Literal].
#[derive(Debug, Clone)]
pub struct Clause {
    id: ClauseId,
    info: ClauseInfo,
    pub(crate) literals: Vec<Literal>,
}

impl Clause {
    /// Create a new clause containing the literals from `vec`.
    pub fn new(vec: Vec<Literal>) -> Self {
        Self {
            id: next_clause_id(),
            info: ClauseInfo { is_initial: false },
            literals: vec,
        }
    }

    /// Create a new clause that is marked as being an initial clause.
    pub fn new_initial(vec: Vec<Literal>) -> Self {
        Self {
            id: next_clause_id(),
            info: ClauseInfo { is_initial: true },
            literals: vec,
        }
    }

    pub fn first_lit(&self) -> &Literal {
        &self.literals[0]
    }

    /// Return true iff the clause is initial, that is, part of the problem we were initially
    /// given.
    pub fn is_initial(&self) -> bool {
        self.info.is_initial
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
        let mut set = FxHashSet::default();
        for lit in self.literals.iter() {
            lit.get_lhs().collect_vars_into(&mut set);
            lit.get_rhs().collect_vars_into(&mut set);
        }

        let mut subst = Substitution::new();
        for old_var in set.iter() {
            subst.insert(*old_var, term_bank.mk_replacement_variable(*old_var));
        }

        self.clone().subst_with(&subst, term_bank)
    }

    pub fn to_vec(self) -> Vec<Literal> {
        self.literals
    }

    pub fn is_rewrite_rule(&self) -> Option<&Literal> {
        if self.is_unit() {
            let lit = self.first_lit();
            if lit.is_eq() {
                return Some(lit);
            }
        }
        None
    }

    pub fn assert_well_typed(&self, term_bank: &TermBank) {
        for lit in self.literals.iter() {
            if term_bank.infer_sort(lit.get_lhs()) != term_bank.infer_sort(lit.get_rhs()) {
                panic!(
                    "In clause: {}, literal: {} has non matching sort",
                    pretty_print(self, term_bank),
                    pretty_print(lit, term_bank)
                );
            }

            lit.get_lhs().subterm_iter().filter(|(_, pos)| !pos.is_root()).for_each(|(term, _)| {
                if term_bank.infer_sort(&term) != Sort::Individual {
                    panic!(
                        "In clause: {}, literal: {}, the lhs subterm: {} is not of sort individual",
                        pretty_print(self, term_bank),
                        pretty_print(lit, term_bank),
                        pretty_print(&term, term_bank)
                    );
                }
            });

            lit.get_rhs().subterm_iter().filter(|(_, pos)| !pos.is_root()).for_each(|(term, _)| {
                if term_bank.infer_sort(&term) != Sort::Individual {
                    panic!(
                        "In clause: {}, literal: {}, the rhs subterm: {} is not of sort individual",
                        pretty_print(self, term_bank),
                        pretty_print(lit, term_bank),
                        pretty_print(&term, term_bank)
                    );
                }
            })
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
        Some(self.cmp(other))
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
            info: self.info,
            literals: new_lits,
        }
    }
}

impl BankPrettyPrint for Clause {
    fn print_into(&self, term_bank: &TermBank, acc: &mut String) {
        if self.is_empty() {
            acc.push('⊥');
        } else {
            for lit_idx in 0..(self.len() - 1) {
                let lit = self.get_literal(LiteralId(lit_idx));
                acc.push('(');
                lit.print_into(term_bank, acc);
                acc.push_str(") ∨ ");
            }
            let lit = self.get_literal(LiteralId(self.len() - 1));
            acc.push('(');
            lit.print_into(term_bank, acc);
            acc.push(')');
        }
    }
}

/// A set of clauses indexed by unique clause identifiers.
pub struct ClauseSet {
    map: FxHashMap<ClauseId, Clause>,
}

impl ClauseSet {
    /// Create an empty clause set.
    pub fn new() -> Self {
        Self {
            map: FxHashMap::default(),
        }
    }

    /// Insert a new clause into the set.
    pub fn insert(&mut self, clause: Clause) {
        self.map.insert(clause.id, clause);
    }

    /// Remove a clause from the set.
    pub fn remove(&mut self, clause: &Clause) {
        self.map.remove(&clause.id);
    }

    /// Length of the clause set
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Get clause by its unique identifier.
    pub fn get_by_id(&self, id: ClauseId) -> Option<&Clause> {
        self.map.get(&id)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Clause> {
        self.map.values()
    }
}

#[cfg(test)]
mod test {
    use crate::{
        clause::Clause,
        subst::{Substitutable, Substitution},
        term_bank::{FunctionInformation, Sort, TermBank, VariableInformation},
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
            sort: Sort::Individual,
        });
        let c2_id = term_bank.add_function(FunctionInformation {
            name: "c2".to_string(),
            arity: 0,
            sort: Sort::Individual,
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
