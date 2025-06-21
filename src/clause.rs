use std::{
    collections::{BTreeMap, HashSet}, hash::Hash, slice, sync::atomic::{AtomicUsize, Ordering}
};

use crate::{
    multi_set::MultiSet,
    subst::{Substitutable, Substitution},
    term_bank::{self, Term, TermBank, VariableInformation},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Polarity {
    Eq,
    Ne,
}

impl Polarity {
    fn negate(&self) -> Polarity {
        match self {
            Polarity::Eq => Polarity::Ne,
            Polarity::Ne => Polarity::Eq,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    lhs: Term,
    rhs: Term,
    kind: Polarity,
}

impl Literal {
    pub fn new(lhs: Term, rhs: Term, kind: Polarity) -> Self {
        Self { lhs, rhs, kind }
    }

    pub fn mk_eq(lhs: Term, rhs: Term) -> Self {
        Self {
            lhs,
            rhs,
            kind: Polarity::Eq,
        }
    }

    pub fn mk_ne(lhs: Term, rhs: Term) -> Self {
        Self {
            lhs,
            rhs,
            kind: Polarity::Ne,
        }
    }

    pub fn get_lhs(&self) -> &Term {
        &self.lhs
    }

    pub fn get_rhs(&self) -> &Term {
        &self.rhs
    }

    pub fn get_kind(&self) -> Polarity {
        self.kind
    }

    pub fn is_negative(&self) -> bool {
        self.kind == Polarity::Ne
    }

    pub fn is_positive(&self) -> bool {
        self.kind == Polarity::Eq
    }

    pub fn negate(self) -> Self {
        Self {
            lhs: self.lhs,
            rhs: self.rhs,
            kind: self.kind.negate(),
        }
    }

    pub fn weight(&self) -> u32 {
        self.lhs.weight() + self.rhs.weight()
    }
}

impl Substitutable for Literal {
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

static CLAUSE_ID_COUNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId(usize);

fn next_clause_id() -> ClauseId {
    ClauseId(CLAUSE_ID_COUNT.fetch_add(1, Ordering::SeqCst))
}

#[derive(Debug, Clone)]
pub struct Clause {
    id: ClauseId,
    literals: MultiSet<Literal>,
}

impl Clause {
    pub fn new(vec: Vec<Literal>) -> Self {
        Self {
            id: next_clause_id(),
            literals: MultiSet::of_vec(vec),
        }
    }

    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    pub fn is_unit(&self) -> bool {
        self.len() == 1
    }

    pub fn weight(&self) -> u32 {
        self.literals.iter().map(Literal::weight).sum()
    }

    pub fn get_literal(&self, literal_idx: usize) -> &Literal {
        self.literals.get(literal_idx)
    }

    pub fn get_literals(&self) -> &MultiSet<Literal> {
        &self.literals
    }

    pub fn get_id(&self) -> ClauseId {
        self.id
    }

    pub fn iter(&self) -> slice::Iter<'_, Literal> {
        self.literals.iter()
    }

    pub fn fresh_variable_clone(&self, term_bank: &mut TermBank) -> Clause {
        let mut set = HashSet::new();
        for lit in self.iter() {
            lit.get_lhs().collect_vars_into(&mut set);
            lit.get_rhs().collect_vars_into(&mut set);
        }

        let mut subst = Substitution::new();
        for old_var in set.iter() {
            subst.insert(*old_var, term_bank.mk_fresh_variable(VariableInformation {
                name: "replacement_variable".to_string(),
            }));
        }

        self.clone().subst_with(&subst, term_bank)
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id)
    }
}

impl Eq for Clause {}

impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.id.partial_cmp(&other.id)
    }
}

impl Ord for Clause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl Hash for Clause {
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

pub struct ClauseSet {
    map: BTreeMap<ClauseId, Clause>,
}

impl ClauseSet {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, clause: Clause) {
        self.map.insert(clause.id, clause);
    }

    pub fn get_by_id(&self, id: ClauseId) -> Option<&Clause> {
        self.map.get(&id)
    }

    pub fn contains_id(&self, id: ClauseId) -> bool {
        self.map.contains_key(&id)
    }

    pub fn contains_clause(&self, clause: &Clause) -> bool {
        self.map.contains_key(&clause.get_id())
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
        assert!(l1.is_positive());
        assert!(!l1.is_negative());
        assert!(l2.is_negative());
        assert!(!l2.is_positive());
        assert_ne!(l1, l2);

        l2 = l2.negate();
        assert_eq!(l1, l2);
        assert!(l2.is_positive());

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
