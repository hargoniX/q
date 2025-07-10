//! ## Clause Queue
//! This module contains the implementation of the clause queue used as the passive set in the
//! given clause procedure. The key exported data structure is [ClauseQueue].

use std::collections::BinaryHeap;

use crate::clause::Clause;

// The public clause ordering instance works with the clause identifier but we want to order it
// after its weight so we use a zero cost wrapper.
struct WeightedClause(Clause);

impl PartialEq for WeightedClause {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

// We use reverse ordering as we want minimal clauses to be selected first.
impl PartialOrd for WeightedClause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for WeightedClause {}

impl Ord for WeightedClause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.weight().cmp(&other.0.weight()).reverse()
    }
}

/// A priority queue for clauses sorted according to some heuristics for given clause selection.
pub struct ClauseQueue {
    queue: BinaryHeap<WeightedClause>,
}

impl ClauseQueue {
    /// Create an empty clause queue.
    pub fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }

    /// Push a clause into the clause queue.
    pub fn push(&mut self, clause: Clause) {
        self.queue.push(WeightedClause(clause));
    }

    /// Obtain the currently best clause from the queue.
    pub fn pop(&mut self) -> Option<Clause> {
        self.queue.pop().map(|c| c.0)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        clause::{Clause, Literal},
        term_bank::{FunctionInformation, TermBank, VariableInformation},
    };

    use super::ClauseQueue;

    #[test]
    fn basic_clause_queue_test() {
        let mut term_bank = TermBank::new();
        let x_id = term_bank.add_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y_id = term_bank.add_variable(VariableInformation {
            name: "y".to_string(),
        });
        let f_id = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
        });

        let x = term_bank.mk_variable(x_id);
        let y = term_bank.mk_variable(y_id);
        let f_x = term_bank.mk_app(f_id, vec![x.clone()]);

        let clause1 = Clause::new(vec![Literal::mk_eq(x.clone(), y.clone())]);
        let clause2 = Clause::new(vec![Literal::mk_eq(f_x.clone(), y.clone())]);
        let clause3 = Clause::new(vec![Literal::mk_eq(f_x.clone(), f_x.clone())]);

        let mut queue = ClauseQueue::new();
        queue.push(clause1.clone());
        queue.push(clause3.clone());
        queue.push(clause3.clone());
        queue.push(clause2.clone());

        assert_eq!(queue.pop(), Some(clause1));
        assert_eq!(queue.pop(), Some(clause2));
        assert_eq!(queue.pop(), Some(clause3.clone()));
        assert_eq!(queue.pop(), Some(clause3));
        assert_eq!(queue.pop(), None);
    }
}
