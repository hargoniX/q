use std::{cmp::Ordering, collections::BinaryHeap};

use crate::clause::Clause;

// We do not implement an Ord instance on clause publicly because it does not fulfill the full
// invariants demanded by the Ord specification. However it is sufficient for BinaryHeap
struct WeightedClause(Clause);

impl PartialEq for WeightedClause {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

// reverse ordering as we want minimal clauses to be selected first
impl PartialOrd for WeightedClause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0
            .weight()
            .partial_cmp(&other.0.weight())
            .map(Ordering::reverse)
    }
}

impl Eq for WeightedClause {}

impl Ord for WeightedClause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.weight().cmp(&other.0.weight()).reverse()
    }
}

pub struct ClauseQueue {
    queue: BinaryHeap<WeightedClause>,
}

impl ClauseQueue {
    pub fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }

    pub fn push(&mut self, clause: Clause) {
        self.queue.push(WeightedClause(clause));
    }

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
