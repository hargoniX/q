//! ## Clause Queue
//! This module contains the implementation of the clause queue used as the passive set in the
//! given clause procedure. The key exported data structure is [ClauseQueue]. It is based on the
//! paper [Performance of Clause Selection Heuristics for Saturation-Based Theorem Proving](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/sm_ijcar-2016.pdf)
//! and implements the `10SC11/FIFO-PI` heuristic as it scores the second best after the "evolved"
//! one.

use std::collections::{BinaryHeap, VecDeque};

use rustc_hash::FxHashSet;

use crate::{
    clause::{Clause, ClauseId, Literal},
    term_bank::Term,
};

// factors based on heuristic SC11
const VAR_FACTOR: u32 = 1;
const FUN_FACTOR: u32 = 1;

impl Term {
    /// Compute the symbolic weight of a term for the clause queue.
    pub fn weight(&self) -> u32 {
        self.function_symbol_count() * FUN_FACTOR + self.variable_count() * VAR_FACTOR
    }
}

impl Literal {
    /// Compute the symbolic weight of a literal for the clause queue.
    pub fn weight(&self) -> u32 {
        self.get_lhs().weight() + self.get_rhs().weight()
    }
}

impl Clause {
    /// Compute the symbolic weight of a clause for the clause queue.
    pub fn weight(&self) -> u32 {
        self.literals.iter().map(Literal::weight).sum()
    }
}

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
        self.0
            .is_initial()
            .cmp(&other.0.is_initial())
            .then_with(|| self.0.weight().cmp(&other.0.weight()).reverse())
    }
}

/// A priority queue for clauses sorted according to some heuristics for given clause selection.
pub struct ClauseQueue {
    /// Priority queue sorted by clause weight + precendence for initial clauses
    weighted_queue: BinaryHeap<WeightedClause>,
    /// FIFO queue
    fifo_queue: VecDeque<Clause>,
    /// Which clauses we already dequeued previously from at least one of the two queues so we can
    /// quickly notice if we are dequeueing a clause that the active set already knows about.
    used_set: FxHashSet<ClauseId>,
    /// Which step we are in for the ratio between `weighted_queue` and `fifo_queue`.
    step: usize,
}

const WEIGHTED_RATIO: usize = 10;

impl ClauseQueue {
    /// Create an empty clause queue.
    pub fn new() -> Self {
        Self {
            weighted_queue: BinaryHeap::new(),
            fifo_queue: VecDeque::new(),
            used_set: FxHashSet::default(),
            step: 0,
        }
    }

    /// Push a clause into the clause queue.
    pub fn push(&mut self, clause: Clause) {
        self.weighted_queue.push(WeightedClause(clause.clone()));
        self.fifo_queue.push_back(clause);
    }

    fn get_next_clause(&mut self) -> Option<Clause> {
        // Crucially as we insert each close into both clauses if one queue goes empty we know for
        // sure the other is also either empty or cannot possibly contain clauses that we didn't
        // work off yet.
        if self.step < WEIGHTED_RATIO {
            while let Some(WeightedClause(clause)) = self.weighted_queue.pop() {
                if !self.used_set.contains(&clause.get_id()) {
                    self.used_set.insert(clause.get_id());
                    return Some(clause);
                }
            }
            None
        } else {
            while let Some(clause) = self.fifo_queue.pop_front() {
                if !self.used_set.contains(&clause.get_id()) {
                    self.used_set.insert(clause.get_id());
                    return Some(clause);
                }
            }
            None
        }
    }

    /// Obtain the next clause to work from the clause queue.
    pub fn pop(&mut self) -> Option<Clause> {
        let next = self.get_next_clause();
        self.step = (self.step + 1) % (WEIGHTED_RATIO + 1);
        next
    }

    /// Length of the clause queue
    pub fn len(&self) -> usize {
        self.weighted_queue.len()
    }
}
