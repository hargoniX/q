//! ## Feature Vector Index
//! This module contains the implementation of a feature vector index as shown in
//! [Simple and Efficient Clause Subsumption with Feature Vector Indexing](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz2013-FVI.pdf)
//! The key exported data structure is [FeatureVectorIndex].

use std::{array, slice, vec};

use crate::{
    clause::{Clause, ClauseId, Polarity},
    persistent_vec_iter::PersistentVecIterator,
    term_bank::{RawTerm, Term, TermBank},
    trie::Trie,
};

// Taken from EProver `FVINDEX_MAX_FEATURES_DEFAULT`.
const FEATURE_VECTOR_SIZE: usize = 16;

/// This implements a feature vector in the DRT-AC config.
struct FeatureVector {
    vec: [usize; FEATURE_VECTOR_SIZE],
}

impl FeatureVector {
    fn count_function_symbols(
        term: &Term,
        accumulator: &mut [usize],
        limit: usize,
        term_bank: &TermBank,
    ) {
        if let RawTerm::App { id, args, .. } = term.as_ref() {
            let idx = term_bank.get_function_index(*id) as usize;
            if idx < limit {
                accumulator[idx + 1] += 1;
            } else {
                accumulator[0] += 1;
            }

            args.iter()
                .for_each(|arg| Self::count_function_symbols(arg, accumulator, limit, term_bank));
        }
    }

    fn new(clause: &Clause, term_bank: &TermBank) -> Self {
        // According to EProver `TermAddSymbolFeaturesLimited` we literally just count the first
        // couple of symbols in a dedicated fashion and accumulate the rest at a catch all index.

        // We reserve:
        // - [0] for |C^+|
        // - [1] for |C^-|
        // - [2] for the catch all |C^+|_f
        // - [3-8] for the first 6 function symbols occuring positively
        // - [9] for the catch all |C^-|_f
        // - [10-15] for the the first 6 function symbols occuring negatively
        let mut vec = [0; FEATURE_VECTOR_SIZE];
        const CPLUS: usize = 0;
        const CMINUS: usize = 1;
        const CPLUS_FUNC_START: usize = CMINUS + 1;
        const CPLUS_FUNC_END: usize = CPLUS_FUNC_START + (FEATURE_VECTOR_SIZE - 2) / 2 - 1;
        const CPLUS_FUNC_SIZE: usize = CPLUS_FUNC_END - CPLUS_FUNC_START;
        const CMINUS_FUNC_START: usize = CPLUS_FUNC_END + 1;
        const CMINUS_FUNC_END: usize = CMINUS_FUNC_START + (FEATURE_VECTOR_SIZE - 2) / 2 - 1;
        const CMINUS_FUNC_SIZE: usize = CMINUS_FUNC_END - CMINUS_FUNC_START;

        for (_, lit) in clause.iter() {
            match lit.get_pol() {
                Polarity::Eq => {
                    vec[CPLUS] += 1;
                    Self::count_function_symbols(
                        lit.get_lhs(),
                        &mut vec[CPLUS_FUNC_START..=CPLUS_FUNC_END],
                        CPLUS_FUNC_SIZE,
                        term_bank,
                    );
                    Self::count_function_symbols(
                        lit.get_rhs(),
                        &mut vec[CPLUS_FUNC_START..=CPLUS_FUNC_END],
                        CPLUS_FUNC_SIZE,
                        term_bank,
                    );
                }
                Polarity::Ne => {
                    vec[CMINUS] += 1;
                    Self::count_function_symbols(
                        lit.get_lhs(),
                        &mut vec[CMINUS_FUNC_START..=CMINUS_FUNC_END],
                        CMINUS_FUNC_SIZE,
                        term_bank,
                    );
                    Self::count_function_symbols(
                        lit.get_rhs(),
                        &mut vec[CMINUS_FUNC_START..=CMINUS_FUNC_END],
                        CMINUS_FUNC_SIZE,
                        term_bank,
                    );
                }
            }
        }

        Self { vec }
    }

    fn into_iter(self) -> array::IntoIter<usize, FEATURE_VECTOR_SIZE> {
        self.vec.into_iter()
    }

    fn into_persistent_iter(self) -> PersistentVecIterator<usize> {
        PersistentVecIterator::new(self.vec.to_vec())
    }
}

pub struct FeatureVectorIndexIter<'a, F: Fn(usize, usize) -> bool> {
    frontier: Vec<(PersistentVecIterator<usize>, &'a Trie<usize, ClauseId>)>,
    found_node_iter: Option<slice::Iter<'a, ClauseId>>,
    comparator: F,
}

impl<'a, F: Fn(usize, usize) -> bool> FeatureVectorIndexIter<'a, F> {
    fn new(
        index: &'a FeatureVectorIndex,
        clause: &Clause,
        term_bank: &TermBank,
        comparator: F,
    ) -> Self {
        let iter = FeatureVector::new(clause, term_bank).into_persistent_iter();
        Self {
            frontier: vec![(iter, &index.trie)],
            found_node_iter: None,
            comparator,
        }
    }
}

impl<F: Fn(usize, usize) -> bool> Iterator for FeatureVectorIndexIter<'_, F> {
    type Item = ClauseId;

    fn next(&mut self) -> Option<Self::Item> {
        if let &mut Some(ref mut found_node_iter) = &mut self.found_node_iter {
            if let Some(next) = found_node_iter.next() {
                return Some(*next);
            } else {
                self.found_node_iter = None;
            }
        }

        while let Some((mut query_pos, trie_pos)) = self.frontier.pop() {
            match query_pos.next() {
                Some(query_feature) => {
                    trie_pos
                        .iter_children()
                        .filter(|(index_feature, _)| {
                            (self.comparator)(**index_feature, query_feature)
                        })
                        .for_each(|(_, child_pos)| {
                            self.frontier.push((query_pos.clone(), child_pos))
                        });
                }
                None => {
                    assert!(self.found_node_iter.is_none());
                    let mut next_iter = trie_pos.iter_values();
                    // We know this will be some, the remainder of this node will be drained on
                    // future calls to our next.
                    let next_elem = next_iter.next();
                    self.found_node_iter = Some(next_iter);
                    return next_elem.copied();
                }
            }
        }

        None
    }
}

pub struct FeatureVectorIndex {
    trie: Trie<usize, ClauseId>,
}

impl FeatureVectorIndex {
    /// Create a fresh empty feature vector index.
    pub fn new() -> Self {
        Self { trie: Trie::new() }
    }

    /// Insert a clause into the feature vector index.
    pub fn insert(&mut self, clause: &Clause, term_bank: &TermBank) {
        let vec = FeatureVector::new(clause, term_bank);
        self.trie.insert(vec.into_iter(), clause.get_id());
    }

    /// Remove a clause from the feature vector index.
    pub fn remove(&mut self, clause: &Clause, term_bank: &TermBank) {
        let vec = FeatureVector::new(clause, term_bank);
        self.trie.remove(vec.into_iter(), clause.get_id());
    }

    /// Obtain an iterator over clauses from the index that might subsume `clause`.
    pub fn forward_candidates<'a>(
        &'a self,
        clause: &Clause,
        term_bank: &TermBank,
    ) -> FeatureVectorIndexIter<'a, impl Fn(usize, usize) -> bool> {
        FeatureVectorIndexIter::new(self, clause, term_bank, |lhs, rhs| lhs <= rhs)
    }

    /// Obtain an iterator over clauses from the index that might be subsumed by `clause`.
    pub fn backward_candidates<'a>(
        &'a self,
        clause: &Clause,
        term_bank: &TermBank,
    ) -> FeatureVectorIndexIter<'a, impl Fn(usize, usize) -> bool> {
        FeatureVectorIndexIter::new(self, clause, term_bank, |lhs, rhs| lhs >= rhs)
    }
}
