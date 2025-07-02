//! ## Feature Vector Index
//! This module contains the implementation of a feature vector index as shown in
//! [Simple and Efficient Clause Subsumption with Feature Vector Indexing](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz2013-FVI.pdf)
//! The key exported data structure is [FeatureVectorIndex].

use std::{slice, vec};

use crate::{
    clause::{Clause, ClauseId, Polarity},
    persistent_vec_iter::PersistentVecIterator,
    trie::Trie,
};

struct FeatureVector {
    vec: Vec<usize>,
}

impl FeatureVector {
    fn new(clause: &Clause) -> Self {
        // |C^+|
        let mut cplus = 0;
        // |C^-|
        let mut cminus = 0;
        // sum of |C^+|_f for all f
        let mut cplusf = 0;
        // sum of |C^-|_f for all f
        let mut cminusf = 0;

        for (_, lit) in clause.iter() {
            match lit.get_pol() {
                Polarity::Eq => {
                    cplus += 1;
                    cplusf += lit.function_symbol_count() as usize;
                },
                Polarity::Ne => {
                    cminus += 1;
                    cminusf += lit.function_symbol_count() as usize;
                },
            }
        }


        // TODO: more clause features from the paper
        Self {
            vec: vec![cplus, cminus, cplusf, cminusf],
        }
    }

    fn into_iter(self) -> vec::IntoIter<usize> {
        self.vec.into_iter()
    }

    fn into_persistent_iter(self) -> PersistentVecIterator<usize> {
        PersistentVecIterator::new(self.vec)
    }
}

pub struct SubsumerIterator<'a> {
    frontier: Vec<(PersistentVecIterator<usize>, &'a Trie<usize, ClauseId>)>,
    found_node_iter: Option<slice::Iter<'a, ClauseId>>,
}

impl<'a> SubsumerIterator<'a> {
    fn new(index: &'a FeatureVectorIndex, clause: &Clause) -> Self {
        let iter = FeatureVector::new(clause).into_persistent_iter();
        Self {
            frontier: vec![(iter, &index.trie)],
            found_node_iter: None,
        }
    }
}

impl<'a> Iterator for SubsumerIterator<'a> {
    type Item = ClauseId;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.found_node_iter {
            &mut Some(ref mut found_node_iter) => {
                if let Some(next) = found_node_iter.next() {
                    return Some(*next);
                } else {
                    self.found_node_iter = None;
                }
            }
            None => {}
        }

        while let Some((mut query_pos, trie_pos)) = self.frontier.pop() {
            match query_pos.next() {
                Some(query_feature) => {
                    trie_pos
                        .iter_children()
                        .filter(|(index_feature, _)| **index_feature <= query_feature)
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
    pub fn insert(&mut self, clause: &Clause) {
        let vec = FeatureVector::new(clause);
        self.trie.insert(vec.into_iter(), clause.get_id());
    }

    /// Obtain an iterator over clauses from the index that might subsume `clause`.
    pub fn get_subsumer_candidates<'a>(&'a self, clause: &Clause) -> SubsumerIterator<'a> {
        SubsumerIterator::new(self, clause)
    }
}
