//! ## Discrimination Tree
//! This module contains an implementation of an imperfect first order discrimination tree as shown
//! in [LMU's ATP course](https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/atp/slides14-efficient-saturation-procedures-outlook.pdf).
//! The key exported data structure is [DiscriminationTree].

use core::slice;
use std::{
    collections::{HashMap, HashSet, hash_map::Entry},
    hash::Hash,
    iter::Peekable,
    rc::Rc,
};

use crate::term_bank::{FunctionIdentifier, RawTerm, Term};

/// Implementation of a [trie](https://en.wikipedia.org/wiki/Trie) with `C` being the characters
/// from its alphabet and `V` the values in the nodes.
#[derive(Debug)]
struct Trie<C, V> {
    values: Vec<V>,
    children: HashMap<C, Box<Trie<C, V>>>,
}

/// The alphabet of a discrimination tree trie.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum DiscrTreeKey {
    /// Stars for representing variables.
    Star,
    /// Function applications containing their identifier and the arity of the function, `0` if its
    /// a constant.
    App {
        id: FunctionIdentifier,
        arity: usize,
    },
}

#[derive(Debug, Clone)]
struct PersistentPreorderTermIterator {
    flatterm: Rc<Vec<DiscrTreeKey>>,
    pos: usize,
}

/// A non perfect discrimination tree with `V` as the values associated with the indexed terms.
#[derive(Debug)]
pub struct DiscriminationTree<V> {
    trie: Trie<DiscrTreeKey, V>,
}

impl<C: Eq + Hash, V> Trie<C, V> {
    /// Create a new empty try.
    fn new() -> Self {
        Self {
            values: Vec::new(),
            children: HashMap::new(),
        }
    }

    /// Insert `value` at the position described by the string produce by `iter`.
    fn insert(&mut self, mut iter: impl Iterator<Item = C>, value: V) {
        match iter.next() {
            Some(char) => match self.children.entry(char) {
                Entry::Occupied(mut occupied_entry) => {
                    occupied_entry.get_mut().insert(iter, value);
                }
                Entry::Vacant(vacant_entry) => {
                    let subtrie = Self::new();
                    let mut filled = vacant_entry.insert_entry(Box::new(subtrie));
                    filled.get_mut().insert(iter, value);
                }
            },
            None => self.values.push(value),
        }
    }
}

impl PersistentPreorderTermIterator {
    fn new(term: &Term) -> Self {
        let mut flatterm = Vec::new();
        let mut stack = vec![term];
        while let Some(curr) = stack.pop() {
            match &**curr {
                RawTerm::Var { .. } => flatterm.push(DiscrTreeKey::Star),
                RawTerm::App { id, args, .. } => {
                    args.iter().rev().for_each(|arg| stack.push(arg));
                    flatterm.push(DiscrTreeKey::App {
                        id: *id,
                        arity: args.len(),
                    });
                }
            }
        }
        Self {
            flatterm: Rc::new(flatterm),
            pos: 0,
        }
    }
}

impl Iterator for PersistentPreorderTermIterator {
    type Item = DiscrTreeKey;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.flatterm.len() {
            let ret = self.flatterm[self.pos];
            self.pos += 1;
            Some(ret)
        } else {
            None
        }
    }
}

/// Skip to the end of the current subterm in an iterator of the discrimination tree alphabet.
/// Precondition: The iterator has at least one element remaining
fn skip_to_next_subterm<T: Iterator<Item = DiscrTreeKey>>(iter: &mut T) {
    let mut to_skip = 0;
    match iter.next().unwrap() {
        DiscrTreeKey::Star => return,
        DiscrTreeKey::App { arity, .. } => {
            to_skip += arity;
        }
    }

    while to_skip != 0 {
        match iter.next().unwrap() {
            DiscrTreeKey::Star => to_skip -= 1,
            DiscrTreeKey::App { arity, .. } => {
                to_skip = (to_skip + arity) - 1;
            }
        }
    }
}

impl<V> Trie<DiscrTreeKey, V> {
    /// Skip to the end of the current subterm in a discrimination tree.
    fn skip_to_next_subterm(&self) -> Vec<&Self> {
        let mut final_positions: Vec<&Self> = Vec::new();
        let mut frontier = vec![(self, 1usize)];
        while let Some((pos, to_skip)) = frontier.pop() {
            for (child_key, child_pos) in pos.children.iter() {
                let to_skip = match child_key {
                    DiscrTreeKey::Star => to_skip - 1,
                    DiscrTreeKey::App { arity, .. } => (to_skip + *arity) - 1,
                };
                if to_skip == 0 {
                    final_positions.push(&child_pos);
                } else {
                    frontier.push((child_pos, to_skip));
                }
            }
        }
        final_positions
    }
}

pub struct UnificationCandidateIter<'a, V> {
    frontier: Vec<(
        Peekable<PersistentPreorderTermIterator>,
        &'a Trie<DiscrTreeKey, V>,
    )>,
    found_node_iter: Option<slice::Iter<'a, V>>,
}

impl<'a, V> Iterator for UnificationCandidateIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        // If at the node we are currently stopped at something is still left, use it.
        match &mut self.found_node_iter {
            &mut Some(ref mut found_node_iter) => {
                if let Some(next) = found_node_iter.next() {
                    return Some(next);
                } else {
                    self.found_node_iter = None;
                }
            }
            None => {}
        }

        // Start looking for a new node.
        while let Some((mut query_pos, trie_pos)) = self.frontier.pop() {
            match query_pos.peek() {
                Some(DiscrTreeKey::Star) => {
                    let subtries = trie_pos.skip_to_next_subterm();
                    query_pos.next();
                    subtries
                        .iter()
                        .for_each(|subtrie| self.frontier.push((query_pos.clone(), subtrie)));
                }
                Some(key @ DiscrTreeKey::App { .. }) => {
                    if let Some(subtrie) = trie_pos.children.get(&key) {
                        let mut next_query_pos = query_pos.clone();
                        next_query_pos.next();
                        self.frontier.push((next_query_pos, subtrie));
                    }

                    if let Some(subtrie) = trie_pos.children.get(&DiscrTreeKey::Star) {
                        skip_to_next_subterm(&mut query_pos);
                        self.frontier.push((query_pos, subtrie));
                    }
                }
                None => {
                    if !trie_pos.values.is_empty() {
                        assert!(self.found_node_iter.is_none());
                        let mut next_iter = trie_pos.values.iter();
                        // We know this will be some, the remainder of this node will be drained on
                        // future calls to our next.
                        let next_elem = next_iter.next();
                        self.found_node_iter = Some(next_iter);
                        return next_elem;
                    }
                }
            }
        }

        // We were unable to find a new node, finished
        None
    }
}

impl<V: Hash + Eq> DiscriminationTree<V> {
    /// Create an empty discrimination tree.
    pub fn new() -> Self {
        Self { trie: Trie::new() }
    }

    /// Insert a new term with some associated value into the discrimination tree.
    pub fn insert(&mut self, term: &Term, value: V) {
        let iter = PersistentPreorderTermIterator::new(term);
        self.trie.insert(iter, value);
    }

    /// Obtain the values associated with all potential generalisations of `term` indexed in `self`,
    /// that is find all values for whose keys there might exist a substitution `subst` s.t.
    /// `subst(term) = key`.
    pub fn get_generalisation_candidates(&self, term: &Term) -> HashSet<&V> {
        let iter = PersistentPreorderTermIterator::new(term).peekable();
        let mut frontier = vec![(iter, &self.trie)];
        let mut set = HashSet::new();
        while let Some((mut query_pos, trie_pos)) = frontier.pop() {
            match query_pos.peek() {
                Some(DiscrTreeKey::Star) => {
                    if let Some(subtrie) = trie_pos.children.get(&DiscrTreeKey::Star) {
                        query_pos.next();
                        frontier.push((query_pos, subtrie))
                    }
                }
                Some(key @ DiscrTreeKey::App { .. }) => {
                    if let Some(subtrie) = trie_pos.children.get(&key) {
                        let mut next_query_pos = query_pos.clone();
                        next_query_pos.next();
                        frontier.push((next_query_pos, subtrie));
                    }

                    if let Some(subtrie) = trie_pos.children.get(&DiscrTreeKey::Star) {
                        skip_to_next_subterm(&mut query_pos);
                        frontier.push((query_pos, subtrie));
                    }
                }
                None => trie_pos.values.iter().for_each(|val| {
                    set.insert(val);
                }),
            }
        }
        set
    }

    /// Obtain the values associated with all potential instances of `term` indexed in `self`,
    /// that is find all values for whose keys there might exist a substitution `subst` s.t.
    /// `term = subst(key)`.
    pub fn get_instance_candidates(&self, term: &Term) -> HashSet<&V> {
        let iter = PersistentPreorderTermIterator::new(term).peekable();
        let mut frontier = vec![(iter, &self.trie)];
        let mut set = HashSet::new();
        while let Some((mut query_pos, trie_pos)) = frontier.pop() {
            match query_pos.peek() {
                Some(DiscrTreeKey::Star) => {
                    let subtries = trie_pos.skip_to_next_subterm();
                    query_pos.next();
                    subtries
                        .iter()
                        .for_each(|subtrie| frontier.push((query_pos.clone(), subtrie)));
                }
                Some(key @ DiscrTreeKey::App { .. }) => {
                    if let Some(subtrie) = trie_pos.children.get(&key) {
                        query_pos.next();
                        frontier.push((query_pos, subtrie));
                    }
                }
                None => trie_pos.values.iter().for_each(|val| {
                    set.insert(val);
                }),
            }
        }
        set
    }

    /// Obtain the values associated with all potential unifications of `term` indexed in `self`,
    /// that is find all values for whose keys there might exist a substitution `subst` s.t.
    /// `subst(term) = subst(key)`.
    pub fn get_unification_candidates(&self, term: &Term) -> UnificationCandidateIter<'_, V> {
        let iter = PersistentPreorderTermIterator::new(term).peekable();
        UnificationCandidateIter {
            frontier: vec![(iter, &self.trie)],
            found_node_iter: None,
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::{HashMap, HashSet};

    use crate::term_bank::{FunctionInformation, Term, TermBank, VariableInformation};

    use super::{DiscrTreeKey, DiscriminationTree, PersistentPreorderTermIterator};

    fn flatterm(t: &Term) -> Vec<DiscrTreeKey> {
        PersistentPreorderTermIterator::new(t).collect()
    }

    #[test]
    fn basic_preorder_iterator_test() {
        let mut term_bank = TermBank::new();
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
        });
        let g = term_bank.add_function(FunctionInformation {
            name: "g".to_string(),
            arity: 2,
        });
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
        });
        let h = term_bank.add_function(FunctionInformation {
            name: "h".to_string(),
            arity: 1,
        });

        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y = term_bank.mk_fresh_variable(VariableInformation {
            name: "y".to_string(),
        });

        let t1 = term_bank.mk_app(
            g,
            vec![
                term_bank.mk_app(h, vec![x.clone()]),
                term_bank.mk_app(h, vec![term_bank.mk_const(c)]),
            ],
        );
        let t2 = term_bank.mk_app(g, vec![x.clone(), x.clone()]);
        let t3 = term_bank.mk_app(
            g,
            vec![term_bank.mk_const(b), term_bank.mk_app(f, vec![x.clone()])],
        );
        let t4 = term_bank.mk_app(f, vec![term_bank.mk_app(g, vec![x.clone(), y.clone()])]);
        let t5 = term_bank.mk_app(
            h,
            vec![term_bank.mk_app(g, vec![x.clone(), term_bank.mk_const(c)])],
        );

        assert_eq!(
            flatterm(&t1),
            vec![
                DiscrTreeKey::App { id: g, arity: 2 },
                DiscrTreeKey::App { id: h, arity: 1 },
                DiscrTreeKey::Star,
                DiscrTreeKey::App { id: h, arity: 1 },
                DiscrTreeKey::App { id: c, arity: 0 }
            ]
        );
        assert_eq!(
            flatterm(&t2),
            vec![
                DiscrTreeKey::App { id: g, arity: 2 },
                DiscrTreeKey::Star,
                DiscrTreeKey::Star
            ]
        );
        assert_eq!(
            flatterm(&t3),
            vec![
                DiscrTreeKey::App { id: g, arity: 2 },
                DiscrTreeKey::App { id: b, arity: 0 },
                DiscrTreeKey::App { id: f, arity: 1 },
                DiscrTreeKey::Star
            ]
        );
        assert_eq!(
            flatterm(&t4),
            vec![
                DiscrTreeKey::App { id: f, arity: 1 },
                DiscrTreeKey::App { id: g, arity: 2 },
                DiscrTreeKey::Star,
                DiscrTreeKey::Star
            ]
        );
        assert_eq!(
            flatterm(&t5),
            vec![
                DiscrTreeKey::App { id: h, arity: 1 },
                DiscrTreeKey::App { id: g, arity: 2 },
                DiscrTreeKey::Star,
                DiscrTreeKey::App { id: c, arity: 0 }
            ]
        );
    }

    #[test]
    fn basic_generalisation_test() {
        let mut term_bank = TermBank::new();
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
        });
        let g = term_bank.add_function(FunctionInformation {
            name: "g".to_string(),
            arity: 2,
        });
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
        });
        let h = term_bank.add_function(FunctionInformation {
            name: "h".to_string(),
            arity: 2,
        });
        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y = term_bank.mk_fresh_variable(VariableInformation {
            name: "y".to_string(),
        });

        let q1 = term_bank.mk_app(f, vec![term_bank.mk_const(c)]);
        let q2 = term_bank.mk_app(f, vec![term_bank.mk_app(f, vec![term_bank.mk_const(c)])]);
        let q3 = term_bank.mk_app(
            g,
            vec![
                term_bank.mk_app(h, vec![x.clone(), y.clone()]),
                term_bank.mk_const(b),
            ],
        );
        let q4 = term_bank.mk_app(
            g,
            vec![term_bank.mk_app(h, vec![x.clone(), y.clone()]), x.clone()],
        );

        let t1 = term_bank.mk_app(f, vec![x.clone()]);
        let t2 = q1.clone();
        let t3 = term_bank.mk_app(g, vec![x.clone(), term_bank.mk_const(b)]);
        let t4 = term_bank.mk_app(g, vec![x.clone(), x.clone()]);
        let t5 = term_bank.mk_app(f, vec![term_bank.mk_app(f, vec![x.clone()])]);
        let mut discr_tree = DiscriminationTree::new();

        let mut map = HashMap::new();
        map.insert(&t1, 1);
        map.insert(&t2, 2);
        map.insert(&t3, 3);
        map.insert(&t4, 4);
        map.insert(&t5, 5);

        discr_tree.insert(&t1, 1);
        discr_tree.insert(&t2, 2);
        discr_tree.insert(&t3, 3);
        discr_tree.insert(&t4, 4);
        discr_tree.insert(&t5, 5);

        let tests = [
            (q1, vec![t1.clone(), t2.clone()]),
            (q2, vec![t1.clone(), t5.clone()]),
            (q3, vec![t3.clone(), t4.clone()]),
            (q4, vec![t4.clone()]),
        ];

        for (query_term, expected_query_results) in tests.iter() {
            let query_result = discr_tree.get_generalisation_candidates(query_term);
            assert_eq!(query_result.len(), expected_query_results.len());
            for expected in expected_query_results.iter() {
                assert!(query_result.contains(map.get(expected).unwrap()));
            }
        }
    }

    #[test]
    fn basic_instance_test() {
        let mut term_bank = TermBank::new();
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
        });
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
        });
        let h = term_bank.add_function(FunctionInformation {
            name: "h".to_string(),
            arity: 2,
        });
        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y = term_bank.mk_fresh_variable(VariableInformation {
            name: "y".to_string(),
        });

        let q1 = term_bank.mk_app(f, vec![x.clone()]);
        let q2 = term_bank.mk_app(f, vec![term_bank.mk_const(c)]);
        let q3 = term_bank.mk_app(f, vec![term_bank.mk_app(f, vec![x.clone()])]);
        let q4 = term_bank.mk_app(h, vec![x.clone(), y.clone()]);
        let q5 = term_bank.mk_app(h, vec![term_bank.mk_app(f, vec![x.clone()]), y.clone()]);

        let t1 = term_bank.mk_app(f, vec![x.clone()]);
        let t2 = term_bank.mk_app(f, vec![term_bank.mk_const(c)]);
        let t3 = term_bank.mk_app(f, vec![term_bank.mk_app(f, vec![term_bank.mk_const(c)])]);
        let t4 = term_bank.mk_app(h, vec![term_bank.mk_const(b), term_bank.mk_const(c)]);
        let t5 = term_bank.mk_app(
            h,
            vec![
                term_bank.mk_app(f, vec![term_bank.mk_const(b)]),
                term_bank.mk_const(c),
            ],
        );
        let t6 = term_bank.mk_app(
            h,
            vec![term_bank.mk_app(f, vec![term_bank.mk_const(b)]), x.clone()],
        );
        let mut discr_tree = DiscriminationTree::new();

        let mut map = HashMap::new();
        map.insert(&t1, 1);
        map.insert(&t2, 2);
        map.insert(&t3, 3);
        map.insert(&t4, 4);
        map.insert(&t5, 5);
        map.insert(&t6, 6);

        discr_tree.insert(&t1, 1);
        discr_tree.insert(&t2, 2);
        discr_tree.insert(&t3, 3);
        discr_tree.insert(&t4, 4);
        discr_tree.insert(&t5, 5);
        discr_tree.insert(&t6, 6);

        let tests = [
            (q1, vec![t1.clone(), t2.clone(), t3.clone()]),
            (q2, vec![t2.clone()]),
            (q3, vec![t3.clone()]),
            (q4, vec![t4.clone(), t5.clone(), t6.clone()]),
            (q5, vec![t5.clone(), t6.clone()]),
        ];

        for (query_term, expected_query_results) in tests.iter() {
            let query_result = discr_tree.get_instance_candidates(query_term);
            assert_eq!(query_result.len(), expected_query_results.len());
            for expected in expected_query_results.iter() {
                assert!(query_result.contains(map.get(expected).unwrap()));
            }
        }
    }

    #[test]
    fn basic_unification_test() {
        let mut term_bank = TermBank::new();
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
        });
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
        });
        let h = term_bank.add_function(FunctionInformation {
            name: "h".to_string(),
            arity: 2,
        });
        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y = term_bank.mk_fresh_variable(VariableInformation {
            name: "y".to_string(),
        });

        let q1 = term_bank.mk_app(f, vec![x.clone()]);
        let q2 = term_bank.mk_app(f, vec![term_bank.mk_const(c)]);
        let q3 = term_bank.mk_app(f, vec![term_bank.mk_app(f, vec![x.clone()])]);
        let q4 = term_bank.mk_app(h, vec![x.clone(), y.clone()]);
        let q5 = term_bank.mk_app(h, vec![term_bank.mk_app(f, vec![x.clone()]), y.clone()]);
        let q6 = term_bank.mk_app(
            f,
            vec![term_bank.mk_app(h, vec![term_bank.mk_app(f, vec![x.clone()]), y.clone()])],
        );

        let t1 = term_bank.mk_app(f, vec![x.clone()]);
        let t2 = term_bank.mk_app(f, vec![term_bank.mk_const(c)]);
        let t3 = term_bank.mk_app(f, vec![term_bank.mk_app(f, vec![term_bank.mk_const(c)])]);
        let t4 = term_bank.mk_app(h, vec![term_bank.mk_const(b), term_bank.mk_const(c)]);
        let t5 = term_bank.mk_app(
            h,
            vec![
                term_bank.mk_app(f, vec![term_bank.mk_const(b)]),
                term_bank.mk_const(c),
            ],
        );
        let t6 = term_bank.mk_app(
            h,
            vec![
                term_bank.mk_app(f, vec![term_bank.mk_app(f, vec![term_bank.mk_const(b)])]),
                x.clone(),
            ],
        );
        let t7 = term_bank.mk_app(f, vec![term_bank.mk_app(f, vec![x.clone()])]);
        let t8 = term_bank.mk_app(
            f,
            vec![term_bank.mk_app(h, vec![x.clone(), term_bank.mk_app(f, vec![y.clone()])])],
        );
        let t9 = term_bank.mk_app(h, vec![x.clone(), term_bank.mk_app(f, vec![y.clone()])]);
        let mut discr_tree = DiscriminationTree::new();

        let mut map = HashMap::new();
        map.insert(&t1, 1);
        map.insert(&t2, 2);
        map.insert(&t3, 3);
        map.insert(&t4, 4);
        map.insert(&t5, 5);
        map.insert(&t6, 6);
        map.insert(&t7, 7);
        map.insert(&t8, 8);
        map.insert(&t9, 9);

        discr_tree.insert(&t1, 1);
        discr_tree.insert(&t2, 2);
        discr_tree.insert(&t3, 3);
        discr_tree.insert(&t4, 4);
        discr_tree.insert(&t5, 5);
        discr_tree.insert(&t6, 6);
        discr_tree.insert(&t7, 7);
        discr_tree.insert(&t8, 8);
        discr_tree.insert(&t9, 9);

        let tests = [
            (
                q1,
                vec![t1.clone(), t2.clone(), t3.clone(), t7.clone(), t8.clone()],
            ),
            (q2, vec![t1.clone(), t2.clone()]),
            (q3, vec![t1.clone(), t3.clone(), t7.clone()]),
            (q4, vec![t4.clone(), t5.clone(), t6.clone(), t9.clone()]),
            (q5, vec![t5.clone(), t6.clone(), t9.clone()]),
            (q6, vec![t1.clone(), t8.clone()]),
        ];

        for (query_term, expected_query_results) in tests.iter() {
            let query_result = discr_tree
                .get_unification_candidates(query_term)
                .collect::<HashSet<_>>();
            assert_eq!(query_result.len(), expected_query_results.len());
            for expected in expected_query_results.iter() {
                assert!(query_result.contains(map.get(expected).unwrap()));
            }
        }
    }
}
