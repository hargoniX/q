use std::{
    collections::{HashMap, HashSet, hash_map::Entry},
    hash::Hash,
    rc::Rc,
};

use crate::term_bank::{FunctionIdentifier, RawTerm, Term};

#[derive(Debug)]
struct Trie<C, V> {
    values: Vec<V>,
    children: HashMap<C, Box<Trie<C, V>>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum DiscrTreeKey {
    Star,
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

#[derive(Debug)]
pub struct DiscriminationTree<V> {
    trie: Trie<DiscrTreeKey, V>,
}

impl<C: Eq + Hash, V> Trie<C, V> {
    fn new() -> Self {
        Self {
            values: Vec::new(),
            children: HashMap::new(),
        }
    }

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

// Precondition: iter has at least one element remaining and iterates over a well formed term
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

impl<V: Hash + Eq> DiscriminationTree<V> {
    pub fn new() -> Self {
        Self { trie: Trie::new() }
    }

    pub fn insert(&mut self, term: &Term, value: V) {
        let iter = PersistentPreorderTermIterator::new(term);
        self.trie.insert(iter, value);
    }

    pub fn get_generalisation_candidates(&self, term: &Term) -> HashSet<&V> {
        let iter = PersistentPreorderTermIterator::new(term).peekable();
        let mut frontier = vec![(iter, &self.trie)];
        let mut set = HashSet::new();
        while let Some((mut candidate_pos, trie_pos)) = frontier.pop() {
            match candidate_pos.peek() {
                Some(key @ DiscrTreeKey::Star) => {
                    if let Some(subtrie) = trie_pos.children.get(&key) {
                        candidate_pos.next();
                        frontier.push((candidate_pos, subtrie))
                    }
                }
                Some(key @ DiscrTreeKey::App { .. }) => {
                    if let Some(subtrie) = trie_pos.children.get(&key) {
                        let mut next_candidate_pos = candidate_pos.clone();
                        next_candidate_pos.next();
                        frontier.push((next_candidate_pos, subtrie));
                    }

                    if let Some(subtrie) = trie_pos.children.get(&DiscrTreeKey::Star) {
                        skip_to_next_subterm(&mut candidate_pos);
                        frontier.push((candidate_pos, subtrie));
                    }
                }
                None => trie_pos.values.iter().for_each(|val| {
                    set.insert(val);
                }),
            }
        }

        set
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::term_bank::{FunctionInformation, Term, TermBank, VariableInformation};

    use super::{DiscrTreeKey, DiscriminationTree, PersistentPreorderTermIterator};

    fn flatterm(t: &Term) -> Vec<DiscrTreeKey> {
        PersistentPreorderTermIterator::new(t).collect()
    }

    #[test]
    fn basic_preorder_iterator_test() {
        let mut term_bank = TermBank::new();
        let b = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
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
            name: "c".to_string(),
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
}
