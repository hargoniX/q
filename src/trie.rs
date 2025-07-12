//! ## Trie
//! Contains the implementation of a basic [trie](https://en.wikipedia.org/wiki/Trie) data structure
//! used mainly for term indices.

use std::{
    collections::{
        BTreeMap,
        btree_map::{self, Entry},
    },
    slice,
};

/// Implementation of a [trie](https://en.wikipedia.org/wiki/Trie) with `C` being the characters
/// from its alphabet and `V` the values in the nodes.
#[derive(Debug)]
pub struct Trie<C, V> {
    values: Vec<V>,
    children: BTreeMap<C, Box<Trie<C, V>>>,
}

impl<C: Copy + Eq + Ord, V: Eq> Trie<C, V> {
    /// Create a new empty try.
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
            children: BTreeMap::new(),
        }
    }

    /// Insert `value` at the position described by the string produced by `iter`.
    pub fn insert(&mut self, mut iter: impl Iterator<Item = C>, value: V) {
        match iter.next() {
            Some(char) => match self.children.entry(char) {
                Entry::Occupied(mut occupied_entry) => {
                    occupied_entry.get_mut().insert(iter, value);
                }
                Entry::Vacant(vacant_entry) => {
                    let subtrie = Self::new();
                    let filled = vacant_entry.insert(Box::new(subtrie));
                    filled.insert(iter, value);
                }
            },
            None => self.values.push(value),
        }
    }

    /// Remove `value` at the position described by the string produce by `iter`.
    pub fn remove(&mut self, mut iter: impl Iterator<Item = C>, value: V) {
        match iter.next() {
            Some(char) => match self.children.entry(char) {
                Entry::Occupied(mut occupied_entry) => {
                    let entry = occupied_entry.get_mut();
                    entry.remove(iter, value);
                    // Remove the subtrie if:
                    // - the subtrie has no values directly attached
                    // - the subtrie has no elements in its subtrie
                    if entry.values.is_empty() && entry.children.is_empty() {
                        self.children.remove(&char);
                    }
                }
                // Element not contained in the trie in the first place
                Entry::Vacant(_) => (),
            },
            None => {
                // Self is the final trie, where the value is stored
                // Could also iter().enumerate() and swap_remove
                self.values.retain(|x| *x != value);
            }
        }
    }

    pub fn get_child(&self, c: &C) -> Option<&Trie<C, V>> {
        self.children.get(c).map(|v| &**v)
    }

    pub fn iter_children(&self) -> btree_map::Iter<'_, C, Box<Trie<C, V>>> {
        self.children.iter()
    }

    pub fn iter_values(&self) -> slice::Iter<'_, V> {
        self.values.iter()
    }

    pub fn has_values(&self) -> bool {
        !self.values.is_empty()
    }
}
