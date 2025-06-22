//! ## Multisets
//! This module provides a basic immutable multiset implementation. The key exported data structure
//! is [MultiSet].

use std::slice;

// Multisets containing values of type `T`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiSet<T> {
    vec: Vec<T>,
}

impl<T> MultiSet<T> {
    /// Create a new empty multiset.
    pub fn new() -> Self {
        Self { vec: Vec::new() }
    }

    /// Create a new multiset containign all elements from `vec`.
    pub fn of_vec(vec: Vec<T>) -> Self {
        Self { vec }
    }

    /// Compute how many elements are in the multiset overall, including duplications, this is
    /// `O(1)`.
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Check if the set is empty, this is `O(1)`.
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    /// Obtain an iterator over all elements in the set.
    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.vec.iter()
    }

    /// Index into the multiset, the i-th element is the one that was inserted as the i-th one.
    pub fn get(&self, idx: usize) -> &T {
        &self.vec[idx]
    }
    // TODO: this will likely need more methods, build them as they come up
}

impl<T> FromIterator<T> for MultiSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            vec: FromIterator::from_iter(iter),
        }
    }
}

impl<T> IntoIterator for MultiSet<T> {
    type Item = T;

    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}
