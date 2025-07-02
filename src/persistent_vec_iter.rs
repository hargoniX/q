//! ## Persistent Vector Iterator
//! This module contains an implementation of an iterator over a vector as a persistent data
//! structure to allow for cheap cloning.

use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct PersistentVecIterator<V> {
    vec: Rc<Vec<V>>,
    pos: usize,
}

impl<V> PersistentVecIterator<V> {
    pub fn new(vec: Vec<V>) -> Self {
        Self {
            vec: Rc::new(vec),
            pos: 0,
        }
    }
}

impl<V: Copy> Iterator for PersistentVecIterator<V> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.vec.len() {
            let ret = self.vec[self.pos];
            self.pos += 1;
            Some(ret)
        } else {
            None
        }
    }
}
