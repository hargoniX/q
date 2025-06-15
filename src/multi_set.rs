use std::{
    collections::{
        hash_map::{self, Entry},
        HashMap,
    },
    hash::Hash,
};

#[derive(Debug, Clone)]
pub struct MultiSet<T> {
    map: HashMap<T, usize>,
}

impl<T: PartialEq + Eq + Hash> MultiSet<T> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn is_unit(&self) -> bool {
        self.len() == 1
    }

    pub fn insert(&mut self, t: T) {
        match self.map.entry(t) {
            Entry::Occupied(mut occupied) => {
                let amount = *occupied.get();
                occupied.insert(amount + 1);
            }
            Entry::Vacant(vacant) => {
                vacant.insert(1);
            }
        }
    }

    pub fn remove(&mut self, t: T) {
        match self.map.entry(t) {
            Entry::Occupied(mut occupied) => {
                let amount = *occupied.get();
                debug_assert_ne!(amount, 0);
                if amount == 1 {
                    occupied.remove();
                } else {
                    occupied.insert(amount - 1);
                }
            }
            Entry::Vacant(_) => {}
        }
    }

    pub fn iter(&self) -> hash_map::Iter<'_, T, usize> {
        self.map.iter()
    }

    fn valid_multi_set(&self) -> bool {
        self.iter().all(|(_, count)| *count > 0)
    }
    // TODO: this will likely need more methods, build them as they come up
}

impl<T: Hash + PartialEq + Eq> FromIterator<(T, usize)> for MultiSet<T> {
    fn from_iter<I: IntoIterator<Item = (T, usize)>>(iter: I) -> Self {
        let set = Self {
            map: FromIterator::from_iter(iter),
        };
        debug_assert!(set.valid_multi_set());
        set
    }
}

impl<T: Hash + PartialEq + Eq> IntoIterator for MultiSet<T> {
    type Item = (T, usize);

    type IntoIter = hash_map::IntoIter<T, usize>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}
