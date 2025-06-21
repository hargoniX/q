use std::slice;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiSet<T> {
    vec: Vec<T>,
}

impl<T> MultiSet<T> {
    pub fn new() -> Self {
        Self { vec: Vec::new() }
    }

    pub fn of_vec(vec: Vec<T>) -> Self {
        Self { vec }
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.vec.iter()
    }

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
