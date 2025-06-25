//! ## Hash Consed Term Manager
//! This module contains a generic [hash consing](https://en.wikipedia.org/wiki/Hash_consing)
//! mechanism based on reference counting. The key data structures are:
//! - [Table] which manages the hash consed values and can be used to create new ones using
//!   [Table::hashcons].
//! - [HashConsed] which is a hash consed smart pointer, bound to some [Table]
//!
//! The crucial guarantees provided by these are:
//! 1. All [HashConsed] managed by the same [Table] will be perfectly shared
//! 2. Assuming constant time hashing and comparison of a `T`, hashconsing a `T` will take constant
//!    time itself.
//! 3. Assuming constant time hashing of a `T` a hashconsed `T` will have constant time hashing.
//! 4. Comparing [HashConsed] managed by the same [Table] is constant time.

use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{HashMap, hash_map::Entry},
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
    rc::{Rc, Weak},
};

use log::warn;

#[derive(Debug)]
struct InnerTable<T>
where
    T: Eq + Hash,
{
    /// The central hashconsing table. This contains maps from reference counted term allocations
    /// to weak [InnerHashConsed] references with the idea that once the reference count of a value
    /// associated with a term drops to `0` we know the term may be removed (and thus free'd) from
    /// the `table`.
    table: RefCell<HashMap<Rc<T>, Weak<InnerHashConsed<T>>>>,
}

/// A term table that can be used to produce [HashConsed] smart pointers.
#[derive(Debug)]
pub struct Table<T>
where
    T: Eq + Hash,
{
    /// We reference count the inner term Table such that the [HashConsed] pointers can identify
    /// where they are coming from and fast path their equality check.
    inner: Rc<InnerTable<T>>,
}

struct InnerHashConsed<T>
where
    T: Eq + Hash,
{
    /// The ref counted term that the above [HashConsed] is managing, the allocation of `T` will
    /// only get free'd once the entry is removed from `table`.
    term: Rc<T>,
    /// The term Table containing `term`.
    table: Rc<InnerTable<T>>,
}

/// A hash consed smart pointer, associated with some [Table].
pub struct HashConsed<T>
where
    T: Eq + Hash,
{
    /// A [HashConsed] holds an [Rc] to the [InnerHashConsed] so we can know once it is okay to
    /// free the entry in the term Table.
    inner: Rc<InnerHashConsed<T>>,
}

impl<T: Eq + Hash> InnerTable<T> {
    pub fn new() -> Self {
        Self {
            table: RefCell::new(HashMap::new()),
        }
    }

    fn gc(&self) {
        // A naive GC loop for the term Table, once we encounter a term where the associated
        // []InnerHashConsed` has no more references we know we can remove this term. This might in
        // turn free further `InnerHashConsed` if `T` recursively contains `HashConsed`. As such we
        // must repeat this loop until no change happens.
        //
        // Alternatively we could keep a worklist of allocations to visit and thus not end up in a
        // highly problematic looping behavior.
        loop {
            let mut table = self.table.borrow_mut();
            let prev_len = table.len();
            table.retain(|_, hc| hc.strong_count() > 0);

            if table.len() == prev_len {
                break;
            }
        }
    }

    fn len(&self) -> usize {
        self.table.borrow().len()
    }
}

impl<T: Eq + Hash> Table<T> {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(InnerTable::new()),
        }
    }

    /// Check if a `term` already exists in the [Table], if it does increment the internal ref
    /// count to the representant of `term` and return it, otherwise add a new entry and return it.
    /// The internal allocation for `term` will not be free'd until all [HashConsed] pointing to it
    /// are dropped and [Table::gc] is called afterwards.
    pub fn hashcons(&self, term: T) -> HashConsed<T> {
        let rc_table = self.inner.clone();
        let mut table = rc_table.table.borrow_mut();

        let term_ref1 = Rc::new(term);
        let term_ref2 = Rc::clone(&term_ref1);

        match table.entry(term_ref1) {
            Entry::Occupied(mut e) => {
                let value = e.get();
                match value.upgrade() {
                    Some(value) => HashConsed { inner: value },
                    None => {
                        let value = InnerHashConsed {
                            term: term_ref2,
                            table: self.inner.clone(),
                        };
                        let hash_consed = Rc::new(value);
                        e.insert(Rc::downgrade(&hash_consed));
                        HashConsed { inner: hash_consed }
                    }
                }
            }
            Entry::Vacant(e) => {
                let value = InnerHashConsed {
                    term: term_ref2,
                    table: self.inner.clone(),
                };
                let hash_consed = Rc::new(value);
                e.insert(Rc::downgrade(&hash_consed));
                HashConsed { inner: hash_consed }
            }
        }
    }

    /// Free all hash consed terms that are no longer referenced outside of this term Table.
    pub fn gc(&self) {
        self.inner.gc();
    }

    /// Return the amount of allocations currently kept in the Table. Note that there might be
    /// allocations that can be free'd but this needs to be triggered by [Table::gc].
    pub fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T: Eq + Hash> Clone for Table<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T: Eq + Hash> HashConsed<T> {
    pub fn as_ptr(&self) -> *const T {
        Rc::as_ptr(&self.inner.term)
    }
}

impl<T: Eq + Hash> Hash for HashConsed<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.term.hash(state);
    }
}

impl<T: Eq + Hash> PartialEq for HashConsed<T> {
    fn eq(&self, other: &Self) -> bool {
        // We can fast-path comparison if both [HashConsed] come from the same term Table, this is
        // usually going to be the case. We could in principle use
        // [`likely`](https://doc.rust-lang.org/std/hint/fn.likely.html) here.
        if Rc::ptr_eq(&self.inner.table, &other.inner.table) {
            Rc::ptr_eq(&self.inner.term, &other.inner.term)
        } else {
            warn!("Comparing HashConsed from different tables");
            self.inner.term == other.inner.term
        }
    }
}

impl<T: Eq + Hash> Eq for HashConsed<T> {}

impl<T: Eq + Hash> Clone for HashConsed<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T: Eq + Hash + Debug> Debug for HashConsed<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.inner.term, f)
    }
}

impl<T: Eq + Hash + Display> Display for HashConsed<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.inner.term, f)
    }
}

impl<T: Eq + Hash> Deref for HashConsed<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner.term
    }
}

impl<T: Eq + Hash> AsRef<T> for HashConsed<T> {
    fn as_ref(&self) -> &T {
        self.inner.term.as_ref()
    }
}

impl<T: Eq + Hash + PartialOrd> PartialOrd for HashConsed<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.inner.term.partial_cmp(&other.inner.term)
    }
}

impl<T: Eq + Hash + Ord> Ord for HashConsed<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.term.cmp(&other.inner.term)
    }
}

#[cfg(test)]
mod test {
    use super::Table;

    #[test]
    fn basic_test() {
        let table = Table::new();
        assert_eq!(table.len(), 0);
        let s1 = table.hashcons("hello_world".to_string());
        let s2 = table.hashcons("bye_world".to_string());
        assert_eq!(table.len(), 2);
        assert_ne!(s1, s2);
        let s3 = table.hashcons("hello_world".to_string());
        assert_eq!(s1, s3);
        assert_eq!(table.len(), 2);
        drop(s2);
        assert_eq!(table.len(), 2);
        table.gc();
        assert_eq!(table.len(), 1);
        drop(s1);
        table.gc();
        assert_eq!(table.len(), 1);
        drop(s3);
        assert_eq!(table.len(), 1);
        table.gc();
        assert_eq!(table.len(), 0);
    }
}
