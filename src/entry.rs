use std::{
    borrow::Borrow,
    collections::HashSet,
    fmt,
    hash::{Hash, Hasher},
    sync::{Arc, Weak},
};

/// an entry in the [`Multiverse`](crate::multiverse::Multiverse) graph
///
#[derive(Debug)]
pub struct Entry<K, V> {
    pub(super) parent: EntryWeakRef<K>,
    pub(super) children: HashSet<EntryRef<K>>,

    pub(super) value: V,
}

pub struct EntryWeakRef<K> {
    key: Weak<K>,
}

pub struct EntryRef<K> {
    pub(super) key: Arc<K>,
}

impl<K, V> Entry<K, V> {
    #[inline]
    pub(super) fn new(parent: EntryWeakRef<K>, value: V) -> Self {
        Self {
            parent,
            children: HashSet::new(),
            value,
        }
    }
}

impl<K, V> Entry<K, V>
where
    K: Eq + Hash,
{
    #[inline]
    pub(super) fn add_child(&mut self, child: EntryRef<K>) {
        self.children.insert(child);
    }
}

impl<K> EntryRef<K> {
    /// create an [`EntryRef`] from the given `key`.
    #[inline]
    pub fn new(key: K) -> Self {
        Self { key: Arc::new(key) }
    }

    #[inline]
    pub fn weak(&self) -> EntryWeakRef<K> {
        EntryWeakRef {
            key: Arc::downgrade(&self.key),
        }
    }

    /// Same result as calling [`Borrow::borrow`] but without
    /// the type inference issues.
    #[inline]
    pub fn inner(&self) -> &K {
        self.key.as_ref()
    }
}

impl<K> EntryWeakRef<K> {
    #[inline]
    pub fn new() -> Self {
        Self { key: Weak::new() }
    }

    #[inline]
    pub fn upgrade(&self) -> Option<EntryRef<K>> {
        let key = self.key.upgrade()?;
        Some(EntryRef { key })
    }
}

impl<K> Borrow<K> for EntryRef<K> {
    #[inline]
    fn borrow(&self) -> &K {
        self.inner()
    }
}

impl<K> AsRef<[u8]> for EntryRef<K>
where
    K: AsRef<[u8]>,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        // just calling `self.key.as_ref()` seems to resolve into
        // `&K` and not into `&[u8]`.
        //
        // This is because `self.key` is
        // type `Rc<K>`. So calling `key.as_ref()` calls the
        // implementation of `AsRef<K> for Rc<K>`.
        self.key.as_ref().as_ref()
    }
}

impl<K> fmt::Debug for EntryWeakRef<K>
where
    K: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.clone().upgrade().fmt(f)
    }
}

impl<K> fmt::Debug for EntryRef<K>
where
    K: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.key.as_ref().fmt(f)
    }
}

impl<K> fmt::Display for EntryRef<K>
where
    K: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.key.as_ref().fmt(f)
    }
}

// make our own implementation of Clone because it does not
// matter the content of the [`EntryWeakRef`] to make it clone
impl<K> Clone for EntryWeakRef<K> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
        }
    }
}

/// make our own implementation of Clone because it does not
/// matter the content of the [`EntryRef`] to make it clone
impl<K> Clone for EntryRef<K> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
        }
    }
}

impl<K: PartialEq> PartialEq for EntryRef<K> {
    fn eq(&self, other: &Self) -> bool {
        self.key.eq(&other.key)
    }
}
impl<K: PartialEq> PartialEq for EntryWeakRef<K> {
    fn eq(&self, other: &Self) -> bool {
        self.clone().upgrade() == other.clone().upgrade()
    }
}
impl<K: Eq + Hash, V: PartialEq> PartialEq for Entry<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
            && self.parent.eq(&other.parent)
            && self.children.eq(&other.children)
    }
}

impl<K: Eq> Eq for EntryRef<K> {}
impl<K: Eq> Eq for EntryWeakRef<K> {}
impl<K: Eq + Hash, V: Eq> Eq for Entry<K, V> {}

impl<K: Hash> Hash for EntryRef<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key.hash(state)
    }
}

impl<K> Default for EntryWeakRef<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K> From<K> for EntryRef<K> {
    fn from(key: K) -> Self {
        EntryRef::new(key)
    }
}

/// add some unit tests to check some of the assumptions we are making
/// regarding the behavior of the [`EntryRef`] and [`EntryWeakRef`].
///
/// These are trivial. We rely entirely on the standard [Rc]
/// implementation that is already battle tested. However here
/// we are testing the assumption we are making of our API. So we
/// can change the content of the [`EntryRef`] and [`EntryWeakRef`]
/// later. We know that everything we are building on top (such as
/// the [`Multiverse`](crate::multiverse::Multiverse)) can rely
/// safely on the expected behavior.
#[cfg(test)]
mod tests {
    use super::*;

    /// test the assumption that an empty weak ref is not upgradable
    #[test]
    fn upgrade_empty_weak_ref() {
        let entry_weak_ref: EntryWeakRef<u64> = EntryWeakRef::new();

        assert!(entry_weak_ref.upgrade().is_none());
    }

    /// test the assumption the weak ref holds its reference to
    /// living [`EntryRef`]
    #[test]
    fn upgrade_weak_ref_1() {
        let entry_ref = EntryRef::new(42);
        let entry_weak_ref = entry_ref.weak();

        assert!(entry_weak_ref.upgrade().is_some());
    }

    /// test the assumption the weak ref loses its reference to
    /// dropped [`EntryRef`]
    #[test]
    fn upgrade_weak_ref_2() {
        let entry_ref = EntryRef::new(42);
        let entry_weak_ref = entry_ref.weak();

        std::mem::drop(entry_ref);

        assert!(entry_weak_ref.upgrade().is_none());
    }
}
