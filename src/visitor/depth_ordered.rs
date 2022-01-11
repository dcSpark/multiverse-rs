use crate::BlockNumber;
use crate::{entry::EntryRef, Multiverse};
use std::{
    collections::{BTreeMap, HashSet},
    hash::Hash,
};

/// iterator through all the elements of the Multiverse
/// ordered by their block number.
///
/// This is equivalent to a breadth first search through the graph
pub struct DepthOrderedIterator<'a, K, V> {
    inner: &'a Multiverse<K, V>,
    tree: BTreeMap<BlockNumber, HashSet<EntryRef<K>>>,
}

impl<'a, K, V> DepthOrderedIterator<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: &'a Multiverse<K, V>) -> Self {
        let tree = inner.ordered.clone();
        Self { inner, tree }
    }
}

impl<'a, K, V> Iterator for DepthOrderedIterator<'a, K, V>
where
    K: Eq + Hash,
{
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        while !self.tree.is_empty() {
            let (bn, set) = self.tree.iter_mut().next()?;
            let bn = *bn;

            if let Some(entry_ref) = set.drain().next() {
                let entry = self.inner.all.get(&entry_ref)?;
                return Some(&entry.value);
            }

            self.tree.remove(&bn);
        }

        None
    }
}
