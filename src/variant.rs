use crate::BlockNumber;

/// convenient trait to enable generalization of [`Multiverse`](crate::Multiverse)
/// state tracking.
///
pub trait Variant: serde::de::DeserializeOwned + serde::Serialize {
    type Key: Clone;

    /// expect to be the unique identifier of the givens state
    fn id(&self) -> &Self::Key;

    /// expect to be the unique identifier of the parent of the state
    fn parent_id(&self) -> &Self::Key;

    /// expect to be the number of blocks present in the given chain
    fn block_number(&self) -> BlockNumber;
}
