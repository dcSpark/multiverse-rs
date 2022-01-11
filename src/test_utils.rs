use super::Variant;
use crate::block_number::BlockNumber;
use serde::{Deserialize, Serialize};
use std::{
    borrow::{Borrow, Cow},
    collections::HashMap,
};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash, Clone)]
pub struct V {
    id: K,
    parent_id: K,
    counter: u64,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub struct K(Cow<'static, str>);

#[derive(Debug, Default)]
pub struct TestContext {
    /// all the created V by ID
    all: HashMap<K, V>,
    /// all the created V ordered by creation time
    ordered: Vec<V>,
}

/// Convenient macro to [`declare`] a set of [`V`]
/// linked together or not
///
/// ```
/// # use forkaholic::declare_blockchain;
/// declare_blockchain! {
///    "root" <= "s1" <= "s2a",
///              "s1" <= "s2b" <= "s3" <= "s4",
/// };
/// ```
///
/// Which gives you something like that:
///
/// ```text
/// +-----+       +-----+       +-----+
/// |Root |<------+S1   |<------+s2a  |
/// |     |       |     |       |     |
/// +-----+       +-----+       +-----+
///                 ^
///                 |
///                 |          +-----+        +------+      +------+
///                 +----------+s2b  +--------+ s3   |<-----+ s4   |
///                            |     |        |      |      |      |
///                            +-----+        +------+      +------+
///
/// ```
#[macro_export]
macro_rules! declare_blockchain {
    ($($any:tt)*) => {
        $crate::declare_blockchain_internal! { $($any)* }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! declare_blockchain_internal_ {
    (
        $ctx:ident,

        $parent:literal <= $id:literal
    ) => {
        $ctx.insert($parent, $id);
    };

    (
        $ctx:ident,

        $parent:literal <= $id:literal $( <= $other:literal )+
    ) => {
        $ctx.insert($parent, $id);
        $crate::declare_blockchain_internal_!($ctx, $id $(<= $other)+ )
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! declare_blockchain_internal {
    (
        $id:literal $(,)?
    ) => {{
        let mut ctx = $crate::test_utils::TestContext::new();

        ctx.push($id);

        ctx
    }};

    (
        $(
            $parent:literal <= $id:literal $( <= $other:literal )*
         ),* $(,)?
    ) => {{
        let mut ctx = $crate::test_utils::TestContext::new();

        //
        $(
            $crate::declare_blockchain_internal_!(
                ctx,
                $parent <= $id $(<= $other)*
            );
        )*

        ctx
    }};
}

impl TestContext {
    pub fn new() -> Self {
        Self::default()
    }

    /// push a single node without parent
    ///
    /// # panics
    ///
    /// The function will panic if the ID is a already present in the
    /// context but this is not the same value (counter and parent are different)
    pub fn push(&mut self, id: &'static str) {
        let v = V::new(id, 1);
        if let Some(_v) = self.all.insert(v.id.clone(), v.clone()) {
            assert_eq!(
                v,
                _v,
                "previous V does not match the new V, the IDs are clashing: {id}",
                id = id
            );
        } else {
            self.ordered.push(v);
        }
    }

    /// insert a new `id` in the [`TestContext`].
    ///
    /// # panics
    ///
    /// The function will panic if the ID is a already present in the
    /// context but this is not the same value (counter and parent are different)
    pub fn insert(&mut self, parent: &'static str, id: &'static str) {
        let parent = self
            .all
            .entry(K::new(parent))
            .or_insert_with(|| V::new(parent, 1));
        self.ordered.push(parent.clone());
        let v = parent.mk_child(id);

        if let Some(_v) = self.all.insert(v.id.clone(), v.clone()) {
            assert_eq!(
                v,
                _v,
                "previous V does not match the new V, the IDs are clashing: {id}",
                id = id
            );
        } else {
            self.ordered.push(v);
        }
    }
}

impl K {
    pub const fn new(id: &'static str) -> Self {
        Self(Cow::Borrowed(id))
    }

    pub fn is(&self, id: &'static str) -> bool {
        self.0.as_ref() == id
    }
}

impl V {
    pub fn new<T>(id: T, counter: u64) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self {
            id: K(id.into()),
            parent_id: K(Cow::Borrowed("N/A")),
            counter,
        }
    }

    pub fn mk_child<T>(&self, id: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self {
            id: K(id.into()),
            parent_id: self.id.clone(),
            counter: self.counter.saturating_add(1),
        }
    }
}

impl AsRef<[u8]> for K {
    fn as_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl Variant for V {
    type Key = K;

    fn id(&self) -> &K {
        &self.id
    }
    fn parent_id(&self) -> &K {
        &self.parent_id
    }
    fn block_number(&self) -> BlockNumber {
        self.counter.into()
    }
}

impl Borrow<str> for K {
    fn borrow(&self) -> &str {
        self.0.borrow()
    }
}

impl IntoIterator for TestContext {
    type IntoIter = <Vec<V> as IntoIterator>::IntoIter;
    type Item = <Vec<V> as IntoIterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        self.ordered.into_iter()
    }
}

#[test]
fn test() {
    let _ctx: TestContext = declare_blockchain! {
        "root"
    };

    let _ctx: TestContext = declare_blockchain! {
        "root",
    };

    let _ctx: TestContext = declare_blockchain! {
        "root" <= "s1"
    };

    let _ctx: TestContext = declare_blockchain! {
        "root" <= "s1" <= "s2a",
                  "s1" <= "s2b" <= "s3" <= "s4",
    };
}
