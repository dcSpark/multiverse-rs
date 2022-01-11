use super::deserialize::NumberVisitor;
use serde::Serialize;
use std::{fmt, num, str};

/// use to identify a block number within the blockchain
///
/// this value is not necessarily monotonically increasing.
#[derive(Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Serialize)]
#[serde(transparent)]
pub struct BlockNumber(u64);

impl BlockNumber {
    /// the largest value a [`BlockNumber`] can be
    pub const MAX: Self = Self::new(u64::MAX);

    /// the smallest value a [`BlockNumber`] can be.
    pub const MIN: Self = Self::new(u64::MIN);

    /// wrap the given value into a BlockNumber type
    ///
    #[inline(always)]
    pub const fn new(block_number: u64) -> Self {
        Self(block_number)
    }

    #[inline(always)]
    #[must_use = "The function does not modify the state, the new value is returned"]
    pub fn into_inner(self) -> u64 {
        self.0
    }

    /// Try to increase by `1` the [`BlockNumber`]
    ///
    /// If the addition will overflow, the function will returns `None`.
    #[must_use = "The function does not modify the state, the new value is returned"]
    #[inline]
    pub fn checked_next(self) -> Option<Self> {
        self.checked_add(1)
    }

    /// Increase by `1` the [`BlockNumber`]
    ///
    /// If the addition will overflow, the function will returns [`Self::MAX`].
    #[must_use = "The function does not modify the state, the new value is returned"]
    #[inline]
    pub fn saturating_next(self) -> Self {
        self.saturating_add(1)
    }

    /// Try to add the right hand side (`rhs`) value to the [`BlockNumber`].
    ///
    /// If the addition will overflow, the function will returns `None`.
    #[must_use = "The function does not modify the state, the new value is returned"]
    #[inline]
    pub fn checked_add(self, rhs: u64) -> Option<Self> {
        self.0.checked_add(rhs).map(Self)
    }

    /// Add the right hand side (`rhs`) value to the [`BlockNumber`].
    ///
    /// If the addition will overflow we returns the [`Self::MAX`].
    #[must_use = "The function does not modify the state, the new value is returned"]
    #[inline]
    pub fn saturating_add(self, rhs: u64) -> Self {
        Self(self.0.saturating_add(rhs))
    }

    /// Subtract the right hand side (`rhs`) value to the [`BlockNumber`].
    ///
    /// If the subtraction will overflow we returns the [`Self::MIN`].
    #[must_use = "The function does not modify the state, the new value is returned"]
    #[inline]
    pub fn saturating_sub(self, rhs: u64) -> Self {
        Self(self.0.saturating_sub(rhs))
    }
}

impl fmt::Display for BlockNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Binary for BlockNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Octal for BlockNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::LowerHex for BlockNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::UpperHex for BlockNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::LowerExp for BlockNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::UpperExp for BlockNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl str::FromStr for BlockNumber {
    type Err = num::ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(Self)
    }
}

impl From<u64> for BlockNumber {
    fn from(block_number: u64) -> Self {
        Self(block_number)
    }
}

impl From<BlockNumber> for u64 {
    fn from(BlockNumber(block_number): BlockNumber) -> Self {
        block_number
    }
}

/// Custom deserializer for BlockNumber(u64).
/// The deserialization is successful when the data (json) is a
/// number (u64) or when the data is a string (number base 10).
impl<'de> serde::de::Deserialize<'de> for BlockNumber {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        deserializer.deserialize_any(NumberVisitor::<BlockNumber>::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;
    use smoke::{generator::num, property};
    use smoke_macros::smoketest;

    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    struct Sample {
        n: u32,
        v: BlockNumber,
    }

    #[test]
    fn checked_next_overflow() {
        assert_eq!(None, BlockNumber::MAX.checked_next())
    }

    #[test]
    fn check_add_overflow() {
        assert_eq!(None, BlockNumber::MAX.checked_add(1))
    }

    #[test]
    fn saturating_next_overflow() {
        assert_eq!(BlockNumber::MAX, BlockNumber::MAX.saturating_next())
    }

    #[test]
    fn saturating_add_overflow() {
        assert_eq!(BlockNumber::MAX, BlockNumber::MAX.saturating_add(1))
    }

    #[smoketest{ a: num::<u64>() }]
    fn checked_next(a: u64) {
        property::equal(
            a.checked_add(1).map(BlockNumber),
            BlockNumber(a).checked_next(),
        )
    }

    #[smoketest{ a: num::<u64>(), b: num::<u64>() }]
    fn checked_add(a: u64, b: u64) {
        property::equal(
            a.checked_add(b).map(BlockNumber),
            BlockNumber(a).checked_add(b),
        )
    }

    #[smoketest{ a: num::<u64>() }]
    fn saturating_next(a: u64) {
        property::equal(
            BlockNumber(a.saturating_add(1)),
            BlockNumber(a).saturating_next(),
        )
    }

    #[smoketest{ a: num::<u64>(), b: num::<u64>() }]
    fn saturating_add(a: u64, b: u64) {
        property::equal(
            BlockNumber(a.saturating_add(b)),
            BlockNumber(a).saturating_add(b),
        )
    }

    #[test]
    fn deserialize_from_number() {
        let expected = Sample {
            n: 35,
            v: BlockNumber(1234),
        };

        let input = r###"
        {
            "n": 35,
            "v": 1234
        }
        "###;

        let output: Sample = serde_json::from_str(input).unwrap();
        assert_eq!(expected, output);
    }

    #[test]
    fn deserialize_from_string() {
        let expected = Sample {
            n: 70,
            v: BlockNumber(4567),
        };

        let input = r###"
        {
            "n": 70,
            "v": "4567"
        }
        "###;

        let output: Sample = serde_json::from_str(input).unwrap();
        assert_eq!(expected, output);
    }
}
