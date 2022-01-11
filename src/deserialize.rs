use bigdecimal::BigDecimal;
use serde;
use std::convert::TryFrom;
use std::marker::PhantomData;
use std::{any, fmt};

/// The Visitor used for the deserialization process.
/// The generic parameter T will be the same type as the
/// type that the visitor is going to produce.
pub struct NumberVisitor<T> {
    /// Unused type.
    _marker: PhantomData<T>,
}

impl<T> Default for NumberVisitor<T> {
    fn default() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

impl<'de, T> serde::de::Visitor<'de> for NumberVisitor<T>
where
    T: TryFrom<u64>,
    <T as TryFrom<u64>>::Error: std::fmt::Display,
{
    type Value = T;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "to deserialise {} from a numerical or a string value",
            any::type_name::<T>()
        )
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        T::try_from(value).map_err(E::custom)
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let v: u64 = value.parse::<u64>().map_err(E::custom)?;
        self.visit_u64(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Serialize;
    use smoke::{generator::num, property};
    use smoke_macros::smoketest;

    #[derive(Default, Debug, Serialize, PartialEq, Eq)]
    struct Sample(u64);

    impl From<u64> for Sample {
        fn from(number: u64) -> Self {
            Self(number)
        }
    }

    impl<'de> serde::de::Deserialize<'de> for Sample {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::de::Deserializer<'de>,
        {
            deserializer.deserialize_any(NumberVisitor::<Sample>::default())
        }
    }

    #[smoketest{ n: num::<u64>() }]
    fn check_visitor_from_struct(n: u64) {
        let input = Sample(n);

        let string = serde_json::to_string(&input).unwrap();
        let result: Sample = serde_json::from_str(&string).unwrap();

        property::equal(input, result)
    }

    #[smoketest{ n: num::<u64>() }]
    fn check_visitor_from_string(n: u64) {
        let input = format!("\"{}\"", n);
        let expected = format!("{}", n);

        let sample: Sample = serde_json::from_str(&input).unwrap();
        let result = serde_json::to_string(&sample).unwrap();

        property::equal(expected, result)
    }

    #[smoketest{ n: num::<u64>() }]
    fn check_visitor_from_number(n: u64) {
        let input = n.to_string();

        let sample: Sample = serde_json::from_str(&input).unwrap();
        let result = serde_json::to_string(&sample).unwrap();

        property::equal(input, result)
    }
}

pub struct BigDecimalVisitor<T> {
    /// Unused type.
    _marker: PhantomData<T>,
}

impl<T> Default for BigDecimalVisitor<T> {
    fn default() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

impl<'de, T> serde::de::Visitor<'de> for BigDecimalVisitor<T>
where
    T: TryFrom<BigDecimal>,
    <T as TryFrom<BigDecimal>>::Error: std::fmt::Display,
{
    type Value = T;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "to deserialise {} from a numerical or a string value",
            any::type_name::<T>()
        )
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let v: BigDecimal = BigDecimal::from(v);
        T::try_from(v).map_err(E::custom)
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let v: BigDecimal = value.parse::<BigDecimal>().map_err(E::custom)?;
        T::try_from(v).map_err(E::custom)
    }
}
