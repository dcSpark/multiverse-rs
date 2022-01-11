use multiverse::BestBlockSelectionRule;
use serde_json::{from_value, json, to_value};

#[test]
fn encode() {
    let expected = json! {{
        "rule": "LongestChain",
        "depth": 1,
        "age_gap": 2
    }};
    let value = BestBlockSelectionRule::LongestChain {
        depth: 1,
        age_gap: 2,
    };

    assert_eq!(to_value(value).unwrap(), expected,);
}

#[test]
fn decode() {
    let value = json! {{
        "rule": "LongestChain",
        "depth": 1,
        "age_gap": 2
    }};
    let expected = BestBlockSelectionRule::LongestChain {
        depth: 1,
        age_gap: 2,
    };

    assert_eq!(
        from_value::<BestBlockSelectionRule>(value).unwrap(),
        expected,
    );
}
