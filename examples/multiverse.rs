use serde::{Deserialize, Serialize};
use std::env;

use multiverse::{BestBlockSelectionRule, Multiverse, Variant};

const MULTIVERSE_STRUCTURE: &str = "\
(0-aaa0)<-(1-abc0)<-(2-bcd0)<-(3-cde0)<-(4-def0)<-(5-efg0)
                 |<-(2-bcd1)<-(3-cde1)<-(4-def1)
                           |<-(3-cde2)
                                     |<-(4-def3)<-(5-efg3)<-(6-fgh3)
";

/// Our custom node/block for multiverse
#[derive(Serialize, Deserialize)]
struct MyNode {
    id: String,
    parent_id: String,
    block_number: u64,
}

impl MyNode {
    fn new(id: &str, block_number: u64, parent_id: &str) -> MyNode {
        MyNode {
            id: String::from(id),
            block_number,
            parent_id: String::from(parent_id),
        }
    }
}

/// We must implement ['Variant'] to work with multiverse.
impl Variant<u64> for MyNode {
    type Key = String;
    fn id(&self) -> &Self::Key {
        &self.id
    }
    fn parent_id(&self) -> &Self::Key {
        &self.parent_id
    }
    fn block_number(&self) -> u64 {
        self.block_number
    }
}

type MyMultiverse = Multiverse<String, MyNode, u64>;

fn main() {
    let args: Vec<String> = env::args().collect();

    let rule = if args.len() == 3 {
        let depth = args[1]
            .parse::<usize>()
            .expect("Fist arg has to be a number");
        let age_gap = args[2]
            .parse::<usize>()
            .expect("Second arg has to be a number");

        println!("\nMULTIVERSE STRUCTURE:\n{}", MULTIVERSE_STRUCTURE);
        println!("\nINPUT:\n\tdepth = {}\n\tage_gap = {}\n", depth, age_gap);

        BestBlockSelectionRule::LongestChain { depth, age_gap }
    } else {
        panic!("ERROR! Must have only 2 CLI arguments <depth> <age_gap>");
    };

    let mut multiverse: MyMultiverse = Multiverse::temporary().unwrap();

    populate_multiverse(&mut multiverse);

    let bb = multiverse.select_best_block(rule);

    println!("RESULTS:");
    println!("\tBest block: {}", bb.selected.unwrap());
    print!("\tDiscarded : ");
    for v in bb.discarded {
        print!("{}, ", v);
    }
    println!();
}

///
/// Here we will populate our multiverse with blocks structure described in ['MULTIVERSE_STRUCTURE'].
///
fn populate_multiverse(mv: &mut MyMultiverse) {
    // This function created just to same some space and 4 fun 2.
    let mut insert = |id: &str, block_number: u64, parent_id: &str| {
        mv.insert(MyNode::new(id, block_number, parent_id)).unwrap();
    };

    insert("0-aaa0", 0, "");
    insert("1-abc0", 1, "0-aaa0");
    insert("2-bcd0", 2, "1-abc0");
    insert("3-cde0", 3, "2-bcd0");
    insert("4-def0", 4, "3-cde0");
    insert("5-efg0", 5, "4-def0");

    insert("2-bcd1", 2, "1-abc0");
    insert("3-cde1", 3, "2-bcd1");
    insert("4-def1", 4, "3-cde1");

    insert("3-cde2", 3, "2-bcd1");

    insert("4-def3", 4, "3-cde2");
    insert("5-efg3", 5, "4-def3");
    insert("6-fgh3", 6, "5-efg3");
}
