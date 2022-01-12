use serde::{Deserialize, Serialize};

use multiverse::{BestBlockSelectionRule, BlockNumber, Multiverse, Variant};

/*
First we have to create our node/block structure and implement Variant trait for it.
*/

#[derive(Serialize, Deserialize)]
struct MyNode {
    id: String,
    parent_id: String,
    block_number: BlockNumber,
}

impl MyNode {
    fn new(id: &str, block_number: BlockNumber, parent_id: &str) -> MyNode {
        MyNode {
            id: String::from(id),
            block_number: block_number,
            parent_id:  String::from(parent_id),
        }
    }
}

impl Variant for MyNode {
    type Key = String;
    fn id(&self) -> &Self::Key { return &self.id; }
    fn parent_id(&self) -> &Self::Key { return &self.parent_id; }
    fn block_number(&self) -> BlockNumber { return self.block_number; }
}

type MyMultiverse = Multiverse<String, MyNode>;

fn main() {
    let mut multiverse: MyMultiverse = Multiverse::temporary().unwrap();

    populate_multiverse(&mut multiverse);

    let rule = BestBlockSelectionRule::LongestChain {
        depth: 1,
        age_gap: 1
    };

    let bb = multiverse.select_best_block(rule);

    println!("Best block {}", bb.selected.unwrap());
    println!("Discarded:");
    for v in bb.discarded  {
        println!("\t - {}", v);
    }
}

///
/// Here we will populate our multiverse with next blocks structure.
/// ```text
/// (1-abc0)<-(2-bcd0)<-(3-cde0)<-(4-def0)<-(5-efg0)
///        |<-(2-bcd1)<-(3-cde1)<-(4-def1)
///                  |<-(3-cde2)
///                            |<-(4-def3)<-(5-efg3)<-(6-fgh3)
/// ```
fn populate_multiverse(mv: &mut MyMultiverse) {
    // This function created just to same some space and 4 fun 2.
    let mut insert = |id: &str, block_number: BlockNumber, parent_id: &str| {
        mv.insert(MyNode::new(id, block_number, parent_id));
    };
    
    insert("1-abc0", 1, "");
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
