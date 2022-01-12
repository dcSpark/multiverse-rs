# Multiverse

[![Linter and unit tests](https://github.com/dcSpark/multiverse-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/dcSpark/multiverse-rs/actions/workflows/rust.yml)
[![Test documentation](https://github.com/dcSpark/multiverse-rs/actions/workflows/rustdoc.yml/badge.svg)](https://github.com/dcSpark/multiverse-rs/actions/workflows/rustdoc.yml)

## TL;DR
Imagine that you require to have next sequence of blocks/nodes/vertexes/etc. 
```text
A<-B<-C<-D<-E<-F
```
But in your data structure you could only refer parent block from child.
Thus you could traverse to root only from tail.
Such approach  allows you to have not only list, but a graph like structure.  
Each root could have many children.
```text
A<-B<-C<-D<-E
|<-B'<-C'
   |<-C''<-D''<-E''<-F''
```

This state could occur when blocks constantly generated by many distributed nodes. 
At some point we need to decide which blocks sequence is preferred and discard others. 

**Milkomeda crate** here is to help you deal with such propbles.

##  Quick start

Please look into [this example](./examples/multiverse.rs).
It creates multiverse with some branches and then selects best block.

You could run example like this
```shell
cargo run --example multiverse -- <depth> <age_gap>
```
CLI args:

- \<depth\> \- required number of block confirmations 
- \<age_gap\> \- discard blocks if their age (delta compared to larger block number) is more than provided  

## Summary

A blockchain in itself is the persistent storage of the state of the ledger.
Each block of the blockchain contains the logs of the operations applied to
the ledger at a given point in time. If you attempt to take a look at the
blockchain in its entirety, you would only see a consistent immutable line
that expands infinitely forward. This is the case because the blockchain is
designed to be an indefinitely growing succession of blocks. As I write this
document there are about 700 thousands blocks in Bitcoin's blockchain and
about 6 millions blocks in Cardano's.

However, as you start zooming toward the head of the blockchain you will begin
seeing the blockchain grow. This is where history is being written, where the
exciting part is happening. Most of us as users of blockchains will be most
interested in what is happening here, wherein  new changes to the distributed
ledger are being applied. Depending on the way the active participants are
cooperating to maintain the distributed ledger (depending on the consensus
algorithm) the head of the blockchain may look more or less broad, more or
less messy. Branches may appear, sometimes short lived ones, and sometimes
seemingly at random. Every blockchain protocol aims to have them be short
lived, but sometimes they may persist for longer than preferred or expected.
We have already seen explicit forks happen on other blockchains which have
taken on a life of their own and built out their own ecosystem. These are
competitive snapshots of the ledger and hopefully the blockchain protocol will
help resolve these fairly quickly.

From a user perspective, these competitive variants of the timeline are not
necessarily relevant. Often these snapshots will intersect in the changes they
are applying to the ledger, with some transactions potentially even appearing
in both variations (though this is not always the case). With these competing
variants continuing forward, eventually the blockchain may operate what is
referred to as a rollback. In essence a rollback is the blockchain simply
“changing its mind” (based on predefined rules) about which variant is the
preferred one. 

These rollbacks are fastidious, create unnecessary stress on the user's side,
and degrade overall UX by several orders of magnitude. Some blocks appear to
disappear from blockchain explorers, transactions lay unconfirmed in the
wallet, and previously confirmed transactions become suddenly removed because
they were not added in the branch which became the preferred branch in the
end. While this may be industry standard in the space, this is clearly
something that must be addressed going forward as we seek to increase
blockchain adoption.

To address the above qualms we are introducing a novel concept: the
Multiverse.

The Multiverse is an innovative approach to reading and representing the state
of blockchains. It provides nodes a competitive edge by maintaining and
eventually participating in the various branches of a chain. This has
waterfall effects through the entire stack, wherein various pieces of core
ecosystem tooling such as blockchain explorers will be able to benefit
significantly as well. Lastly, this also translates to a better end user
experience, which we will cover in addressing how user wallets can maintain
state via the Multiverse data structure directly.

Note: the concept was first coined by [Vincent Hanquez] when designing and
architecting [Jörmungandr] back in 2019. At the time it was our belief we
could actually provide a simpler and faster way to manage rollback by following
all the branches of a given blockchain. With time and maturity we came to
the conclusion this could actually be useful through all the stack of the
blockchain.

[Jörmungandr]: https://github.com/input-output-hk/jormungandr
[Vincent Hanquez]: https://github.com/vincenthz
