# Formal Modeling of MongoDB Distributed Transactions

This directory contains formal specifications that model the high level behavior of the [distributed, cross-shard transactions protocol in MongoDB](https://github.com/mongodb/mongo/blob/master/src/mongo/db/s/README_sessions_and_transactions.md#transactions). You can interact with the current model on the web here: [MultiShardTxn](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fmuratdem%2FMDBTLA%2Fmain%2FMultiShardTxn%2FMultiShardTxn.tla&constants%5BKeys%5D=%7Bk1%2Ck2%2Ck3%7D&constants%5BTxId%5D=%7Bt1%2Ct2%2Ct3%7D&constants%5BShard%5D=%7Bs1%2Cs2%7D&constants%5BNoValue%5D=%22NoVal%22&constants%5BWC%5D=%22majority%22&constants%5BRC%5D=%22snapshot%22&constants%5BMaxStmts%5D=2&constants%5BRouter%5D=%7Br1%7D&hiddenVars=epoch%2CcommitIndex%2Clsn%2Coverlap%2Caborted). The main specification resides in [`MultiShardTxn.tla`](MultiShardTxn.tla), which models MongoDB's distributed transaction commit protocol. 

At a high level, the protocol modeled here can be viewed as a distributed transaction protocol implementing snapshot isolation. This is acheived this by running a two-phase commit style protocol against shards that individually implement snapshot isolated key-value stores. In practice, each shard is operated as a MongoDB replica set, providing fault tolerance for each shard.

The participants of the protocol consist of *clients*, *routers*, and *shards*. Routers handle incoming transaction operations issued to them by clients, and there may be many of them. Routers forward these transaction operations to shards in an interactive fashion, based on routing logic determined by the "catalog". Essentially, the catalog is a mapping from keys to shards i.e., it determines the placement of keys in a collection across a sharded cluster. Individual shards are responsible for executing transaction operations as they receive them, and reporting their responses back to a router. If errors or conflicts occur at local shards, this is reported back to the router, which can initiate a global abort process. 

After issuing the last operation of a transaction, and if all operations have completed successfully, a client may then issue a transaction commit operation, prompting the router to initiate a two-phase commit procedure. The router does this by handing off this responsbility to a *coordinator* shard, which coordinates the two-phase ommit process across all shards. That is, the coordinator sends *prepare* messages to all participant shards that were involved in the transaction, waits for affirmative responses from all shards, and then makes a decision to commit the transaction, sending out a message indicating this to all shards, which can then individually commit the transaction on that shard.

## Interaction with the Catalog and Migrations

Within a sharded cluster, the placement of keys in a collection on shards is determined by the "catalog", which stores information about which keys are "owned" by which shards. 

The current specification [models a static catalog](https://github.com/muratdem/MDBTLA/blob/dc5fc9acdfc2f143c183b52558e4646402e0d80c/MultiShardTxn/MultiShardTxn.tla#L121), as a mapping from keys to shards that is fixed once at initialization and never changes. Eventually our goal is to model a dynamic catalog, which will require considerations around how the protocol interacts with chunk migation, shard versioning, etc.

TODO.

## Model Checking

Currently, we check a core, high level safety property, which is that the overall transaction protocol implements [snapshot isolation](https://github.com/muratdem/MDBTLA/blob/3989af405310e74dee45a702be9831e0c6dad7ab/MultiShardTxn/MultiShardTxn.tla#L553-L554) correctly. This is done using a global history of transaction operations maintained in the [`ops`](https://github.com/muratdem/MDBTLA/blob/21d23fc50d391629e0a4d7a31c2cfc851c024a62/MultiShardTxn/MultiShardTxn.tla#L85-L86) map. We have so far checked small models for correctness e.g. 2 keys, 2 shards, a single router, and ~2-3 operations max per transaction:

```
Keys = {k1, k2}
TxId = {t1, t2}
Shard = {s1, s2}
Router = {r1}
MaxStmts = 3
```
We verify snapshot isolation using the [client-centric isolation model of Crooks](https://www.cs.cornell.edu/lorenzo/papers/Crooks17Seeing.pdf), and utilizing the [formalization of this in TLA+](https://github.com/muratdem/MDBTLA/blob/3989af405310e74dee45a702be9831e0c6dad7ab/MultiShardTxn/ClientCentric.tla) by [Soethout](https://link.springer.com/chapter/10.1007/978-3-030-67220-1_4).


## Other specs in this directory

`MDB.tla`: This spec models the replica set as a single log at a high level

`ClientCentric.tla`: (from Tim Soethout's work) We use this to be able to properly check transactions for snapshot isolation semantics.


