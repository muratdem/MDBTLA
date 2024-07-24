# Formal Modeling of MongoDB Distributed Transactions

The goal of this specification is to model the high level behavior of the [distributed, cross-shard transactions protocol in MongoDB](https://github.com/mongodb/mongo/blob/master/src/mongo/db/s/README_sessions_and_transactions.md#transactions). You can interact with the current model on the web here: [MultiShardTxn](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fmuratdem%2FMDBTLA%2Fmain%2FMultiShardTxn%2FMultiShardTxn.tla&constants%5BKeys%5D=%7Bk1%2Ck2%7D&constants%5BTxId%5D=%7Bt1%2Ct2%7D&constants%5BShard%5D=%7Bs1%2Cs2%7D&constants%5BNoValue%5D=%22NoVal%22&constants%5BWC%5D=%22majority%22&constants%5BRC%5D=%22linearizable%22&constants%5BMaxStmts%5D=2&constants%5BRouter%5D=%7Br1%7D&hiddenVars=epoch%2CcommitIndex%2Clsn%2Coverlap%2Caborted). The main specification resides in [`MultiShardTxn.tla`](MultiShardTxn.tla), which models the general behavior of MongoDB's distributed transaction commit protocol. 

At a high level, the MongoDB protocol can be viewed as a distributed transaction protocol implementation that satisfies snapshot isolation guarantees. The protocol achieves this by executing a two-phase commit style protocol against shards that individually implement snapshot isolated key-value stores. In practice, each shard is run as a MongoDB replica set, providing fault tolerance for shard transaction participants.

The overall protocol consists of *clients*, *routers*, and *shards*. There may be multiple routers, which handle incoming transaction operations issued to them by clients. Routers forward these transaction operations to shards in an interactive fashion, based on routing logic determined by the "catalog". Essentially, the catalog is a mapping from keys to shards i.e., it determines the placement of keys in a collection across a sharded cluster. Individual shards are responsible for executing transaction operations as they receive them, and reporting their responses back to a router. If errors or conflicts occur at local shards, this is reported back to the router, which can initiate a global abort process. 

If all operations of a transaction finish, a client may then issue a commit operation, prompting the router to initiate a two-phase commit procedure, which it does by handing off this responsbility to a *coordinator* shard, which coordinates the two-phase ommit process across all shards. That is, the coordinator sends *prepare* messages to all participant shards that were involved in the transaction, waits for affirmative responses from all shards, and then makes a decision to commit the transaction, sending out a message indicating this to all shards, which can then individually commit the transaction on that shard.

## Interaction with the Catalog and Migrations

Within a sharded cluster, the placement of keys in a collection on shards is determined by the "catalog", which in practice stores information about which shards different ranges of keys live. 

The current spec models a static catalog, as a mapping from keys to shards that is fixed once at initialization and never changes. Eventually our goal is to model a dynamic catalog, which will require considerations around how the protocol interacts with chunk migation, shard versioning, etc.

TODO.

## Other specs in this directory

`MDB.tla`: This spec models the replica set as a single log at a high level

`ClientCentric.tla`: (from Tim Soethout's work) We use this to be able to properly check transactions for snapshot isolation semantics.


