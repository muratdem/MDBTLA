# Formal Modeling of MongoDB Distributed Transactions

The goal of this specification is to model the high level behavior of the distributed, cross-shard transactions protocol in MongoDB. You can interact with the current model on the web here: [MultiShardTxn](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fmuratdem%2FMDBTLA%2Fmain%2FMultiShardTxn%2FMultiShardTxn.tla&constants%5BKeys%5D=%7Bk1%2Ck2%7D&constants%5BTxId%5D=%7Bt1%2Ct2%7D&constants%5BShard%5D=%7Bs1%2Cs2%7D&constants%5BNoValue%5D=%22NoVal%22&constants%5BWC%5D=%22majority%22&constants%5BRC%5D=%22linearizable%22&constants%5BMaxStmts%5D=2&constants%5BRouter%5D=%7Br1%7D&hiddenVars=epoch%2CcommitIndex%2Clsn%2Coverlap%2Caborted).

The main specification resides in `MultiShardTxn.tla`, which models the general behavior of MongoDB's distributed transaction commit protocol. At a high level, this protocol can be viewed as an implementation of distributed transactions satisfying snapshot isolation. The protocol achieves this by executing a two-phase commit style protocol against shards that individually implement snapshot isolated key-value stores. In practice, each shard is made fault tolerant by running as a MongoDB replica set.

The general protocol consists of *clients*, *router*, and *shard* participants. In general, there may be multiple routers, which handle incoming transaction operations issued to them by clients. Routers forward these transaction operations to shards in an interactive fashion, based on routing logic determined by the `catalog`. Essentially, this is a mapping from keys to shards, which determines the placement of data across the sharded cluster. Individual shards are responsible for executing transaction operations as it executes, and reporting their responses back to a router. If errors or conflicts occur at local shards, this is reported back to the router, which can initiate a global abort process. 

If the transaction operations finish and a client issues a commit operation, the router then initiates a two-phase commit procedure by handing off this responsbility to a *coordinator* shard, which is then responsible for coordinating the commit process across all shards. That is, it sends *prepare* messages to all participant shards that were involved in the transaction, waits for affirmative responses from all shards, and then makes a decision to commit the transaction, sending out a message indicating this to all shards, which can then individually commit the transaction on that shard.

## Interaction with the Catalog and Migrations

Within a sharded cluster, the placement of keys in a collection on shards is determined by the "catalog", which in practice stores information about which shards different ranges of keys live. 

The current spec models a static catalog, as a mapping from keys to shards that is fixed once at initialization and never changes. Eventually our goal is to model a dynamic catalog, which will require considerations around how the protocol interacts with chunk migation, shard versioning, etc.

TODO.

## Other specs in this directory

`MDB.tla`: This spec models the replica set as a single log at a high level

`ClientCentric.tla`: (from Tim Soethout's work) We use this to be able to properly check transactions for snapshot isolation semantics.


