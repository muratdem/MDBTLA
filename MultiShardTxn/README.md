# README

The goal of this specification is to show transactions on a sharded cluster.

Open the current model in web explorer here: [MultiShardTxnTLA](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fmuratdem%2FMDBTLA%2Fmain%2FMultiShardTxn%2FMultiShardTxn.tla&constants%5BKeys%5D=%7Bk1%2Ck2%7D&constants%5BTxId%5D=%7Bt1%2Ct2%7D&constants%5BShard%5D=%7Bs1%2Cs2%7D&constants%5BNoValue%5D=%22NoVal%22&constants%5BWC%5D=%22majority%22&constants%5BRC%5D=%22linearizable%22&constants%5BMaxStmts%5D=2&hiddenVars=epoch%2CcommitIndex%2Clsn%2Coverlap%2Caborted).


## Main specs in this directory

`MDB.tla`: This spec models the replicaset as a single log and specificies actions for IncreaseReadIndexAndOrCommitIndex and TruncateLog, which regulate the replication and failure. Note that the write action and read action are not exercised from this spec; those come in the `MDBProps.tla` and `MDBLinearizability.tla` specs that instantiate this spec, and use it to check consistency.

`ClientCentric.tla`: (from Tim Soethout's work) We use this to be able to properly check transactions for snapshot isolation semantics.

### Model checking result


