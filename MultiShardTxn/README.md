# README

The goal of this specification is to show transactions on a sharded cluster.


## Main specs in this directory

`MDB.tla`: This spec models the replicaset as a single log and specificies actions for IncreaseReadIndexAndOrCommitIndex and TruncateLog, which regulate the replication and failure. Note that the write action and read action are not exercised from this spec; those come in the `MDBProps.tla` and `MDBLinearizability.tla` specs that instantiate this spec, and use it to check consistency.

`ClientCentric.tla`: (from Tim Soethout's work) We use this to be able to properly check transactions for snapshot isolation semantics.

### Model checking result


