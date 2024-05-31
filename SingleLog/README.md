# README

The goal of this specification is to communicate/explore the precise consistency behavior of MongoDB under any given WC and RC setting. These behavior could be subtle due to leader takeover and log rollbacks.

This specification provides a high level model of a MongoDB replicaset. We model a replicaset's external exposed behavior by using just a single log. The single log still allows us to capture the important consistency behavior of the replicaset in high

Limitations: This version is for modeling a single replicaset. 
Since we use a single log, and since read preference does not make sense for single log, we don't model single log.

## Main specs in this directory

`MDB.tla`: This spec models the replicaset as a single log and specificies actions for IncreaseReadIndexAndOrCommitIndex and TruncateLog, which regulate the replication and failure. Note that the write action and read action are not exercised from this spec; those come in the `MDBProps.tla` and `MDBLinearizability.tla` specs that instantiate this spec, and use it to check consistency.

`MDBProps.tla`: This spec exercises write and read actions on MDB.tla which it extends, and checks strong-consistency (aka linearizability) and causal-consistency properties on the MDB.tla spec.  

`MDBLinearizability.tla`: This spec provides another way of linearizability testing of MDB spec. It imposes DictSpec as a property for LinSpec (which invokes MDB!Init and MDB!Next) to satisfy. In other words, we are claiming LinSpec refines DictSpec which lists all linearizable behavior of a simple dictionary writing values to keys and exposing results.

### Model checking result
When we model check MCMDBProps.cfg with RC:linearizability and WC:One, we get a counterexample to ReadYourWrites as expected. With WC:one, a write gets acknowledged, but later it gets rolled back, making the read returned an earlier value than what was written in the write operation.

