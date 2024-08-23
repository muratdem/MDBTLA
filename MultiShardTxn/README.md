# Formal Specification of Distributed Transactions in MongoDB

This directory contains formal specifications that model the high level behavior of the [distributed, cross-shard transactions protocol in MongoDB](https://github.com/mongodb/mongo/blob/master/src/mongo/db/s/README_sessions_and_transactions.md#transactions). You can interact with some models of the current specification on the web here: 

- [MultiShardTxn (2 keys, 2 transactions, 2 shards)](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fmuratdem%2FMDBTLA%2Fmain%2FMultiShardTxn%2FMultiShardTxn.tla&constants%5BKeys%5D=%7Bk1%2Ck2%7D&constants%5BTxId%5D=%7Bt1%2Ct2%7D&constants%5BShard%5D=%7Bs1%2Cs2%7D&constants%5BNoValue%5D=%22NoVal%22&constants%5BWC%5D=%22majority%22&constants%5BRC%5D=%22snapshot%22&constants%5BMaxOpsPerTxn%5D=2&constants%5BRouter%5D=%7Br1%7D&hiddenVars=epoch%2CcommitIndex%2Clsn%2Coverlap%2Caborted&explodedConstantExpr=Shard) 
- [MultiShardTxn (3 keys, 3 transactions, 2 shards)](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fmuratdem%2FMDBTLA%2Fmain%2FMultiShardTxn%2FMultiShardTxn.tla&constants%5BKeys%5D=%7Bk1%2Ck2%2Ck3%7D&constants%5BTxId%5D=%7Bt1%2Ct2%2Ct3%7D&constants%5BShard%5D=%7Bs1%2Cs2%7D&constants%5BNoValue%5D=%22NoVal%22&constants%5BWC%5D=%22majority%22&constants%5BRC%5D=%22snapshot%22&constants%5BMaxOpsPerTxn%5D=2&constants%5BRouter%5D=%7Br1%7D&hiddenVars=epoch%2CcommitIndex%2Clsn%2Coverlap%2Caborted&explodedConstantExpr=Shard) 

The main specification resides in [`MultiShardTxn.tla`](MultiShardTxn.tla), which models MongoDB's distributed, multi-document transaction protocol. 

## Protocol Specification

At a high level, the protocol modeled here can be viewed as a distributed transaction protocol implementing snapshot isolation. This is acheived this by running a two-phase commit style protocol against shards that individually implement snapshot isolated key-value stores, while also maintaining causally consistent timestamps across the cluster which are used to manage ordering and visibility between transactions. In practice, each shard is operated as a MongoDB replica set, providing fault tolerance for each shard. 

The main logical participants of the protocol consist of *client*, *router*, and *shard* roles, and currently utilizes the following constant parameters:
-  `Shard`: a fixed set of shards. 
-  `Router`: a set of routers. 
-  `TxId`: a set of unique transaction ids. 
-  `Key`: a set of collection keys. 
-  `RC`: a global read concern parameter, which sets the read concern setting for all transactions (at either `"local"` or `"snapshot"`).

### Routers

Routers, of which there may be several, handle incoming transaction operations issued to them by clients. In the current model, clients are not represented explicitly, but we represent a client operation occurring at the router in the [router specific actions](https://github.com/muratdem/MDBTLA/blob/a973471f74ebaf8b20150bbf97583a51bc82162d/MultiShardTxn/MultiShardTxn.tla#L575-L576) for starting or continuing a transaction with a specified operation type and key.

Routers forward transaction operations to shards in an interactive fashion, and individual shards are responsible for executing transaction operations as they receive them, reporting their responses back to a router. If errors or conflicts occur at local shards, this is also reported back to the router, which can initiate a global abort process. In the current specification, we represent this messaging as an RPC based mechanism. Routers push new operations onto a [queue](https://github.com/muratdem/MDBTLA/blob/a973471f74ebaf8b20150bbf97583a51bc82162d/MultiShardTxn/MultiShardTxn.tla#L43-L45) that is maintained at each shard, for each transaction id, and shards process new operations from this queue one at a time. That is, routers [wait until a shard](https://github.com/muratdem/MDBTLA/blob/a973471f74ebaf8b20150bbf97583a51bc82162d/MultiShardTxn/MultiShardTxn.tla#L296-L298) has processed a transaction operation before sending the next one, in an effort to simulate a synchronous RPC semantics. We may consider generalizing this messaging semantics in future (e.g. to a more asynchronous, out-of-order model).  

After issuing the last operation of a transaction, if all operations have completed successfully, a client may then issue a transaction commit operation, prompting the router to initiate a two-phase commit procedure across all participant shards. The router may does this by handing off responsbility to a *coordinator* shard, which coordinates the two-phase commit process across all participant shards. Our specification also currently models a few special cases where full 2PC can be bypassed, allowing thee router to go ahead and send commit operations directly to each shard e.g. for [read-only or single shard transactions](https://github.com/muratdem/MDBTLA/blob/a973471f74ebaf8b20150bbf97583a51bc82162d/MultiShardTxn/MultiShardTxn.tla#L578-L579).


### Shards

Each shard passively waits for transaction operations to be sent from the router, and processes these incrementally by pulling the ops off of its incoming request queue for each transaction at that shard. After [starting a transaction](https://github.com/muratdem/MDBTLA/blob/a973471f74ebaf8b20150bbf97583a51bc82162d/MultiShardTxn/MultiShardTxn.tla#L584) on a shard in response to the first statement of a transaction, it [processes different types of operations accordingly](https://github.com/muratdem/MDBTLA/blob/a973471f74ebaf8b20150bbf97583a51bc82162d/MultiShardTxn/MultiShardTxn.tla#L585-L587) as the transaction executes. This includes, for example, the behavior to abort if a [write conflict occurs](https://github.com/muratdem/MDBTLA/blob/3bce495f360b9a433a7e708159acf39d8a039b87/MultiShardTxn/MultiShardTxn.tla#L447-L448) on that shard.


When a router initiates two-phase commit for a transaction, as described above, it hands off this responsibility to a coordinator shard, which is responsible for coordinating the commit process across all participant shards. The coordinator shard then sends *prepare* messages to all participant shards that were involved in the transaction, waits for affirmative responses from all shards, and then makes a decision to commit the transaction, sending out a message indicating this to all shards, which can then individually commit the transaction on that shard. Two-phase commit messages are then [exhanged between coordinator and participant](https://github.com/muratdem/MDBTLA/blob/a973471f74ebaf8b20150bbf97583a51bc82162d/MultiShardTxn/MultiShardTxn.tla#L588-L594) shards to drive the transaction to commit.

### Modeling the Storage/Replication Layer

The current model aims to model the storage/replication layer (e.g. including abstract WiredTiger semantics) at each shard in a modular way. This is done by having `MDB` encapsulate most of the storage/replication specific logic, and [instantiating one of these modules per shard](https://github.com/muratdem/MDBTLA/blob/2fd5ddc7f4767aace7cfc4bd7ff19b44027de530/MultiShardTxn/MultiShardTxn.tla#L99-L109).

The composition as currently defined breaks these boundaries a bit, but essentially the interface to the MDB instance at each shard is captured in [these wrapper definitions](https://github.com/muratdem/MDBTLA/blob/2fd5ddc7f4767aace7cfc4bd7ff19b44027de530/MultiShardTxn/MultiShardTxn.tla#L178-L238). Ideally we would like to define MDB as a completely independent state machine that is composed synchronously with `MultiShardTxn` via joint actions, but in practice there are [some difficulties](https://groups.google.com/g/tlaplus/c/77DR8ngQllo) with defining this cleanly.

### Cluster Timestamp Semantics

Timestamps are used in the sharded transaction protocol to manage ordering and visibility of transactions across the cluster. Timestamps are used in global transaction *read timestamps*, and also for *prepare* and *commit* timestamps in the two-phase commit protocol. We currently try to model things in as general a way as possible, so we allow routers, for example, to [select any read timestamp](https://github.com/muratdem/MDBTLA/blob/11f864d9724f4dd01e204b55f48ebd40e8997eb5/MultiShardTxn/MultiShardTxn.tla#L586) within the range of current timestamp history, even though the implementation may select timestamps more strictly e.g. based on the latest cluster timestamp it knows about. 

Timestamp selection at shards occurs on prepare and commit (by the coordinator), and it should be the case that timestamps only need to satisfy a few conditions for correctness. First, commit timestamps on a local shard should increase monotonically, to give a total order of committed transactions on that shard. This can be enforced by [choosing the "next timestamp" ](https://github.com/muratdem/MDBTLA/blob/776b545ac33df8e2bef5bab49d7ce4247e29a35d/MultiShardTxn/MDB.tla#L129-L130) appropriately. A key property for snapshot isolation correctness seems to be that if a transaction reads at a timestamp T, then it must be true that no transaction ever commits at a timestamp < T in future i.e. so that the read knows about the "consistent" history of transactions visible up to that timestamp. 

Technically, this ordering criterion should only be true for sets of causally related transactions, since, for example, non-conflicting transactions may run concurrently on different sets of shards and commit, for example, at the same timestamp, or one commits behind the other, which should be acceptable if their read/write sets are disjoint.


### Interaction with the Catalog and Migrations

Within a sharded cluster, the placement of keys in a collection on shards is determined by the "catalog", which stores information about which keys are "owned" by which shards. 

The current specification [models a static catalog](https://github.com/muratdem/MDBTLA/blob/dc5fc9acdfc2f143c183b52558e4646402e0d80c/MultiShardTxn/MultiShardTxn.tla#L121), as a mapping from keys to shards that is fixed once at initialization and never changes. Eventually our goal is to model a dynamic catalog, which will require considerations around how the protocol interacts with chunk migration, shard versioning, etc. To extend the current specification to handle modifications of the catalog (i.e. placement changes) we expect we will need to expand the model to give each router and shard its own cached view of the catalog, and work towards a specification of the shard versioning protocol which handles proper handling of invalidation of this cached information across the cluster. 

Currently we have also added [router specific catalog cache state](https://github.com/muratdem/MDBTLA/blob/3c144133c857f56fefe32b76ba2b5ae3f2d0d272/MultiShardTxn/MultiShardTxn.tla#L40-L41), but this is [initialized once](https://github.com/muratdem/MDBTLA/blob/3c144133c857f56fefe32b76ba2b5ae3f2d0d272/MultiShardTxn/MultiShardTxn.tla#L136-L137) and never modified.

### Note on Write Concern and Rollback

Note that we don't really model replication rollback and the semantics of different write concerns in the current model. The thought is that transactions that commit at `w:1` may abort, and so provide no semantic guarantees to clients. Also, if a transaction reads at a "local" snapshot when it starts, transaction commit at `w:majority` will require some write to commit on that shard after its timestamp ,so successful commit impies all data it read must have been majority committed (i.e. the speculative majority notion). So, we don't represent the case where a transaction reads some data that is then later rolled back.

## Checking Isolation Guarantees

Currently, we check some high level isolation safety properties of the transaction protocol specification. In MongoDB, consistency/isolation of a multi-document transaction is [determined by its read/write concern parameters](https://www.mongodb.com/docs/manual/core/transactions/), so we try to reflect those settings in our model and check them against standard isolation levels. 

Essentially, MongoDB provides associated guarantees for a transaction only if it commits at `w:majority`, so in practice it is the selection of `readConcern` that determines the transaction's consistency semantics. Furthermore, due to the implementation of [*speculative majority*](https://github.com/mongodb/mongo/blob/2aaaa4c0ca6281088d766def53e86b01c99a8dba/src/mongo/db/repl/README.md#read-concern-behavior-within-transactions), "local" and "majority" read concern behave in the same way during establishment of the transaction on each shard (i.e. they don't read from a consistent timestamp across shards). So, we focus on two distinct classes of guarantees:

1. `{readConcern: "snapshot", writeConcern: "majority"}`
2. `{readConcern: "local"/"majority", writeConcern: "majority"}`

where we expect (1) to satisfy [snapshot isolation](https://jepsen.io/consistency/models/snapshot-isolation) and (2) to satisfy [repeatable reads](https://jepsen.io/consistency/models/repeatable-read). 

Note that we expect (2) to satisfy repeatable reads but not snapshot isolation, since transactions will essentially execute on each shard (locally) at snapshot isolation, but they may not read from a consistent snapshot across shards. For example, you can see a snapshot violation when running at read concern "local" [here](https://github.com/muratdem/MDBTLA/blob/70c370f87066740e485a4d8b2cd5bccd84e9fd2f/MultiShardTxn/cexs/snapshot_violation_at_local.txt). Clearly, we expect repeatable reads to be satisfied, though, since having snapshot isolation locally at each shard should imply read-committed semantics and repeatable reads with respect to a particular key (since SI provides repeatable reads). That is, repeatable reads should permit reads of different keys in a transaction to [read from different snapshots](https://github.com/muratdem/MDBTLA/blob/70c370f87066740e485a4d8b2cd5bccd84e9fd2f/MultiShardTxn/ClientCentricTests.tla#L115-L131), as long as each read of the same key reads from a consistent snapshot. 


We verify snapshot isolation using the [client-centric isolation model of Crooks](https://www.cs.cornell.edu/lorenzo/papers/Crooks17Seeing.pdf), and utilizing the [formalization of this in TLA+](https://github.com/muratdem/MDBTLA/blob/3989af405310e74dee45a702be9831e0c6dad7ab/MultiShardTxn/ClientCentric.tla) by [Soethout](https://link.springer.com/chapter/10.1007/978-3-030-67220-1_4). To check isolation, we use a global history of transaction operations maintained in the [`ops`](https://github.com/muratdem/MDBTLA/blob/21d23fc50d391629e0a4d7a31c2cfc851c024a62/MultiShardTxn/MultiShardTxn.tla#L85-L86) map. The formal definitions of [snapshot isolation](https://github.com/muratdem/MDBTLA/blob/736182575d96acdf9961504b5daf28900671def6/MultiShardTxn/ClientCentric.tla#L177-L178) and [repeatable reads](https://github.com/muratdem/MDBTLA/blob/736182575d96acdf9961504b5daf28900671def6/MultiShardTxn/ClientCentric.tla#L208) in this model are given in the [`ClientCentric.tla`](ClientCentric.tla) file. You can also see some concrete isolation tests defined in [`ClientCentricTests.tla`](ClientCentricTests.tla).

So far we have checked small models for correctness, using the `MaxOpsPerTxn` parameter and `StateConstraint` constraint to bound the maximum number of operations run by each transaction. For example, we have checked models for `"snapshot"` read concern:

| Constants | Symmetry | Invariant | Time | States | Depth | Error |
|------| ------|------|------|------|------|------|
| <ul><li>`Keys={k1, k2}`</li><li>`TxId={t1, t2}`</li><li> `Router={r1}`</li> <li> `MaxOpsPerTxn=3`</li> <li> `RC="snapshot"`</li>  </ul>| `Symmetry` | `SnapshotIsolation` | ~10 min | 35,002,143 | 37 |  None |
| <ul><li>`Keys={k1, k2, k3}`</li><li>`TxId={t1, t2}`</li><li> `Router={r1}`</li> <li> `MaxOpsPerTxn=3`</li> <li> `RC="snapshot"`</li>  </ul> | `Symmetry` | `SnapshotIsolation` | ~1h | 139,659,282 | 37 | None |

 and for `"local"` read concern:

| Constants | Symmetry | Invariant | Time | States | Depth | Error |
|------| ------|------|------|------|------|------|
| <ul><li>`Keys={k1, k2}`</li><li>`TxId={t1, t2}`</li><li> `Router={r1}`</li> <li> `MaxOpsPerTxn=3`</li> <li> `RC="local"`</li>  </ul>| `Symmetry` | `RepeatableReadIsolation` | ~20 min | 34,020,934 | 37 |  None |
| <ul><li>`Keys={k1, k2, k3}`</li><li>`TxId={t1, t2}`</li><li> `Router={r1}`</li> <li> `MaxOpsPerTxn=3`</li> <li> `RC="local"`</li>  </ul> | `Symmetry` | `RepeatableReadIsolation` | - | - | 38 | None |

You can also use the `check.py` script to run model checking more easily for a specified set of model parameters. The default model used for this script is defined in `MultiShardTxn.config.json`, and you can override its settings from the command line. 

For example, to check `RepeatableReadIsolation` at `"local"` read concern, you can run something like the following command:

```bash
python3 check.py --tlc_jar /usr/local/bin/tla2tools.jar --constants "Keys={k1,k2,k3}" "Shard={s1,s2}" "MaxOpsPerTxn=3"  "RC=\"local\"" --invariants RepeatableReadIsolation --tlc_args "-workers 8 -cleanup -deadlock" 
```

## Other specifications in this directory

- `MDB.tla`: This spec models the replication/storage level at an abstract level.

- `ClientCentric.tla`: (from Tim Soethout's [work](https://github.com/cwi-swat/tla-ci)) We use this to be able to check transactions for snapshot isolation semantics.


