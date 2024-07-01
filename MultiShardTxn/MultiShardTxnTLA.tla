--------------------------- MODULE MultiShardTxnTLA ---------------------------------
(**************************************************************************)
(* Model of distributed, cross-shard transactions in MongoDB.             *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Util, TLC

CONSTANTS Keys, Values, NoValue, TxId, Shard, STMTS
CONSTANTS WC, RC

\* Instantiating ClientCentric enables us to check transaction isolation guarantees
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC == INSTANCE ClientCentric WITH Keys <- Keys, Values <- TxId \union {NoValue}          

\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)    
InitialState == [k \in Keys |-> NoValue]   

\* Set of in-progress transactions per-shard.
VARIABLES shardTxns

\* The router writes transaction operations for a shard to 'rlog', 
\* and shards scan this log to learn transaction ops that have been routed to them. 
VARIABLE rlog 

\* Prepare transaction messages sent from the router to participant shards.
VARIABLE msgsPrepare

\* Snapshot of data store for each transaction on each shard.
VARIABLE snapshotStore

\* For each shard and transaction, keeps track of whether that transaction aborted e.g.
\* due to a write conflict.
VARIABLE aborted 

\* For each shard, the set of transactions running concurrently with a given transaction.
VARIABLE overlap 

\* For each shard, the set of keys updated by a transaction running on that shard.
VARIABLE updated

\* For each shard and each transaction, a counter which tracks the 
\* current statement number of that transaction. 
VARIABLE lsn

VARIABLE rtxn

\* Each shard, for each transaction, maintains a record of whether it has been designated as
\* the 2PC coordinator for that transaction.
VARIABLE isCoordinator

\* For each transaction, the router tracks a list of shards that are participants in that
\* transaction. The router forwards this information to the coordinator when ready to commit.
\* By default, the first participant in this list is designated as the coordinator.
VARIABLE participants

\* Global history of all operations per transaction.
VARIABLE ops

\* We maintain a MongoDB "log" (i.e. a replica set/oplog abstraction) for each shard.
VARIABLE log 
VARIABLE commitIndex 
VARIABLE epoch

vars == << shardTxns, updated, overlap, rlog, aborted, log, commitIndex, epoch, rtxn, lsn, snapshotStore, ops, participants, isCoordinator, msgsPrepare >>

\* Instance of a MongoDB replica set log for a given shard.
ShardMDB(s) == INSTANCE MDB WITH log <- log[s], commitIndex <- commitIndex[s], epoch <- epoch[s]

Ops == {"read", "write", "commit"}
Entry == [k: Keys, op: Ops]
CreateEntry(k, op, s, coord) == [k |-> k, op |-> op, shard |-> s, coordinator |-> coord]
CreateCommitEntry(k, op, s, p) == [k |-> k, op |-> op, shard |-> s, participants |-> p]


Init ==
    /\ rlog = [s \in Shard |-> [t \in TxId |->  <<>>]]
    /\ shardTxns = [s \in Shard |-> {}]
    /\ rtxn = [t \in TxId |-> 0]
    /\ lsn = [s \in Shard |-> [t \in TxId |-> 0]]
    /\ snapshotStore = [s \in Shard |-> [t \in TxId |-> [k \in Keys |-> NoValue]]]
    /\ updated = [s \in Shard |-> [t \in TxId |-> {}]]
    /\ overlap = [s \in Shard |-> [t \in TxId |-> {}]]
    /\ ops = [s \in TxId |-> <<>>]
    /\ aborted = [s \in Shard |-> [t \in TxId |-> FALSE]]
    /\ log = [s \in Shard |-> <<>>]
    /\ commitIndex = [s \in Shard |-> 0]
    /\ epoch = [s \in Shard |-> 1]
    /\ participants = [t \in TxId |-> <<>>]
    /\ isCoordinator = [s \in Shard |-> [t \in TxId |-> FALSE]]
    /\ msgsPrepare = {}

\* Router handles a new transaction operation that is routed to the appropriate shard.
RouterTxnOp(s, tid, k, op) == 
    \* TODO: Router selects a specific cluster time to start the transaction at (?)
    \* TODO: How should we consider how an op gets routed to a shard based on key in the op (e.g. catalog routing info)?
    \* Route the new transaction op to the shard.
    \* TODO: Mark first op of transaction with 'coordinator' label.
    /\ op \in {"read", "write"}
    /\ rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateEntry(k, op, s, rtxn[tid] = 0))]
    /\ rtxn' = [rtxn EXCEPT ![tid] = rtxn[tid]+1]
    \* Update participants list if new participant joined the transaction.
    /\ participants' = [participants EXCEPT ![tid] = participants[tid] \o (IF s \in Range(participants[tid]) THEN <<>> ELSE <<s>>)]
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, log, commitIndex, epoch, lsn, snapshotStore, ops,isCoordinator, msgsPrepare >>

\* Router handles a transaction commit operation, which it forwards to the appropriate shard to initiate 2PC to
\* commit the transaction.
RouterTxnCommit(s, tid, k, op) == 
    \* TODO: Router handles commits any differently than other ops in terms of forwarding behavior?
    \* TODO: Send commit/coordinateCommit to the coordinator, and prepareTxn to all participant shards.
    /\ op = "commit"
    /\ participants[tid] # <<>>
    /\ s = participants[tid][1] \* Coordinator shard is the first participant in the list.
    /\ rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateCommitEntry(k, op, s, participants[tid]))]
    /\ rtxn' = [rtxn EXCEPT ![tid] = rtxn[tid]+1]
    \* Send prepare messages to all participant shards.
    /\ msgsPrepare' = msgsPrepare \cup {[shard |-> p, tid |-> tid, coordinator |-> s] : p \in Range(participants[tid])}
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, log, commitIndex, epoch, lsn, snapshotStore, ops, participants, isCoordinator >>

\*****************************************
\* Shard transaction operations.
\*****************************************

\* Shard starts a new transaction.
ShardTxnStart(s, tid) == 
    \* Transaction has new statements in the router log, and has not been started on this shard yet.
    /\ lsn[s][tid] < Len(rlog[s][tid])
    /\ tid \notin shardTxns[s]
    /\ lsn[s][tid] = 0 
    \* We don't advance to the next statement (lsn), but mark the transaction as
    \* having started on this shard, so transaction statements can now be processed.
    /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \union {tid}]
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    /\ snapshotStore' = [snapshotStore EXCEPT ![s][tid] = 
                            [k \in Keys |-> (CHOOSE read \in ShardMDB(s)!Read(k) : TRUE).value]]
    \* Update the record of which transactions are running concurrently with each other.
    /\ overlap' = [overlap EXCEPT ![s] = 
                    [t \in TxId |-> IF t = tid THEN shardTxns'[s] 
                                    ELSE IF t \in shardTxns'[s] THEN overlap[s][t] \union {tid} 
                                    ELSE overlap[s][t]]]
    /\ isCoordinator' = [isCoordinator EXCEPT ![s][tid] = rlog[s][tid][lsn[s][tid] + 1].coordinator]
    /\ UNCHANGED << lsn, updated, rlog, aborted, log, commitIndex, epoch, rtxn, ops, participants, msgsPrepare >>   

\* Shard processes a transaction read operation.
ShardTxnRead(s, tid, k) == 
    \* Transaction has new statements in the router log.
    /\ lsn[s][tid] < Len(rlog[s][tid])
    \* Transaction has started running on this shard.
    /\ tid \in shardTxns[s]
    /\ rlog[s][tid][lsn[s][tid] + 1].op = "read"
    /\ rlog[s][tid][lsn[s][tid] + 1].k = k
    \* Read the value of the key from the snapshot store, record the op, and 
    \* advance to the next transaction statement.
    /\ ops' = [ops EXCEPT ![tid] = Append( ops[tid], rOp(k, snapshotStore[s][tid][k]) )]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    /\ UNCHANGED << shardTxns, updated, overlap, rlog, aborted, log, commitIndex, epoch, rtxn, snapshotStore, participants, isCoordinator, msgsPrepare >>    

\* Shard processes a transaction write operation.
ShardTxnWrite(s, tid, k) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    /\ lsn[s][tid] < Len(rlog[s][tid])
    /\ rlog[s][tid][lsn[s][tid] + 1].op = "write"
    /\ rlog[s][tid][lsn[s][tid] + 1].k = k
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ \A t \in overlap[s][tid] \ {tid} : k \notin updated[s][t]
    \* Update the transaction's snapshot data, and advance to the next statement.
    /\ snapshotStore' = [snapshotStore EXCEPT ![s][tid][k] = tid]
    /\ updated' = [updated EXCEPT ![s][tid] = updated[s][tid] \union {k}]
    /\ ops' = [ops EXCEPT ![tid] = Append( ops[tid], wOp(k, tid) )]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    /\ UNCHANGED << shardTxns, log, commitIndex, aborted, epoch, overlap, rlog, rtxn, participants, isCoordinator, msgsPrepare >>

\* Shard processes a transaction write operation which encoutners a write conflict, triggering an abort.
ShardTxnWriteConflict(s, tid, k) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    /\ lsn[s][tid] < Len(rlog[s][tid])
    \* The write to this key conflicts with another concurrent transaction on this shard.
    /\ \E t \in overlap[s][tid] \ {tid} : k \in updated[s][t]
    /\ aborted' = [aborted EXCEPT ![s][tid] = TRUE]
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch, lsn, overlap, rlog, rtxn, updated, snapshotStore, ops, participants, isCoordinator, msgsPrepare >>

\* 
\* Shard processes a transaction commit operation, which triggers a 2PC to commit the transaction using this
\* shard as coordinator.
\* 
\* TODO: Do we need to explicitly track a "coordinator" identity for each transaction when transactions start?
\* 
ShardTxnCommit(s, tid) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    /\ lsn[s][tid] < Len(rlog[s][tid])
    /\ rlog[s][tid][lsn[s][tid] + 1].op = "commit"
    /\ isCoordinator[s][tid]
    \* TODO: Initiate 2PC to commit the transaction, then go ahead and commit it and
    \* update the local shard MongoDB instances state.
    \* Note: more accurately, we will wait to hear votes from participant shards, since 'prepare' messages should have been sent 
    \* to them by the router (?)
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch, lsn, overlap, rlog, rtxn, updated, aborted, snapshotStore, participants, isCoordinator, msgsPrepare, ops >>

Next == 
    \/ \E s \in Shard, t \in TxId, k \in Keys, op \in Ops: RouterTxnOp(s, t, k, op)
    \/ \E s \in Shard, t \in TxId, k \in Keys, op \in Ops: RouterTxnCommit(s, t, k, op)
    \/ \E s \in Shard, tid \in TxId: ShardTxnStart(s, tid)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnRead(s, tid, k)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWrite(s, tid, k)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWriteConflict(s, tid, k)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnCommit(s, tid)

Spec == Init /\ [][Next]_vars


        \* /\ WF_vars(Router)
        \* /\ \A self \in Shard : WF_vars(s(self))

\* TypeOK == \* type invariant
\*     /\ tx \subseteq TxId
\*     /\ updated \in [TxId -> SUBSET Keys]
\*     /\ \A t1,t2 \in TxId: t1 \in overlap[t2] => t2 \in overlap[t1] 

\* \* Snapshot isolation invariant
SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

\* \* Serializability would not be satisfied due to write-skew
\* Serialization == CC!Serializability(InitialState, Range(ops))

Symmetry == Permutations(TxId) \cup Permutations(Keys)

\* \* LogIndicesImpl == 1..4

\* \* CheckpointsImpl == LogIndicesImpl \cup {0}

\* \* EpochsImpl == 1..3

\* \* SpecificStateSpace ==
\* \*     /\ epoch < EpochMax

BaitLog == 
    /\ TRUE
    \* /\ \A s \in Shard, t \in TxId : Cardinality(overlap[s][t]) <= 1
    \* /\ \A s \in Shard, t \in TxId : aborted[s][t] = FALSE
    /\ msgsPrepare = {}
    \* /\ \A s \in Shard, t \in TxId : Len(rlog[s][t]) = 0
    \* /\ commitIndex < 5
    \* /\ Len(log) < 6
    
\* Alias == [
\*     log |-> log,
\*     commitIndex |-> commitIndex,
\*     readIndex |-> readIndex,
\*     epoch |-> epoch
\* ]
===========================================================================
