---- MODULE MDBTest ----
EXTENDS Sequences, Naturals, Util, TLC, MDB

\* 
\* Action wrappers for operations on the MDB instance.
\* 
\* This should more or less be the abstract transaction interface each shard
\* needs to consider when executing transactions that are part of distributed,
\* cross-shard transaction.
\* 

ShardMDBTxnStart(tid, readTs, rc) == 
    \* Start the transaction on the MDB KV store.
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = SnapshotKV(readTs, rc)]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch>>
   
\* Writes to the local KV store of a shard.
ShardMDBTxnWrite(tid, k) == 
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ tid \in ActiveTransactions
    /\ ~WriteConflictExists(tid, k)
    \* Update the transaction's snapshot data.
    /\ mtxnSnapshots' = UpdateSnapshot(tid, k, tid)
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch>>

\* Reads from the local KV store of a shard.
ShardMDBTxnRead(tid, k) ==
    \* Non-snapshot read aren't actually required to block on prepare conflicts (see https://jira.mongodb.org/browse/SERVER-36382). 
    /\ tid \in ActiveTransactions
    /\ RC = "snapshot" => ~PrepareConflict(tid, k)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["readSet"] = @ \cup {k}]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch>>

ShardMDBTxnCommit(tid, commitTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the shard oplog.
    /\ tid \in ActiveTransactions
    /\ mlog' = CommitTxnToLog(tid, commitTs)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = Nil]
    /\ UNCHANGED <<mepoch, mcommitIndex>>

ShardMDBTxnPrepare(tid, prepareTs) == 
    /\ tid \in ActiveTransactions
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["prepared"] = TRUE]
    /\ mlog' = PrepareTxnToLog(tid, prepareTs)
    /\ UNCHANGED <<mcommitIndex, mepoch>>

ShardMDBTxnAbort(tid) == 
    /\ tid \in ActiveTransactions
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = Nil]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch>>

vars == <<mlog, mcommitIndex, mepoch, mtxnSnapshots>>

Init == 
    /\ mlog = <<>>
    /\ mcommitIndex = 0
    /\ mepoch = 1
    /\ mtxnSnapshots = [t \in MTxId |-> Nil]

Timestamps == 1..3

Next == 
    \/ \E tid \in MTxId, readTs \in Timestamps : ShardMDBTxnStart(tid, readTs, RC)
    \/ \E tid \in MTxId, k \in Keys : ShardMDBTxnWrite(tid, k)
    \/ \E tid \in MTxId, k \in Keys : ShardMDBTxnRead(tid, k)
    \/ \E tid \in MTxId, commitTs \in Timestamps : ShardMDBTxnCommit(tid, commitTs)
    \/ \E tid \in MTxId, prepareTs \in Timestamps : ShardMDBTxnPrepare(tid, prepareTs)
    \/ \E tid \in MTxId : ShardMDBTxnAbort(tid)


Symmetry == Permutations(Keys) \union Permutations(Values) \union Permutations(MTxId)
StateConstraint == Len(mlog) <= 3

Bait1 == Len(mlog) < 4

======================
