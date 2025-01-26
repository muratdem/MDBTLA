---- MODULE MDBTest ----
EXTENDS Sequences, Naturals, Util, TLC, MDB

\* Stores latest operation status for each operation of a transaction (e.g.
\* records error codes, etc.)
VARIABLE txnStatus

\* Tracks the global "stable timestamp" within the storage layer.
VARIABLE stableTs

STATUS_OK == "OK"
STATUS_ROLLBACK == "WT_ROLLBACK"

\* 
\* Action wrappers for operations on the MDB WiredTiger/storage instance.
\* 
\* This should more or less be the abstract transaction interface each shard
\* needs to consider when executing transactions that are part of distributed,
\* cross-shard transaction.
\* 

StartTransaction(tid, readTs, rc) == 
    \* Start the transaction on the MDB KV store.
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    /\ tid \notin ActiveTransactions
    /\ ~\E i \in DOMAIN mlog : mlog[i].tid = tid \* don't re-use transactions ids.
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = SnapshotKV(readTs, rc)]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, txnStatus, stableTs>>
   
\* Writes to the local KV store of a shard.
TransactionWrite(tid, k, v) == 
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    \* Transactions always write their own ID as the value, to uniquely identify their writes.
    /\ v = tid
    /\ \/ /\ ~WriteConflictExists(tid, k)
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = UpdateSnapshot(tid, k, v)
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
       \/ /\ WriteConflictExists(tid, k)
          \* If there is a write conflict, the transaction must roll back.
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_ROLLBACK]
          /\ UNCHANGED mtxnSnapshots
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, stableTs>>

\* Reads from the local KV store of a shard.
TransactionRead(tid, k, v) ==
    \* Non-snapshot read aren't actually required to block on prepare conflicts (see https://jira.mongodb.org/browse/SERVER-36382). 
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    /\ ~PrepareConflict(tid, k)
    /\ v = TxnRead(tid, k)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["readSet"] = @ \cup {k}]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, stableTs>>

\* Delete a key.
TransactionRemove(tid, k) ==
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    /\ \/ /\ ~WriteConflictExists(tid, k)
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["writeSet"] = @ \cup {k}, 
                                                    ![tid].data[k] = NoValue]
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
       \/ /\ WriteConflictExists(tid, k)
          \* If there is a write conflict, the transaction must roll back.
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_ROLLBACK]
          /\ UNCHANGED mtxnSnapshots
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, stableTs>>

CommitTimestamps == {mlog[i].ts : i \in DOMAIN mlog}

CommitTransaction(tid, commitTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the shard oplog.
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    \* Must be greater than the newest known commit timestamp.
    /\ (ActiveReadTimestamps \cup CommitTimestamps) # {} => commitTs > Max(ActiveReadTimestamps \cup CommitTimestamps)
    /\ mlog' = CommitTxnToLog(tid, commitTs)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = Nil]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<mepoch, mcommitIndex, stableTs>>

CommitPreparedTransaction(tid, commitTs, durableTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the shard oplog.
    /\ commitTs = durableTs \* for now force these equal.
    /\ tid \in ActiveTransactions
    /\ tid \in PreparedTransactions
    \* Must be greater than the newest known commit timestamp.
    /\ (ActiveReadTimestamps \cup CommitTimestamps) # {} => commitTs > Max(ActiveReadTimestamps \cup CommitTimestamps)
    /\ mlog' = CommitTxnToLogWithDurable(tid, commitTs, durableTs)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = Nil]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<mepoch, mcommitIndex, stableTs>>

PrepareTransaction(tid, prepareTs) == 
    /\ tid \in ActiveTransactions
    /\ ~mtxnSnapshots[tid]["prepared"]
    /\ prepareTs > mtxnSnapshots[tid].ts
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["prepared"] = TRUE]
    /\ mlog' = PrepareTxnToLog(tid, prepareTs)
    /\ UNCHANGED <<mcommitIndex, mepoch, txnStatus, stableTs>>

AbortTransaction(tid) == 
    /\ tid \in ActiveTransactions
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = Nil]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, stableTs>>

SetStableTimestamp(ts) == 
    /\ stableTs' = ts
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, mtxnSnapshots, txnStatus>>

vars == <<mlog, mcommitIndex, mepoch, mtxnSnapshots, txnStatus, stableTs>>

Init == 
    /\ mlog = <<>>
    /\ mcommitIndex = 0
    /\ mepoch = 1
    /\ mtxnSnapshots = [t \in MTxId |-> Nil]
    /\ txnStatus = [t \in MTxId |-> STATUS_OK]
    /\ stableTs = 0

Timestamps == 1..5

Next == 
    \/ \E tid \in MTxId, readTs \in Timestamps : StartTransaction(tid, readTs, RC)
    \/ \E tid \in MTxId, k \in Keys, v \in Values : TransactionWrite(tid, k, v)
    \/ \E tid \in MTxId, k \in Keys, v \in (Values \cup {NoValue}) : TransactionRead(tid, k, v)
    \/ \E tid \in MTxId, k \in Keys : TransactionRemove(tid, k)
    \/ \E tid \in MTxId, commitTs \in Timestamps : CommitTransaction(tid, commitTs)
    \/ \E tid \in MTxId, commitTs, durableTs \in Timestamps : CommitPreparedTransaction(tid, commitTs, durableTs)
    \/ \E tid \in MTxId, prepareTs \in Timestamps : PrepareTransaction(tid, prepareTs)
    \/ \E tid \in MTxId : AbortTransaction(tid)
    \/ \E ts \in Timestamps : SetStableTimestamp(ts)


Symmetry == Permutations(Keys) \union Permutations(Values) \union Permutations(MTxId)
StateConstraint == Len(mlog) <= 2

\* Bait1 == ~(Len(mlog) = 3 /\ \E tid \in MTxId : txnStatus[tid] = STATUS_ROLLBACK)
\* Bait1 == ~(\E tid \in MTxId : txnStatus[tid] = STATUS_ROLLBACK)
\* Bait1 == ~(Len(mlog) = 3 /\ \E tid \in MTxId, k \in Keys : mtxnSnapshots[tid] # Nil /\ mtxnSnapshots[tid][k] = NoValue)
Bait1 == ~(Len(mlog) = 2)
BaitLevel == TLCGet("level") < 12
======================
