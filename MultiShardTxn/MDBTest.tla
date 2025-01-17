---- MODULE MDBTest ----
EXTENDS Sequences, Naturals, Util, TLC, MDB

\* Stores latest operation status for each operation of a transaction (e.g.
\* records error codes, etc.)
VARIABLE txnStatus

STATUS_OK == "OK"
STATUS_ROLLBACK == "WT_ROLLBACK"

\* 
\* Action wrappers for operations on the MDB instance.
\* 
\* This should more or less be the abstract transaction interface each shard
\* needs to consider when executing transactions that are part of distributed,
\* cross-shard transaction.
\* 

MDBTxnStart(tid, readTs, rc) == 
    \* Start the transaction on the MDB KV store.
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    /\ tid \notin ActiveTransactions
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = SnapshotKV(readTs, rc)]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, txnStatus>>
   
\* Writes to the local KV store of a shard.
MDBTxnWrite(tid, k, v) == 
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ tid \in ActiveTransactions
    \* Transactions always write their own ID as the value, to uniquely identify their writes.
    /\ v = tid
    /\ \/ /\ ~WriteConflictExists(tid, k)
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = UpdateSnapshot(tid, k, v)
          /\ UNCHANGED <<txnStatus>>
       \/ /\ WriteConflictExists(tid, k)
          \* If there is a write conflict, the transaction must roll back.
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_ROLLBACK]
          /\ UNCHANGED mtxnSnapshots
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch>>

\* Reads from the local KV store of a shard.
MDBTxnRead(tid, k, v) ==
    \* Non-snapshot read aren't actually required to block on prepare conflicts (see https://jira.mongodb.org/browse/SERVER-36382). 
    /\ tid \in ActiveTransactions
    /\ ~PrepareConflict(tid, k)
    /\ v = TxnRead(tid, k)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["readSet"] = @ \cup {k}]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, txnStatus>>

MDBTxnCommit(tid, commitTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the shard oplog.
    /\ tid \in ActiveTransactions
    \* Must be greater than the newest known commit timestamp.
    /\ {mlog[i].ts : i \in DOMAIN mlog} # {} => commitTs > Max({mlog[i].ts : i \in DOMAIN mlog})
    /\ mlog' = CommitTxnToLog(tid, commitTs)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = Nil]
    /\ UNCHANGED <<mepoch, mcommitIndex, txnStatus>>

MDBTxnPrepare(tid, prepareTs) == 
    /\ tid \in ActiveTransactions
    /\ ~mtxnSnapshots[tid]["prepared"]
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["prepared"] = TRUE]
    /\ mlog' = PrepareTxnToLog(tid, prepareTs)
    /\ UNCHANGED <<mcommitIndex, mepoch, txnStatus>>

MDBTxnAbort(tid) == 
    /\ tid \in ActiveTransactions
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = Nil]
    /\ UNCHANGED <<mlog, mcommitIndex, mepoch, txnStatus>>

vars == <<mlog, mcommitIndex, mepoch, mtxnSnapshots, txnStatus>>

Init == 
    /\ mlog = <<>>
    /\ mcommitIndex = 0
    /\ mepoch = 1
    /\ mtxnSnapshots = [t \in MTxId |-> Nil]
    /\ txnStatus = [t \in MTxId |-> STATUS_OK]

Timestamps == 1..4

Next == 
    \/ \E tid \in MTxId, readTs \in Timestamps : MDBTxnStart(tid, readTs, RC)
    \/ \E tid \in MTxId, k \in Keys, v \in Values : MDBTxnWrite(tid, k, v)
    \/ \E tid \in MTxId, k \in Keys, v \in (Values \cup {NoValue}) : MDBTxnRead(tid, k, v)
    \/ \E tid \in MTxId, commitTs \in Timestamps : MDBTxnCommit(tid, commitTs)
    \* \/ \E tid \in MTxId, prepareTs \in Timestamps : MDBTxnPrepare(tid, prepareTs)
    \/ \E tid \in MTxId : MDBTxnAbort(tid)


Symmetry == Permutations(Keys) \union Permutations(Values) \union Permutations(MTxId)
StateConstraint == Len(mlog) <= 3

\* Bait1 == ~(Len(mlog) = 3 /\ \E tid \in MTxId : txnStatus[tid] = STATUS_ROLLBACK)
Bait1 == ~(\E tid \in MTxId : txnStatus[tid] = STATUS_ROLLBACK)

======================
