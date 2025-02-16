---- MODULE Storage ----
EXTENDS Sequences, Naturals, Integers, Util, TLC


\* 
\* Abstract model of single MongoDB node using WiredTiger storage instance.
\* 
\* This should more or less be the abstract transaction interface each shard
\* needs to consider when executing transactions that are part of distributed,
\* cross-shard transaction.
\* 
\* Status of each transaction operation can be "returned"/checked by a client
\* by checking the value of the 'txnStatus' variable after the execution of
\* an action/transition. This is a simple way to emulate the notion of
\* return/status codes in a standard programming-oriented API.
\* 



CONSTANT Node

CONSTANTS RC   \* read concern

CONSTANTS Keys, 
          MTxId,
          NoValue

CONSTANT Timestamps

WCVALUES == {"one", 
             "majority"}

RCVALUES == {"linearizable", 
             "snapshot", 
             "local",
             "available"}

LogIndices == Nat \ {0}

\* Make values the same as transaction IDs.
Values == MTxId

\* The result a read will have if no value can be found.
NotFoundReadResult == [
    mlogIndex |-> 0,
    value |-> NoValue
]

\* Log entries contain one key-value pair each, modeled as a record
LogEntries ==
    [
        key: Keys,
        value: Values
    ]

Logs == Seq(LogEntries)

Max(S) == CHOOSE x \in S : \A y \in S : x >= y


VARIABLE mlog
VARIABLE mcommitIndex

\* Stores snapshots for running transactions on the underlying MongoDB instance.
VARIABLE mtxnSnapshots

mvars == <<mlog, mcommitIndex, mtxnSnapshots>>

TypesOK ==
    /\ mlog \in Logs
    /\ mcommitIndex \in Nat

\* This operator initiates a write, adding it to the mlog.
WriteInit(key, value) ==
    /\ mlog' = Append(mlog, [
            key |-> key,
            value |-> value
       ])


\* For a given key, a read can be entirely defined by a value and a flag:
\* - point is a point in the mlog to which the read should be applied.
\*   for mlog entries at or "before" (index <=) point, the latest
\*   value associated with key will be included in the result.
\*   If the mlog at or before point does not mention the given key at all,
\*   then the result set will include NotFoundReadResult.
\*   An empty set as a result means the read is not possible; any valid read, even
\*   one that returns a "not found" result, will have at least one element in
\*   its set.
\* - allowDirty controls a secondary behavior: for elements of the mlog
\*   whose index > point, if allowDirty = TRUE then they will also
\*   be included in the result set. If allowDirty = FALSE, then only
\*   the single latest value whose index <= point will be in the result set.
GeneralRead(key, index, allowDirty) ==
    LET maxCandidateIndices == { i \in DOMAIN mlog :
            /\ mlog[i].key = key
            /\ i <= index }
        allIndices == { i \in DOMAIN mlog :
            /\ allowDirty
            /\ mlog[i].key = key
            /\ i > index }
    IN  { [mlogIndex |-> i, value |-> mlog[i].value]
          : i \in allIndices \cup (
            IF   maxCandidateIndices # {}
            THEN {Max(maxCandidateIndices)}
            ELSE {}) } \cup 
        (IF   maxCandidateIndices = {}
         THEN {NotFoundReadResult}
         ELSE {})

Read(key) == CASE
            \* linearizable reads from mcommitIndex and forbids dirty reads
            RC = "linearizable" -> GeneralRead(key, mcommitIndex, FALSE)

        \*     \* available reads from readIndex, because the node we reach may be behind mcommitIndex; 
        \*     \* it also allows dirty reads
        \*  [] RC = "available"    -> GeneralRead(key, readIndex, TRUE)

\* causal hlc read at or more recent than what we received last from a read/write
ReadAtTime(token, key) ==
        IF   TRUE
             \* \/ mepoch = token.mepoch  \* invalidate token on mepoch change
             \* \/ token = [checkpoint |-> 0,mepoch |-> 0] \* NoSessionToken hack !!
        THEN LET sessionIndex ==  token.checkpoint \* Max({token.checkpoint, readIndex})
             IN  GeneralRead(key, sessionIndex, TRUE)
        ELSE {}


--------------------------------------------------------

PrepareOrCommitTimestamps(n) == {IF "ts" \in DOMAIN e THEN e.ts ELSE  0 : e \in Range(mlog[n])}

ActiveReadTimestamps(n) == { IF ~mtxnSnapshots[n][tx]["active"] THEN 0 ELSE mtxnSnapshots[n][tx].ts : tx \in DOMAIN mtxnSnapshots[n]}

\* Next timestamp to use for a transaction operation.
NextTs(n) == Max(PrepareOrCommitTimestamps(n) \cup ActiveReadTimestamps(n)) + 1

ActiveTransactions(n) == {tid \in MTxId : mtxnSnapshots[n][tid]["active"]}
PreparedTransactions(n) == {tid \in ActiveTransactions(n) : mtxnSnapshots[n][tid].prepared}

\* 
\* Perform a snapshot read of a given key at timestamp.
\* 
\* That is, return the latest value associated with the key 
\* that was written at ts <= index. If no value was yet written
\* to the key, then return NotFoundReadResult.
\* 
SnapshotRead(n, key, ts) == 
    LET snapshotKeyWrites == 
        { i \in DOMAIN mlog[n] :
            /\ "data" \in DOMAIN mlog[n][i] \* exclude 'prepare' entries.
            /\ \E k \in DOMAIN mlog[n][i].data : k = key
            \* Determine read visibility based on commit timestamp.
            /\ mlog[n][i].ts <= ts } IN
        IF snapshotKeyWrites = {}
            THEN NotFoundReadResult
            ELSE [mlogIndex |-> Max(snapshotKeyWrites), value |-> mlog[n][Max(snapshotKeyWrites)].data[key]]

\* Snapshot of the full KV store at a given index/timestamp.
SnapshotKV(n, ts, rc) == 
    \* Local reads just read at the latest timestamp in the log.
    LET txnReadTs == IF rc = "snapshot" THEN ts ELSE Len(mlog[n]) IN
    [
        ts |-> txnReadTs,
        data |-> [k \in Keys |-> SnapshotRead(n, k, txnReadTs).value],
        prepared |-> FALSE,
        prepareTs |-> 0,
        aborted |-> FALSE,
        committed |-> FALSE,
        readSet |-> {},
        writeSet |-> {},
        active |-> TRUE
    ]
    


WriteReadConflictExists(n, tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in MTxId \ {tid}:
        \* Transaction is running. 
        \/ /\ tid \in ActiveTransactions(n)
           /\ tOther \in ActiveTransactions(n)
           \* The other transaction is on the same snapshot and read this value.
           /\ mtxnSnapshots[tOther].ts = mtxnSnapshots[tOther].ts
           /\ k \in mtxnSnapshots[tOther].readSet

\* Alternate equivalent definition of the above.
WriteConflictExists(n, tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in MTxId \ {tid}:
        \* Transaction is running concurrently. 
        \/ /\ tid \in ActiveTransactions(n)
           /\ tOther \in ActiveTransactions(n)
           \* The other transaction wrote to this value.
        \*    /\ mtxnSnapshots[n][tOther].data[k] = tOther
           /\ k \in mtxnSnapshots[n][tOther].writeSet
        \* If there exists another transaction that has written to this key and
        \* committed at a timestamp newer than your snapshot, this also should
        \* manifest as a conflict, since it implies this transaction may have
        \* overlapped with you (in timestamp order).
        \/ \E ind \in DOMAIN mlog[n] :
            /\ "data" \in DOMAIN mlog[n][ind]
            /\ mlog[n][ind].ts > mtxnSnapshots[n][tid].ts
            /\ k \in (DOMAIN mlog[n][ind].data)

\* CleanSnapshots == [t \in MTxId |-> Nil]

\* If a prepared transaction has committed behind our snapshot read timestamp
\* while we were running, then we must observe the effects of its writes.
TxnRead(n, tid, k) == 
    IF  \E tOther \in MTxId \ {tid}:
        \E pmind \in DOMAIN mlog[n] :
        \E cmind \in DOMAIN mlog[n] :
            \* Prepare log entry exists.
            /\ "prepare" \in DOMAIN mlog[n][pmind]
            /\ mlog[n][pmind].tid = tOther
            \* Commit log entry exists and is at timestamp <= our snapshot.
            /\ "data" \in DOMAIN mlog[n][cmind]
            /\ mlog[n][cmind].tid = tOther
            /\ mlog[n][cmind].ts <= mtxnSnapshots[n][tid].ts
            /\ k \in DOMAIN mlog[n][cmind].data
            \* If we wrote to this key within our transaction, then we will always read our latest write.
            /\ k \notin mtxnSnapshots[n][tid].writeSet
        \* Snapshot read directly from the log.
        THEN SnapshotRead(n, k, mtxnSnapshots[n][tid].ts).value 
        \* Just read from your stored snapshot.
        ELSE mtxnSnapshots[n][tid].data[k]

UpdateSnapshot(tid, k, v) == [mtxnSnapshots EXCEPT ![tid].data[k] = v]

SnapshotUpdatedKeys(n, tid) == {
    k \in Keys : 
        /\ tid \in ActiveTransactions(n)
        /\ k \in mtxnSnapshots[n][tid]["writeSet"]
}

CommitLogEntry(n, tid, commitTs) == [
    data |-> [key \in SnapshotUpdatedKeys(n, tid) |-> mtxnSnapshots[n][tid].data[key]],
    ts |-> commitTs, 
    tid |-> tid
]

CommitTxnToLog(n, tid, commitTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(mlog[n], CommitLogEntry(n, tid, commitTs))

CommitTxnToLogWithDurable(n, tid, commitTs, durableTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(mlog[n], CommitLogEntry(n, tid, commitTs) @@ [durableTs |-> durableTs])


PrepareTxnToLog(n, tid, prepareTs) ==
    Append(mlog[n], [prepare |-> TRUE, ts |-> prepareTs, tid |-> tid])

TxnCanStart(n, tid, readTs) ==
    \* Cannot start a transaction at a timestamp T if there is another 
    \* currently prepared transaction at timestamp < T.
    ~\E tother \in MTxId :
        /\ tother \in ActiveTransactions(n)
        /\ mtxnSnapshots[tother].prepared 
        /\ mtxnSnapshots[tother].ts < readTs 

PrepareConflict(n, tid, k) ==
    \* Is there another transaction prepared at T <= readTs that has modified this key?
    \E tother \in MTxId :
        /\ tother \in ActiveTransactions(n)
        /\ mtxnSnapshots[n][tother].prepared
        /\ k \in SnapshotUpdatedKeys(n, tother)
        /\ \E pind \in DOMAIN mlog[n] : 
            /\ "prepare" \in DOMAIN mlog[n][pind] 
            /\ mlog[n][pind].tid = tother 
            /\ mlog[n][pind].ts <= mtxnSnapshots[n][tid].ts 







---------------------------------------------------------------------

\* Expand the prefix of the mlog that can no longer be lost.
IncreaseCommitIndex ==
    /\ mcommitIndex' \in mcommitIndex..Len(mlog)
    /\ UNCHANGED <<mlog>>

\* Any data that is not part of the checkpointed mlog prefix may be lost at any time. 
TruncatedLog == \E i \in (mcommitIndex+1)..Len(mlog) :
    /\ mlog' = SubSeq(mlog, 1, i - 1)
    /\ UNCHANGED <<mcommitIndex>>
  

\* StartTxn(tid, readTs) ==
\*     /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = SnapshotKV(readTs, "snapshot")]
\*     /\ UNCHANGED <<mlog, mcommitIndex, mepoch>>

\* Explicit initialization for each state variable.
Init_mlog == <<>>
Init_mcommitIndex == 0
Init_mtxnSnapshots == [t \in MTxId |-> [active |-> FALSE]]

\* MInit ==
    \* /\ mlog = [n \in Nodes |-> <<>>]
    \* /\ mcommitIndex = [n \in Nodes |-> 0]
    \* /\ mepoch = [n \in Nodes |-> 1]
    \* /\ mtxnSnapshots = [n \in Nodes |-> [t \in MTxId |-> Nil]]

\* \* This relation models all possible mlog actions, without performing any write.
\* MNext ==
    \* \/ \E n \in Nodes : \E t \in MTxId, ts \in {0,1,2} : TxnStart(n, t, ts, "snapshot")
    \* \/ \E n \in Nodes : \E t \in MTxId, k \in Keys : TxnWrite(n, t, k)





\* Stores latest operation status for each operation of a transaction (e.g.
\* records error codes, etc.)
VARIABLE txnStatus

\* Tracks the global "stable timestamp" within the storage layer.
VARIABLE stableTs

STATUS_OK == "OK"
STATUS_ROLLBACK == "WT_ROLLBACK"
STATUS_NOTFOUND == "WT_NOTFOUND"
STATUS_PREPARE_CONFLICT == "WT_PREPARE_CONFLICT"

\* Checks the status of a transaction is OK after it has executed some enabled action.
TransactionPostOpStatus(n, tid) == txnStatus'[n][tid]

StartTransaction(n, tid, readTs, rc) == 
    \* Start the transaction on the MDB KV store.
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    /\ tid \notin ActiveTransactions(n)
    \* Only run transactions for a given transactionid once.
    /\ ~mtxnSnapshots[n][tid]["committed"]
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Don't re-use transaction ids.
    /\ ~\E i \in DOMAIN (mlog[n]) : mlog[n][i].tid = tid
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid] = SnapshotKV(n, readTs, rc)]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs>>
   
\* Writes to the local KV store of a shard.
TransactionWrite(n, tid, k, v) == 
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ tid \in ActiveTransactions(n)
    /\ tid \notin PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Transactions always write their own ID as the value, to uniquely identify their writes.
    /\ v = tid
    /\ \/ /\ ~WriteConflictExists(n, tid, k)
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["writeSet"] = @ \cup {k}, 
                                                    ![n][tid].data[k] = tid]
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
       \/ /\ WriteConflictExists(n, tid, k)
          \* If there is a write conflict, the transaction must roll back (i.e. it is aborted).
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_ROLLBACK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["aborted"] = TRUE]
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs>>

\* Reads from the local KV store of a shard.
TransactionRead(n, tid, k, v) ==
    \* Non-snapshot read aren't actually required to block on prepare conflicts (see https://jira.mongodb.org/browse/SERVER-36382). 
    /\ tid \in ActiveTransactions(n)    
    /\ tid \notin PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    /\ v = TxnRead(n, tid, k)
    /\ \/ /\ ~PrepareConflict(n, tid, k)
          /\ v # NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
          \* Disable read-set tracking for now.
          /\ mtxnSnapshots' = mtxnSnapshots \* [mtxnSnapshots EXCEPT ![n][tid]["readSet"] = @ \cup {k}]
       \* Key does not exist.
       \/ /\ ~PrepareConflict(n, tid, k)
          /\ v = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_NOTFOUND]
          /\ UNCHANGED mtxnSnapshots
      \* Prepare conflict (transaction is not aborted).
       \/ /\ PrepareConflict(n, tid, k)
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_PREPARE_CONFLICT]
          /\ UNCHANGED mtxnSnapshots
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs>>

\* Delete a key.
TransactionRemove(n, tid, k) ==
    /\ tid \in ActiveTransactions(n)
    /\ tid \notin PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    /\ \/ /\ ~WriteConflictExists(n, tid, k)
          /\ TxnRead(n, tid, k) # NoValue 
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["writeSet"] = @ \cup {k}, 
                                                    ![n][tid].data[k] = NoValue]
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
       \* If key does not exist in your snapshot then you can't remove it.
       \/ /\ ~WriteConflictExists(n, tid, k)
          /\ TxnRead(n, tid, k) = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_NOTFOUND]
          /\ UNCHANGED mtxnSnapshots
       \/ /\ WriteConflictExists(n, tid, k)
          \* If there is a write conflict, the transaction must roll back.
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_ROLLBACK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["aborted"] = TRUE]
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs>>

CommitTimestamps(n) == {mlog[n][i].ts : i \in DOMAIN mlog[n]}

CommitTransaction(n, tid, commitTs) == 
    \* TODO: Eventually make this more permissive and explictly check errors on
    \* invalid commit timestamps w.r.t stable timestamp (?)
    /\ commitTs > stableTs[n] 
    /\ tid \in ActiveTransactions(n)
    /\ tid \notin PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Must be greater than the newest known commit timestamp.
    /\ (ActiveReadTimestamps(n) \cup CommitTimestamps(n)) # {} => commitTs > Max(ActiveReadTimestamps(n) \cup CommitTimestamps(n))
    \* Commit the transaction on the KV store and write all updated keys back to the log.
    /\ mlog' = [mlog EXCEPT ![n] = CommitTxnToLog(n, tid, commitTs)]
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["active"] = FALSE, ![n][tid]["committed"] = TRUE]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ UNCHANGED <<mcommitIndex, stableTs>>

CommitPreparedTransaction(n, tid, commitTs, durableTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the shard oplog.
    /\ commitTs = durableTs \* for now force these equal.
    /\ commitTs > stableTs[n] 
    /\ tid \in ActiveTransactions(n)
    /\ tid \in PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Commit timestamp must be greater than the prepare timestamp.
    \* For distributed transactions commit timestamps may be chosen older than active read timestamps, though.
    \* /\ mtxnSnapshots[n][tid].prepareTs # Nil 
    \* /\ mtxnSnapshots[n][tid]["active"]
    /\ commitTs >= mtxnSnapshots[n][tid].prepareTs
    /\ mlog' = [mlog EXCEPT ![n] = CommitTxnToLogWithDurable(n, tid, commitTs, durableTs)]
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["active"] = FALSE, ![n][tid]["committed"] = TRUE]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ UNCHANGED <<mcommitIndex, stableTs>>

PrepareTransaction(n, tid, prepareTs) == 
    \* TODO: Eventually make this more permissive and explictly check errors on
    \* invalid commit timestamps w.r.t stable timestamp (?)
    /\ prepareTs > stableTs[n]
    /\ tid \in ActiveTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["prepared"]
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Prepare timestamp must be greater than our own read timestamp,
    \* and greater than any active read timestamp.
    /\ prepareTs > mtxnSnapshots[n][tid].ts
    /\ prepareTs > Max(ActiveReadTimestamps(n))
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["prepared"] = TRUE, ![n][tid]["prepareTs"] = prepareTs]
    /\ mlog' = [mlog EXCEPT ![n] = PrepareTxnToLog(n,tid, prepareTs)]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ UNCHANGED <<mcommitIndex, stableTs>>

AbortTransaction(n, tid) == 
    /\ tid \in ActiveTransactions(n)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["active"] = FALSE, ![n][tid]["aborted"] = TRUE]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs>>

SetStableTimestamp(n, ts) == 
    /\ ts > stableTs[n]
    /\ stableTs' = [stableTs EXCEPT ![n] = ts]
    /\ UNCHANGED <<mlog, mcommitIndex, mtxnSnapshots, txnStatus>>

RollbackToStable(n) == 
    \* Mustn't initiate a RTS call if there are any open transactions.
    /\ ActiveTransactions(n) = {}
    /\ stableTs[n] > 0 \* Stable timestamp has been set.
    \* Truncate all log operations at timestamps in front of the stable timestamp.
    /\ mlog' = [mlog EXCEPT ![n] = SelectSeq(mlog[n], LAMBDA op : op.ts <= stableTs[n])]
    /\ stableTs' = stableTs
    /\ UNCHANGED <<mtxnSnapshots, txnStatus, mcommitIndex>>

vars == <<mlog, mcommitIndex, mtxnSnapshots, txnStatus, stableTs>>

Init == 
    /\ mlog = [n \in Node |-> <<>>]
    /\ mcommitIndex = [n \in Node |-> 0]
    /\ mtxnSnapshots = [n \in Node |-> [t \in MTxId |-> [active |-> FALSE, committed |-> FALSE, aborted |-> FALSE]]]
    /\ txnStatus = [n \in Node |-> [t \in MTxId |-> STATUS_OK]]
    /\ stableTs = [n \in Node |-> -1]

Next == 
    \/ \E n \in Node : \E tid \in MTxId, readTs \in Timestamps : StartTransaction(n, tid, readTs, RC)
    \/ \E n \in Node : \E tid \in MTxId, k \in Keys, v \in Values : TransactionWrite(n, tid, k, v)
    \/ \E n \in Node : \E tid \in MTxId, k \in Keys, v \in (Values \cup {NoValue}) : TransactionRead(n, tid, k, v)
    \/ \E n \in Node : \E tid \in MTxId, k \in Keys : TransactionRemove(n, tid, k)
    \/ \E n \in Node : \E tid \in MTxId, prepareTs \in Timestamps : PrepareTransaction(n, tid, prepareTs)
    \/ \E n \in Node : \E tid \in MTxId, commitTs \in Timestamps : CommitTransaction(n, tid, commitTs)
    \/ \E n \in Node : \E tid \in MTxId, commitTs, durableTs \in Timestamps : CommitPreparedTransaction(n, tid, commitTs, durableTs)
    \/ \E n \in Node : \E tid \in MTxId : AbortTransaction(n, tid)
    \/ \E n \in Node : \E ts \in Timestamps : SetStableTimestamp(n, ts)
    \/ \E n \in Node : RollbackToStable(n)
    \* TODO Also consider adding model actions to read/query various timestamps (e.g. all_durable, oldest, etc.)


Symmetry == Permutations(MTxId) \cup Permutations(Keys)

===============================================================================