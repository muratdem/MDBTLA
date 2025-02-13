---- MODULE MDB ----
EXTENDS Sequences, Naturals, Util

CONSTANTS RC   \* read concern

CONSTANTS Keys, 
        \*   Values, 
          NoValue,
          MTxId,
          Nil

WCVALUES == {"one", 
             "majority"}

RCVALUES == {"linearizable", 
             "snapshot", 
             "local",
             "available"}

LogIndices == Nat \ {0}

Epochs == Nat \ {0}

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


---------------------------------------------------------------------
\* CommitIndex and mepoch express a high-level view of
\* underlying processes like replication and failure recovery:
\* - the mcommitIndex indicates a position in the mlog (or 0 for no position)
\*   before which data is durable.
\* - the mepoch increments strictly monotonically whenever mlog is non-deterministically
\*   truncated in the range (mcommitIndex+1)..Len(mlog)), modeling loss of uncommitted data
\*   due to node failures

VARIABLE mlog
VARIABLE mcommitIndex
VARIABLE mepoch

\* Stores snapshots for running transactions on the underlying MongoDB instance.
VARIABLE mtxnSnapshots

mvars == <<mlog, mcommitIndex, mepoch, mtxnSnapshots>>

TypesOK ==
    /\ mlog \in Logs
    /\ mcommitIndex \in Nat
    /\ mepoch \in Epochs

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

PrepareOrCommitTimestamps == {IF "ts" \in DOMAIN e THEN e.ts ELSE  0 : e \in Range(mlog)}

ActiveReadTimestamps == { IF mtxnSnapshots[tx] = Nil THEN 0 ELSE mtxnSnapshots[tx].ts : tx \in DOMAIN mtxnSnapshots}

\* Next timestamp to use for a transaction operation.
NextTs == Max(PrepareOrCommitTimestamps \cup ActiveReadTimestamps) + 1

ActiveTransactions == {tid \in MTxId : mtxnSnapshots[tid] # Nil}
PreparedTransactions == {tid \in MTxId : mtxnSnapshots[tid] # Nil /\ mtxnSnapshots[tid].prepared}

\* 
\* Perform a snapshot read of a given key at timestamp.
\* 
\* That is, return the latest value associated with the key 
\* that was written at ts <= index. If no value was yet written
\* to the key, then return NotFoundReadResult.
\* 
SnapshotRead(key, ts) == 
    LET snapshotKeyWrites == 
        { i \in DOMAIN mlog :
            /\ "data" \in DOMAIN mlog[i] \* exclude 'prepare' entries.
            /\ \E k \in DOMAIN mlog[i].data : k = key
            \* Determine read visibility based on commit timestamp.
            /\ mlog[i].ts <= ts } IN
        IF snapshotKeyWrites = {}
            THEN NotFoundReadResult
            ELSE [mlogIndex |-> Max(snapshotKeyWrites), value |-> mlog[Max(snapshotKeyWrites)].data[key]]

\* Snapshot of the full KV store at a given index/timestamp.
SnapshotKV(ts, rc) == 
    \* Local reads just read at the latest timestamp in the log.
    LET readTs == IF rc = "snapshot" THEN ts ELSE Len(mlog) IN
    [
        ts |-> readTs,
        data |-> [k \in Keys |-> SnapshotRead(k, readTs).value],
        prepared |-> FALSE,
        prepareTs |-> Nil,
        aborted |-> FALSE,
        readSet |-> {},
        writeSet |-> {}
    ]
    


WriteReadConflictExists(tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in MTxId \ {tid}:
        \* Transaction is running. 
        \/ /\ mtxnSnapshots[tid] # Nil
           /\ mtxnSnapshots[tOther] # Nil
           \* The other transaction is on the same snapshot and read this value.
           /\ mtxnSnapshots[tOther].ts = mtxnSnapshots[tOther].ts
           /\ k \in mtxnSnapshots[tOther].readSet

\* Alternate equivalent definition of the above.
WriteConflictExists(tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in MTxId \ {tid}:
        \* Transaction is running concurrently. 
        \/ /\ mtxnSnapshots[tid] # Nil
           /\ mtxnSnapshots[tOther] # Nil
           \* The other transaction wrote to this value.
        \*    /\ mtxnSnapshots[tOther].data[k] = tOther
           /\ k \in mtxnSnapshots[tOther].writeSet
        \* If there exists another transaction that has written to this key and
        \* committed at a timestamp newer than your snapshot, this also should
        \* manifest as a conflict, since it implies this transaction may have
        \* overlapped with you (in timestamp order).
        \/ \E ind \in DOMAIN mlog :
            /\ "data" \in DOMAIN mlog[ind]
            /\ mlog[ind].ts > mtxnSnapshots[tid].ts
            /\ k \in (DOMAIN mlog[ind].data)

CleanSnapshots == [t \in MTxId |-> Nil]

\* If a prepared transaction has committed behind our snapshot read timestamp
\* while we were running, then we must observe the effects of its writes.
TxnRead(tid, k) == 
    IF  \E tOther \in MTxId \ {tid}:
        \E pmind \in DOMAIN mlog :
        \E cmind \in DOMAIN mlog :
            \* Prepare log entry exists.
            /\ "prepare" \in DOMAIN mlog[pmind]
            /\ mlog[pmind].tid = tOther
            \* Commit log entry exists and is at timestamp <= our snapshot.
            /\ "data" \in DOMAIN mlog[cmind]
            /\ mlog[cmind].tid = tOther
            /\ mlog[cmind].ts <= mtxnSnapshots[tid].ts
            /\ k \in DOMAIN mlog[cmind].data
            \* If we wrote to this key within our transaction, then we will always read our latest write.
            /\ k \notin mtxnSnapshots[tid].writeSet
        \* Snapshot read directly from the log.
        THEN SnapshotRead(k, mtxnSnapshots[tid].ts).value 
        \* Just read from your stored snapshot.
        ELSE mtxnSnapshots[tid].data[k]

UpdateSnapshot(tid, k, v) == [mtxnSnapshots EXCEPT ![tid].data[k] = v]

SnapshotUpdatedKeys(tid) == {
    k \in Keys : 
        /\ mtxnSnapshots[tid] # Nil 
        /\ k \in mtxnSnapshots[tid]["writeSet"]
}

CommitTxnToLog(tid, commitTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(mlog, [
        data |-> [key \in SnapshotUpdatedKeys(tid) |-> tid], 
        ts |-> commitTs, 
        tid |-> tid
    ])

CommitTxnToLogWithDurable(tid, commitTs, durableTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(mlog, [
        data |-> [key \in SnapshotUpdatedKeys(tid) |-> tid],
        ts |-> commitTs, 
        durableTs |-> durableTs,
        tid |-> tid
    ])


PrepareTxnToLog(tid, prepareTs) ==
    Append(mlog, [prepare |-> TRUE, ts |-> prepareTs, tid |-> tid])

TxnCanStart(tid, readTs) ==
    \* Cannot start a transaction at a timestamp T if there is another 
    \* currently prepared transaction at timestamp < T.
    ~\E tother \in MTxId :
        /\ mtxnSnapshots[tother] # Nil 
        /\ mtxnSnapshots[tother].prepared 
        /\ mtxnSnapshots[tother].ts < readTs 

PrepareConflict(tid, k) ==
    \* Is there another transaction prepared at T <= readTs that has modified this key?
    \E tother \in MTxId :
        /\ mtxnSnapshots[tother] # Nil 
        /\ mtxnSnapshots[tother].prepared
        /\ k \in SnapshotUpdatedKeys(tother)
        /\ \E pind \in DOMAIN mlog : 
            /\ "prepare" \in DOMAIN mlog[pind] 
            /\ mlog[pind].tid = tother 
            /\ mlog[pind].ts <= mtxnSnapshots[tid].ts 

---------------------------------------------------------------------

\* Expand the prefix of the mlog that can no longer be lost.
IncreaseCommitIndex ==
    /\ mcommitIndex' \in mcommitIndex..Len(mlog)
    /\ UNCHANGED <<mlog, mepoch>>

\* Any data that is not part of the checkpointed mlog prefix may be lost at any time. 
TruncatedLog == \E i \in (mcommitIndex+1)..Len(mlog) :
    /\ mlog' = SubSeq(mlog, 1, i - 1)
    /\ mepoch' = mepoch + 1
    /\ UNCHANGED <<mcommitIndex>>
  

\* StartTxn(tid, readTs) ==
\*     /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = SnapshotKV(readTs, "snapshot")]
\*     /\ UNCHANGED <<mlog, mcommitIndex, mepoch>>

\* Explicit initialization for each state variable.
Init_mlog == <<>>
Init_mcommitIndex == 0
Init_mepoch == 1
Init_mtxnSnapshots == [t \in MTxId |-> Nil]

\* Init ==
\*     /\ mlog = <<>>
\*     /\ mcommitIndex = 0
\*     /\ mepoch = 1
\*     /\ mtxnSnapshots = [t \in TxId |-> Nil]

\* \* This relation models all possible mlog actions, without performing any write.
\* Next ==
\*     \/ IncreaseCommitIndex
\*     \/ TruncateLog

===============================================================================