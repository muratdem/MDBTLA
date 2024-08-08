--------------------------- MODULE MultiShardTxn ---------------------------------
(**************************************************************************)
(* Model of distributed, cross-shard transactions in MongoDB.             *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Util, TLC

CONSTANTS Keys, TxId

CONSTANT Router
CONSTANT Shard

CONSTANT NoValue
CONSTANTS WC, RC

\* Instantiating ClientCentric enables us to check transaction isolation guarantees
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC == INSTANCE ClientCentric WITH Keys <- Keys, Values <- TxId \union {NoValue}          

\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)    
InitialState == [k \in Keys |-> NoValue]  

(* Router state *)

\* Tracks count of transaction statements processed on a router.
VARIABLE rtxn

\* The read timestamp being used for each running transaction on the router.
VARIABLE rTxnReadTs

\* Tracks whether a transaction at the router has initiated commit.
VARIABLE rInCommit

\* For each transaction, the router tracks a list of shards that are rParticipants in that
\* transaction. The router forwards this information to the coordinator when ready to commit.
\* By default, the first participant in this list is designated as the coordinator.
VARIABLE rParticipants


(* Shard state *)

\* The router writes transaction operations for a shard to 'rlog', 
\* and shards scan this log to learn transaction ops that have been routed to them. 
VARIABLE rlog 

\* Set of in-progress transactions on each shard.
VARIABLES shardTxns

\* Set of prepared transactions on a shard.
VARIABLE shardPreparedTxns

\* Set of commit votes recorded by each coordinator shard, for each transaction.
VARIABLE coordCommitVotes


\* For each shard and transaction, keeps track of whether that transaction aborted e.g.
\* due to a write conflict.
VARIABLE aborted 

\* For each shard and each transaction, a counter which tracks the 
\* current statement number of that transaction. 
VARIABLE lsn

\* Each shard, for each transaction, maintains a record of whether it has been designated as
\* the 2PC coordinator for that transaction.
VARIABLE coordInfo


(* Network and global state *)

VARIABLE msgsPrepare
VARIABLE msgsVoteCommit
VARIABLE msgsAbort
VARIABLE msgsCommit

\* History of all operations per transaction on each shard.
VARIABLE shardOps

\* Global history of all operations per transaction.
VARIABLE ops

\* 
\* Stores a fixed mapping from keys to shards, for routing purposes.
\* 
\* Eventually, with full modeling of catalog, this mapping can change over time (e.g chunk migrations)
\* but for now we assume it is static.
\* 
VARIABLE catalog

\* We maintain a MongoDB "log" (i.e. a replica set/oplog abstraction) for each shard.
VARIABLE log 
VARIABLE commitIndex 
VARIABLE epoch
\* Snapshot of data store for each transaction on each shard.
VARIABLE txnSnapshots

vars == << shardTxns, rInCommit,   rlog, aborted, log, commitIndex, epoch, rtxn, lsn, txnSnapshots, ops, shardOps, rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, msgsAbort, coordCommitVotes, catalog, msgsCommit, rTxnReadTs, shardPreparedTxns >>

\* Instance of a MongoDB replica set log for a given shard, that 
\* supports abstracted snapshot KV store.
ShardMDB(s) == INSTANCE MDB WITH 
                    mlog <- log[s], 
                    mcommitIndex <- commitIndex[s], 
                    mepoch <- epoch[s], 
                    mtxnSnapshots <- txnSnapshots[s],
                    Values <- TxId,
                    MTxId <- TxId,
                    Nil <- NoValue

Ops == {"read", "write", "coordCommit"}
Entry == [k: Keys, op: Ops]
CreateEntry(k, op, s, coord, start, ts) == [
    k |-> k, 
    op |-> op, 
    shard |-> s, 
    coord |-> coord, 
    start |-> start, 
    readTs |-> ts,
    rc |-> RC \* fixed, global read concern for now.
]
CreateCoordCommitEntry(op, s, p) == [op |-> op, shard |-> s, participants |-> p]


Init ==
    /\ catalog \in [Keys -> Shard]
    /\ ops = [s \in TxId |-> <<>>]
    \* Router state.
    /\ rtxn = [r \in Router |-> [t \in TxId |-> 0]]
    /\ rParticipants = [r \in Router |-> [t \in TxId |-> <<>>]]
    /\ rTxnReadTs = [r \in Router |-> [t \in TxId |-> NoValue]]
    /\ rInCommit = [r \in Router |-> [t \in TxId |-> FALSE]]
    \* Shard state.
    /\ rlog = [s \in Shard |-> [t \in TxId |->  <<>>]]
    /\ shardTxns = [s \in Shard |-> {}]
    /\ shardPreparedTxns = [s \in Shard |-> {}]
    /\ lsn = [s \in Shard |-> [t \in TxId |-> 0]]
    /\ aborted = [s \in Shard |-> [t \in TxId |-> FALSE]]
    /\ coordInfo = [s \in Shard |-> [t \in TxId |-> [self |-> FALSE, participants |-> <<>>, committing |-> FALSE]]]
    /\ coordCommitVotes = [s \in Shard |-> [t \in TxId |-> {}]]
    /\ shardOps = [s \in Shard |-> [t \in TxId |-> <<>>]]
    \* 2PC related messages.
    /\ msgsPrepare = {}
    /\ msgsVoteCommit = {}
    /\ msgsAbort = {}
    /\ msgsCommit = {}
    \* MongoDB replica set log state.
    /\ log = [s \in Shard |-> ShardMDB(s)!Init_mlog]
    /\ commitIndex = [s \in Shard |-> ShardMDB(s)!Init_mcommitIndex]
    /\ epoch = [s \in Shard |-> ShardMDB(s)!Init_mepoch]
    /\ txnSnapshots = [s \in Shard |-> ShardMDB(s)!Init_mtxnSnapshots]

\* 
\* A shard crashes, erasing all in memory data.
\* 
\* We can think of this a crash of the primary of a shard replica set, which
\* will naturally erase all in-memory state, but majority committed data will be
\* retained in the replica set.
\* 
Restart(s) == 
    /\ shardTxns' = [shardTxns EXCEPT ![s] = {}]
    /\ shardPreparedTxns' = [shardPreparedTxns EXCEPT ![s] = {}]
    /\ lsn' = [lsn EXCEPT ![s] = [t \in TxId |-> 0]]
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![s] = ShardMDB(s)!CleanSnapshots]
    /\ aborted' = [aborted EXCEPT ![s] = [t \in TxId |-> FALSE]]
    /\ coordInfo' = [coordInfo EXCEPT ![s] = [t \in TxId |-> [self |-> FALSE, participants |-> <<>>, committing |-> FALSE]]]
    /\ coordCommitVotes' = [coordCommitVotes EXCEPT ![s] = [t \in TxId |-> {}]]
    /\ rlog' = [rlog EXCEPT ![s] = [t \in TxId |-> <<>>]]
    \* All in-progress transactions on this shard will be aborted, so clear out ops on this shard from unprepared txns. 
    /\ ops' = [tid \in TxId |-> 
                IF tid \in (shardTxns[s] \ shardPreparedTxns[s]) 
                    THEN SelectSeq(ops[tid], LAMBDA op : catalog[op.key] # s)
                    ELSE ops[tid]]
    /\ UNCHANGED << rtxn, rInCommit, log, commitIndex, epoch, rParticipants, rTxnReadTs, catalog, msgsPrepare, msgsVoteCommit, msgsAbort, msgsCommit, rInCommit >>


-------------------------------------------------

\* 
\* Sub-action wrappers for operations on the per-shard MDB instances.
\* 
\* This should more or less be the abstract transaction interface each shard
\* needs to consider when executing transactions that are part of distributed,
\* cross-shard transaction.
\* 

ShardMDBTxnStart(s, tid, readTs, rc) == 
    \* Start the transaction on the MDB KV store.
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    /\ ShardMDB(s)!TxnCanStart(tid, readTs)
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![s][tid] = ShardMDB(s)!SnapshotKV(readTs, rc)]
    /\ UNCHANGED <<log, commitIndex, epoch>>
   
\* Writes to the local KV store of a shard.
ShardMDBTxnWrite(s, tid, k) == 
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ ~ShardMDB(s)!WriteConflictExists(tid, k)
    \* Did some concurrent transaction read this key?
    \* /\ ~ShardMDB(s)!WriteReadConflictExists(tid, k)
    \* Update the transaction's snapshot data.
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![s] = ShardMDB(s)!UpdateSnapshot(tid, k, tid)]
    /\ UNCHANGED <<log, commitIndex, epoch>>

\* Reads from the local KV store of a shard.
ShardMDBTxnRead(s, tid, k) == 
    \* Am I reading from a key that has been written to concurrently?
    \* /\ ~ShardMDB(s)!WriteConflictExists(tid, k)
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![s][tid]["readSet"] = @ \cup {k}]
    /\ UNCHANGED <<log, commitIndex, epoch>>

ShardMDBTxnCommit(s, tid, commitTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the shard oplog.
    /\ log' = [log EXCEPT ![s] = ShardMDB(s)!CommitTxnToLog(tid, commitTs)]
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![s][tid] = NoValue]
    /\ UNCHANGED <<epoch, commitIndex>>

ShardMDBTxnPrepare(s, tid) == 
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![s][tid]["prepared"] = TRUE]
    /\ UNCHANGED <<log, commitIndex, epoch>>

ShardMDBTxnAbort(s, tid) == 
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![s][tid] = NoValue]
    /\ UNCHANGED <<log, commitIndex, epoch>>

ShardMDBRollback(s) == 
    \E i \in (commitIndex[s]+1)..Len(log[s]) :
        /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, i - 1)]
        /\ UNCHANGED <<commitIndex, epoch, txnSnapshots>>
        /\ UNCHANGED <<rlog, rtxn, shardTxns, shardPreparedTxns, lsn, rInCommit, rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, msgsAbort, msgsCommit, coordCommitVotes, catalog, rTxnReadTs, ops, aborted>>
    
ShardMDBAdvanceCommitIndex(s) == 
    /\ commitIndex[s] < Len(log[s])
    /\ \E newCommitIndex \in (commitIndex[s]+1)..Len(log[s]) : commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED <<log, epoch, txnSnapshots>>
    /\ UNCHANGED <<rlog, rtxn, shardTxns, shardPreparedTxns, lsn, rInCommit, rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, msgsAbort, msgsCommit, coordCommitVotes, catalog, rTxnReadTs, ops, aborted>>


-------------------------------------------------

\*****************************************
\* Router transaction operations.
\*****************************************

\* 
\* Clients identify transactions via sessionId + txnNumber pairs, where session
\* IDs are globally unique and txnNumbers are unique within a session. We assume
\* that clients send all of their operations for a transaction to a single
\* router, so in this abstract model, for a fixed transaction id, we require
\* that all ops for that transaction id are processed on the same router.
\* 
\* If that router dies or becomes unreachable, there is a recovery
\* procedure for a client to learn about the status of a transaction by sending
\* a "recovery" token to a new router. This procedure simply exists for the
\* client to learn the commit/abort status of the transaction, by contacting the
\* recovery/coordinator shard.
\* 

\* Update router shard participant list for a transaction, while also
\* recording the type of ops done on each shard, and maintaining order when 
\* shards joined the transaction.
UpdateParticipants(r, tid, snew, op) == 
    (IF (\E el \in Range(rParticipants[r][tid]) : el[1] = snew) 
        THEN [ind \in DOMAIN rParticipants[r][tid] |-> 
                (IF rParticipants[r][tid][ind][1] = snew 
                    THEN <<snew, rParticipants[r][tid][ind][2] \cup {op}>> 
                    ELSE rParticipants[r][tid][ind])] 
        ELSE Append(rParticipants[r][tid], <<snew, {op}>>))

AllLogTimestamps == UNION {0..Len(log[sh]) : sh \in Shard}
CandidateReadTimestamps == AllLogTimestamps \cup {max(AllLogTimestamps) + 1}

\* Represents the "start" of a transaction at the router as a separate operation, 
\* which simply consists of picking a read timestamp. 
RouterTxnStart(r, tid, readTs) == 
    \* Pick a read timestamp non-deterministically at any point in the existing log of any shard. 
    \* This is a generalized version of what we do in practice, which will be a
    \* best effort guess at read timestamp to select will be maintained on a
    \* router based on previous responses from commands.
    /\ rTxnReadTs[r][tid] = NoValue
    /\ rTxnReadTs' = [rTxnReadTs EXCEPT ![r][tid] = readTs]
    /\ UNCHANGED << shardTxns, rParticipants, rlog, rtxn,  aborted, log, commitIndex, epoch, lsn, txnSnapshots, ops,coordInfo, msgsPrepare, msgsVoteCommit, msgsAbort, coordCommitVotes, catalog, msgsCommit, shardPreparedTxns, rInCommit, shardOps >>

\* Router handles a new transaction operation that is routed to the appropriate shard.
RouterTxnOp(r, s, tid, k, op) == 
    /\ op \in {"read", "write"}
    \* If a shard of this transaction has aborted, don't continue the transaction.
    /\ ~\E as \in Shard : aborted[as][tid]
    \* Transaction has not already initiated commit at the router.
    /\ rInCommit[r][tid] = FALSE
    \* Route to the shard that owns this key.
    /\ catalog[k] = s
    \* Assume that the router interacts with shards over a request-response RPC mechanism i.e.
    \* so we wait for an op to be processed before sending the next op.
    /\ rlog[s][tid] = <<>>
    \* Update rParticipants list if new participant joined the transaction, and also 
    /\ rParticipants' = [rParticipants EXCEPT ![r][tid] = UpdateParticipants(r, tid, s, op)]
    \* A read timestamp was chosen.
    /\ rTxnReadTs[r][tid] # NoValue
    \* /\ rTxnReadTs' = [rTxnReadTs EXCEPT ![r][tid] = IF rtxn[r][tid] = 0 THEN readTs ELSE rTxnReadTs[r][tid]]
    /\ LET firstShardOp == ~\E el \in Range(rParticipants[r][tid]) : el[1] = s IN
           rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateEntry(k, op, s, rtxn[r][tid] = 0, firstShardOp, rTxnReadTs[r][tid]))]
    /\ rtxn' = [rtxn EXCEPT ![r][tid] = rtxn[r][tid]+1]
    /\ UNCHANGED << shardTxns, rTxnReadTs,  aborted, log, commitIndex, epoch, lsn, txnSnapshots, ops,coordInfo, msgsPrepare, msgsVoteCommit, msgsAbort, coordCommitVotes, catalog, msgsCommit, shardPreparedTxns, rInCommit, shardOps >>

\* Router handles a transaction commit operation, which it forwards to the appropriate shard to initiate 2PC to
\* commit the transaction. It also sends out prepare messages to all participant shards.
RouterTxnCoordinateCommit(r, s, tid, op) == 
    /\ op = "coordCommit"
    \* Assume that the router interacts with shards over a request-response RPC mechanism.
    /\ rlog[s][tid] = <<>>
    \* Transaction has started and has targeted multiple shards.
    /\ Len(rParticipants[r][tid]) > 1
    /\ ~rInCommit[r][tid]
    \* No shard of this transaction has aborted.
    /\ ~\E as \in Shard : aborted[as][tid]
    /\ s = rParticipants[r][tid][1][1] \* Coordinator shard is the first participant in the list.
    \* Send coordinate commit message to the coordinator shard.
    /\ rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateCoordCommitEntry(op, s, [i \in DOMAIN rParticipants[r][tid] |-> rParticipants[r][tid][i][1]]))]
    /\ rtxn' = [rtxn EXCEPT ![r][tid] = rtxn[r][tid]+1]
    /\ rInCommit' = [rInCommit EXCEPT ![r][tid] = TRUE]
    /\ UNCHANGED << shardTxns,   aborted, log, commitIndex, epoch, lsn, txnSnapshots, ops, rParticipants, coordInfo, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, msgsPrepare, rTxnReadTs, shardPreparedTxns, shardOps >>

\* If a transaction only executed reads, even against multiple shards, then the
\* router can bypass 2PC and send commits directly to shards.
RouterTxnCommitReadOnly(r, s, tid) == 
    \* Transaction has targeted this single shard.
    /\ Len(rParticipants[r][tid]) > 1
    \* All shards were reads.
    /\ \A p \in Range(rParticipants[r][tid]) : p[2] = {"read"}
    \* Assume that the router interacts with shards over a request-response RPC mechanism.
    /\ rlog[s][tid] = <<>>
    /\ ~rInCommit[r][tid]
    \* Shard hasn't aborted.
    /\ ~aborted[s][tid]
    \* Send commit message directly to shard (bypass 2PC).
    /\ msgsCommit' = msgsCommit \cup { [shard |-> sp[1], tid |-> tid, commitTs |-> 0] : sp \in Range(rParticipants[r][tid])}
    /\ rInCommit' = [rInCommit EXCEPT ![r][tid] = TRUE]
    /\ UNCHANGED << shardTxns,   aborted, rlog, rtxn, log, commitIndex, epoch, lsn, txnSnapshots, ops, rParticipants, coordInfo, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsPrepare, rTxnReadTs, shardPreparedTxns, shardOps >>

\* If a transaction only targeted a single shard, then the router can commit the
\* transaction without going through a full 2PC. Instead, it just sends a commit
\* message directly to that shard.
RouterTxnCommitSingleShard(r, s, tid) == 
    \* Transaction has targeted this single shard.
    /\ Len(rParticipants[r][tid]) = 1 /\ rParticipants[r][tid][1][1] = s
    \* Assume that the router interacts with shards over a request-response RPC mechanism.
    /\ rlog[s][tid] = <<>>
    \* Shard hasn't aborted.
    /\ ~aborted[s][tid]
    /\ ~rInCommit[r][tid]
    \* Send commit message directly to shard (bypass 2PC).
    /\ msgsCommit' = msgsCommit \cup { [shard |-> s, tid |-> tid, commitTs |-> rTxnReadTs[r][tid] + 1] }
    /\ rInCommit' = [rInCommit EXCEPT ![r][tid] = TRUE]
    /\ UNCHANGED << shardTxns,   aborted, rlog, rtxn, log, commitIndex, epoch, lsn, txnSnapshots, ops, rParticipants, coordInfo, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsPrepare, rTxnReadTs, shardPreparedTxns, shardOps >>

\* The set of shard rParticipants for a transaction that were written to.
WriteParticipants(tid) == {s \in Shard : \E i \in DOMAIN rlog[s][tid] : rlog[s][tid][i].op = "write"}

\* If a transaction has touched multiple shards, but only written to a single
\* shard, then we optimize this case by first sending commits directly to the
\* read only shards, and then, if these are successfully, directly sending
\* commit to the write shard.
\* TODO: Send commit to write shards upon hearing read responses.
RouterTxnCommitSingleWriteShard(r, tid) == 
    \* Transaction has started and has targeted multiple shards,
    \* but only written to a single shard.
    /\ Len(rParticipants[r][tid]) > 1
    /\ Cardinality(WriteParticipants(tid)) = 1
    \* No shard of this transaction has aborted.
    /\ ~\E as \in Shard : aborted[as][tid]
    \* Send commit message directly to shard (bypass 2PC).
    /\ msgsCommit' = msgsCommit \cup { [shard |-> s, tid |-> tid] : s \in (Shard \ WriteParticipants(tid))}
    /\ rInCommit' = [rInCommit EXCEPT ![r][tid] = TRUE]
    /\ UNCHANGED << shardTxns,   aborted, rlog, rtxn, log, commitIndex, epoch, lsn, txnSnapshots, ops, rParticipants, coordInfo, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsPrepare, rTxnReadTs, shardPreparedTxns, shardOps >>

\* 
\* Router aborts the transaction, which it can do at any point.
\* 
\* In practice, a router may also abort if it hears about failure of a statement
\* executed in the midst of an ongoing transaction (e.g. due to write conflict),
\* but this covers the more general case i.e. where a router could potentially
\* send abort at any time for any reason (e.g client sends explicit abort.)
\* 
RouterTxnAbort(r, tid) == 
    /\ rParticipants[r][tid] # <<>>
    \* Didn't already initiate commit.
    /\ ~rInCommit[r][tid]
    /\ msgsAbort' = msgsAbort \cup {[tid |-> tid, shard |-> s[1]] : s \in Range(rParticipants[r][tid])}
    /\ UNCHANGED << shardTxns,   aborted, log, commitIndex, epoch, lsn, txnSnapshots, ops, rlog, rtxn, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, rParticipants, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, shardOps >>


\*****************************************
\* Shard transaction operations.
\*****************************************

\* Shard starts a new transaction.
ShardTxnStart(s, tid) == 
    \* Transaction has new read/write statements in the router log, and has not been started on this shard yet.
    /\ rlog[s][tid] # <<>>
    /\ Head(rlog[s][tid]).op \in {"read", "write"}
    \* First statement of the transaction on this shard.
    /\ Head(rlog[s][tid]).start
    /\ tid \notin shardTxns[s]
    \* We don't advance to the next statement (lsn), but mark the transaction as
    \* having started on this shard, so transaction statements can now be processed.
    /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \union {tid}]
    /\ coordInfo' = [coordInfo EXCEPT ![s][tid] = [self |-> Head(rlog[s][tid]).coord, participants |-> <<s>>, committing |-> FALSE]]
    /\ ShardMDBTxnStart(s, tid, Head(rlog[s][tid]).readTs, Head(rlog[s][tid]).rc)
    /\ UNCHANGED << lsn, rlog,  aborted,  log, commitIndex, epoch, rtxn, ops, rParticipants, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, shardOps >>   

\* Shard processes a transaction read operation.
ShardTxnRead(s, tid, k) == 
    \* Transaction has new statements in the router log.
    /\ rlog[s][tid] # <<>>
    \* Transaction has started running on this shard.
    /\ tid \in shardTxns[s]
    \* Transaction is not prepared.
    /\ tid \notin shardPreparedTxns[s]
    /\ Head(rlog[s][tid]).op = "read"
    /\ Head(rlog[s][tid]).k = k
    \* Read the value of the key from the snapshot store, record the op, and 
    \* advance to the next transaction statement.
    /\ shardOps' = [shardOps EXCEPT ![s][tid] = Append( shardOps[s][tid], rOp(k, ShardMDB(s)!TxnRead(tid, k)) )]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    \* Consume the transaction op.
    /\ rlog' = [rlog EXCEPT ![s][tid] = Tail(rlog[s][tid])]
    /\ ShardMDBTxnRead(s, tid, k)
    /\ UNCHANGED << shardTxns, aborted, rtxn, rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, ops >>    

\* Shard processes a transaction write operation.
ShardTxnWrite(s, tid, k) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    \* Transaction is not prepared.
    /\ tid \notin shardPreparedTxns[s]
    /\ rlog[s][tid] # <<>>
    /\ Head(rlog[s][tid]).op = "write"
    /\ Head(rlog[s][tid]).k = k
    /\ shardOps' = [shardOps EXCEPT ![s][tid] = Append( shardOps[s][tid], wOp(k, tid) )]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    \* Consume the transaction op.
    /\ rlog' = [rlog EXCEPT ![s][tid] = Tail(rlog[s][tid])]
    /\ ShardMDBTxnWrite(s, tid, k)
    /\ UNCHANGED << shardTxns, log,  commitIndex, aborted, epoch,  rtxn, rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, ops >>

\* Shard processes a transaction write operation which encoutners a write conflict, triggering an abort.
ShardTxnWriteConflict(s, tid, k) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    /\ rlog[s][tid] # <<>>
    /\ Head(rlog[s][tid]).op = "write"
    /\ Head(rlog[s][tid]).k = k
    \* Transaction is not prepared.
    /\ tid \notin shardPreparedTxns[s]
    \* The write to this key conflicts with another concurrent transaction on this shard.
    /\ ShardMDB(s)!WriteConflictExists(tid, k)
    /\ ShardMDBTxnAbort(s, tid)
    \* Transaction gets aborted on this shard.
    /\ aborted' = [aborted EXCEPT ![s][tid] = TRUE]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \ {tid}]
    \* Consume the transaction op.
    /\ rlog' = [rlog EXCEPT ![s][tid] = Tail(rlog[s][tid])]
    \* Since it was aborted on this shard, update the transaction's op history.
    /\ shardOps' = [shardOps EXCEPT ![s][tid] = SelectSeq(ops[tid], LAMBDA op : catalog[op.key] # s)]
    /\ UNCHANGED << log, commitIndex, epoch,  rtxn,  rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, ops >>

\*******************
\* Shard 2PC actions.
\*******************

\* Transaction coordinator shard receives a message from router to start coordinating commit for a transaction.
\* In this message, it will also receive the set of shards that are rParticipants in this transaction.
ShardTxnCoordinateCommit(s, tid) == 
    /\ tid \in shardTxns[s]
    /\ rlog[s][tid] # <<>>
    /\ Head(rlog[s][tid]).op = "coordCommit"
    \* I am the coordinator shard of this transaction.
    /\ coordInfo[s][tid].self  
    \* Record the set of all transaction rParticipants and get ready to receive votes (i.e. prepare responses) from them.
    /\ coordInfo' = [coordInfo EXCEPT ![s][tid] = [self |-> TRUE, participants |-> (Head(rlog[s][tid]).participants), committing |-> TRUE]] 
    /\ coordCommitVotes' = [coordCommitVotes EXCEPT ![s][tid] = {}]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    \* Send prepare messages to all participant shards.
    /\ msgsPrepare' = msgsPrepare \cup {[shard |-> p, tid |-> tid, coordinator |-> s] : p \in Range(coordInfo'[s][tid].participants)}
    \* Consume the transaction op.
    /\ rlog' = [rlog EXCEPT ![s][tid] = Tail(rlog[s][tid])]
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch,  rtxn,  aborted, txnSnapshots, rParticipants, msgsVoteCommit, ops, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, shardOps >>

\* Transaction coordinator shard receives a vote from a participant shard to commit a transaction.
ShardTxnCoordinatorRecvCommitVote(s, tid, from) == 
    /\ tid \in shardTxns[s]
    \* We are the coordinator and received coordinateCommit with full participant list, indicating we are now ready to run 2PC to commit.
    /\ coordInfo[s][tid].self 
    /\ coordInfo[s][tid].committing 
    /\ \E m \in msgsVoteCommit : 
        /\ m.shard = from 
        /\ m.tid = tid
        /\ msgsVoteCommit' = msgsVoteCommit \ {m}
        /\ coordCommitVotes' = [coordCommitVotes EXCEPT ![s][tid] = coordCommitVotes[s][tid] \union {<<from,m.prepareTs>>}]
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch, lsn,  rlog, rtxn,  aborted, txnSnapshots, rParticipants, coordInfo, msgsPrepare, ops, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, shardOps >>

\* Coordinator shard decides to commit a transaction, if it has gathered all the necessary commit votes.
ShardTxnCoordinatorDecideCommit(s, tid) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    \* I am the coordinator, and I received all commit votes from rParticipants.
    /\ coordInfo[s][tid].self
    /\ {v[1] : v \in coordCommitVotes[s][tid]} = Range(coordInfo[s][tid].participants)
    /\ LET commitTs == max({v[2] : v \in coordCommitVotes[s][tid]}) IN
            msgsCommit' = msgsCommit \cup { [shard |-> p, tid |-> tid, commitTs |-> commitTs] : p \in Range(coordInfo[s][tid].participants) }
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch, lsn,  rlog, rtxn,  aborted, txnSnapshots, rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, ops, coordCommitVotes, catalog, msgsAbort, rTxnReadTs, shardPreparedTxns, rInCommit, shardOps >>

\* Shard processes a transaction prepare message.
\* Note that it will receive prepare messages from the router, but sends it vote decision to the coordinator shard.
ShardTxnPrepare(s, tid) == 
    \E m \in msgsPrepare : 
        \* TODO: Choose prepareTimestamp for this transaction and track prepared state (?).
        \* Transaction is started on this shard.
        /\ m.shard = s /\ m.tid = tid
        /\ tid \in shardTxns[s]
        /\ tid \notin shardPreparedTxns[s]
        \* We have not aborted.
        /\ ~aborted[s][tid]
        /\ shardPreparedTxns' = [shardPreparedTxns EXCEPT ![s] = shardPreparedTxns[s] \union {tid}]
        \* Prepare and then send your vote to the coordinator.
        /\ LET prepareTs == IF log[s] = <<>> THEN 1 ELSE log[s][Len(log[s])].ts + 1 IN 
                msgsVoteCommit' = msgsVoteCommit \cup { [shard |-> s, tid |-> tid, to |-> m.coordinator, prepareTs |-> prepareTs] }
        \* Prepare the transaction in the underyling snapshot store.
        /\ ShardMDBTxnPrepare(s, tid)
        /\ UNCHANGED << shardTxns, lsn,  rlog, rtxn,  aborted, rParticipants, coordInfo, msgsPrepare, ops, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, rInCommit, shardOps >>

\* Shard receives a commit message for transaction, and commits.
ShardTxnCommit(s, tid) == 
    /\ tid \in shardTxns[s]
    /\ \E m \in msgsCommit : 
        /\ m.shard = s 
        /\ m.tid = tid
        /\ msgsCommit' = msgsCommit \ {m}
        /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \ {tid}]
        /\ shardPreparedTxns' = [shardPreparedTxns EXCEPT ![s] = shardPreparedTxns[s] \ {tid}]
        \* Increment lsn.
        /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
        \* If we commit, we by default clear out any incoming RPC requests.
        /\ rlog' = [rlog EXCEPT ![s][tid] = <<>>]
        /\ ops' = [ops EXCEPT ![tid] = ops[tid] \o shardOps[s][tid]]
        /\ ShardMDBTxnCommit(s, tid, m.commitTs)
    /\ UNCHANGED <<epoch, rtxn, rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, aborted, rTxnReadTs, rInCommit, shardOps >>

\* Shard receives an abort message for transaction, and aborts.
ShardTxnAbort(s, tid) == 
    /\ tid \in shardTxns[s]
    /\ \E m \in msgsAbort : 
        /\ m.shard = s 
        /\ m.tid = tid
        /\ msgsAbort' = msgsAbort \ {m}
    /\ aborted' = [aborted EXCEPT ![s][tid] = TRUE]
    /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \ {tid}]
    \* Since it was aborted on this shard, update the transaction's op history.
    \* We remove all transaction ops that occurred for this transaction on this
    \* shard, by removing ops with keys that (a) were touched by this transaction and
    \* (b) are owned by this shard.
    /\ shardOps' = [shardOps EXCEPT ![s][tid] = <<>>]
    \* If we abort, we by default clear out any incoming RPC requests.
    /\ rlog' = [rlog EXCEPT ![s][tid] = <<>>]
    /\ ShardMDBTxnAbort(s, tid)
    /\ UNCHANGED << log, commitIndex, epoch, lsn,  rtxn,  rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, ops>>


\* Migrate a key from one shard to another.
\* TODO: Abstract placeholder for a more accurate chunk/key migration protocol.
MoveKey(k, sfrom, sto) == 
    /\ sfrom # sto
    /\ catalog' = [catalog EXCEPT ![k] = sto]
    /\ UNCHANGED << shardTxns,   rlog, rtxn, epoch, lsn, txnSnapshots, ops, rParticipants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit, aborted, log, commitIndex >>

Next == 
    \* Router actions.
    \/ \E r \in Router, t \in TxId, ts \in CandidateReadTimestamps : RouterTxnStart(r, t, ts)
    \/ \E r \in Router, s \in Shard, t \in TxId, k \in Keys, op \in Ops : RouterTxnOp(r, s, t, k, op)
    \/ \E r \in Router, s \in Shard, t \in TxId, op \in Ops: RouterTxnCoordinateCommit(r, s, t, op)
    \/ \E r \in Router, s \in Shard, t \in TxId: RouterTxnCommitReadOnly(r, s, t)
    \/ \E r \in Router, s \in Shard, t \in TxId: RouterTxnCommitSingleShard(r, s, t)
    \* TODO: Enable this single write shard optimization once modeled fully.
    \* \/ \E r \in Router, t \in TxId: RouterTxnCommitSingleWriteShard(r, t)
    \* \/ \E r \in Router, t \in TxId : RouterTxnAbort(r, t)
    \* Shard transaction actions.
    \/ \E s \in Shard, tid \in TxId: ShardTxnStart(s, tid)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnRead(s, tid, k)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWrite(s, tid, k)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWriteConflict(s, tid, k)
    \* Shard 2PC actions.
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnPrepare(s, tid)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnCoordinateCommit(s, tid)
    \/ \E s, from \in Shard, tid \in TxId, k \in Keys: ShardTxnCoordinatorRecvCommitVote(s, tid, from)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnCoordinatorDecideCommit(s, tid)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnCommit(s, tid)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnAbort(s, tid)
    \* Environment/background actions (crashes, chunk migration, etc.)
    \* \/ \E k \in Keys, sfrom \in Shard, sto \in Shard : MoveKey(k, sfrom, sto)
    \* \/ \E s \in Shard: Restart(s)
    \* \/ \E s \in Shard : ShardMDBRollback(s)
    \* \/ \E s \in Shard : ShardMDBAdvanceCommitIndex(s)

Fairness == TRUE
    /\ WF_vars(\E r \in Router, s \in Shard, t \in TxId, k \in Keys, op \in Ops: RouterTxnOp(r, s, t, k, op))
    /\ WF_vars(\E r \in Router, s \in Shard, t \in TxId, op \in Ops: RouterTxnCoordinateCommit(r, s, t, op))
    /\ WF_vars(\E r \in Router, s \in Shard, t \in TxId: RouterTxnCommitSingleShard(r, s, t))
    /\ WF_vars(\E r \in Router, t \in TxId: RouterTxnCommitSingleWriteShard(r, t))
    /\ WF_vars(\E r \in Router, t \in TxId : RouterTxnAbort(r, t))
    /\ WF_vars(\E s \in Shard, tid \in TxId: ShardTxnStart(s, tid))
    /\ WF_vars(\E s \in Shard, tid \in TxId, k \in Keys: ShardTxnRead(s, tid, k))
    /\ WF_vars(\E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWrite(s, tid, k))
    /\ WF_vars(\E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWriteConflict(s, tid, k))
    /\ WF_vars(\E s \in Shard, tid \in TxId, k \in Keys: ShardTxnPrepare(s, tid))
    /\ WF_vars(\E s \in Shard, tid \in TxId, k \in Keys: ShardTxnCoordinateCommit(s, tid))
    /\ WF_vars(\E s, from \in Shard, tid \in TxId, k \in Keys: ShardTxnCoordinatorRecvCommitVote(s, tid, from))
    /\ WF_vars(\E s \in Shard, tid \in TxId, k \in Keys: ShardTxnCoordinatorDecideCommit(s, tid))
    /\ WF_vars(\E s \in Shard, tid \in TxId, k \in Keys: ShardTxnCommit(s, tid))
    /\ WF_vars(\E s \in Shard, tid \in TxId, k \in Keys: ShardTxnAbort(s, tid))

Spec == Init /\ [][Next]_vars /\ Fairness

        \* /\ WF_vars(Router)
        \* /\ \A self \in Shard : WF_vars(s(self))


ReadUncommittedIsolation == CC!ReadUncommitted(InitialState, Range(ops))

ReadCommittedIsolation == CC!ReadCommitted(InitialState, Range(ops))

\* Snapshot isolation invariant
SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

\* Serializability would not be satisfied due to write-skew
SerializableIsolation == CC!Serializability(InitialState, Range(ops))

\* For all shards, if they scurrently have a running transaction at any point,
\* then eventually all transactions get committed or aborted on that shard.
AllRunningTransactionsTerminate == \A s \in Shard : (shardTxns[s] # {}) ~> (shardTxns[s] = {})

\* \* LogIndicesImpl == 1..4

\* \* CheckpointsImpl == LogIndicesImpl \cup {0}

\* \* EpochsImpl == 1..3

\* \* SpecificStateSpace ==
\* \*     /\ epoch < EpochMax

BaitLog == 
    /\ TRUE
    \* /\ \A s \in Shard, t \in TxId : aborted[s][t] = FALSE
    \* /\ Cardinality(msgsPrepare) # 2
    \* /\ \A s \in Shard, tid \in TxId : Cardinality(coordCommitVotes[s][tid]) # 1
    /\ \A s \in Shard, tid \in TxId : Cardinality(coordCommitVotes[s][tid]) < 1
    \* /\ \A tid \in TxId : Len(ops[tid]) < 2
    \* /\ coord
    \* /\ \A s \in Shard, t \in TxId : Len(rlog[s][t]) = 0
    \* /\ commitIndex < 5
    \* /\ Len(log) < 6

-----------------------------------------

CONSTANT MaxStmts

KeysOwnedByShard(s) == { k \in Keys : catalog[k] = s }

CatalogConstraint == 
    \* Prevents cases where all keys are distributed to a single shard.
    /\ \A s \in Shard : KeysOwnedByShard(s) # Keys

InitCatalogConstraintKeysOnDifferentShards ==
    \* Prevents cases where all keys are distributed to a single shard (for 3 total keys).
    /\ Init
    /\ \A s \in Shard : Cardinality(KeysOwnedByShard(s)) < Cardinality(Keys)

\* Don't execute more than a max number of statements per transaction.
StateConstraint == 
    /\ \A t \in TxId, r \in Router : rtxn[r][t] <= MaxStmts
    
Symmetry == Permutations(TxId) \cup Permutations(Keys) \cup Permutations(Shard) \cup Permutations(Router)


\* Alias == [
\*     log |-> log,
\*     commitIndex |-> commitIndex,
\*     readIndex |-> readIndex,
\*     epoch |-> epoch
\* ]
===========================================================================
