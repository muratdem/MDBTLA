--------------------------- MODULE MultiShardTxn ---------------------------------
(**************************************************************************)
(* Model of distributed, cross-shard transactions in MongoDB.             *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Util, TLC

CONSTANTS Keys, TxId, Shard
CONSTANT NoValue
CONSTANTS WC, RC

\* Instantiating ClientCentric enables us to check transaction isolation guarantees
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC == INSTANCE ClientCentric WITH Keys <- Keys, Values <- TxId \union {NoValue}          

\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)    
InitialState == [k \in Keys |-> NoValue]   

\* The router writes transaction operations for a shard to 'rlog', 
\* and shards scan this log to learn transaction ops that have been routed to them. 
VARIABLE rlog 

\* Prepare transaction messages sent from the router to participant shards.
VARIABLE msgsPrepare
VARIABLE msgsVoteCommit
VARIABLE msgsAbort
VARIABLE msgsCommit

\* Set of in-progress transactions on each shard.
VARIABLES shardTxns

VARIABLE shardPreparedTxns

\* Set of commit votes recorded by each coordinator shard, for each transaction.
VARIABLE coordCommitVotes

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
VARIABLE coordInfo

\* For each transaction, the router tracks a list of shards that are participants in that
\* transaction. The router forwards this information to the coordinator when ready to commit.
\* By default, the first participant in this list is designated as the coordinator.
VARIABLE participants


\* The read timestamp being used for each running transaction on the router.
VARIABLE rTxnReadTs

\* Tracks whether a transaction at the router has initiated commit.
VARIABLE rInCommit

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

vars == << shardTxns, rInCommit, updated, overlap, rlog, aborted, log, commitIndex, epoch, rtxn, lsn, snapshotStore, ops, participants, coordInfo, msgsPrepare, msgsVoteCommit, msgsAbort, coordCommitVotes, catalog, msgsCommit, rTxnReadTs, shardPreparedTxns >>

\* Instance of a MongoDB replica set log for a given shard.
ShardMDB(s) == INSTANCE MDB WITH mlog <- log[s], mcommitIndex <- commitIndex[s], mepoch <- epoch[s], Values <- TxId

Ops == {"read", "write", "coordCommit"}
Entry == [k: Keys, op: Ops]
CreateEntry(k, op, s, coord, ts) == [k |-> k, op |-> op, shard |-> s, coordinator |-> coord, readTs |-> ts]
CreateCoordCommitEntry(op, s, p) == [op |-> op, shard |-> s, participants |-> p]


Init ==
    /\ rlog = [s \in Shard |-> [t \in TxId |->  <<>>]]
    /\ shardTxns = [s \in Shard |-> {}]
    /\ rtxn = [t \in TxId |-> 0]
    /\ lsn = [s \in Shard |-> [t \in TxId |-> 0]]
    /\ snapshotStore = [s \in Shard |-> [t \in TxId |-> [ts |-> NoValue, data |-> [k \in Keys |-> NoValue]]]]
    /\ updated = [s \in Shard |-> [t \in TxId |-> {}]]
    /\ overlap = [s \in Shard |-> [t \in TxId |-> {}]]
    /\ ops = [s \in TxId |-> <<>>]
    /\ aborted = [s \in Shard |-> [t \in TxId |-> FALSE]]
    /\ log = [s \in Shard |-> <<>>]
    /\ commitIndex = [s \in Shard |-> 0]
    /\ epoch = [s \in Shard |-> 1]
    /\ participants = [t \in TxId |-> <<>>]
    /\ coordInfo = [s \in Shard |-> [t \in TxId |-> [self |-> FALSE, participants |-> <<>>, committing |-> FALSE]]]
    /\ msgsPrepare = {}
    /\ msgsVoteCommit = {}
    /\ msgsAbort = {}
    /\ msgsCommit = {}
    /\ coordCommitVotes = [s \in Shard |-> [t \in TxId |-> {}]]
    /\ catalog \in [Keys -> Shard]
    /\ rTxnReadTs = [t \in TxId |-> NoValue]
    /\ rInCommit = [t \in TxId |-> FALSE]
    /\ shardPreparedTxns = [s \in Shard |-> {}]

\*****************************************
\* Router transaction operations.
\*****************************************

\* Router handles a new transaction operation that is routed to the appropriate shard.
RouterTxnOp(s, tid, k, op) == 
    /\ op \in {"read", "write"}
    \* If a shard of this transaction has aborted, don't continue the transaction.
    /\ ~\E as \in Shard : aborted[as][tid]
    \* Transaction has not already initiated commit at the router.
    /\ rInCommit[tid] = FALSE
    \* Route to the shard that owns this key.
    /\ catalog[k] = s
    \* For now, we just pick our read timestamp as the latest timestamp on the
    \* currently targeted shard. In practice, a best effort guess at read
    \* timestamp to select will be maintained on a router based on previous
    \* responses from commands.
    /\ rTxnReadTs' = [rTxnReadTs EXCEPT ![tid] = IF rTxnReadTs[tid] = NoValue THEN Len(log[s]) ELSE rTxnReadTs[tid]]
    /\ rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateEntry(k, op, s, rtxn[tid] = 0, rTxnReadTs'[tid]))]
    /\ rtxn' = [rtxn EXCEPT ![tid] = rtxn[tid]+1]
    \* Update participants list if new participant joined the transaction.
    /\ participants' = [participants EXCEPT ![tid] = participants[tid] \o (IF s \in Range(participants[tid]) THEN <<>> ELSE <<s>>)]
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, log, commitIndex, epoch, lsn, snapshotStore, ops,coordInfo, msgsPrepare, msgsVoteCommit, msgsAbort, coordCommitVotes, catalog, msgsCommit, shardPreparedTxns, rInCommit >>

\* Router handles a transaction commit operation, which it forwards to the appropriate shard to initiate 2PC to
\* commit the transaction. It also sends out prepare messages to all participant shards.
RouterTxnCoordinateCommit(s, tid, op) == 
    /\ op = "coordCommit"
    \* Transaction has started and has targeted multiple shards.
    /\ Len(participants[tid]) > 1
    \* No shard of this transaction has aborted.
    /\ ~\E as \in Shard : aborted[as][tid]
    /\ s = participants[tid][1] \* Coordinator shard is the first participant in the list.
    \* Send coordinate commit message to the coordinator shard.
    /\ rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateCoordCommitEntry(op, s, participants[tid]))]
    /\ rtxn' = [rtxn EXCEPT ![tid] = rtxn[tid]+1]
    /\ rInCommit' = [rInCommit EXCEPT ![tid] = TRUE]
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, log, commitIndex, epoch, lsn, snapshotStore, ops, participants, coordInfo, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, msgsPrepare, rTxnReadTs, shardPreparedTxns >>

\* If a transaction only targeted a single shard, then the router can commit the
\* transaction without going through a full 2PC. Instead, it just sends a commit
\* message directly to that shard.
RouterTxnCommitSingleShard(s, tid) == 
    \* Transaction has targeted this single shard.
    /\ participants[tid] = <<s>>
    \* Shard hasn't aborted.
    /\ ~aborted[s][tid]
    \* Send commit message directly to shard (bypass 2PC).
    /\ msgsCommit' = msgsCommit \cup { [shard |-> s, tid |-> tid] }
    /\ rInCommit' = [rInCommit EXCEPT ![tid] = TRUE]
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, rlog, rtxn, log, commitIndex, epoch, lsn, snapshotStore, ops, participants, coordInfo, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsPrepare, rTxnReadTs, shardPreparedTxns >>

\* The set of shard participants for a transaction that were written to.
WriteParticipants(tid) == {s \in Shard : \E i \in DOMAIN rlog[s][tid] : rlog[s][tid][i].op = "write"}

\* If a transaction has touched multiple shards, but only written to a single
\* shard, then we optimize this case by first sending commits directly to the
\* read only shards, and then, if these are successfully, directly sending
\* commit to the write shard.
\* TODO: Send commit to write shards upon hearing read responses.
RouterTxnCommitSingleWriteShard(tid) == 
    \* Transaction has started and has targeted multiple shards,
    \* but only written to a single shard.
    /\ Len(participants[tid]) > 1
    /\ Cardinality(WriteParticipants(tid)) = 1
    \* No shard of this transaction has aborted.
    /\ ~\E as \in Shard : aborted[as][tid]
    \* Send commit message directly to shard (bypass 2PC).
    /\ msgsCommit' = msgsCommit \cup { [shard |-> s, tid |-> tid] : s \in (Shard \ WriteParticipants(tid))}
    /\ rInCommit' = [rInCommit EXCEPT ![tid] = TRUE]
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, rlog, rtxn, log, commitIndex, epoch, lsn, snapshotStore, ops, participants, coordInfo, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsPrepare, rTxnReadTs, shardPreparedTxns >>

\* 
\* Router aborts the transaction, which it can do at any point.
\* 
\* In practice, a router may also abort if it hears about failure of a statement
\* executed in the midst of an ongoing transaction (e.g. due to write conflict),
\* but this covers the more general case i.e. where a router could potentially
\* send abort at any time for any reason (e.g client sends explicit abort.)
\* 
RouterTxnAbort(tid) == 
    /\ participants[tid] # <<>>
    /\ msgsAbort' = msgsAbort \cup {[tid |-> tid, shard |-> s] : s \in Range(participants[tid])}
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, log, commitIndex, epoch, lsn, snapshotStore, ops, rlog, rtxn, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, participants, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit >>


\*****************************************
\* Shard transaction operations.
\*****************************************

\* Shard starts a new transaction.
ShardTxnStart(s, tid) == 
    \* First transaction statement.
    /\ lsn[s][tid] = 0 
    \* Transaction has new read/write statements in the router log, and has not been started on this shard yet.
    /\ lsn[s][tid] < Len(rlog[s][tid])
    /\ tid \notin shardTxns[s]
    /\ rlog[s][tid][lsn[s][tid] + 1].op \in {"read", "write"}
    \* Cannot start a transaction at a timestamp T if there is another 
    \* currently prepared transaction at timestamp < T.
    /\ ~\E tother \in TxId : 
        /\ tother \in shardPreparedTxns[s] 
        /\ snapshotStore[s][tother].ts < rlog[s][tid][lsn[s][tid] + 1].readTs
    \* We don't advance to the next statement (lsn), but mark the transaction as
    \* having started on this shard, so transaction statements can now be processed.
    /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \union {tid}]
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    \* Store the timestamp of the snapshot read as well, alongside the key-value snapshot.
    /\ LET readTs == rlog[s][tid][lsn[s][tid] + 1].readTs IN
        snapshotStore' = [snapshotStore EXCEPT ![s][tid] = 
                            [
                                ts |-> readTs,
                                data |-> [k \in Keys |-> ShardMDB(s)!SnapshotRead(k, readTs).value]
                            ]]
    \* Update the record of which transactions are running concurrently with each other.
    /\ coordInfo' = [coordInfo EXCEPT ![s][tid] = [self |-> rlog[s][tid][lsn[s][tid] + 1].coordinator, participants |-> <<s>>, committing |-> FALSE]]
    /\ UNCHANGED << lsn, updated, rlog, aborted, overlap, log, commitIndex, epoch, rtxn, ops, participants, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit >>   

\* Shard processes a transaction read operation.
ShardTxnRead(s, tid, k) == 
    \* Transaction has new statements in the router log.
    /\ lsn[s][tid] < Len(rlog[s][tid])
    \* Transaction has started running on this shard.
    /\ tid \in shardTxns[s]
    \* Transaction is not prepared.
    /\ tid \notin shardPreparedTxns[s]
    /\ rlog[s][tid][lsn[s][tid] + 1].op = "read"
    /\ rlog[s][tid][lsn[s][tid] + 1].k = k
    \* Read the value of the key from the snapshot store, record the op, and 
    \* advance to the next transaction statement.
    /\ ops' = [ops EXCEPT ![tid] = Append( ops[tid], rOp(k, snapshotStore[s][tid].data[k]) )]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    /\ UNCHANGED << shardTxns, updated, overlap, rlog, aborted, log, commitIndex, epoch, rtxn, snapshotStore, participants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit >>    

\* Alternate equivalent definition of the above.
WriteConflictExists(s, tid, k) ==
    \E tOther \in TxId \ {tid}: 
    \E val \in updated[s][tOther] :
        \* Someone else wrote to this key at a timestamp newer than your snapshot.
        /\ val[1] = k
        /\ val[2] > snapshotStore[s][tid].ts

\* Shard processes a transaction write operation.
ShardTxnWrite(s, tid, k) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    \* Transaction is not prepared.
    /\ tid \notin shardPreparedTxns[s]
    /\ lsn[s][tid] < Len(rlog[s][tid])
    /\ rlog[s][tid][lsn[s][tid] + 1].op = "write"
    /\ rlog[s][tid][lsn[s][tid] + 1].k = k
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ ~WriteConflictExists(s, tid, k)
    \* Update the transaction's snapshot data, and advance to the next statement.
    /\ snapshotStore' = [snapshotStore EXCEPT ![s][tid]["data"][k] = tid]
    \* Record timestamp of the write to the key as well.
    /\ updated' = [updated EXCEPT ![s][tid] = updated[s][tid] \union {<<k,snapshotStore[s][tid].ts + 1>>}]
    /\ ops' = [ops EXCEPT ![tid] = Append( ops[tid], wOp(k, tid) )]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    /\ UNCHANGED << shardTxns, log, commitIndex, aborted, epoch, overlap, rlog, rtxn, participants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit >>

\* Shard processes a transaction write operation which encoutners a write conflict, triggering an abort.
ShardTxnWriteConflict(s, tid, k) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    /\ lsn[s][tid] < Len(rlog[s][tid])
    /\ rlog[s][tid][lsn[s][tid] + 1].op = "write"
    /\ rlog[s][tid][lsn[s][tid] + 1].k = k
    \* Transaction is not prepared.
    /\ tid \notin shardPreparedTxns[s]
    \* The write to this key conflicts with another concurrent transaction on this shard.
    /\ WriteConflictExists(s, tid, k)
    \* Transaction gets aborted on this shard.
    /\ aborted' = [aborted EXCEPT ![s][tid] = TRUE]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \ {tid}]
    /\ UNCHANGED << log, commitIndex, epoch, overlap, rlog, rtxn, updated, snapshotStore, ops, participants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit >>

\*******************
\* Shard 2PC actions.
\*******************

\* Transaction coordinator shard receives a message from router to start coordinating commit for a transaction.
\* In this message, it will also receive the set of shards that are participants in this transaction.
ShardTxnCoordinateCommit(s, tid) == 
    /\ tid \in shardTxns[s]
    /\ lsn[s][tid] < Len(rlog[s][tid])
    /\ rlog[s][tid][lsn[s][tid] + 1].op = "coordCommit"
    \* I am the coordinator shard of this transaction.
    /\ coordInfo[s][tid].self  
    \* Record the set of all transaction participants and get ready to receive votes (i.e. prepare responses) from them.
    /\ coordInfo' = [coordInfo EXCEPT ![s][tid] = [self |-> TRUE, participants |-> (rlog[s][tid][lsn[s][tid] + 1].participants), committing |-> TRUE]] 
    /\ coordCommitVotes' = [coordCommitVotes EXCEPT ![s][tid] = {}]
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    \* Send prepare messages to all participant shards.
    /\ msgsPrepare' = msgsPrepare \cup {[shard |-> p, tid |-> tid, coordinator |-> s] : p \in Range(coordInfo'[s][tid].participants)}
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch, overlap, rlog, rtxn, updated, aborted, snapshotStore, participants, msgsVoteCommit, ops, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit >>

\* Transaction coordinator shard receives a vote from a participant shard to commit a transaction.
ShardTxnCoordinatorRecvCommitVote(s, tid, from) == 
    /\ tid \in shardTxns[s]
    /\ \E m \in msgsVoteCommit : m.shard = from /\ m.tid = tid
    \* We are the coordinator and received coordinateCommit with full participant list, indicating we are now ready to run 2PC to commit.
    /\ coordInfo[s][tid].self 
    /\ coordInfo[s][tid].committing  
    /\ coordCommitVotes' = [coordCommitVotes EXCEPT ![s][tid] = coordCommitVotes[s][tid] \union {from}]
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch, lsn, overlap, rlog, rtxn, updated, aborted, snapshotStore, participants, coordInfo, msgsPrepare, msgsVoteCommit, ops, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit >>

\* Coordinator shard decides to commit a transaction, if it has gathered all the necessary commit votes.
ShardTxnCoordinatorDecideCommit(s, tid) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    \* I am the coordinator, and I received all commit votes from participants.
    /\ coordInfo[s][tid].self
    /\ coordCommitVotes[s][tid] = Range(coordInfo[s][tid].participants)
    /\ msgsCommit' = msgsCommit \cup { [shard |-> p, tid |-> tid] : p \in Range(coordInfo[s][tid].participants) }
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch, lsn, overlap, rlog, rtxn, updated, aborted, snapshotStore, participants, coordInfo, msgsPrepare, msgsVoteCommit, ops, coordCommitVotes, catalog, msgsAbort, rTxnReadTs, shardPreparedTxns, rInCommit >>

\* Shard processes a transaction prepare message.
\* Note that it will receive prepare messages from the router, but sends it vote decision to the coordinator shard.
ShardTxnPrepare(s, tid) == 
    \E m \in msgsPrepare : 
        \* TODO: Choose prepareTimestamp for this transaction and track prepared state (?).
        \* Transaction is started on this shard.
        /\ tid \in shardTxns[s]
        /\ tid \notin shardPreparedTxns[s]
        \* We have not aborted.
        /\ ~aborted[s][tid]
        /\ shardPreparedTxns' = [shardPreparedTxns EXCEPT ![s] = shardPreparedTxns[s] \union {tid}]
        /\ m.shard = s /\ m.tid = tid
        \* Prepare and then send your vote to the coordinator.
        /\ msgsVoteCommit' = msgsVoteCommit \cup { [shard |-> s, tid |-> tid, to |-> m.coordinator] }
        /\ UNCHANGED << shardTxns, log, commitIndex, epoch, lsn, overlap, rlog, rtxn, updated, aborted, snapshotStore, participants, coordInfo, msgsPrepare, ops, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, rInCommit >>

\* Shard receives a commit message for transaction, and commits.
ShardTxnCommit(s, tid) == 
    /\ tid \in shardTxns[s]
    /\ \E m \in msgsCommit : m.shard = s /\ m.tid = tid
    /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \ {tid}]
    /\ shardPreparedTxns' = [shardPreparedTxns EXCEPT ![s] = shardPreparedTxns[s] \ {tid}]
    \* Write all updated keys back to the shard oplog.
    /\ log' = [log EXCEPT ![s] = log[s] \o SetToSeq({[key |-> key, value |-> tid]: <<key,ts>> \in updated[s][tid]})]
    /\ commitIndex' = [commitIndex EXCEPT ![s] = Len(log'[s])]
    \* Increment lsn.
    /\ lsn' = [lsn EXCEPT ![s][tid] = lsn[s][tid] + 1]
    \* Remove prepared keys.
    /\ UNCHANGED <<  overlap, rlog, epoch, rtxn, updated, participants, coordInfo, msgsPrepare, snapshotStore, msgsVoteCommit, ops, coordCommitVotes, catalog, msgsAbort, msgsCommit, aborted, rTxnReadTs, rInCommit >>

\* Shard receives an abort message for transaction, and aborts.
ShardTxnAbort(s, tid) == 
    /\ tid \in shardTxns[s]
    /\ \E m \in msgsAbort : m.shard = s /\ m.tid = tid
    /\ aborted' = [aborted EXCEPT ![s][tid] = TRUE]
    /\ shardTxns' = [shardTxns EXCEPT ![s] = shardTxns[s] \ {tid}]
    \* Since it was aborted on this shard, update the transaction's op history.
    \* We remove all transaction ops that occurred for this transaction on this
    \* shard, by removing ops with keys that (a) were touched by this transaction and
    \* (b) are owned by this shard.
    /\ ops' = [ops EXCEPT ![tid] = SelectSeq(ops[tid], LAMBDA op : catalog[op.key] # s)]
    /\ UNCHANGED << log, commitIndex, epoch, lsn, overlap, rlog, rtxn, updated, snapshotStore, participants, coordInfo, msgsPrepare, msgsVoteCommit, coordCommitVotes, catalog, msgsAbort, msgsCommit, rTxnReadTs, shardPreparedTxns, rInCommit>>


Next == 
    \* Router actions.
    \/ \E s \in Shard, t \in TxId, k \in Keys, op \in Ops: RouterTxnOp(s, t, k, op)
    \/ \E s \in Shard, t \in TxId, op \in Ops: RouterTxnCoordinateCommit(s, t, op)
    \/ \E s \in Shard, t \in TxId: RouterTxnCommitSingleShard(s, t)
    \/ \E t \in TxId: RouterTxnCommitSingleWriteShard(t)
    \/ \E t \in TxId : RouterTxnAbort(t)
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



Fairness ==
    /\ WF_vars(\E s \in Shard, t \in TxId, k \in Keys, op \in Ops: RouterTxnOp(s, t, k, op))
    /\ WF_vars(\E s \in Shard, t \in TxId, op \in Ops: RouterTxnCoordinateCommit(s, t, op))
    /\ WF_vars(\E t \in TxId : RouterTxnAbort(t))


Spec == Init /\ [][Next]_vars /\ Fairness

        \* /\ WF_vars(Router)
        \* /\ \A self \in Shard : WF_vars(s(self))

\* Snapshot isolation invariant
SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

\* Serializability would not be satisfied due to write-skew
Serialization == CC!Serializability(InitialState, Range(ops))

\* Eventually all shards end up in a state with no more running transactions.
AllTransactionsTerminate == \A s \in Shard : <>(Cardinality(shardTxns[s]) = 0)

\* \* LogIndicesImpl == 1..4

\* \* CheckpointsImpl == LogIndicesImpl \cup {0}

\* \* EpochsImpl == 1..3

\* \* SpecificStateSpace ==
\* \*     /\ epoch < EpochMax

BaitLog == 
    /\ TRUE
    \* /\ \A s \in Shard, t \in TxId : Cardinality(overlap[s][t]) <= 1
    \* /\ \A s \in Shard, t \in TxId : aborted[s][t] = FALSE
    \* /\ Cardinality(msgsPrepare) # 2
    \* /\ \A s \in Shard, tid \in TxId : Cardinality(coordCommitVotes[s][tid]) # 1
    /\ \A tid \in TxId : Len(ops[tid]) < 2
    \* /\ \A s \in Shard, t \in TxId : Len(rlog[s][t]) = 0
    \* /\ commitIndex < 5
    \* /\ Len(log) < 6

-----------------------------------------

CONSTANT MaxStmts

KeysOwnedByShard(s) == { k \in Keys : catalog[k] = s }

CatalogConstraint == 
    \* Prevents cases where all keys are distributed to a single shard.
    /\ \A s \in Shard : KeysOwnedByShard(s) # Keys

\* Don't execute more than a max number of statements per transaction.
StateConstraint == 
    /\ \A t \in TxId : rtxn[t] <= MaxStmts
    
Symmetry == Permutations(TxId) \cup Permutations(Keys) \cup Permutations(Shard)


\* Alias == [
\*     log |-> log,
\*     commitIndex |-> commitIndex,
\*     readIndex |-> readIndex,
\*     epoch |-> epoch
\* ]
===========================================================================
