--------------------------- MODULE MultiShardTxnTLA ---------------------------------
(**************************************************************************)
(* Pluscal algoritm for a simple key-value store with snapshot isolation  *)
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

(* --COMMENTED_algorithm ShardedTxns {

variables 
    \* The set of open snapshot transactions
    tx = {};

    \* The set of local updates each txn makes
    updated = [t \in TxId |-> {}];
    \* Txns that overlapped with each txn at any point 
    overlap = [t \in TxId |-> {}];   

    \* The router writes transaction operations for a shard to 'rlog', 
    \* and shards scan this log to learn transaction ops that have been routed to them. 
    rlog = [s \in Shard |-> [t \in TxId |->  <<>>]];

    \* Signal aborted txns to the router        
    aborted = [t \in TxId |-> FALSE]; 

    \* We maintain a MongoDB "log" (i.e. a replica set/oplog abstraction) for each shard.
    log = [s \in Shard |-> <<>>];
    commitIndex = [s \in Shard |-> 0]; 
    epoch = [s \in Shard |-> 1];

define {
    MDB == INSTANCE MDB

    \* 
    \* Parameterize the MDB instance with the log of each shard.
    \* 
    \* (This seems one possible approach on how to handle this while using 
    \* the underlying MDB module as an abstraction of replica sets / oplogs.
    \* 
    ShardMDB(s) == INSTANCE MDB WITH log <- log[s]
    
    \* Apparently PlusCal doesn't allow INSTANCE with multiple definitions?
    \* See https://github.com/tlaplus/tlaplus/issues/136
    \* , commitIndex <- commitIndex[s], epoch <- epoch[s]

    ASSUME WC \in MDB!WCVALUES
    ASSUME RC \in MDB!RCVALUES

    Ops == {"read", "write"}
    Entry == [k: Keys, op: Ops]
    CreateEntry(k, op, s) == [k |-> k, op |-> op, shard |-> s] 

    \* See end of file for invariants
}

\* 
\* Router processes new statement for a transaction, and forwards it
\* to appropriate shard. Routers route a statement to shard based on the mapping from 
\* key (??) which determines its position in shard keyspace range?
\* 

fair process (Router = "Router")
variables
    \* track statements in each txn
    rtxn = [t \in TxId |-> 0]; 
{
ROUTER: \*   
    \* while ( \E t \in TxId: rtxn[t] < STMTS /\ ~aborted[t] ) {
    while ( \E t \in TxId: rtxn[t] < STMTS ) {
        \* with (  t \in {tid \in TxId: rtxn[tid] < STMTS /\ ~aborted[tid]};
        with (  t \in {tid \in TxId: rtxn[tid] < STMTS};
                k \in Keys;
                op \in Ops;
                s \in Shard) { 
            \* TODO: Route ops based on shard.
            rlog[s][t]:= Append(rlog[s][t], CreateEntry(k, op, s));
            rtxn[t] := rtxn[t]+1;
        }
    }
}  

\* 
\* Shards process new incoming statement from router, and return with response.
\* 

\* Transaction processing
fair process (s \in Shard)
variables
    lsn = 0;  \* tracks which statement in txn
    snapshotStore = [k \in Keys |-> NoValue];   \* local snapshot of the store
    ops = <<>>;     \* reads & writes txn executes; used for interfacing to CC
{
TXN:  
    \* while ( lsn < STMTS /\ ~aborted[self] ){
    while ( lsn < STMTS ){
        with (tid \in TxId){
        await lsn < Len(rlog[self][tid]); \* router log has new stmt for me
        lsn := lsn + 1;
        if ( lsn = 1 ) { \* initialize txn if first statement
            tx := tx \union {tid};
            snapshotStore := \* take my snapshot of MDB
                [k \in Keys |-> (CHOOSE read \in ShardMDB(self)!Read(k) : TRUE).value];
            overlap := [t \in TxId |-> IF t = tid THEN tx 
                                       ELSE IF t \in tx THEN overlap[t] \union {tid} 
                                            ELSE overlap[t]];
        };       
    };
READ: 
        with (  tid \in TxId;
                op = rlog[self][tid][lsn].op; 
                k = rlog[self][tid][lsn].k; ){
            if (op = "read") {
                \* log read for CC isolation check 
                ops := Append( ops, rOp(k, snapshotStore[k]) );
                goto TXN; 
            }; 
        }; 

WRITE:            
        with (  tid \in TxId;
                op = rlog[self][tid][lsn].op; 
                k = rlog[self][tid][lsn].k; ){        
            \* perform write on my snapshot if there is no conflict with a non-aborted txn
            if ( \A t \in overlap[self] \ {tid}: k \notin updated[t] ) {
                updated[tid] := updated[tid] \union {k}; 
                snapshotStore[k] := tid;
                \* log write for CC isolation check 
                ops := Append( ops, wOp(k, tid) );  

                if ( lsn = STMTS ) { \* end of txn, so COMMIT
                    \* update MDB by writing to logs directly/atomically
                    log := log \o SetToSeq({ [key |-> key, value |-> tid]: key \in updated[tid]});  
                    commitIndex :=  Len(log);
                    tx := tx \ {tid};  \* take self off of active txn set
                };
            } else { \* abort
                    tx := tx \ {tid};  \* take self off of active txn set
                    \* aborted[tid] := TRUE;
                    updated[tid] := {};
                    ops := <<>>; \* update CC view because the txn is aborted
            };
        }
    } \* end while
}
}


}
*)

\* \* BEGIN TRANSLATION (chksum(pcal) = "2ae1c653" /\ chksum(tla) = "d1befa68")

\* MDB == INSTANCE MDB
\* ASSUME WC \in MDB!WCVALUES
\* ASSUME RC \in MDB!RCVALUES


----------------------------------------------------------------------------------------------


\* Set of in-progress transactions per-shard.
VARIABLES shardTxns

\* The router writes transaction operations for a shard to 'rlog', 
\* and shards scan this log to learn transaction ops that have been routed to them. 
VARIABLE rlog 

\* Snapshot of data store for each transaction on each shard.
VARIABLE snapshotStore

\* For each shard and transaction, keeps track of whether that transaction aborted e.g.
\* due to a write conflict.
VARIABLE aborted 

\* For each shard, the set of transactions running concurrently with a given transaction.
VARIABLE overlap 

\* For each shard, the set of keys updated by a transaction running on that shard.
VARIABLE updated

\* We maintain a MongoDB "log" (i.e. a replica set/oplog abstraction) for each shard.
VARIABLE log 
VARIABLE commitIndex 
VARIABLE epoch

\* For each shard and each transaction, a counter which tracks the 
\* current statement number of that transaction. 
VARIABLE lsn

VARIABLE rtxn

VARIABLE ops

vars == << shardTxns, updated, overlap, rlog, aborted, log, commitIndex, epoch, rtxn, lsn, snapshotStore, ops >>

\* Instance of a MongoDB replica set log for a given shard.
ShardMDB(s) == INSTANCE MDB WITH log <- log[s], commitIndex <- commitIndex[s], epoch <- epoch[s]

Ops == {"read", "write", "commit"}
Entry == [k: Keys, op: Ops]
CreateEntry(k, op, s) == [k |-> k, op |-> op, shard |-> s]


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

\* Router handles a new transaction operation that is routed to the appropriate shard.
RouterTxnOp(s, tid, k, op) == 
    \* TODO: Router selects a specific cluster time to start the transaction at (?)
    \* Route the new transaction op to the shard.
    /\ op \in {"read", "write"}
    /\ rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateEntry(k, op, s))]
    /\ rtxn' = [rtxn EXCEPT ![tid] = rtxn[tid]+1]
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, log, commitIndex, epoch, lsn, snapshotStore, ops >>

\* Router handles a transaction commit operation, which it forwards to the appropriate shard to initiate 2PC to
\* commit the transaction.
RouterTxnCommit(s, tid, k, op) == 
    \* TODO: Router handles commits any differently than other ops in terms of forwarding behavior?
    /\ op = "commit"
    /\ rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateEntry(k, op, s))]
    /\ rtxn' = [rtxn EXCEPT ![tid] = rtxn[tid]+1]
    /\ UNCHANGED << shardTxns, updated, overlap, aborted, log, commitIndex, epoch, lsn, snapshotStore, ops >>

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
    /\ UNCHANGED << lsn, updated, rlog, aborted, log, commitIndex, epoch, rtxn, ops >>   

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
    /\ UNCHANGED << shardTxns, updated, overlap, rlog, aborted, log, commitIndex, epoch, rtxn, snapshotStore >>    

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
    /\ UNCHANGED << shardTxns, log, commitIndex, aborted, epoch, overlap, rlog, rtxn >>

\* Shard processes a transaction write operation which encoutners a write conflict, triggering an abort.
ShardTxnWriteConflict(s, tid, k) == 
    \* Transaction started on this shard and has new statements in the router log.
    /\ tid \in shardTxns[s]
    /\ lsn[s][tid] < Len(rlog[s][tid])
    \* The write to this key conflicts with another concurrent transaction on this shard.
    /\ \E t \in overlap[s][tid] \ {tid} : k \notin updated[s][t]
    /\ aborted' = [aborted EXCEPT ![s][tid] = TRUE]
    /\ UNCHANGED << shardTxns, log, commitIndex, epoch, lsn, overlap, rlog, rtxn, updated >>

Next == 
    \/ \E s \in Shard, t \in TxId, k \in Keys, op \in Ops: RouterTxnOp(s, t, k, op)
    \/ \E s \in Shard, tid \in TxId: ShardTxnStart(s, tid)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnRead(s, tid, k)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWrite(s, tid, k)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWriteConflict(s, tid, k)

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
    /\ \A s \in Shard, t \in TxId : Cardinality(overlap[s][t]) <= 1
    \* /\ \A s \in Shard, t \in TxId : lsn[s][t] = 0
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
