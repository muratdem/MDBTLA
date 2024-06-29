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


VARIABLES tx
VARIABLE overlap 

\* The router writes transaction operations for a shard to 'rlog', 
\* and shards scan this log to learn transaction ops that have been routed to them. 
VARIABLE rlog 

VARIABLE aborted 
VARIABLE updated

\* We maintain a MongoDB "log" (i.e. a replica set/oplog abstraction) for each shard.
VARIABLE log 
VARIABLE commitIndex 
VARIABLE epoch

\* Snapshot of data store for each transaction on each shard.
VARIABLE snapshotStore

VARIABLES rtxn, lsn, ops

vars == << tx, updated, overlap, rlog, aborted, log, commitIndex, epoch, rtxn, lsn, snapshotStore, ops >>

\* Instance of a MongoDB replica set log for a given shard.
ShardMDB(s) == INSTANCE MDB WITH log <- log[s], commitIndex <- commitIndex[s], epoch <- epoch[s]

Ops == {"read", "write"}
Entry == [k: Keys, op: Ops]
CreateEntry(k, op, s) == [k |-> k, op |-> op, shard |-> s]


\* ProcSet == {"Router"} \cup (Shard)

Init ==
    /\ tx = {}
    /\ updated = [t \in TxId |-> {}]
    /\ overlap = [t \in TxId |-> {}]
    /\ rlog = [s \in Shard |-> [t \in TxId |->  <<>>]]
    /\ aborted = [t \in TxId |-> FALSE]
    /\ log = [s \in Shard |-> <<>>]
    /\ commitIndex = [s \in Shard |-> 0]
    /\ epoch = [s \in Shard |-> 1]
    (* Process Router *)
    /\ rtxn = [t \in TxId |-> 0]
    (* Process s *)
    /\ lsn = [self \in Shard |-> 0]
    /\ snapshotStore = [s \in Shard |-> [t \in TxId |-> [k \in Keys |-> NoValue]]]
    /\ ops = [self \in Shard |-> <<>>]

\* 
\* Router handles a new transaction operation that is routed to the appropriate shard.
\* 
RouterOp(s, tid, k, op) == 
    \* Route the new transaction op to the shard.
    /\ rlog' = [rlog EXCEPT ![s][tid] = Append(rlog[s][tid], CreateEntry(k, op, s))]
    /\ rtxn' = [rtxn EXCEPT ![tid] = rtxn[tid]+1]
    /\ UNCHANGED << tx, updated, overlap, aborted, log, commitIndex, epoch, lsn, snapshotStore, ops >>


\*****************************************
\* Shard transaction operations.
\*****************************************

\* Shard starts a new transaction.
ShardTxnStart(s, tid) == 
    /\ lsn[s] < Len(rlog[s][tid])
    /\ lsn[s] < STMTS
    /\ lsn' = [lsn EXCEPT ![s] = lsn[s] + 1]
    /\ lsn'[s] = 1
    /\ tx' = (tx \union {tid})
    /\ snapshotStore' = [snapshotStore EXCEPT ![s][tid] = [k \in Keys |-> (CHOOSE read \in ShardMDB(s)!Read(k) : TRUE).value]]
    /\ overlap' = [t \in TxId |-> IF t = tid THEN tx' ELSE IF t \in tx' THEN overlap[t] \union {tid} ELSE overlap[t]]
    /\ UNCHANGED << updated, rlog, aborted, log, commitIndex, epoch, rtxn, ops >>   

\* Shard processes a transaction read operation.
ShardTxnRead(s, tid, k) == 
    /\ rlog[s][tid][lsn[s]].op = "read"
    /\ rlog[s][tid][lsn[s]].k = k
    /\ ops' = [ops EXCEPT ![s] = Append( ops[s], rOp(k, snapshotStore[s][tid][k]) )]
    /\ UNCHANGED << tx, updated, overlap, rlog, aborted, log, commitIndex, epoch, rtxn, lsn, snapshotStore >>    

\* Shard processes a transaction write operation.
ShardTxnWrite(s, tid, k) == 
    \* TODO: Implement properly.
    \* /\ \A t \in overlap[self] \ {tid}: k \notin updated[t]
    /\ updated' = [updated EXCEPT ![tid] = updated[tid] \union {k}]
    /\ snapshotStore' = [snapshotStore EXCEPT ![s][tid][k] = tid]
    /\ ops' = [ops EXCEPT ![tid] = Append( ops[tid], wOp(k, tid) )]
    \* /\ lsn[self] = STMTS
    /\ UNCHANGED << tx, log, commitIndex >>

Next == 
    \/ \E s \in Shard, t \in TxId, k \in Keys, op \in Ops: RouterOp(s, t, k, op)
    \/ \E s \in Shard, tid \in TxId: ShardTxnStart(s, tid)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnRead(s, tid, k)
    \/ \E s \in Shard, tid \in TxId, k \in Keys: ShardTxnWrite(s, tid, k)

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
    \* /\ commitIndex < 5
    \* /\ Len(log) < 6
    
\* Alias == [
\*     log |-> log,
\*     commitIndex |-> commitIndex,
\*     readIndex |-> readIndex,
\*     epoch |-> epoch
\* ]
===========================================================================
