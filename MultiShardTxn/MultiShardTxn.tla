--------------------------- MODULE MultiShardTxn ---------------------------------
(**************************************************************************)
(* Pluscal algoritm for a simple key-value store with snapshot isolation  *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Util, TLC

CONSTANTS Keys, Values, NoValue, TxId, Shard, STMTS
CONSTANTS WC, RC

\* TxId == Values           \* The set of all transaction IDs

\* Instantiating ClientCentric enables us to check transaction isolation guarantees
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC == INSTANCE ClientCentric WITH Keys <- Keys, Values <- TxId \union {NoValue}          

\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)    
InitialState == [k \in Keys |-> NoValue]   

(* --algorithm ShardedTxns {

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
VARIABLES tx, updated, overlap, rlog, aborted, log, commitIndex, epoch, pc

(* define statement *)
MDB == INSTANCE MDB







ShardMDB(s) == INSTANCE MDB WITH log <- log[s]





ASSUME WC \in MDB!WCVALUES
ASSUME RC \in MDB!RCVALUES

Ops == {"read", "write"}
Entry == [k: Keys, op: Ops]
CreateEntry(k, op, s) == [k |-> k, op |-> op, shard |-> s]

VARIABLES rtxn, lsn, snapshotStore, ops

vars == << tx, updated, overlap, rlog, aborted, log, commitIndex, epoch, pc, 
           rtxn, lsn, snapshotStore, ops >>

ProcSet == {"Router"} \cup (Shard)

Init == (* Global variables *)
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
        /\ snapshotStore = [self \in Shard |-> [k \in Keys |-> NoValue]]
        /\ ops = [self \in Shard |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self = "Router" -> "ROUTER"
                                        [] self \in Shard -> "TXN"]

ROUTER == /\ pc["Router"] = "ROUTER"
          /\ IF \E t \in TxId: rtxn[t] < STMTS
                THEN /\ \E t \in {tid \in TxId: rtxn[tid] < STMTS}:
                          \E k \in Keys:
                            \E op \in Ops:
                              \E s \in Shard:
                                /\ rlog' = [rlog EXCEPT ![s][t] = Append(rlog[s][t], CreateEntry(k, op, s))]
                                /\ rtxn' = [rtxn EXCEPT ![t] = rtxn[t]+1]
                     /\ pc' = [pc EXCEPT !["Router"] = "ROUTER"]
                ELSE /\ pc' = [pc EXCEPT !["Router"] = "Done"]
                     /\ UNCHANGED << rlog, rtxn >>
          /\ UNCHANGED << tx, updated, overlap, aborted, log, commitIndex, 
                          epoch, lsn, snapshotStore, ops >>

Router == ROUTER

TXN(self) == /\ pc[self] = "TXN"
             /\ IF lsn[self] < STMTS
                   THEN /\ \E tid \in TxId:
                             /\ lsn[self] < Len(rlog[self][tid])
                             /\ lsn' = [lsn EXCEPT ![self] = lsn[self] + 1]
                             /\ IF lsn'[self] = 1
                                   THEN /\ tx' = (tx \union {tid})
                                        /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Keys |-> (CHOOSE read \in ShardMDB(self)!Read(k) : TRUE).value]]
                                        /\ overlap' = [t \in TxId |-> IF t = tid THEN tx'
                                                                      ELSE IF t \in tx' THEN overlap[t] \union {tid}
                                                                           ELSE overlap[t]]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << tx, overlap, 
                                                        snapshotStore >>
                        /\ pc' = [pc EXCEPT ![self] = "READ"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << tx, overlap, lsn, snapshotStore >>
             /\ UNCHANGED << updated, rlog, aborted, log, commitIndex, epoch, 
                             rtxn, ops >>

READ(self) == /\ pc[self] = "READ"
              /\ \E tid \in TxId:
                   LET op == rlog[self][tid][lsn[self]].op IN
                     LET k == rlog[self][tid][lsn[self]].k IN
                       IF op = "read"
                          THEN /\ ops' = [ops EXCEPT ![self] = Append( ops[self], rOp(k, snapshotStore[self][k]) )]
                               /\ pc' = [pc EXCEPT ![self] = "TXN"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "WRITE"]
                               /\ ops' = ops
              /\ UNCHANGED << tx, updated, overlap, rlog, aborted, log, 
                              commitIndex, epoch, rtxn, lsn, snapshotStore >>

WRITE(self) == /\ pc[self] = "WRITE"
               /\ \E tid \in TxId:
                    LET op == rlog[self][tid][lsn[self]].op IN
                      LET k == rlog[self][tid][lsn[self]].k IN
                        IF \A t \in overlap[self] \ {tid}: k \notin updated[t]
                           THEN /\ updated' = [updated EXCEPT ![tid] = updated[tid] \union {k}]
                                /\ snapshotStore' = [snapshotStore EXCEPT ![self][k] = tid]
                                /\ ops' = [ops EXCEPT ![self] = Append( ops[self], wOp(k, tid) )]
                                /\ IF lsn[self] = STMTS
                                      THEN /\ log' = log \o SetToSeq({ [key |-> key, value |-> tid]: key \in updated'[tid]})
                                           /\ commitIndex' = Len(log')
                                           /\ tx' = tx \ {tid}
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << tx, log, 
                                                           commitIndex >>
                           ELSE /\ tx' = tx \ {tid}
                                /\ updated' = [updated EXCEPT ![tid] = {}]
                                /\ ops' = [ops EXCEPT ![self] = <<>>]
                                /\ UNCHANGED << log, commitIndex, 
                                                snapshotStore >>
               /\ pc' = [pc EXCEPT ![self] = "TXN"]
               /\ UNCHANGED << overlap, rlog, aborted, epoch, rtxn, lsn >>

s(self) == TXN(self) \/ READ(self) \/ WRITE(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Router
           \/ (\E self \in Shard: s(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Router)
        /\ \A self \in Shard : WF_vars(s(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* \* END TRANSLATION 


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
