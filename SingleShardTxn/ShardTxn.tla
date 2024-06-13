--------------------------- MODULE ShardTxn ---------------------------------
(**************************************************************************)
(* Pluscal algoritm for a simple key-value store with snapshot isolation  *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Util, TLC

CONSTANTS Keys, Values, NoValue, EpochMax
CONSTANTS WC, RC

TxId == Values           \* The set of all transaction IDs

\* Instantiating ClientCentric enables us to check transaction isolation guarantees
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC == INSTANCE ClientCentric WITH Keys <- Keys, Values <- TxId \union {NoValue}          

\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)    
InitialState == [k \in Keys |-> NoValue]   

(* --algorithm KVsnap {

variables 
    \* The set of open snapshot transactions
    tx = {};

    \* The set of writes invisible to each transaction
    missed = [t \in TxId |-> {}];

    \* MDB init
    log = <<>>; 
    commitIndex = 0; 
    epoch = 1;

define {
    MDB == INSTANCE MDB
    ASSUME WC \in MDB!WCVALUES
    ASSUME RC \in MDB!RCVALUES

    \* See end of file for invariants
}

\* Transaction processing
fair process (t \in TxId)
variables
    snapshotStore = [k \in Keys |-> NoValue], \* local snapshot of the store
    read_keys  = {},   \* read keys  for the transaction
    write_keys = {},   \* write keys for the transaction 
    ops = <<>>;   \* a log of reads & writes this transaction executes; used for interfacing to CC
{
START: \* Start the transaction
    tx := tx \union {self};
    snapshotStore := \* take my snapshot of MDB
        [k \in Keys |-> (CHOOSE read \in MDB!Read(k) : TRUE).value];

    with (rk \in SUBSET Keys \ { {} }; wk \in SUBSET Keys \ { {} }) {
        read_keys := rk;     \* select a random read-key-set  from possible read-keys
        write_keys := wk;    \* select a random write-key-set from possible write-keys  
    };


READ: \* Perform reads on my snapshot          
    \* log reads for CC isolation check 
    ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k \in read_keys}); 
    
EXEC: \* Execute the transaction if there is no conflict   
    if (missed[self] \intersect write_keys = {}) { 
        \* Perform writes on my snapshot, write 'self' as value
        snapshotStore := [k \in Keys |-> IF k \in write_keys THEN self ELSE snapshotStore[k] ];    

        \* take self off of active txn set
        tx := tx \ {self}; 

        \* Update the missed writes for other open transactions (nonlocal update!)
        missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
        
        \* update MDB by writing to logs directly/atomically
        log := log \o SetToSeq({ [key |-> k, value |-> self]: k \in write_keys});  
        commitIndex :=  Len(log);

        \* log writes for CC isolation check 
        ops := ops \o SetToSeq({wOp(k, self): k \in write_keys}); 
    } else { \* abort
        \* take self off of active txn set
        tx := tx \ {self};         
    }
}


}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "3075ef0a" /\ chksum(tla) = "edc99a51")
VARIABLES tx, missed, log, commitIndex, epoch, pc

(* define statement *)
MDB == INSTANCE MDB
ASSUME WC \in MDB!WCVALUES
ASSUME RC \in MDB!RCVALUES

VARIABLES snapshotStore, read_keys, write_keys, ops

vars == << tx, missed, log, commitIndex, epoch, pc, snapshotStore, read_keys, 
           write_keys, ops >>

ProcSet == (TxId)

Init == (* Global variables *)
        /\ tx = {}
        /\ missed = [t \in TxId |-> {}]
        /\ log = <<>>
        /\ commitIndex = 0
        /\ epoch = 1
        (* Process t *)
        /\ snapshotStore = [self \in TxId |-> [k \in Keys |-> NoValue]]
        /\ read_keys = [self \in TxId |-> {}]
        /\ write_keys = [self \in TxId |-> {}]
        /\ ops = [self \in TxId |-> <<>>]
        /\ pc = [self \in ProcSet |-> "START"]

START(self) == /\ pc[self] = "START"
               /\ tx' = (tx \union {self})
               /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Keys |-> (CHOOSE read \in MDB!Read(k) : TRUE).value]]
               /\ \E rk \in SUBSET Keys \ { {} }:
                    \E wk \in SUBSET Keys \ { {} }:
                      /\ read_keys' = [read_keys EXCEPT ![self] = rk]
                      /\ write_keys' = [write_keys EXCEPT ![self] = wk]
               /\ pc' = [pc EXCEPT ![self] = "READ"]
               /\ UNCHANGED << missed, log, commitIndex, epoch, ops >>

READ(self) == /\ pc[self] = "READ"
              /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({rOp(k, snapshotStore[self][k]): k \in read_keys[self]})]
              /\ pc' = [pc EXCEPT ![self] = "EXEC"]
              /\ UNCHANGED << tx, missed, log, commitIndex, epoch, 
                              snapshotStore, read_keys, write_keys >>

EXEC(self) == /\ pc[self] = "EXEC"
              /\ IF missed[self] \intersect write_keys[self] = {}
                    THEN /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Keys |-> IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k] ]]
                         /\ tx' = tx \ {self}
                         /\ missed' = [o \in TxId |-> IF o \in tx' THEN missed[o] \union write_keys[self] ELSE missed[o]]
                         /\ log' = log \o SetToSeq({ [key |-> k, value |-> self]: k \in write_keys[self]})
                         /\ commitIndex' = Len(log')
                         /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({wOp(k, self): k \in write_keys[self]})]
                    ELSE /\ tx' = tx \ {self}
                         /\ UNCHANGED << missed, log, commitIndex, 
                                         snapshotStore, ops >>
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << epoch, read_keys, write_keys >>

t(self) == START(self) \/ READ(self) \/ EXEC(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in TxId: t(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in TxId : WF_vars(t(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


\* Snapshot isolation invariant
SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

TypeOK == \* type invariant
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Keys] 


\* Serializability would not be satisfied due to write-skew
Serialization == CC!Serializability(InitialState, Range(ops))

TxIdSymmetric == Permutations(TxId)

\* LogIndicesImpl == 1..4

\* CheckpointsImpl == LogIndicesImpl \cup {0}

\* EpochsImpl == 1..3

SpecificStateSpace ==
    /\ epoch < EpochMax

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
