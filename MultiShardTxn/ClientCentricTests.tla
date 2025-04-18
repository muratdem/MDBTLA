--------------------------- MODULE ClientCentricTests ---------------------------
EXTENDS TLC, Util

NoValue == "NoValue"

\* 
\* Snapshot isolation example tests.
\* 


CC == INSTANCE ClientCentric WITH 
                    Keys <- {"k1", "k2"}, 
                    Values <- {"t1", "t2"} \union {NoValue}          

Ops1 == 
     ( 
        "t1" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "read", value |-> NoValue, key |-> "k2"],
               [op |-> "write", value |-> "t1", key |-> "k1"] >> @@
        "t2" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "read", value |-> NoValue, key |-> "k2"],
               [op |-> "write", value |-> "t2", key |-> "k1"] >> )

ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(Ops1)) = FALSE


OpsReadYourWrite == 
     ( 
        "t1" :>
            << [op |-> "write", value |-> "t1", key |-> "k1"],
               [op |-> "read", value |-> "t1", key |-> "k1"] >> )

ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(OpsReadYourWrite)) = TRUE


Ops2 == 
     ( 
        "t1" :>
            << [op |-> "write", value |-> "t1", key |-> "k1"],
               [op |-> "write", value |-> "t1", key |-> "k2"] >> @@
        "t2" :>
            << [op |-> "read", value |-> "t1", key |-> "k1"],
               [op |-> "read", value |-> NoValue, key |-> "k2"] >> )

ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(Ops2)) = FALSE


Ops3 == 
     ( 
        "t1" :>
            << [op |-> "write", value |-> "t1", key |-> "k1"],
               [op |-> "write", value |-> "t1", key |-> "k2"] >> @@
        "t2" :>
            << [op |-> "read", value |-> "t1", key |-> "k1"],
               [op |-> "read", value |-> "t1", key |-> "k2"] >> )

ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(Ops3)) = TRUE

Ops4 == 
     ( 
        "t1" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "write", value |-> "t1", key |-> "k2"] >> @@
        "t2" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "write", value |-> "t2", key |-> "k2"] >> )

\* This actually does satisfy SI, since even though both txns write to the same key. 
\* There is an ordering that gives a complete read state to both in a
\* way that doesn't create conflict.
ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(Ops4)) = TRUE

OpsWriteSkew == 
     ( 
        "t1" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "read", value |-> NoValue, key |-> "k2"],
               [op |-> "write", value |-> "t1", key |-> "k1"] >> @@
        "t2" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "read", value |-> NoValue, key |-> "k2"],
               [op |-> "write", value |-> "t2", key |-> "k2"] >> )

ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(OpsWriteSkew)) = TRUE

OpsWriteSkewSmall == 
     ( 
        "t1" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "write", value |-> "t1", key |-> "k2"] >> @@
        "t2" :>
            << [op |-> "read", value |-> NoValue, key |-> "k2"],
               [op |-> "write", value |-> "t2", key |-> "k1"] >> )

ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(OpsWriteSkewSmall)) = TRUE

\* 
\* Repeatable read example tests.
\* 

\* All cases satisfying SI should also satisfy RR.
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(OpsReadYourWrite)) = TRUE
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(OpsReadYourWrite)) = TRUE
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(OpsReadYourWrite)) = TRUE
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(Ops3)) = TRUE
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(Ops4)) = TRUE
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(OpsWriteSkewSmall)) = TRUE
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(OpsWriteSkew)) = TRUE

\* Violates SI but satisfies RR.
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(Ops2)) = TRUE

RR1 == 
     ( 
        "t1" :>
            << [op |-> "write", value |-> "t1", key |-> "k1"],
               [op |-> "write", value |-> "t1", key |-> "k2"] >> @@
        "t2" :>
            << [op |-> "write", value |-> "t2", key |-> "k1"],
               [op |-> "write", value |-> "t2", key |-> "k2"] >> @@
        "t3" :>
            << [op |-> "read", value |-> "t1", key |-> "k1"],
               [op |-> "read", value |-> "t2", key |-> "k2"],
               [op |-> "read", value |-> "t1", key |-> "k1"]>>)

\* Satisfies RR but not snapshot isolation, since different reads in t3 must have 
\* read from different snapshots.
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(RR1)) = TRUE
ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(RR1)) = FALSE

RR2 == 
     ( 
        "t1" :>
            << [op |-> "write", value |-> "t1", key |-> "k1"],
               [op |-> "write", value |-> "t1", key |-> "k2"] >> @@
        "t2" :>
            << [op |-> "write", value |-> "t2", key |-> "k1"],
               [op |-> "write", value |-> "t2", key |-> "k2"] >> @@
        "t3" :>
            << [op |-> "read", value |-> "t1", key |-> "k1"],
               [op |-> "read", value |-> "t2", key |-> "k2"],
               [op |-> "read", value |-> "t1", key |-> "k2"]
               >>)

ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(RR2)) = FALSE

RRReadYourWrite == 
     ( 
        "t1" :>
            << [op |-> "write", value |-> "t1", key |-> "k1"],
               [op |-> "write", value |-> "t1", key |-> "k2"] >> @@
        "t2" :>
            << [op |-> "write", value |-> "t2", key |-> "k1"],
               [op |-> "write", value |-> "t2", key |-> "k2"] >> @@
        "t3" :>
            << [op |-> "read", value |-> "t1", key |-> "k1"],
               [op |-> "write", value |-> "t3", key |-> "k1"],
               [op |-> "read", value |-> "t3", key |-> "k1"]
               >>)

\* Internal reads should be allowed to read effect of previous writes in the transaction.
ASSUME CC!RepeatableRead([k \in {"k1", "k2"} |-> NoValue], Range(RRReadYourWrite)) = TRUE

\* 
\* Read committed example tests.
\* 

\* Violates RR but satisfies read committed.
ASSUME CC!ReadCommitted([k \in {"k1", "k2"} |-> NoValue], Range(RR2)) = TRUE


--------------------------------------------------------------------------

\* 
\* Further experiments with isolation level properties and comparisions.
\* 

CONSTANT KeysGen \* == {"k1", "k2"}
CONSTANT TxId \* ==  {"t1", "t2"}

BoundedSeq(S, nmin, nmax) == UNION {[1..i -> S] : i \in nmin..nmax}

CCGen == INSTANCE ClientCentric WITH 
                    Keys <- KeysGen, 
                    Values <- TxId \union {NoValue} 

MaxNumTxnOps == 2
InitialState == [k \in KeysGen |-> NoValue]

TxnOperation == {
    o \in CCGen!Operation : 
        \* Only reads can have a value of NoValue.
        \* /\ o.op = "write" => o.value # NoValue
        /\ TRUE
}

OpSeqs(nmin, nmax) == 
    {ops \in BoundedSeq(TxnOperation, nmin, nmax) : 
        \A i,j \in 1..Len(ops) : 
            /\ TRUE
           \* At most one write to the same key.
           \* /\ ops[i].op = "write" /\ ops[j].op = "write" /\ ops[i].key = ops[j].key => i = j
    }

TxnSetsAll == {
    tset \in [TxId -> OpSeqs(0, MaxNumTxnOps)] : 
        \* Enforce that all writes in a transaction have a value equal to their transaction id.
        /\ \A t \in TxId : \A op \in Range(tset[t]) : op.op = "write" => op.value = t
}

\* Committed transaction sets per isolation level.
TxnSetsReadUncommitted == {t \in TxnSetsAll : CCGen!ReadUncommitted(InitialState, Range(t))}
TxnSetsReadCommitted == {t \in TxnSetsAll : CCGen!ReadCommitted(InitialState, Range(t))}
TxnSetsRepeatableRead == {t \in TxnSetsAll : CCGen!RepeatableRead(InitialState, Range(t))}
TxnSetsSnapshotIsolation == {t \in TxnSetsAll : CCGen!SnapshotIsolation(InitialState, Range(t))}
TxnSetsSerializable == {t \in TxnSetsAll : CCGen!Serializability(InitialState, Range(t))}

ASSUME PrintT("All") /\ PrintT(Cardinality(TxnSetsAll))
ASSUME PrintT("ReadUncommitted") /\ PrintT(Cardinality(TxnSetsReadUncommitted))
ASSUME PrintT("ReadCommitted") /\ PrintT(Cardinality(TxnSetsReadCommitted))
\* ASSUME PrintT("ReadCommitted") /\ PrintT(TxnSetsReadCommitted)
\* ASSUME PrintT("RepeatableRead") /\ PrintT(Cardinality(TxnSetsRepeatableRead))
ASSUME PrintT("SnapshotIsolation") /\ PrintT(Cardinality(TxnSetsSnapshotIsolation))
ASSUME PrintT("Serializable") /\ PrintT(Cardinality(TxnSetsSerializable))

ASSUME PrintT("--------")

ASSUME PrintT(TxnSetsRepeatableRead \subseteq TxnSetsReadCommitted)
ASSUME PrintT(TxnSetsSnapshotIsolation \subseteq TxnSetsRepeatableRead)
ASSUME PrintT(TxnSetsSnapshotIsolation \subseteq TxnSetsReadCommitted)
ASSUME PrintT(TxnSetsSerializable \subseteq TxnSetsSnapshotIsolation)


VARIABLE txnSet

Init == 
    /\ txnSet \in TxnSetsAll
    /\ CCGen!SnapshotIsolation(InitialState, Range(txnSet))
    \* /\ CCGen!RepeatableRead(InitialState, Range(txnSet))
    \* /\ PrintT(txnSet)

Next == UNCHANGED <<txnSet>>

Symmetry == Permutations(TxId) \cup Permutations(KeysGen)

=============================================================================
