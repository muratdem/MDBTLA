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


=============================================================================