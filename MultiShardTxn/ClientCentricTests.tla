--------------------------- MODULE ClientCentricTests ---------------------------
EXTENDS TLC, Util


\* 
\* Snapshot isolation example tests.
\* 

NoValue == "NoValue"

CC == INSTANCE ClientCentric WITH 
                    Keys <- {"k1", "k2"}, 
                    Values <- {"t1", "t2"} \union {NoValue}          

Ops1 == 
     ( 
        "t1" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "read", value |-> NoValue, key |-> "k2"],
               [op |-> "write", value |-> "t1", key |-> "k2"] >> @@
        "t2" :>
            << [op |-> "read", value |-> NoValue, key |-> "k1"],
               [op |-> "read", value |-> NoValue, key |-> "k2"],
               [op |-> "write", value |-> "t2", key |-> "k2"] >> )

ASSUME CC!SnapshotIsolation([k \in {"k1", "k2"} |-> NoValue], Range(Ops1)) = FALSE


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


=============================================================================