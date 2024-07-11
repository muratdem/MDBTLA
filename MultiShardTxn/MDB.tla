---- MODULE MDB ----
EXTENDS Sequences, Naturals

CONSTANTS WC,  \* write concern
          RC   \* read concern

CONSTANTS Keys, 
          Values, 
          NoValue

WCVALUES == {"one", 
             "majority"}

RCVALUES == {"linearizable", 
             "snapshot", 
             "local",
             "available"}

LogIndices == Nat \ {0}

Epochs == Nat \ {0}


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

VARIABLES mlog, mcommitIndex, mepoch

mvars == <<mlog, mcommitIndex, mepoch>>

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

---------------------------------------------------------------------
\* actions and main spec

\* Expand the prefix of the mlog that can no longer be lost.
IncreaseCommitIndex ==
    /\ mcommitIndex' \in mcommitIndex..Len(mlog)
    /\ UNCHANGED <<mlog, mepoch>>

\* Any data that is not part of the checkpointed mlog prefix may be lost at any time. 
TruncateLog ==
    \E i \in (mcommitIndex+1)..Len(mlog) :
        /\ mlog' = SubSeq(mlog, 1, i - 1)
        /\ mepoch' = mepoch + 1
        /\ UNCHANGED <<mcommitIndex>>

\* Init ==
\*     /\ mlog = <<>>
\*     /\ readIndex = 0
\*     /\ mcommitIndex = 0
\*     /\ mepoch = 1

\* \* This relation models all possible mlog actions, without performing any write.
\* Next ==
\*     \/ IncreaseCommitIndex
\*     \/ TruncateLog

===============================================================================