---- MODULE MDB ----
EXTENDS Sequences, Naturals

CONSTANTS WC,
          RC  

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
    logIndex |-> 0,
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
\* Additionally, commitIndex, readIndex, and epoch express a high-level view of
\* underlying processes like replication and failure recovery:
\* - the commitIndex indicates a position in the log (or 0 for no position)
\*   before which data is durable. One can think of this as tracking global consensus,
\*   and in fact strongly consistent reads will always return the latest relevant
\*   information whose index is <= commitIndex.
\* - the readIndex arbitrarily lags behind the commitIndex, and models the point
\*   before which _every single replica in the entire system_ has already replicated
\*   the data in the log. No operation should ever return out of sync data staler
\*   than this point in the log, because by definition no replica can be staler than
\*   this point in the log.
\* - the epoch increments strictly monotonically whenever  log  is non-deterministically
\*   truncated in the range (commitIndex+1)..Len(log)), modeling loss of uncommitted data
\*   due to node failures when all session tokens of the current epoch become invalid.
\*   Thus, Epoch is only used by session consistency to detect data loss due to truncation
\*   and prevent invalid reads/writes when session consistency can no longer be guaranteed
\*   for a given token.
\*

VARIABLES log, commitIndex, readIndex, epoch

vars == <<log, commitIndex, readIndex, epoch>>

TypesOK ==
    /\ log \in Logs
    /\ commitIndex \in Nat
    /\ readIndex \in Nat
    /\ epoch \in Epochs



\* This operator initiates a write, adding it to the log.
WriteInit(key, value) ==
    /\ log' = Append(log, [
            key |-> key,
            value |-> value
       ])

\* Adjacent to WriteInit, this operator will return a token
\* representative of that write.
\* This token is suitable both as a fresh session token, and as an ephemeral
\* token tracking the progress of a write from init to success or failure.
\* WriteInitToken == [
\*     epoch |-> epoch,
\*     checkpoint |-> Len(log) + 1
\* ]


\* For a given key, a read can be entirely defined by a value and a flag:
\* - point is a point in the log to which the read should be applied.
\*   for log entries at or "before" (index <=) point, the latest
\*   value associated with key will be included in the result.
\*   If the log at or before point does not mention the given key at all,
\*   then the result set will include NotFoundReadResult.
\*   An empty set as a result means the read is not possible; any valid read, even
\*   one that returns a "not found" result, will have at least one element in
\*   its set.
\* - allowDirty controls a secondary behavior: for elements of the log
\*   whose index > point, if allowDirty = TRUE then they will also
\*   be included in the result set. If allowDirty = FALSE, then only
\*   the single latest value whose index <= point will be in the result set.
GeneralRead(key, index, allowDirty) ==
    LET maxCandidateIndices == { i \in DOMAIN log :
            /\ log[i].key = key
            /\ i <= index }
        allIndices == { i \in DOMAIN log :
            /\ allowDirty
            /\ log[i].key = key
            /\ i > index }
    IN  { [logIndex |-> i, value |-> log[i].value]
          : i \in allIndices \cup (
            IF   maxCandidateIndices # {}
            THEN {Max(maxCandidateIndices)}
            ELSE {}) } \cup 
        (IF   maxCandidateIndices = {}
         THEN {NotFoundReadResult}
         ELSE {})

StrongConsistencyRead(key) ==
        GeneralRead(key, commitIndex, FALSE)

EventualConsistencyRead(key) ==
        GeneralRead(key, readIndex, TRUE)

---------------------------------------------------------------------
\* actions and main spec

\* Expand the prefix of the log that can no longer be lost.
\* In reality, this and IncreasereadIndex correspond to the
\* human-assisted process of ensuring propagation and
\* replication happens such that durability is guaranteed.
IncreaseReadIndexAndOrCommitIndex ==
    /\ commitIndex' \in commitIndex..Len(log)
    /\ readIndex' \in readIndex..commitIndex'
    /\ UNCHANGED <<log, epoch>>

\* Any data that is not part of the checkpointed log prefix
\* (see above) may be lost at any time. Operations that
\* require durability would wait until the commitIndex
\* "catches up" to ensure the data they add to the log is not
\* lost.
TruncateLog ==
    \E i \in (commitIndex+1)..Len(log) :
        /\ log' = SubSeq(log, 1, i - 1)
        /\ epoch' = epoch + 1
        /\ UNCHANGED <<readIndex, commitIndex>>

Init ==
    /\ log = <<>>
    /\ readIndex = 0
    /\ commitIndex = 0
    /\ epoch = 1

\* This relation models all possible log actions, without performing any write.
\* To check general features of this specification, see CosmosDBProps.
\* To use this specification as part of your own, look at the show*simple.tla or
\* CosmosDBClient specs to see how specific writes should be modeled.
Next ==
    \/ IncreaseReadIndexAndOrCommitIndex
    \/ TruncateLog

====