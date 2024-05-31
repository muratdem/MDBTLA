---- MODULE MDBProps ----
EXTENDS MDB, Bags, FiniteSets, SequencesExt

WriteInitState == "init"
WriteSucceededState == "succeeded"
WriteFailedState == "failed"

-------------------------------------------------------------------------------
\* Session token definitions

Checkpoints == Nat

\* Session tokens represent a point in the log, as well as a particular "epoch".
\* Each session-consistent read and write will produce an updated token
SessionTokens == [
    checkpoint: Checkpoints,
    epoch: Epochs
]

NoSessionToken == [
    checkpoint |-> 0,
    epoch |-> 0
]

MaybeSessionTokens ==
    SessionTokens \cup {NoSessionToken}

SessionTokenLEQ(token1, token2) ==
    /\ token1.epoch = token2.epoch \/ token1.epoch = 0
    /\ token1.checkpoint <= token2.checkpoint

\* return a token for corresponding write
WriteInitToken == [
    epoch |-> epoch,
    checkpoint |-> Len(log) + 1
]

\* can't read from the future
SessionTokenIsValid(token) ==
    SessionTokenLEQ(token, WriteInitToken)

UpdateTokenFromRead(origToken, read) == [
    epoch |-> epoch,
    checkpoint |-> Max({origToken.checkpoint, read.logIndex})
]

MaybeValues == Values \cup {NoValue}

ValidReadResults == [
    logIndex: LogIndices,
    value: Values
]

ReadResults ==
    ValidReadResults \cup {NotFoundReadResult}

ReadsLEQ(r1, r2) == r1.logIndex <= r2.logIndex

ReadsLT(r1, r2) == r1.logIndex < r2.logIndex


\* This predicate indicates whether a write identified by the given
\* token can succeed. Writes can always happen to fail, but successful
\* writes must meet the conditions listed here.
WriteCanSucceed(token) ==
    /\ SessionTokenIsValid(token)
    /\ (WC = "majority" =>
        /\ token.epoch = epoch
        /\ token.checkpoint <= commitIndex)

-------------------------------------------------------------------------------

WriteStates == {
    WriteInitState,
    WriteSucceededState,
    WriteFailedState
}

WriteHistoryEntries == [
    token: SessionTokens,
    key: Keys,
    value: Values,
    state: WriteStates
]

WriteHistories == SubBag(SetToBag(WriteHistoryEntries))

AddToBag(bag, elem) ==
    bag (+) SetToBag({elem})

RemoveFromBag(bag, elem) ==
    bag (-) SetToBag({elem})

\* writeHistory tracks in-progress and completed writes in the system.
\* It is a bag of records containing key, value, success/failure/in-progress,
\* and write tokens which represent points in the log where the write should be,
\* and the epoch in which the write took place
VARIABLE writeHistory
varsWithHistory == <<vars, writeHistory>>

WTypesOK ==
    /\ TypesOK
    \* writeHistory will be a sequence of HistoryEntries, recording the sequence
    \* of writes that were performed in the system
    /\ writeHistory \in WriteHistories

\* write-related actions

\* Begin a write. this means the DB has received a write request and has begin
\* acting on it. Immediately adding the value to the log is intended.
WriteBegin ==
    \E key \in Keys, value \in Values :
        /\ WriteInit(key, value)
        /\ LET modHistory(initState) ==
                /\ writeHistory' = AddToBag(writeHistory, [
                    token |-> WriteInitToken,
                    key |-> key,
                    value |-> value,
                    state |-> initState
                   ])
           IN  \/ /\ WriteCanSucceed(WriteInitToken)
                  /\ modHistory(WriteSucceededState)
               \/ /\ modHistory(WriteInitState)
        /\ UNCHANGED <<readIndex, commitIndex, epoch>>

\* When a write succeeds, the DB would report that success to the client.
\* Depending on WC, this can either freely happen at any time,
\* or it has some restrictions.
WriteSuccess ==
    \E record \in DOMAIN writeHistory :
        /\ record.state = WriteInitState
        /\ WriteCanSucceed(record.token)
        /\ writeHistory' = AddToBag(
            RemoveFromBag(writeHistory, record),
            [record EXCEPT !.state = WriteSucceededState])
        /\ UNCHANGED <<log, readIndex, commitIndex, epoch>>

\* When a write fails, for whatever reason. The reason is left implicit, but in principle
\* this can always happen for any reason.
WriteFail ==
    \E record \in DOMAIN writeHistory :
        /\ record.state = WriteInitState
        /\ writeHistory' = AddToBag(
            RemoveFromBag(writeHistory, record),
            [record EXCEPT !.state = WriteFailedState])
        /\ UNCHANGED <<log, readIndex, commitIndex, epoch>>

StateOps ==
    /\ UNCHANGED writeHistory
    /\ Next

WriteOps ==
    \/ WriteBegin
    \/ WriteSuccess
    \/ WriteFail

WInit ==
    /\ Init
    /\ writeHistory = <<>>

WNext ==
    \/ StateOps
    \/ WriteOps

Spec ==
    /\ WInit /\ [][WNext]_varsWithHistory
    \* assuming a write will eventually succeed, or at least give up
    \* without waiting forever, WritesEventuallyComplete asserts that
    \* there is no case where neither of those things can happen
    /\ WF_varsWithHistory(WriteSuccess \/ WriteFail)

\* Below are all of the correctness properties, some of which are
\* written in terms of the writeHistory variable to capture possible writes.

---------------------------------------------------------------------

\* sanity rules for readIndex and commitIndex. they should
\* progress monotonically
PointsValid ==
    [][/\ readIndex <= commitIndex
       /\ readIndex <= readIndex'
       /\ commitIndex <= commitIndex']_vars

\* type-like invariants

ReadsOK(read(_)) ==
    \A key \in Keys :
        /\ read(key) \subseteq ReadResults
        /\ \A r \in read(key) :
            SessionTokenIsValid(
                UpdateTokenFromRead(NoSessionToken, r))

StrongConsistencyReadsOK ==
    ReadsOK(Read)

SessionConsistencyReadsOK ==
    \A token \in MaybeSessionTokens :
        /\ ReadsOK(LAMBDA key : ReadAtTime(token, key))
        /\ \A key \in Keys :
            \A read \in ReadAtTime(token, key) :
                SessionTokenLEQ(token, UpdateTokenFromRead(token, read))

\* If two records are different, then their tokens are necessarily different.
\* Also, writeHistory should not contain the same record/write twice.
HistoryTokensUnique ==
    /\ \A record1, record2 \in DOMAIN writeHistory :
        record1 # record2 => record1.token # record2.token
    /\ \A record \in DOMAIN writeHistory :
        writeHistory[record] <= 1

---------------------------------------------------------------------

\* commitIndex implies that all elements of log whose index
\* is <= commitIndex will always remain unchanged
CommitIndexImpliesDurability ==
    \A checkpoint \in Checkpoints :
        \A prefix \in SeqOf(LogEntries, checkpoint) :
            [](/\ checkpoint = commitIndex
               /\ \/ log = <<>> /\ prefix = <<>>
                  \/ SubSeq(log, 1, checkpoint) = prefix
               =>
               [](IF   log = <<>>
                  THEN /\ checkpoint = 0
                       /\ prefix = <<>>
                  ELSE /\ Len(log) >= checkpoint
                       /\ SubSeq(log, 1, checkpoint) = prefix))

\* all writes that begin will eventually complete or fail
\* by assumption of token uniqueness, these existentials
\* should be sufficient to find the same write in the writeHistory
\* each time
WritesEventuallyComplete ==
    \A token \in SessionTokens :
        /\ \E record \in DOMAIN writeHistory :
            /\ record.token = token
            /\ record.state = WriteInitState
        ~>
        /\ \E record \in DOMAIN writeHistory :
            /\ record.token = token
            /\ record.state \in {
                WriteSucceededState,
                WriteFailedState
               }

---------------------------------------------------------------------
\* invariants and properties grouped by consistency level

ObsoleteValues(key) ==
    { log[i].value : i \in { i \in DOMAIN log :
        /\ i <= readIndex
        /\ log[i].key = key
        /\ \E j \in (i+1)..readIndex : log[j].key = key } }

\* Asserts that a given read operation's results are "low monotonic".
\* This is a very weak condition, which just means that the earliest
\* value a given read operation can return increases monotonically
\* over time. This is true of all read types, because the readIndex,
\* which should govern the earliest allowable read, increases
\* monotonically itself.
IsLowMonotonic(read(_)) ==
    \A key \in Keys :
        LET low == CHOOSE r1 \in read(key) :
                \A r2 \in read(key) :
                    ReadsLEQ(r1, r2)
        IN  /\ read(key) # {}
            /\ read(key)' # {}
            => ReadsLEQ(low, low')

\* Asserts that a given read operation must always return
\* either a unique result or nothing. This is called
\* "consistent" because the alternative, that there might
\* be more than one valid read result for the same key,
\* means that, without any changes in system state, multiple
\* executions of the same read operation may "jump around"
\* between multiple possible results.
\* This property only holds for strong consistency.
IsConsistent(read(_)) ==
    \A key \in Keys :
        Cardinality(read(key)) \in {0, 1}

\* No read operations may return "obsolete values".
\* That is, no value that has a more recent version recorded in
\* a log entry whose index <= readIndex may be returned, because,
\* by definition, there should not exist a replica or region that
\* has stale enough data for that to be possible.
FollowsReadIndex(read(_)) ==
    \A key \in Keys :
        \A v1 \in ObsoleteValues(key) :
            v1 \notin read(key)

--------------------------------------------------------------------------------
\* StrongConsistency

\* this is a log-based formulation of the "read after write"
\* property, requiring that a strongly consistent read may
\* not ignore any more recent durable log entry for a certain
\* key. This is weaker than the next property, however, because
\* the log may be truncated. The next property, using the complete
\* write writeHistory, would catch e.g rogue log truncations.
StrongConsistencyReadsGiveLatestDurableSCValue ==
    \A key \in Keys :
        \A r1 \in Read(key) :
            \lnot \E i \in DOMAIN log :
                RC = "linearizable"
                =>
                /\ i <= commitIndex
                /\ log[i].key = key
                /\ ReadsLT(r1, [logIndex |-> i, value |-> log[i].value])

\* this is a second "read after write" property, written
\* in terms of writeHistory: any strongly consistent
\* read must not return a value with a smaller log index
\* than some successful write in the write log.
StrongConsistencyReadsGiveLatestSuccessfulWrite ==
    WC = "majority" =>
    \A key \in Keys :
        \A r1 \in Read(key) :
            \lnot \E record \in DOMAIN writeHistory :
                RC = "linearizable"
                =>            
                /\ record.key = key
                /\ record.state = WriteSucceededState
                /\ record.token.checkpoint > r1.logIndex

StrongConsistencyReadsConsistent ==
    RC = "linearizable"
    => 
    IsConsistent(Read)

\* this is the read-your-writes property, guaranteeing that
\* a strong consistency write that succeeds will be witnessed by any
\* following reads
StrongConsistencyCommittedWritesDurable ==
    \A token \in SessionTokens :
        [](/\ WC = "majority"
           /\ \E record \in DOMAIN writeHistory :
                /\ record.token = token
                /\ record.state = WriteSucceededState
           =>
           [](/\ WC = "majority"
              /\ \E record \in DOMAIN writeHistory :
                /\ record.token = token
                /\ \A read \in Read(record.key) :
                        RC = "linearizable"
                        =>                
                        token.checkpoint <= read.logIndex))


StrongConsistencyReadsMonotonic ==
    [][
       \A key \in Keys :
        \A r1 \in Read(key) :
            \A r2 \in Read(key)' :
                RC = "linearizable"
                =>            
                ReadsLEQ(r1, r2)]_vars

StrongConsistencyReadsFollowReadIndex ==
    RC = "linearizable"
    =>    
    FollowsReadIndex(Read)
--------------------------------------------------------------------------------
\* causal consistency related properties

ReadYourWrites ==
    \A token1, token2 \in MaybeSessionTokens, key \in Keys, value \in Values :
        /\ SessionTokenLEQ(token1, token2)
        =>
        []((\E record \in DOMAIN writeHistory :
                /\ record.token = token1
                /\ record.state = WriteSucceededState
                /\ record.key = key
                /\ record.value = value)
           => [](LET lowRead == [
                        value |-> value,
                        logIndex |-> token1.checkpoint
                     ]
                 IN  
                    /\ \A read \in ReadAtTime(token2, key) :
                            ReadsLEQ(lowRead, read)))


CasualRead(key) == \* Not to be confused with causal read
        GeneralRead(key, Len(log), TRUE)

ReadsLowMonotonic ==
    [][IsLowMonotonic(CasualRead)]_vars
-------------------------------------------------------------------------------
\* BaitInvariants to provoke a counterexample trace from the model-checker

BaitWriteHistory == 
    [] [Len(log)>1 => Len(log') >= Len(log)]_varsWithHistory

BaitWH2 == \A r1, r2 \in DOMAIN writeHistory :
                SessionTokenLEQ(r1.token, r2.token) 
                => \A read \in ReadAtTime(r2.token, r2.key):
                            ReadsLEQ([logIndex |-> r1.token.checkpoint], read)


        
    
BaitReadIndex == readIndex<2
===============================================================================