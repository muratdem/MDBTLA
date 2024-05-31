---- MODULE MDBLinearizability ----
EXTENDS Naturals, Sequences

CONSTANTS Keys, Values, NoValue
CONSTANTS WC, RC


CONSTANT  LogLength

VARIABLES log, commitIndex, readIndex, epoch

mdbVarsExceptLog == <<commitIndex, readIndex, epoch>>
mdbVars == <<mdbVarsExceptLog, log>>

MDB == INSTANCE MDB

ASSUME WC \in MDB!WCVALUES
ASSUME RC \in MDB!RCVALUES

---------------------------------------------------------------------

\* This is a specification that performs arbitrary writes to MDB
vars == <<mdbVars>>

WriteBegin ==
    \E key \in Keys, value \in Values :
        /\ MDB!WriteInit(key, value)
        /\ UNCHANGED mdbVarsExceptLog

DBNext ==
    /\ MDB!Next

LinInit ==
    /\ MDB!Init

LinNext ==
    \/ DBNext
    \/ WriteBegin

LinSpec ==
    /\ LinInit
    /\ [][LinNext]_vars

\* dictView is expressed as a refinement mapping over MDB reads, choosing
\* the single strong consistency read value for each key per state for RC:linearizable
dictView == [ key \in Keys |->
    CHOOSE read \in MDB!Read(key) : TRUE
]

---------------------------------------------------------------------

\* This other section defines an atomic key-value store with two
\* state variables:
\* - commitIndex, which increases on every write
\* - dictView, a mapping from keys to pairs of value and commitIndex as of writing
\* The model performs a number of arbitrary writes to dictView on each step, or skips steps.
\* The point is, if the MDB arbitrary writes spec refines this one, then
\* the MDB spec at strong consistency offers linearizable operations.


DictInit ==
    /\ commitIndex = 0
    /\ dictView = [ key \in Keys |-> MDB!NotFoundReadResult ]

\* commitIndex may advance more than once per step,
\* DictWrite has this recursive structure that performs `n` writes per step.
\* Each write is tagged with a distinct value of commitIndex, and represents
\* the precise point in time at which a MDB strong consistency write becomes
\* both durable and readable.
RECURSIVE DictWriteNTimes(_, _, _)

DictWriteNTimes(n, dv, idx) ==
    IF   n = 0
    THEN /\ dictView' = dv
         /\ commitIndex' = idx
    ELSE \E key \in Keys, value \in Values :
            DictWriteNTimes(
                n - 1,
                [dv EXCEPT ![key] = [value |-> value, logIndex |-> idx + 1]],
                idx + 1)

\* DictWrite updates its DictView, and we check if this is in line with above DictView view
DictWrite ==
    \E n \in 1..LogLength-1 :
        DictWriteNTimes(n, dictView, commitIndex)

DictNext ==
    \/ DictWrite
    \/ UNCHANGED <<dictView, commitIndex>>

DictSpec == 
    /\ DictInit 
    /\ [][DictNext]_<<dictView, commitIndex>>

---------------------------------------------------------------------

SpecificStateSpace ==
    /\ epoch < LogLength
    /\ Len(log) < LogLength

Alias == [
    dictView |-> dictView,
    log |-> log,
    commitIndex |-> commitIndex,
    readIndex |-> readIndex,
    epoch |-> epoch
]

============================================================================