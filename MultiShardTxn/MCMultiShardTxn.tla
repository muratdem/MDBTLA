--------------------------- MODULE MCMultiShardTxn ---------------------------------
EXTENDS MultiShardTxn

CONSTANT MaxOpsPerTxn

KeysOwnedByShard(s) == { k \in Keys : catalog[k] = s }

CatalogConstraint == 
    \* Prevents cases where all keys are distributed to a single shard.
    /\ \A s \in Shard : KeysOwnedByShard(s) # Keys

InitCatalogConstraintKeysOnDifferentShards ==
    \* Prevents cases where all keys are distributed to a single shard, if there is more than one shard.
    /\ Init
    /\ (Cardinality(Shard) > 1) => \A s \in Shard : Cardinality(KeysOwnedByShard(s)) < Cardinality(Keys)

\* Don't execute more than a max number of statements per transaction.
StateConstraint == 
    /\ \A t \in TxId, r \in Router : rtxn[r][t] <= MaxOpsPerTxn
    
Symmetry == Permutations(TxId) \cup Permutations(Keys) \cup Permutations(Shard) \cup Permutations(Router)


=======================