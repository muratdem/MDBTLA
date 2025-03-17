#!/bin/bash
ignore_vars="rtxn,rTxnReadTs,rInCommit,rParticipants,rCatalog,shardTxnReqs,shardTxns,shardPreparedTxns,coordCommitVotes,aborted,coordInfo,msgsPrepare,msgsVoteCommit,msgsAbort,msgsCommit,shardOps,catalog,log,txnSnapshots,txnStatus,stableTs,oldestTs,allDurableTs"

# rc=snapshot
# java -cp tla2tools-json-test.jar tlc2.TLC -cacheStatesIgnoreVars $ignore_vars -cacheStates cache -deadlock -workers 1 -config MCMultiShardTxn_RC_snapshot.cfg MCMultiShardTxn.tla | tee logout_permissive_rc_snapshot.txt

# rc=local with prepare blocking.
java -cp tla2tools-json-test.jar tlc2.TLC -cacheStatesIgnoreVars $ignore_vars -cacheStates cache -deadlock -workers 1 -config MCMultiShardTxn_RC_with_prepare_block.cfg MCMultiShardTxn.tla | tee logout_permissive_rc_with_prepare_block.txt

# rc=local with no prepare blocking.
java -cp tla2tools-json-test.jar tlc2.TLC -cacheStatesIgnoreVars $ignore_vars -cacheStates cache -deadlock -workers 1 -config MCMultiShardTxn_RC_no_prepare_block.cfg MCMultiShardTxn.tla  | tee logout_permissive_rc_no_prepare_block.txt

# rc=local with no prepare blocking or ww.
# java -cp tla2tools-json-test.jar tlc2.TLC -cacheStatesIgnoreVars $ignore_vars -cacheStates cache -deadlock -workers 10 -config MultiShardTxn_RC_no_prepare_block_or_ww.cfg MCMultiShardTxn.tla | tee logout_permissive_rc_no_prepare_block_or_ww.txt

# Baseline
# java -cp tla2tools-json.jar tlc2.TLC ClientCentricTests.tla | tee logout_baseline.txt



# Consider loading cached states for more precise schedule counting (?).
# java -cp tla2tools-test.jar tlc2.TLC -cacheStatesIgnoreVars $ignore_vars -cacheStates load -cacheStatesIgnoreVarsInvListCounts 2  -deadlock -workers 10 -config MultiShardTxn_RC_no_prepare_block.cfg MultiShardTxn.tla | grep "op.*value" | sort | uniq | grep -v "<<>>" | wc -l
