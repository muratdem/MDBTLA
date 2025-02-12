#!/bin/bash
ignore_vars="rtxn,rTxnReadTs,rInCommit,rParticipants,rCatalog,shardTxnReqs,shardTxns,shardPreparedTxns,coordCommitVotes,aborted,coordInfo,msgsPrepare,msgsVoteCommit,msgsAbort,msgsCommit,shardOps,catalog,log,txnSnapshots"

# rc=local with prepare blocking.
java -cp tla2tools-json.jar tlc2.TLC -cacheStatesIgnoreVars $ignore_vars -cacheStates cache -deadlock -workers 10 -config MultiShardTxn_RC_with_prepare_block.cfg MultiShardTxn.tla | tee logout_permissive_rc_with_prepare_block.txt

# rc=local with no prepare blocking.
java -cp tla2tools-json.jar tlc2.TLC -cacheStatesIgnoreVars $ignore_vars -cacheStates cache -deadlock -workers 10 -config MultiShardTxn_RC_no_prepare_block.cfg MultiShardTxn.tla  | tee logout_permissive_rc_no_prepare_block.txt

# rc=local with no prepare blocking or ww.
java -cp tla2tools-json.jar tlc2.TLC -cacheStatesIgnoreVars $ignore_vars -cacheStates cache -deadlock -workers 10 -config MultiShardTxn_RC_no_prepare_block_or_ww.cfg MultiShardTxn.tla | tee logout_permissive_rc_no_prepare_block_or_ww.txt

# Baseline
java -cp tla2tools-json.jar tlc2.TLC ClientCentricTests.tla | tee logout_baseline.txt