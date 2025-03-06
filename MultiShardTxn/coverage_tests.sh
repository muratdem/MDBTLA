#!/bin/sh

# 1 txn.
for cvg in 0.1 0.2 0.3 0.4 0.5; do
    python3 trace.py --compact --constants MTxId "{t1}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_json_graph && source copy_test.sh "coverage $cvg, 1 txns"
done

# 2 txns.
for cvg in 0.1 0.2 0.3 0.4 0.5; do
    python3 trace.py --compact --constants MTxId "{t1,t2}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_json_graph && source copy_test.sh "coverage $cvg, 2 txns"
done


