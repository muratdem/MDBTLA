#!/bin/sh

# 
# Run this script on server where it is next to WiredTiger source tree.
# 

# txids="{t1,t2,t3}"
# cvg="0.5"
# python3 trace.py --compact --constants MTxId "$txids" Keys "{k1}" Timestamps "{1,2,3}" --generate_only
# python3 trace.py --compact --constants MTxId "$txids" Keys "{k1}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_cached_graphs && source copy_test.sh "coverage $cvg, 3 txns"

# exit 0

# cvg_pcts="0.2 0.4 0.6 0.8 1.0"
# cvg_pcts="0.8 1.0"
cvg_pcts=$1

# 2 txns.
txids="{t1,t2}"

# Generate the graph upfront.
jobs=1
python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --generate_only
for cvg in $cvg_pcts; do
    cd /home/ubuntu/MDBTLA/MultiShardTxn
    python3 trace.py --parallel_test_split $jobs --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_cached_graphs 
    cp test_txn_model_traces*.py /home/ubuntu/wiredtiger/test/suite

    # Run tests and generate coverage report.
    report_file="model_coverage_2txns_${cvg}pct.json"
    cd /home/ubuntu/wiredtiger
    rm -rf build_*

    # Run tests.
    python3 ../test/suite/run.py -v 2 -j 6 test_txn_model_traces_1
done
