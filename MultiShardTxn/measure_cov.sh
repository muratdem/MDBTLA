#!/bin/sh

# 
# Run this script on server where it is next to WiredTiger source tree.
# 

# txids="{t1,t2,t3}"
# cvg="0.5"
# python3 trace.py --compact --constants MTxId "$txids" Keys "{k1}" Timestamps "{1,2,3}" --generate_only
# python3 trace.py --compact --constants MTxId "$txids" Keys "{k1}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_cached_graphs && source copy_test.sh "coverage $cvg, 3 txns"

# exit 0

cvg_pcts="0.2 0.4 0.6 0.8 1.0"
# cvg_pcts="0.8 1.0"

# 1 txn.
# txids="{t1}"

# # Generate the graph upfront.
# python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --generate_only
# for cvg in $cvg_pcts; do
#     python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_cached_graphs 
#     # && source copy_test.sh "coverage $cvg, 1 txns"
#     scp test_txn_model_traces.py mongo-dev-workstation:/home/ubuntu/wiredtiger/test/suite/
#     ssh mongo-dev-workstation "cd wiredtiger && ./measure_model_cov.sh model_tests_coverage_1txn_${cvg}pct.json"
# done

# 2 txns.
txids="{t1,t2}"

# Generate the graph upfront.
python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --generate_only
for cvg in $cvg_pcts; do
    cd /home/ubuntu/MDBTLA/MultiShardTxn
    python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_cached_graphs 
    cp test_txn_model_traces*.py /home/ubuntu/wiredtiger/test/suite

    # Run tests and generate coverage report.
    report_file=$1
    cd /home/ubuntu/wiredtiger
    python3 test/evergreen/code_coverage/parallel_code_coverage.py -c test/evergreen/code_coverage/code_coverage_config.json -b $(pwd)/build_ -s --bucket python
    python3 -m gcovr -f "src/(txn|cursor|session|btree|include/txn_inline.h)" --json-summary-pretty -j 6 --json-summary $report_file --gcov-ignore-parse-errors negative_hits.warn
done
