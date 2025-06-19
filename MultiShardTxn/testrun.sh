#!/bin/sh

# 
# Run this script on server where it is next to WiredTiger source tree.
# 

cvg_pct=$1

# 2 txns.
txids="{t1}"
wt_base_dir="/home/ubuntu/wiredtiger"

# Generate test cases from WiredTiger model.
jobs=2
# python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --generate_only
cd /home/ubuntu/MDBTLA/MultiShardTxn
python3 testgen.py --parallel_test_split $jobs --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg_pct 
cp tests/test_txn_model_traces*.py $wt_base_dir/test/suite

# Run the tests against WiredTiger.
cd $wt_base_dir/build
test_list=""
for i in $(seq 1 $jobs); do
    test_list="$test_list test_txn_model_traces_$i"
done

echo "Running tests: $test_list"
python3 ../test/suite/run.py -v 2 -j 6 $test_list
