#!/bin/sh

# 
# Run this script on server where it is next to WiredTiger source tree.
# 

cvg_pct=$1

# 2 txns.
txids="{t1,t2}"
wt_base_dir="/home/ubuntu/wiredtiger"

#
# Generate unit test cases from WiredTiger TLA+ model 
# via path coverings of state space.
#
jobs=6
python3 testgen.py --parallel_test_split $jobs --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg_pct 
cp tests/test_txn_model_traces*.py $wt_base_dir/test/suite

#
# Run the tests against WiredTiger.
#
cd $wt_base_dir/build
test_list=""
for i in $(seq 1 $jobs); do
    test_list="$test_list test_txn_model_traces_$i"
done

echo "Running tests: $test_list"
python3 ../test/suite/run.py -v 2 -j 6 $test_list
