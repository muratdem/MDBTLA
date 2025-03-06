#!/bin/sh


# txids="{t1,t2,t3}"
# cvg="0.5"
# python3 trace.py --compact --constants MTxId "$txids" Keys "{k1}" Timestamps "{1,2,3}" --generate_only
# python3 trace.py --compact --constants MTxId "$txids" Keys "{k1}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_cached_graphs && source copy_test.sh "coverage $cvg, 3 txns"

# exit 0

cvg_pcts="0.2 0.4 0.6 0.8 1.0"

# 1 txn.
txids="{t1}"

# Generate the graph upfront.
python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --generate_only
for cvg in $cvg_pcts; do
    python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_cached_graphs && source copy_test.sh "coverage $cvg, 1 txns"
done

# 2 txns.
txids="{t1,t2}"

# Generate the graph upfront.
python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --generate_only
for cvg in $cvg_pcts; do
    python3 trace.py --compact --constants MTxId "$txids" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct $cvg --use_cached_graphs && source copy_test.sh "coverage $cvg, 2 txns"
done
