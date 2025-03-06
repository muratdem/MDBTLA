#!/bin/sh
python3 trace.py --compact --constants MTxId "{t1,t2}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct 0.1 --use_json_graph && source copy_test.sh "0.1"
python3 trace.py --compact --constants MTxId "{t1,t2}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct 0.2 --use_json_graph && source copy_test.sh "0.2"
python3 trace.py --compact --constants MTxId "{t1,t2}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct 0.3 --use_json_graph && source copy_test.sh "0.3"
python3 trace.py --compact --constants MTxId "{t1,t2}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct 0.4 --use_json_graph && source copy_test.sh "0.4"
python3 trace.py --compact --constants MTxId "{t1,t2}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct 0.5 --use_json_graph && source copy_test.sh "0.5"
python3 trace.py --compact --constants MTxId "{t1,t2}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct 0.6 --use_json_graph && source copy_test.sh "0.6"