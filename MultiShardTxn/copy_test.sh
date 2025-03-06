#!/bin/sh
tag=$1
scp test_txn_model_traces.py mongo-dev-workstation:/home/ubuntu/wiredtiger/test/suite/
ssh mongo-dev-workstation "cd wiredtiger && git add test/suite/test_txn_model_traces.py && git commit -m save"
evg_cmd="/home/ubuntu/evergreen patch --large -p wiredtiger -t coverage-report-python,generate-coverage-report -v code-statistics -d '$tag' -f -y"
ssh mongo-dev-workstation "cd wiredtiger && $evg_cmd"