#!/bin/sh
tlc -dumpTrace json trace.json -simulate -workers 10 -cleanup -deadlock MDBTest

# Parse the trace to generate a WiredTiger test script and upload it.
python3 trace.py && scp test_txn_trace1.py mongo-dev-workstation:/home/ubuntu/wiredtiger/test/suite/