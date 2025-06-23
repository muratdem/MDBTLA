#!/bin/bash

# Copy locallly generated test files to remote WiredTiger build directory.
scp tests/test_txn_model_traces*.py mongo-dev-workstation:/home/ubuntu/wiredtiger/test/suite/