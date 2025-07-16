#!/bin/bash

# Copy locallly generated test files to remote WiredTiger build directory.
scp model_tests/model_tests*.py mongo-dev-workstation:/home/ubuntu/wiredtiger/test/suite/