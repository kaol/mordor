#!/bin/bash
cd "$(dirname "$0")"; until ! pgrep -f "run2.sh" >/dev/null; do sleep 5; done
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
timeout 1500 ./run4.sh > run4.out 2>&1
