#!/bin/bash
# Run 1 (audit, Repair): irreparable W0^2 models on the base corpus; one job, cap 1500 s.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
timeout 1500 python3 ../irrep_probe.py irrep maxn 40 closure 5 11 4 30 + tall 8 4 1 12 + tall 10 4 2 20 > run1_out.txt 2>&1
echo "exit $?" >> run1_out.txt
