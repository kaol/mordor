#!/bin/bash
# Run 4 (lead push): |C(m)| >= 5, exact N 3 and 4, width M 8, height 14
cd "$(dirname "$0")/r4"; P=../../probes/plu_probe.py
python3 $P pls,plu,pl planted 6 6 21 15 5 k5
python3 $P pls,plu,pl planted 8 4 22 12 3 k3 E3
python3 $P pls,plu,pl planted 8 4 23 12 3 k3 E4
python3 $P pls,plu,pl planted 10 8 24 6 3 k3
python3 $P pls,plu,pl planted 14 4 25 4 3 k3
