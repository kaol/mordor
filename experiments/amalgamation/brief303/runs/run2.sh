#!/bin/bash
# Run 2 (lead), room |C(m)| >= 4 (planted k = 4) and the closure corpus where PairLocal was refuted
cd "$(dirname "$0")/r2"; P=../../probes/plu_probe.py
python3 $P plu,pls,ns,pl planted 6 5 4 20 4 k4
python3 $P plu,pls,ns,pl closure 6 12 1 40 k3
python3 $P plu,pls,ns,pl planted 8 4 5 12 4 k4
python3 $P plu,pls,ns,pl planted 7 8 6 12 5 k4
