#!/bin/bash
# Run 1 (lead PairLocalU / PairLocalS / NSL, mutant PairLocal), room |C(m)| >= 3 at heights 6, 8, 10 (planted corpora)
cd "$(dirname "$0")/r1"; P=../../probes/plu_probe.py
python3 $P plu,pls,ns,pl planted 6 5 1 30 3 k3
python3 $P plu,pls,ns,pl planted 8 4 2 15 3 k3
python3 $P plu,pls,ns,pl planted 10 4 3 10 3 k3
python3 $P plu,pls,ns,pl planted 12 4 4 6 3 k3
