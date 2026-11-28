#!/bin/bash
# Run 5 (restarted ~1 min after a first start, with mode tri added; nothing from the first start is reported):
# Helly2 push (|C(m)| room 5, width M 7, H 14), triangle room check, lead push at exact N 5
cd "$(dirname "$0")/r5"; P=../../probes/plu_probe.py
python3 $P helly,hellyM,tri planted 6 6 21 15 5
python3 $P tri closure 6 12 1 40
python3 $P pls,pl planted 10 4 31 8 3 k3 E5
python3 $P helly,hellyM,tri tall 10 7 1 5 maxn 50
python3 $P helly,hellyM,tri tall 14 4 2 20 maxn 45
