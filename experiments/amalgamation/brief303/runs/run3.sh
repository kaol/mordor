#!/bin/bash
# Run 3 (programme P2, Helly2; mutant = UnivCol-in-W, refuted on 81 stored W-models)
cd "$(dirname "$0")/r3"; P=../../probes/plu_probe.py
python3 $P helly,hellyM closure 6 12 1 40
python3 $P helly,hellyM tall 8 4 1 12
python3 $P helly,hellyM planted 8 4 2 15 3
python3 $P helly,hellyM tall 10 4 2 20 maxn 40
python3 $P helly,hellyM tall 12 4 1 8 maxn 45
