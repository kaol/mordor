#!/bin/bash
# Run 5 (lead PairLocal, pushes in exact N and number of colours): modes plocal (candidate), plocalM (mutant d2pM)
cd "$(dirname "$0")/r5" || exit 1
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation:/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run27/brief/probes
P=../../probes/plocal_probe.py
python3 $P plocal,plocalM tall 10 4 2 20 maxn 40 E3
python3 $P plocal,plocalM tall 10 4 2 20 maxn 40 E4
python3 $P plocal,plocalM closure 6 12 1 40 min4
python3 $P plocal,plocalM tall 12 4 1 8 maxn 45 E5
