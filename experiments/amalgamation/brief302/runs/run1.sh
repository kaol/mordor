#!/bin/bash
# Run 1 (lead PairLocal, base corpora): modes plocal, plocalM (mutant), plne (open half)
cd "$(dirname "$0")/r1" || exit 1
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation:/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run27/brief/probes
P=../../probes/plocal_probe.py
python3 $P plocal,plocalM,plne closure 6 12 1 40
python3 $P plocal,plocalM,plne tall 8 4 1 12
python3 $P plocal,plocalM,plne tall 10 4 2 20 maxn 40
