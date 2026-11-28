#!/bin/bash
# Run 3 (lead CaseBEmpty): modes caseB (lead), caseAall (mutant), base corpora then room corpora
cd "$(dirname "$0")/r3" || exit 1
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation:/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run27/brief/probes
P=../../probes/plocal_probe.py
python3 $P caseB,caseAall closure 6 12 1 40
python3 $P caseB,caseAall tall 8 4 1 12
python3 $P caseB,caseAall tall 10 4 2 20 maxn 40
python3 $P caseB,caseAall tall 12 4 1 8 maxn 45
python3 $P caseB,caseAall tall 13 4 1 8 maxn 45
python3 $P caseB,caseAall tall 14 4 2 20 maxn 45
python3 $P caseB,caseAall tall 10 6 1 8 maxn 45
python3 $P caseB,caseAall tall 10 7 1 5 maxn 50
