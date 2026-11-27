#!/bin/bash
# Run 3 (P2 probe, TopLand_S in branch a, N >= 2).  topland_probe.py: SAT = a W0 model (branch / N flags) on which the
# virtual row g_S never gets low (TopLand_S fails).  Candidate: Ba Nge2.  Calibration (refuted relatives, must SAT):
#   (c0) Bb Nge2 on the lattices of the 16 stored refuting models (cex/TopLand_S.json, |L| <= 34);
#   (m1) T1 Ba Nge2 = TopLand_t1 in branch a (refuted on 4 of 9 stored branch-a N >= 2 models);
#   (m2) Bb Nge2 = TopLand_S in branch atom (refuted, smallest stored |L| 15 H 5 N 2).
# One job, cap 1500 s total.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
P=../topland_probe.py
END=$(( $(date +%s) + 1500 ))
step() { LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before: $*"; return; }; echo "=== $* (time left ${LEFT}s)"; DUMP=$1 timeout $LEFT python3 $P "${@:2}"; echo "exit $?"; }
{
step c0_models.json Bb Nge2 maxn 34 file ../cex/TopLand_S.json
for C in "closure 5 11 4 30" "tall 8 4 1 12" "tall 10 4 2 20" "tall 12 4 1 8"; do
  T=$(echo $C | tr ' ' '_')
  step cand_$T.json Ba Nge2 maxn 40 $C
  step m1_$T.json T1 Ba Nge2 maxn 40 $C
  step m2_$T.json Bb Nge2 maxn 40 $C
done
} > run3_out.txt 2>&1
