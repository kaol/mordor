#!/bin/bash
# Run 2 (P3, sharpness of the frontier's pushed lead where the target is now a theorem): StairTb at exact N = 1
# (orbit_probe.py nofix 0 Stair E1; SAT = a Stair-world model with no mu-fixed atom, i.e. StairTb fails), branch read off
# the "model:" lines (A1 = branch a).  Mutant: LastEither E1 (refuted relative, bank s292_lasteither_h10).
# Same room corpora as run 1.  One job, cap 1500 s total.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
A=/home/user/mordor/experiments/amalgamation
END=$(( $(date +%s) + 1500 ))
for C in "tall 13 4 1 8 maxn 40" "tall 14 4 2 20 maxn 40" "tall 10 6 1 8 maxn 45" "tall 10 7 1 5 maxn 50"; do
  T=$(echo $C | sed 's/ maxn [0-9]*//' | tr ' ' '_')
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before $C"; continue; }
  echo "=== Stair nofix E1 $C (time left ${LEFT}s)"
  DUMP=stair_E1_$T.json timeout $LEFT python3 $A/orbit_probe.py nofix 0 Stair E1 $C; echo "exit $?"
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before mutant $C"; continue; }
  echo "=== MUTANT LastEither E1 $C (time left ${LEFT}s)"
  DUMP=le_E1_$T.json timeout $LEFT python3 $A/orbit_probe.py nofix 0 LastEither E1 $C; echo "exit $?"
done > run2_out.txt 2>&1
