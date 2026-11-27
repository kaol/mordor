#!/bin/bash
# Run 4 (P3, sharpness at N = 1 of the pushed rung TwoRowTb): orbit_probe.py nofix 0 Meet2 E1 = W0^2 at exact N = 1;
# SAT = a W0^2 model with no mu-fixed atom (TwoRowTb fails), branch read off the "model:" lines (A1 = branch a).
# Mutant column: run 1's Row1 E1 on the same four corpora (8/8 SAT, 7 in branch a).  One job, cap 1500 s total.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
A=/home/user/mordor/experiments/amalgamation
END=$(( $(date +%s) + 1500 ))
for C in "tall 13 4 1 8 maxn 40" "tall 14 4 2 20 maxn 40" "tall 10 6 1 8 maxn 45" "tall 10 7 1 5 maxn 50" "tall 12 4 1 8 maxn 45" "tall 11 5 1 8 maxn 45"; do
  T=$(echo $C | sed 's/ maxn [0-9]*//' | tr ' ' '_')
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before $C"; continue; }
  echo "=== Meet2 nofix E1 $C (time left ${LEFT}s)"
  DUMP=meet2_E1_$T.json timeout $LEFT python3 $A/orbit_probe.py nofix 0 Meet2 E1 $C; echo "exit $?"
  if [[ "$C" == "tall 12 4 1 8 maxn 45" || "$C" == "tall 11 5 1 8 maxn 45" ]]; then
    LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before mutant $C"; continue; }
    echo "=== MUTANT Row1 E1 $C (time left ${LEFT}s)"
    DUMP=row1_E1_$T.json timeout $LEFT python3 $A/orbit_probe.py nofix 0 Row1 E1 $C; echo "exit $?"
  fi
done > run4_out.txt 2>&1
