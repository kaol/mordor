#!/bin/bash
# Run 5 (lead, push): StairTb at exact N = 2, 3 (branch atom with N >= 2 is silent in run 3) on H 12, and at width
# M 6 (tall 10 6 1 8), each paired with the calibrated mutant LastEither (orbit_probe.py) under the same flags.
# One job, cap 1500 s total.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
A=/home/user/mordor/experiments/amalgamation
END=$(( $(date +%s) + 1500 ))
for J in "E2|tall 12 4 1 8|40" "E3|tall 12 4 1 8|40" "E2|tall 10 6 1 8|40" "E1|tall 10 6 1 8|40"; do
  IFS='|' read E CC MX <<< "$J"
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before Stair $E $CC"; continue; }
  echo "=== Stair nofix $E $CC maxn $MX (time left ${LEFT}s)"
  DUMP=stair_models_${E}_$(echo $CC | tr ' ' '_').json timeout $LEFT python3 ../stair_probe.py nofix maxn $MX $E $CC; echo "exit $?"
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before mutant $E $CC"; continue; }
  echo "=== MUTANT LastEither $E $CC maxn $MX (time left ${LEFT}s)"
  DUMP=le_models_${E}_$(echo $CC | tr ' ' '_').json timeout $LEFT python3 $A/orbit_probe.py nofix 0 LastEither $E $CC maxn $MX; echo "exit $?"
done > run5_out.txt 2>&1
