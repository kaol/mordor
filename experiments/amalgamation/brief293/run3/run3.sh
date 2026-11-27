#!/bin/bash
# Run 3 (lead, sharpness/new conjecture): StairTb = CertAtom with Tb at atom rows ONLY at staircase-boundary columns
# (stair_probe.py, this briefer's encoding), all N; paired per corpus with the calibrated mutant LastEither
# (orbit_probe.py nofix 0 LastEither, refuted §292: s292_lasteither_h10).  One job, cap 1500 s total.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
A=/home/user/mordor/experiments/amalgamation
END=$(( $(date +%s) + 1500 ))
for C in "tall 8 4 1 12" "tall 10 4 2 20 maxn 40" "tall 12 4 1 8 maxn 40"; do
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before $C"; continue; }
  echo "=== Stair nofix $C (time left ${LEFT}s)"
  if [[ "$C" == *maxn* ]]; then MX=$(echo $C | awk '{print $NF}'); CC=$(echo $C | sed 's/ maxn [0-9]*//'); else MX=999; CC=$C; fi
  DUMP=stair_models_$(echo $CC | tr ' ' '_').json timeout $LEFT python3 ../stair_probe.py nofix maxn $MX $CC; echo "exit $?"
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before mutant $C"; continue; }
  echo "=== MUTANT LastEither $C (time left ${LEFT}s)"
  DUMP=le_models_$(echo $CC | tr ' ' '_').json timeout $LEFT python3 $A/orbit_probe.py nofix 0 LastEither $C; echo "exit $?"
done > run3_out.txt 2>&1
