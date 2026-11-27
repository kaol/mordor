#!/bin/bash
# Run 2 (lead): TwoRowTb at exact N = 1 (Meet2 E1; branch atom = the B1 theorem, branch a = the open A1 case),
# paired with the calibrated mutant Row1 E1 (refuted relative, bank s292_row1_h8 lies in B1); one job, cap 1500 s total.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
A=/home/user/mordor/experiments/amalgamation
END=$(( $(date +%s) + 1500 ))
for C in "tall 8 4 1 12" "tall 10 4 2 20 maxn 40" "tall 12 4 1 8 maxn 40"; do
  for R in Meet2 Row1; do
    LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP 1500s reached before $R $C"; continue; }
    echo "=== $R E1 $C (time left ${LEFT}s)"
    DUMP=dump_${R}_$(echo $C | tr ' ' '_').json timeout $LEFT python3 $A/orbit_probe.py nofix 0 $R E1 $C
    echo "exit $?"
  done
done > run2_out.txt 2>&1
