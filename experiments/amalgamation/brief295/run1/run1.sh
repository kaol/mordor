#!/bin/bash
# Run 1 (LEAD, CertAtom at N = 1): orbit_probe.py nofix 0 E1 = full W0 (T) world, exact N = 1, SAT = no mu-fixed atom.
# Theorem (Lean, PairTrap.lean certAtom_N1): must be UNSAT on every lattice. Paired with the calibrated mutant Row1 E1
# (refuted relative, bank s292_row1_h8, N = 1) whose SAT models are dumped and replayed by pairtrap.py (footprint check).
# Room: H 13, 14 and width M 6, 7 (one step above the H 8-12, M 4 of brief293 runs 2/3/5). One job, cap 1500 s total.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
A=/home/user/mordor/experiments/amalgamation
END=$(( $(date +%s) + 1500 ))
for C in "tall 13 4 1 8 maxn 40" "tall 14 4 2 20 maxn 40" "tall 10 6 1 8 maxn 45" "tall 10 7 1 5 maxn 50"; do
  T=$(echo $C | sed 's/ maxn [0-9]*//' | tr ' ' '_')
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before $C"; continue; }
  echo "=== W0 nofix E1 $C (time left ${LEFT}s)"
  DUMP=w0_E1_$T.json timeout $LEFT python3 $A/orbit_probe.py nofix 0 E1 $C; echo "exit $?"
  LEFT=$(( END - $(date +%s) )); [ $LEFT -le 0 ] && { echo "CAP reached before mutant $C"; continue; }
  echo "=== MUTANT Row1 E1 $C (time left ${LEFT}s)"
  DUMP=row1_E1_$T.json timeout $LEFT python3 $A/orbit_probe.py nofix 0 Row1 E1 $C; echo "exit $?"
done > run1_out.txt 2>&1
