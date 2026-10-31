#!/usr/bin/env bash
# DC2 on M_ω² × C₃ at larger pool sizes, with independently checked UNSAT proofs (log §34.3z⁵³, §34.3z⁵⁸).
#   run_dc2.sh WORKDIR SOLVER [k,m ...]      default instances: 4,2 2,4 5,2 4,3 3,4 5,3 4,4
# SOLVER: an external DRAT-producing solver binary called as `SOLVER cnf proof` (kissat or cadical); SOLVER=pysat
#   solves in process without a proof (as in the log). DRAT_TRIM must point to drat-trim for proof checking.
# Writes WORKDIR/cnf/<instance>.cnf (dumped in about a minute each, < 1 GB), the proof, the drat-trim verdict, and one
# line per instance in WORKDIR/dc2_summary.txt. Delete a proof after verification: they can be tens of GB.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
W=${1:?workdir}; SOLVER=${2:?solver binary or pysat}; shift 2
INST=("$@"); [ ${#INST[@]} -eq 0 ] && INST=(4,2 2,4 5,2 4,3 3,4 5,3 4,4)
mkdir -p "$W/cnf"; cd "$W"
for km in "${INST[@]}"; do
  tag="dc2_dim2_n3_${km/,/_}"; cnf="cnf/$tag.cnf"
  if [ "$SOLVER" = pysat ]; then
    python3 "$HERE/dc2_batch.py" solve "$km" | tee -a dc2_summary.txt; continue
  fi
  [ -f "$cnf" ] || python3 "$HERE/dc2_batch.py" dump "$km" --out cnf > /dev/null
  start=$(date +%s)
  res=$("$SOLVER" "$cnf" "cnf/$tag.drat" | grep -E '^s ' | head -1)
  secs=$(( $(date +%s) - start ))
  ver="unchecked"
  if [ "$res" = "s UNSATISFIABLE" ] && [ -n "${DRAT_TRIM:-}" ]; then
    ver=$("$DRAT_TRIM" "$cnf" "cnf/$tag.drat" -t 200000 | grep -E '^s ' | head -1)
    [ -n "$ver" ] || ver="no verdict (drat-trim killed or crashed)"
  fi
  echo "$tag  $res  ${secs}s  drat-trim: $ver" | tee -a dc2_summary.txt
done
