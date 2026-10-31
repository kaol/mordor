#!/usr/bin/env bash
# Certify an UNSAT ground refutation from run_height.py and turn it into Lean (log §34.3h workflow).
#   certify_ground.sh H TAG [SOLVER]
# Needs, in the current directory: cut_H<H>_<TAG>.cnf and cut_H<H>_<TAG>.maps.pkl (written by run_height.py on UNSAT).
# Environment: DRAT_TRIM (path to drat-trim, required), MORDOR (repo root, default: two levels up from this script).
# SOLVER (optional): an external DRAT-producing solver binary, called as `SOLVER cnf proof`; kissat and cadical both
#   accept that form (binary DRAT by default, which drat-trim detects); SOLVER_ARGS adds flags. Without it, PySAT's
#   Glucose 4 produces the proof in process (drat_certify.py; fine for small cores, slow for large instances).
# Refuses to overwrite an existing lean/Mordor/CutHeight<H>.lean unless FORCE=1.
# Output: cut_H<H>_<TAG>.core (drat-trim core), lean/Mordor/CutHeight<H>.lean, and a `lake build` of it.
set -euo pipefail
H=$1; TAG=$2; SOLVER=${3:-}
HERE=$(cd "$(dirname "$0")" && pwd); MORDOR=${MORDOR:-$(cd "$HERE/../.." && pwd)}
: "${DRAT_TRIM:?set DRAT_TRIM to the drat-trim binary}"
B=cut_H${H}_${TAG}
[ -f "$B.cnf" ] && [ -f "$B.maps.pkl" ] || { echo "missing $B.cnf or $B.maps.pkl"; exit 1; }
if [ -n "$SOLVER" ]; then
  echo "== $SOLVER $B.cnf (DRAT to $B.drat)"
  set +e; "$SOLVER" ${SOLVER_ARGS:-} "$B.cnf" "$B.drat" | grep -E '^s '; set -e
  echo "== drat-trim"
  "$DRAT_TRIM" "$B.cnf" "$B.drat" -c "$B.core" | grep -E 'VERIFIED|ERROR|core|lemmas'
else
  echo "== Glucose 4 + drat-trim (drat_certify.py)"
  python3 "$MORDOR/experiments/sat/drat_certify.py" "$B.cnf" "$DRAT_TRIM" "$B.core"
fi
grep -q . "$B.core" || { echo "no core written: not certified"; exit 2; }
OUT="$MORDOR/lean/Mordor/CutHeight${H}.lean"
if [ -e "$OUT" ] && [ "${FORCE:-0}" != 1 ]; then echo "$OUT exists; set FORCE=1 to overwrite (core is in $B.core)"; exit 3; fi
echo "== cut_lean.py: $(grep -vc '^p' "$B.core") core clauses"
python3 "$MORDOR/experiments/sat/cut_lean.py" "$H" "$B.core" "$B.maps.pkl" "$OUT"
echo "== lake build Mordor.CutHeight${H} (bv_decide; the H = 5 core of 832 clauses took 14 min)"
cd "$MORDOR/lean" && lake build "Mordor.CutHeight${H}"
echo "Certified. Add 'import Mordor.CutHeight${H}' to lean/Mordor.lean and derive semi/cl as in Height5.lean."
