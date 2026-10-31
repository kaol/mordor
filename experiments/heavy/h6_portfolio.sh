#!/usr/bin/env bash
# Edge-height 6 ground refutation, a portfolio of independent trajectories (log §34.3h, §34.3z⁴⁰, §34.3z⁵⁴).
# UNSAT on any one of them proves Cut, semi-CL and CL on every bounded poset / complete lattice of edge-height ≤ 6
# (M_ω² × C₃ included) once certified (certify_ground.sh). SAT at the cap is inconclusive.
#   h6_portfolio.sh WORKDIR [VARIANTS...]      e.g.  h6_portfolio.sh ~/h6 A B      (default: A B C)
# Each variant runs in WORKDIR under its own checkpoint tag, restarts itself from the checkpoint after a crash (both
# CaDiCaL builds have crashed rarely in long runs, §34.3h), and stops on UNSAT or at the term cap.
# Logs: WORKDIR/<variant>.log; on UNSAT: cut_H6_<tag>.cnf and .maps.pkl in WORKDIR.
set -u
HERE=$(cd "$(dirname "$0")" && pwd); RH="$HERE/../sat/run_height.py"; H=${H:-6}   # H overridable for smoke tests
W=${1:?workdir}; shift; mkdir -p "$W"; cd "$W"
declare -A V
# variant -> "cap per_round opts"; memory figures are measured peaks of the same settings (§34.3z⁵⁴), growing roughly
# quadratically with the term count.
V[A]="20000 2 front,forget=2000000"                    # 2 GB at 800 terms
V[B]="20000 4 front,allmid,forget=2000000,cd195"       # 8 GB at 1180 terms
V[C]="20000 1 front,forget=2000000,cd195,nophases"     # slowest per term, smallest steps
V[D]="20000 8 front,allmid,forget=4000000"             # most aggressive; expect > 16 GB past 1500 terms
VARS=("$@"); [ ${#VARS[@]} -eq 0 ] && VARS=(A B C)
run_variant() {
  local name=$1; read -r cap pr opts <<< "${V[$name]}"
  for attempt in $(seq 1 50); do
    echo "== $(date -Is) $name attempt $attempt: run_height.py $H $cap $pr $opts" >> "$name.log"
    python3 -X faulthandler "$RH" "$H" "$cap" "$pr" "$opts" >> "$name.log" 2>&1; rc=$?
    if grep -q "UNSAT" "$name.log"; then echo "== $(date -Is) $name UNSAT" >> "$name.log"; return 0; fi
    [ $rc -eq 0 ] && { echo "== $(date -Is) $name stopped (cap reached, inconclusive)" >> "$name.log"; return 0; }
    echo "== $(date -Is) $name exited with $rc; resuming from checkpoint in 30 s" >> "$name.log"; sleep 30
  done
}
for v in "${VARS[@]}"; do [ -n "${V[$v]:-}" ] || { echo "unknown variant $v"; exit 1; }; run_variant "$v" & done
echo "started ${VARS[*]} in $W; follow with: tail -F $W/*.log | grep --line-buffered -E 'round|UNSAT|exited|stopped'"
wait
