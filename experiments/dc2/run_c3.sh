#!/bin/bash
# Full DC2 check on M_ω² × C_n, all level-0 patterns, claim-based workers (resumable).
# usage: ./run_c3.sh N_WORKERS [n=3]
# Results: c3_results_<host>_<i>.jsonl (append-only JSON lines); summary: python3 c3_summary.py
cd "$(dirname "$0")"
W=${1:-8}; N=${2:-3}; H=$(hostname -s)
for i in $(seq 0 $((W-1))); do
  nohup bash -c "for r in 1 2 3 4 5 6 7 8; do python3 -u c3_driver.py $N $i $W c3_results_${H}_$i.jsonl && break; done" \
    > c3_worker_${H}_$i.log 2>&1 &
done
echo "started $W workers; monitor with: python3 c3_summary.py"
