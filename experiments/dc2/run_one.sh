#!/bin/bash
# Per-k check of one pattern with an explicit closure (e.g. a width-5 closure for a NO-CLOSURE pattern).
# usage: ./run_one.sh CLOSURE_JSON [K_MIN [K_MAX]]   one process per k (default 0 .. 2w), all in parallel
# Results go to c3_results_one_<host>.jsonl, which c3_summary.py reads (the closure record is written first).
cd "$(dirname "$0")"
C=$1; H=$(hostname -s); OUT=c3_results_one_$H.jsonl
W=$(python3 -c "import json,sys; print(json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])['w'])" $C)
K0=${2:-0}; K1=${3:-$((2*W))}
grep -qF "$(tail -n 1 $C)" $OUT 2>/dev/null || tail -n 1 $C >> $OUT
for k in $(seq $K0 $K1); do
  nohup python3 -u c3_one.py $C $k $OUT > c3one_${H}_$k.log 2>&1 &
done
echo "started k=$K0..$K1 for $(basename $C); results in $OUT; summary: python3 c3_summary.py"
