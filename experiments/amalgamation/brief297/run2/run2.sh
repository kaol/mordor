#!/bin/bash
# Run 2: world CGW = a(bot)=bot, ZT, n1, h(top)>=3, (T) at bot, Ta at every row of Z, and at every row x != bot of Z
# only the TopRow'-consequences: land_not_le, ColourGain (some colour <= lambda(x), not <= x), no dominated exit.
# Tb at rows of Z other than bot is DROPPED.  With NoFix, UNB (colours unbounded in Z), A2 (exactly two colours).
# SAT = a CGW model with no mu-fixed atom and two unbounded colours.  Mutants: one ingredient dropped.
cd "$(dirname "$0")"; export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
P=../open_probe.py
streamA() {
  for C in "closure 5 11 4 30" "tall 8 4 1 12" "tall 10 4 2 20 maxn 40" "tall 12 4 1 8 maxn 45" "tall 13 4 1 8 maxn 45" "tall 10 6 1 8 maxn 45"; do
    tag=$(echo $C | tr ' ' '_')
    DUMP=CGW_$tag.json timeout 240 python3 $P nofix 0 CGW UNB A2 $C > CGW_$tag.txt 2>&1
  done
}
streamB() {
  for R in CGWnoCG CGWnoND CGWnoLN; do
    for C in "closure 5 11 4 30" "tall 8 4 1 12"; do
      tag=$(echo $C | tr ' ' '_')
      DUMP=${R}_$tag.json timeout 230 python3 $P nofix 0 $R UNB A2 $C > ${R}_$tag.txt 2>&1
    done
  done
}
streamA & streamB & wait
