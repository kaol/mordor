#!/bin/bash
# Run 1 (footprint + world check): NoFix with exactly two colour atoms unbounded in Z, in W0 and in relaxed worlds.
# SAT = a model of the stated world in which no atom of Z is mu-fixed, |A| = 2, A unbounded in Z.
cd "$(dirname "$0")"; export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
P=../open_probe.py
streamA() {
  for C in "closure 5 11 4 30" "tall 8 4 1 12"; do
    tag=$(echo $C | tr ' ' '_')
    DUMP=W0_$tag.json timeout 400 python3 $P nofix 0 UNB A2 $C > W0_$tag.txt 2>&1
    DUMP=D2_$tag.json timeout 400 python3 $P nofix 0 D2 UNB A2 $C > D2_$tag.txt 2>&1
  done
}
streamB() {
  for R in Desc1 Row1 LastEither; do
    for C in "closure 5 11 4 30" "tall 8 4 1 12"; do
      tag=$(echo $C | tr ' ' '_')
      DUMP=${R}_$tag.json timeout 230 python3 $P nofix 0 $R UNB A2 $C > ${R}_$tag.txt 2>&1
    done
  done
}
streamA & streamB & wait
