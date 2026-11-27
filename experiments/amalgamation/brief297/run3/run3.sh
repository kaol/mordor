#!/bin/bash
# Run 3: which ColourGain instances does the CGW contradiction use?  Sub-worlds of CGW (Tb dropped at rows of Z but
# bot; Ta, land_not_le, no dominated exit kept at every row) with ColourGain only at colour rows (CGcol), only at
# atom rows (CGat), only at height-2 rows (CGh2).  NoFix, UNB, A2.  SAT = model of that sub-world with no mu-fixed atom.
cd "$(dirname "$0")"; export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
P=../open_probe.py
for R in CGcol CGh2 CGat; do
  for C in "closure 5 11 4 30" "tall 8 4 1 12"; do
    tag=$(echo $C | tr ' ' '_')
    DUMP=${R}_$tag.json timeout 240 python3 $P nofix 0 $R UNB A2 $C > ${R}_$tag.txt 2>&1
  done
done
