#!/bin/bash
# Run 4 (part b; part a = hand_lattices.json, hand_out.txt): the three-row world R3.
# R3 = a(bot)=bot, ZT, n1, h(top)>=3, (T) at bot; at the two colour rows a, b only: Ta (they land), land_not_le,
# no dominated exit, ColourGain (lambda(a) >= b, lambda(b) >= a); every other row of Z unconstrained (monotone only).
# NoFix, UNB, A2.  SAT = R3 model with no mu-fixed atom.  Variants drop no-dominated-exit / land_not_le; mutant drops CG.
cd "$(dirname "$0")"; export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
P=../open_probe.py
for V in "R3" "R3 CGWnoND" "R3 CGWnoLN" "R3 CGWnoCG"; do
  for C in "closure 5 11 4 30" "tall 8 4 1 12" "tall 10 4 2 20 maxn 40"; do
    tag=$(echo $V $C | tr ' ' '_')
    DUMP=$tag.json timeout 120 python3 $P nofix 0 $V UNB A2 $C > $tag.txt 2>&1
  done
done
