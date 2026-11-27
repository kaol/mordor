#!/bin/bash
# Run 5 (LEAD push, reserved): the three-row world R3 with room.
# R3 = a(bot)=bot, ZT, n1, h(top)>=3, (T) at bot; at the colour rows only: Ta (land), land_not_le, no dominated exit,
# ColourGain (lambda(c) carries a colour other than c).  Every other row of Z unconstrained (monotone only).
# Candidate: R3 + NoFix + UNB (+ A2) has no model.  SAT = R3 model with no mu-fixed atom (candidate fails).
# Calibrated mutant CGone: ColourGain at ONE colour row only (one instance dropped).
cd "$(dirname "$0")"; export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
P=../open_probe.py
job() { tag=$1; shift; DUMP=$tag.json timeout $T python3 $P nofix 0 "$@" > $tag.txt 2>&1; }
streamA() {
  T=150 job R3_A2_closure_6_12_1_40      R3 UNB A2 closure 6 12 1 40
  T=150 job R3_A2_closure_8_10_1_300     R3 UNB A2 closure 8 10 1 300 maxn 45
  T=120 job R3_A2_tall_13_4_1_8          R3 UNB A2 tall 13 4 1 8 maxn 45
  T=150 job R3_A2_tall_14_4_2_20         R3 UNB A2 tall 14 4 2 20 maxn 45
  T=120 job R3_A2_tall_10_6_1_8          R3 UNB A2 tall 10 6 1 8 maxn 45
  T=150 job R3_A2_tall_10_7_1_5          R3 UNB A2 tall 10 7 1 5 maxn 50
  for E in E3 E4 E5 E6; do T=60 job R3_A2_${E}_tall_12_4_1_8 R3 UNB A2 $E tall 12 4 1 8 maxn 45; done
  T=120 job R3_any_closure_6_12_1_40     R3 UNB closure 6 12 1 40
  T=100 job R3_A3_tall_10_6_1_8          R3 UNB A3 tall 10 6 1 8 maxn 45
}
streamB() {
  T=150 job M_CGone_closure_6_12_1_40    R3 CGone UNB A2 closure 6 12 1 40
  T=100 job M_CGone_closure_5_11_4_30    R3 CGone UNB A2 closure 5 11 4 30
  T=150 job M_CGone_tall_13_4_1_8        R3 CGone UNB A2 tall 13 4 1 8 maxn 45
  T=150 job M_CGone_tall_14_4_2_20       R3 CGone UNB A2 tall 14 4 2 20 maxn 45
  T=120 job M_CGone_tall_10_6_1_8        R3 CGone UNB A2 tall 10 6 1 8 maxn 45
  T=150 job M_CGone_tall_10_7_1_5        R3 CGone UNB A2 tall 10 7 1 5 maxn 50
  for E in E3 E4 E5 E6; do T=60 job M_CGone_${E}_tall_12_4_1_8 R3 CGone UNB A2 $E tall 12 4 1 8 maxn 45; done
  T=120 job M_CGone_any_closure_6_12_1_40 R3 CGone UNB closure 6 12 1 40
}
streamA & streamB & wait
