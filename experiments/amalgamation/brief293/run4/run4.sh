#!/bin/bash
# Run 4 (audit P2, Repair): irreparable W0^2 models, 'fast' TbFibre-restricted encoding (same SAT set), |L| <= 30,
# heights 8 and 10 (room of the B1 relatives) and closure height 6; one job, cap 1500 s.
cd "$(dirname "$0")"
export PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation
timeout 1500 python3 ../irrep_probe.py irrep fast maxn 30 tall 8 4 1 12 + tall 10 4 2 20 + closure 6 12 1 40 > run4_out.txt 2>&1
echo "exit $?" >> run4_out.txt
