#!/usr/bin/env python3
"""Stand-in for an external DRAT solver: `pysat_drat.py cnf proof` solves with Glucose 4 (PySAT) and writes a textual
DRAT proof on UNSAT, printing the solver's `s ...` line. Use it as SOLVER when kissat/cadical are not installed; it is
much slower than kissat on the large DC2 instances and keeps the whole proof in memory."""
import sys
from pysat.formula import CNF
from pysat.solvers import Glucose4
F = CNF(from_file=sys.argv[1])
with Glucose4(bootstrap_with=F.clauses, with_proof=True) as s:
    if s.solve(): print("s SATISFIABLE"); sys.exit(10)
    with open(sys.argv[2], 'w') as fh: fh.write('\n'.join(s.get_proof()) + '\n')
    print("s UNSATISFIABLE"); sys.exit(20)
