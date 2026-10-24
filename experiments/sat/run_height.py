"""Ground refutation of the cut theory at edge-height H (log §34.3h), as a long-running job.
On UNSAT, writes the clause set to cut_H<H>.cnf for DRAT certification (glucose -certified, drat-trim) and the
Lean generator cut_lean.py.

  python3 run_height.py H [maxterms] [per_round]     e.g.  nohup python3 run_height.py 6 4000 1 > h6.log &"""
import sys, cut_ground as c
H = int(sys.argv[1]); cap = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
pr = int(sys.argv[3]) if len(sys.argv) > 3 else 1
ok, G = c.run(H, cap, per_round=pr, wlog=True, room='fit', stream=f"cut_H{H}_pr{pr}.body")   # clauses to disk, not RAM
if ok:
    c.write_dimacs(G, f"cut_H{H}_pr{pr}.cnf"); print(f"wrote cut_H{H}_pr{pr}.cnf ({G.nclauses} clauses)", flush=True)
