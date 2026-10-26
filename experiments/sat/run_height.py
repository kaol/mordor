"""Ground refutation of the cut theory at edge-height H (log §34.3h), as a long-running job.
On UNSAT, writes the clause set to cut_H<H>.cnf for DRAT certification (glucose -certified, drat-trim) and the
Lean generator cut_lean.py.

  python3 run_height.py H [maxterms] [per_round] [allmid]   e.g.  nohup python3 run_height.py 6 4000 1 allmid > h6.log &
allmid: add a transitivity clause for every middle element of each violated pair (fewer re-solves; about 2× faster
per term at H = 6, 230–380 terms; a different, equally sound search trajectory)."""
import sys, cut_ground as c
H = int(sys.argv[1]); cap = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
pr = int(sys.argv[3]) if len(sys.argv) > 3 else 1
am = len(sys.argv) > 4 and sys.argv[4] == 'allmid'
tag = f"pr{pr}" + ("am" if am else "")
ok, G = c.run(H, cap, per_round=pr, wlog=True, room='fit', stream=f"cut_H{H}_{tag}.body", allmid=am)   # clauses to disk, not RAM
if ok:
    c.write_dimacs(G, f"cut_H{H}_{tag}.cnf"); print(f"wrote cut_H{H}_{tag}.cnf ({G.nclauses} clauses)", flush=True)
