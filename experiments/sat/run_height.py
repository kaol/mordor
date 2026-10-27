"""Ground refutation of the cut theory at edge-height H (log §34.3h), as a long-running job.
On UNSAT, writes the clause set to cut_H<H>_<tag>.cnf for DRAT certification (glucose -certified, drat-trim) and the
Lean generator cut_lean.py.

  python3 run_height.py H [maxterms] [per_round] [opts]   e.g.  nohup python3 run_height.py 6 4000 1 forget=1000000 > h6.log &
opts, comma-separated:
  allmid      add a transitivity clause for every middle element of each violated pair (fewer re-solves; about 2× faster
              per term at H = 6, 230–380 terms; a different, equally sound search trajectory).
  forget=B    bound the solver's transitivity clauses: when more than max(B, twice the number kept at the last rebuild)
              are live, rebuild the solver keeping only those whose premises hold in the current model (§34.3z¹⁵).
              H = 6, 300 terms: 3.5M transitivity clauses without, ≤ 0.9M live with B = 10⁶. Another, equally sound
              trajectory; the .cnf then holds the solver's final clause set.
  cd195       use CaDiCaL 1.9.5 instead of 1.5.3 (pysat's Cadical195).
  nophases    forget rebuilds do not seed the new solver with the last model's phases (set_phases).
The term list is checkpointed to cut_H<H>_<tag>.ckpt every 25 rounds (nophases does not change the tag). Rerunning
the same command after a crash resumes from it: the same terms, then a new trajectory. The resumed run regenerates
every clause of those terms, so the .body and the .cnf on UNSAT are complete for it.
"""
import sys, cut_ground as c
H = int(sys.argv[1]); cap = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
pr = int(sys.argv[3]) if len(sys.argv) > 3 else 1
opts = sys.argv[4].split(',') if len(sys.argv) > 4 else []
am = 'allmid' in opts
if 'cd195' in opts: c.SOLVER = c.Cadical195
if 'nophases' in opts: c.PHASES = False
fg = next((int(float(o.split('=')[1])) for o in opts if o.startswith('forget=')), None)
tag = f"pr{pr}" + ("am" if am else "") + (f"f{fg}" if fg else "") + ("cd195" if 'cd195' in opts else "")
ok, G = c.run(H, cap, per_round=pr, wlog=True, room='fit', stream=None if fg else f"cut_H{H}_{tag}.body", allmid=am, forget=fg,
              ckpt=f"cut_H{H}_{tag}.ckpt")
if ok:
    c.write_dimacs(G, f"cut_H{H}_{tag}.cnf"); print(f"wrote cut_H{H}_{tag}.cnf", flush=True)
