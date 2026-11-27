"""Free (relaxation Row1 at N = 1, branch a; dumped models of run 2): q0 = phi(r_d).  For each (q0, x)-staircase
(x in Z above q0): boundary colours; connectors (atom colours q' != q0, then q' = phi(G)); Tb failures (colour <= q0).
Also the same for every other atom.  Prints per model and a tally."""
import sys, json, collections
sys.path.insert(0, '.'); from corners import staircase
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
C = collections.Counter()
for f in sys.argv[1:]:
    for d in json.load(open(f)):
        w = W(d['sets'], d['F']); le, F, h = w.le, w.F, w.h; dd, N = w.dN()
        if not (N == 1 and h[dd] == 2): continue
        q0 = F[w.bot][w.last_hi(dd)]
        out = []
        for q in w.atoms:
            for x in w.Z:
                if not le[q][x]: continue
                G, kap, cs = staircase(w, q, x)
                cols = [F[q][G(l, kap[l] - 1)] for l in range(len(kap))]
                kinds = ['fail' if le[e][q] else ('conn' if h[e] == 1 else 'h2') for e in cols]
                if 'fail' in kinds or 'conn' in kinds: out.append((q == q0, x, w.lam(x) == w.lam(q), kinds))
        tag = (('q0 is atom' if h[q0] == 1 else 'q0 = d'),
               'q0 conn' if any(o[0] and 'conn' in o[3] for o in out) else 'q0 no conn',
               'q0 fail' if any(o[0] and 'fail' in o[3] for o in out) else 'q0 no fail',
               'other fail' if any((not o[0]) and 'fail' in o[3] for o in out) else 'no other fail')
        C[tag] += 1
for k, v in sorted(C.items()): print(v, k)
