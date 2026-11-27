"""Free: over the stored models in W0^2, per pair (q, x) (q atom of Z, x in Z above q): boundary points l < i(q)
(B_l = u_l(q) ^ u_{kappa(l)-1}(x)); count pairs with a connector (boundary value an atom), pairs landing differently,
and check LandEq: no connector => lambda(x) = lambda(q)."""
import sys, collections
sys.path.insert(0, '.'); from corners import staircase, w0sq
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter(); nm = 0
for name, w in dedup(load_all()):
    if not w.base() or any(w.lam(x) is None for x in w.Z) or not w0sq(w): continue
    nm += 1; le, F, h = w.le, w.F, w.h
    for q in w.atoms:
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            vals = [F[q][G(l, kap[l] - 1)] for l in range(len(kap))]
            assert all(not le[e][q] for e in vals)
            conn = any(h[e] == 1 for e in vals); same = w.lam(x) == w.lam(q)
            C[('connector' if conn else 'no connector', 'same landing' if same else 'DIFFERENT landing')] += 1
print('models', nm); [print(v, k) for k, v in sorted(C.items())]
