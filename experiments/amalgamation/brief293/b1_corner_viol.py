"""Free check of the B1 theorem's decisive instance on stored NoFix models of relaxed worlds lying in branch b/g, N = 1
(phi(high) = {d}): the proof says W0^2 must fail at a CORNER of the (d, x)-staircase for x = lambda(d) (or for some
x >= d in Z with lambda(x) != lambda(d)).  For each such model print, per pair (d, x), the corners, their colour
F(d, G) and whether Tb fails there (F(d, G) <= d)."""
import sys, json, glob, collections
sys.path.insert(0, '.'); from corners import staircase
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W, load_all, dedup
C = collections.Counter()
for name, w in dedup(load_all()):
    if not w.base() or any(w.lam(x) is None for x in w.Z): continue
    if any(w.h[x] == 2 and w.le[w.lam(x)][x] for x in w.Z): continue
    d, N = w.dN()
    if N != 1 or w.h[d] != 1 or not w.nofix(): continue
    le, F, h = w.le, w.F, w.h
    res = []
    for x in w.Z:
        if not le[d][x] or w.lam(x) == w.lam(d): continue
        G, kap, cs = staircase(w, d, x)
        bad = [(l, k, G(l, k), F[d][G(l, k)]) for (l, k) in cs if le[F[d][G(l, k)]][d]]
        res.append((x, w.lam(x), len(cs), bad))
    hit = any(r[3] for r in res)
    C[hit] += 1
    print(name, 'n', w.n, 'H', h[w.top], 'lam(d)', w.lam(d), 'pairs (x, lam x, #corners, Tb-failing corners (l,k,G,F(d,G))):', res)
print('models with a Tb failure at a staircase corner:', dict(C))
