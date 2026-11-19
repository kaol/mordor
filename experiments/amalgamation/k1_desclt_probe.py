"""DescLT counterexamples and their LT pairs (log §34.3z²⁰⁶).

Models: SAT models of 'desclt multi notop nofeeder abot' (k = 1, a(⊥) = ⊥, a column fixed point y = m ⊔ F(m, y), w = F(m, y)
≱ m, x = F(⊥, w) ≠ w of rank 1, F(x, w) ≰ w).  For each violating (y, w, x): t = F(x, w); is (x, t) an LT pair; does the
row-x orbit v ↦ F(x, v) from w reach an LT pair; is there an LT pair on row x; any LT pair (MinLT); is y = y*.
   python3 k1_desclt_probe.py (closure … | sweep …)
"""
import sys, collections, json
sys.argv += ['multi', 'notop', 'nofeeder', 'abot']
sys.path.insert(0, '../separation')
from rstages import stages
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc
FLAGS = ('multi', 'notop', 'nofeeder', 'abot')
C = collections.Counter(); best = {}
def keep(tag, n, d):
    if tag not in best or n < best[tag]:
        best[tag] = n; json.dump(d, open(f'k1dl_{tag}_min{n}.json', 'w'))
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS]):
    if L.height < 3: continue
    for m in range(L.n):
        if L.rank[m] != 2: continue
        F = sc.query(L, m, 'desclt', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; st = stages(L, F); bot = h.index(0)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        LT = lambda x, v: inR(x, 1) and h[x] == 1 and le[x][v] and x != v and not le[m][v] and le[F[x][v]][v] and le[F[bot][v]][x]
        ys = ystar(L, F, m)
        allp = [(x, v) for x in range(n) for v in range(n) if LT(x, v)]
        C['models'] += 1
        C[('any LT pair (MinLT)', bool(allp))] += 1
        for w in range(n):
            if le[m][w] or F[m][L.join[m][w]] != w: continue
            x = F[bot][w]
            if h[x] != 1 or x == w or le[F[x][w]][w]: continue
            t = F[x][w]; orb = [w]
            while len(orb) <= n and F[x][orb[-1]] not in orb: orb.append(F[x][orb[-1]])
            C[('violation', 'y = y*', L.join[m][w] == ys, 'x ∥ m', not le[x][m], 'LT(x, t)', LT(x, t), 'x-orbit hits LT', any(LT(x, v) for v in orb), 'LT on row x', any(p[0] == x for p in allp))] += 1
            if not LT(x, t): keep('noxt', n, dict(sets=L.S, F=F, m=m, w=w, x=x))
for k_, v in sorted(C.items(), key=str): print(k_, v)
for k_, v in sorted(best.items()): print('MIN', k_, v)
