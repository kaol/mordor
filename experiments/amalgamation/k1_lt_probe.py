"""k = 1 (log §34.3z²⁰⁵): canonical LT pairs.  LT(x, v): x ∈ R_1 of height 1, x < v, m ≰ v, F(x,v) ≤ v, F(⊥,v) ≤ x.

Models as in k1_probe.py.  Candidates: (desc) the last pair of the ⊥-row descent v ↦ F(⊥, v) from w (v of height ≥ 2,
x = F(⊥, v) of height 1); (meet) x = m ⊓ w, v = w; (sat) x = g = F(c, q), v = w; and any LT pair with v ≤ w / v ≤ y*.
   python3 k1_lt_probe.py (closure … | sweep …)
"""
import sys, collections, json
sys.argv += ['multi', 'notop', 'nofeeder']
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc
FLAGS = ('multi', 'notop', 'nofeeder')
C = collections.Counter(); best = {}
def keep(tag, n, d):
    if tag not in best or n < best[tag]:
        best[tag] = n; json.dump(d, open(f'k1lt_{tag}_min{n}.json', 'w'))
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS]):
    if L.height < 3: continue
    for m in range(L.n):
        if L.rank[m] != 2: continue
        F = sc.query(L, m, 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; st = stages(L, F); bot = h.index(0)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        ys = ystar(L, F, m); w = F[m][ys]
        LT = lambda x, v: inR(x, 1) and h[x] == 1 and le[x][v] and x != v and not le[m][v] and le[F[x][v]][v] and le[F[bot][v]][x]
        C['models'] += 1
        v = w; pair = None
        while True:
            x = F[bot][v]
            if x == v: break
            if h[x] <= 1: pair = (x, v) if h[x] == 1 else None; break
            v = x
        if pair is None: C[('desc: no height-1 end', 'last', h[v], 'F(⊥,w) = w', F[bot][w] == w)] += 1
        else:
            x, v = pair
            C[('desc pair: b(v) ≤ v', le[b_of(L, F, v)][v], 'F(v,v) ≤ v', le[F[v][v]][v], 'x ≤ m', le[x][m], 'v = w', v == w)] += 1
            if v == w: C[('desc pair v = w: F(y*,w) ≤ w', le[F[ys][w]][w], 'F(w,y*) ≤ w', le[F[w][ys]][w], 'b(w) = x', b_of(L, F, w) == x)] += 1
            C[('desc pair (x, v)', 'LT', LT(x, v), 'F(x,v) ≤ v', le[F[x][v]][v], 'x ≤ m', le[x][m], 'v = w', v == w)] += 1
            if not LT(x, v): keep('descfail', n, dict(sets=L.S, F=F, m=m, w=w, x=x, v=v))
        chain = [w]
        while F[bot][chain[-1]] != chain[-1] and len(chain) < n: chain.append(F[bot][chain[-1]])
        kl2 = lambda v: le[F[F[bot][v]][v]][v]
        C[('K2 along the whole ⊥-descent from w', all(kl2(v) for v in chain))] += 1
        C[('K2 for every v ≤ w with F(⊥,v) ≤ v', all(kl2(v) for v in range(n) if le[v][w] and le[F[bot][v]][v]))] += 1
        C[('K2 for every v ≱ m with F(⊥,v) ≤ v', all(kl2(v) for v in range(n) if not le[m][v] and le[F[bot][v]][v]))] += 1
        allp = [(x, v) for x in range(n) for v in range(n) if LT(x, v)]
        C[('LT with v ≤ w', any(le[v][w] for _, v in allp), 'v ≤ y*', any(le[v][ys] for _, v in allp), 'any', bool(allp))] += 1
        C[('LT rows', tuple(sorted({'≤m' if le[x][m] else '∥m' for x, _ in allp})))] += 1
for k_, v in sorted(C.items(), key=str): print(k_, v)
for k_, v in sorted(best.items()): print('MIN', k_, v)
