"""RowLT: which columns carry the LT pair on row x = F(⊥, w*) (log §34.3z²⁰⁷).

Models: SAT models of 'desclt multi notop nofeeder abot' restricted to y = y* (Python filter), i.e. F(x, w*) ≰ w*.
For each LT column v of row x: v ≤ y*, v ≤ w*, v = t = F(x, w*), v minimal among row-x pre-fixed points above x, F(x, v) = x
(lower cell), v ∈ R_2, v = x ⊔ (atom), F(m, v) relation.  Also: is there an LT column that is minimal pre-fixed above x?
   python3 k1_rowcol_probe.py (closure … | sweep …)
"""
import sys, collections, json
sys.argv += ['multi', 'notop', 'nofeeder', 'abot']
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc
FLAGS = ('multi', 'notop', 'nofeeder', 'abot')
C = collections.Counter()
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS]):
    if L.height < 3: continue
    for m in range(L.n):
        if L.rank[m] != 2: continue
        F = sc.query(L, m, 'desclt', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; st = stages(L, F); bot = h.index(0)
        inR = lambda z, j: st[z] is not None and st[z] <= j
        ys = ystar(L, F, m); w = F[m][ys]; x = F[bot][w]
        if le[m][w] or h[x] != 1 or x == w or le[F[x][w]][w]: C['DescLT holds at y* (violation only at another y)'] += 1; continue
        t = F[x][w]
        LT = lambda v: le[x][v] and x != v and not le[m][v] and le[F[x][v]][v] and le[F[bot][v]][x]
        P = [v for v in range(n) if le[x][v] and v != x and le[F[x][v]][v]]
        Pmin = [v for v in P if not any(u != v and le[u][v] for u in P)]
        cols = [v for v in range(n) if LT(v)]
        C['DescLT violated at y*'] += 1
        C[('x ∥ m', not le[x][m], 'F(x,x) ≤ x', le[F[x][x]][x], 'some LT column', bool(cols))] += 1
        C[('some LT column minimal pre-fixed above x', any(v in Pmin for v in cols), 'all minimal pre-fixed are LT', all(LT(v) for v in Pmin if not le[m][v]))] += 1
        C[('some LT column = t', t in cols, '≤ w', any(le[v][w] for v in cols), '≤ y*', any(le[v][ys] for v in cols), 'lower cell F(x,v)=x', any(F[x][v] == x for v in cols), 'in R_2', any(inR(v, 2) for v in cols))] += 1
        C[('t vs w', 'incomparable' if not le[t][w] and not le[w][t] else '>w' if le[w][t] else '<w', 't ≤ y*', le[t][ys], 'F(⊥,t) ≤ x', le[F[bot][t]][x], 'F(x,t) ≤ t', le[F[x][t]][t])] += 1
        mt = L.S.index(L.S[w] & L.S[t]) if (L.S[w] & L.S[t]) in L.S else None
        C[('w ⊓ t', 'x' if mt == x else ('>x' if mt is not None and le[x][mt] else 'other'))] += 1
for k_, v in sorted(C.items(), key=str): print(k_, v)
