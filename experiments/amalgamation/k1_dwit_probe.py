"""k = 1 (log §34.3z²⁰⁵): anchored descent witnesses and the carrier of the cell.

Models as in k1_probe.py.  DW(x, v): x ∈ R_1 of height 1, x < v, F(x, v) ≤ v, m ≰ v, x ≤ F(x, u) for every pre-fixed u ∈ (x, v]
(`DescentWitness`; it gives a cell of row x in (x, v]).  Counts: DW with v ≤ w; DW with v ≤ y*; DW anywhere; and for
the saturated shadow (q, g, e) of c = m ⊓ w: e ≤ F(e, q), F(e, q) ≤ q, F(e, w) ≤ w, DW(e, q), DW(e, w), e ≤ F(⊥, q).
   python3 k1_dwit_probe.py (closure … | sweep …)
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
        best[tag] = n; json.dump(d, open(f'k1d_{tag}_min{n}.json', 'w'))
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS]):
    if L.height < 3: continue
    for m in range(L.n):
        if L.rank[m] != 2: continue
        F = sc.query(L, m, 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; st = stages(L, F); bot = min(range(n), key=lambda x: h[x])
        inR = lambda x, j: st[x] is not None and st[x] <= j
        cell = lambda x, z: le[x][z] and z != x and (le[F[x][z]][x] or le[z][F[x][z]])
        ys = ystar(L, F, m); w = F[m][ys]
        A1 = [x for x in range(n) if inR(x, 1) and h[x] == 1]
        DW = lambda x, v: le[x][v] and x != v and le[F[x][v]][v] and not le[m][v] and all(le[x][F[x][u]] for u in range(n) if le[x][u] and u != x and le[u][v] and le[F[x][u]][u])
        dws = [(x, v) for x in A1 for v in range(n) if DW(x, v)]
        C['models'] += 1
        C[('DW anywhere', bool(dws), 'DW with v ≤ y*', any(le[v][ys] for _, v in dws), 'DW with v ≤ w', any(le[v][w] for _, v in dws))] += 1
        if not any(le[v][w] for _, v in dws): keep('nodw_w', n, dict(sets=L.S, F=F, m=m, w=w))
        x1 = F[bot][w]
        C[('F(⊥,w)', 'atom ≤ m' if h[x1] == 1 and le[x1][m] else 'atom ∥ m' if h[x1] == 1 else 'height ≥ 2')] += 1
        LW = [(x, v) for x in A1 for v in range(n) if le[x][v] and x != v and le[v][w] and le[F[x][v]][v] and le[F[bot][v]][x]]
        LT = [(x, v) for x in A1 for v in range(n) if le[x][v] and x != v and not le[m][v] and le[F[x][v]][v] and le[F[bot][v]][x]]
        C[('LW: ∃ x ∈ R_1, x < v ≤ w, F(x,v) ≤ v, F(⊥,v) ≤ x', bool(LW), 'LT: same with m ≰ v', bool(LT))] += 1
        if h[x1] == 1 and not le[x1][m]: C[('F(⊥,w) atom ∥ m: F(F(⊥,w), w) ≤ w', le[F[x1][w]][w])] += 1
        if not LW: keep('noLW', n, dict(sets=L.S, F=F, m=m, w=w))
        if not LT: keep('noLT', n, dict(sets=L.S, F=F, m=m, w=w))
        c = L.S.index(L.S[m] & L.S[w])
        if c not in A1: continue
        u = w                                            # saturated shadow of row c from w
        while True:
            t = L.S.index(L.S[c] | L.S[F[c][u]]) if (L.S[c] | L.S[F[c][u]]) in L.S else None
            j = [z for z in range(n) if le[c][z] and le[F[c][u]][z]]; t = min(j, key=lambda z: h[z])
            if t == u or le[F[c][u]][c] or le[u][F[c][u]]: break
            u = t
        if le[F[c][u]][c] or le[u][F[c][u]]: C['c has a cell on its saturation path'] += 1; continue
        q = u; g = F[c][q]
        es = [e for e in A1 if le[e][g] and not le[e][m]]
        C['saturated shadow reached (no cell of c on the path)'] += 1
        x1 = F[bot][w]
        C[('shadow: F(⊥,w) = g', x1 == g, 'F(⊥,w) ≤ g', le[x1][g], 'F(g,w) ≤ w', le[F[g][w]][w], 'g < w', le[g][w] and g != w)] += 1
        C[('shadow: F(⊥,q) = g', F[bot][q] == g, 'g an atom', h[g] == 1, 'q = w', q == w)] += 1
        for e in es:
            C[('e ≤ g: e ≤ F(e,q)', le[e][F[e][q]], 'F(e,q) ≤ q', le[F[e][q]][q], 'F(e,w) ≤ w', le[F[e][w]][w], 'DW(e,q)', DW(e, q), 'DW(e,w)', DW(e, w), 'e ≤ F(⊥,q)', le[e][F[bot][q]], 'IC(e)', any(cell(e, z) for z in range(n)))] += 1
for k_, v in sorted(C.items(), key=str): print(k_, v)
for k_, v in sorted(best.items()): print('MIN', k_, v)
