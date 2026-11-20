"""Sampled structure of the fibre covers of the ⊥-descent atom c* (log §34.3z²³⁴): one hypothesis model per (L, m) of
m ∈ R_2 \\ R_1, h(m) = 2, R_1 and R_2 tight, w ∥ m; hypothesis generation only.   python3 cover_sample.py
"""
import sys, collections
sys.argv = ['dich1_region.py', 'region', 'closure'] ; sys.path.insert(0, '.'); sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
C = collections.Counter()
for spec in (['closure', '5', '7', '1', '12'], ['closure', '5', '8', '2', '12'], ['sweep', '4', '10']):
  for L in lattices(spec):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join; mt = L.meet
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        add([r(2, m)]); add([-r(1, m)])
        for z in range(n):
            if h[z] > 2: add([-r(2, z)])
            if h[z] > 1: add([-r(1, z)])
        U = lambda i, z: E.v('U', i, z); NO = L.height + 1
        for z in range(n): add([U(0, z)] if z == top else [-U(0, z)])
        for i in range(NO - 1):
            for z in range(n):
                lits = []
                for v in range(n):
                    for g in range(n):
                        if jn[m][g] == z: o = E.v('Ust', i, v, g); E.iff_and(o, [U(i, v), f(m, v, g)]); lits.append(o)
                E.iff_or(U(i + 1, z), lits)
        for z in range(n):
            for g in range(n):
                if le[g][m] or le[m][g]: add([-U(NO - 1, z), -f(m, z, g)])
        if not E.S.solve(): E.S.delete(); continue
        F = E.decode(); E.S.delete()
        u = top
        while True:
            v = jn[m][F[m][u]]
            if v == u: break
            u = v
        w = F[m][u]; v = w; seen = set(); cs = None
        while v not in seen:
            seen.add(v)
            if h[v] == 1: cs = v
            v = F[bot][v]
        c = cs; C['models'] += 1
        covs = [v for v in L.covers_up[c] if h[v] == 2 and not le[m][v] and F[bot][v] == c]
        good = [v for v in covs if le[F[c][v]][v]]
        gap = [v for v in covs if not le[F[c][v]][v] and not le[v][F[c][v]]]
        up = [v for v in covs if le[v][F[c][v]] and not le[F[c][v]][v]]
        C[('#fibre covers', len(covs), '#pre-fixed', len(good), '#gap', len(gap), '#upper-only', len(up))] += 1
        C[('c* ≤ m', le[c][m])] += 1
        C[('pre-fixed covers kind', tuple(sorted('lower' if F[c][v] == c else 'fixed' for v in good)))] += 1
for k, v in sorted(C.items(), key=lambda kv: -kv[1])[:30]: print(k, v)
