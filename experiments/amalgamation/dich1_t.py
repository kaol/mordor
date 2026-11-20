"""Properties of t = F(m, ⊤) under the Dichotomy(1) hypotheses (log §34.3z²²⁶), rank(m) = 2, exact.
For each property P, search a model of the hypotheses with ¬P; re-check in Python.  [nonpl]: drop nopostlayer.
  python3 dich1_t.py PROP (sweep N MAX | closure K M SEED CNT) [nonpl]
PROPs: mlet (m ≰ t)  h2 (h(t) = 2)  le2 (h(t) ≤ 2)  tpoint (t is a G-comparable height-2 point: F(⊥, t) an atom c < t and
  F(c, t) comparable with t)  catom (F(⊥, t) is an atom)  clem (F(⊥, t) ≤ m)  below (some height-2 y ≤ t, y ≱ m, is a G-comparable point)
  tR2 (t ∈ R_2)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages
P = sys.argv[1]; NONPL = 'nonpl' in sys.argv; args = [a for a in sys.argv[2:] if a != 'nonpl']
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        feeders = [p for p in L.covers_dn[m] if h[p] == 1]
        if not feeders: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        add([r(2, m)]); add([-r(1, m)]); add([-ic(m)]); add([-r(3, top)])
        low = []
        for p in feeders: o = E.v('low', p); E.iff_and(o, [r(1, p), fle(p, m, p)]); low.append(o)
        add(low)
        for z in range(n):
            if h[z] > 2: add([-r(2, z)])
            if h[z] > 1: add([-r(1, z)])
            if h[z] == 1 and not NONPL: add([-r(1, z), -yle(z, z)])
        T = lambda t: f(m, top, t)
        def gpoint(y):                                   # y is a G-comparable height-2 point (literal list: OR over c)
            lits = []
            for c in L.covers_dn[y]:
                if h[c] == 1:
                    for q in (fle(c, y, y), yle(c, y)): o = E.v('gp', y, c, q); E.iff_and(o, [f(bot, y, c), q]); lits.append(o)
            return lits
        for t in range(n):                               # clauses: T(t) → ¬P
            if P == 'mlet' and not le[m][t]: add([-T(t)])
            if P == 'h2' and h[t] == 2: add([-T(t)])
            if P == 'le2' and h[t] <= 2: add([-T(t)])
            if P == 'catom': [add([-T(t), -f(bot, t, c)]) for c in range(n) if h[c] == 1]
            if P == 'clem': [add([-T(t), -f(bot, t, c)]) for c in range(n) if le[c][m]]
            if P == 'tR2': add([-T(t), -r(2, t)])
            if P == 'tpoint':
                if h[t] == 2 and not le[m][t]:
                    for o in gpoint(t): add([-T(t), -o])
            if P == 'below':
                for y in range(n):
                    if h[y] == 2 and not le[m][y] and le[y][t]:
                        for o in gpoint(y): add([-T(t), -o])
        if E.S.solve():
            F = E.decode(); t = F[m][top]; G = lambda y: F[F[bot][y]][y]
            gp = lambda y: h[y] == 2 and not le[m][y] and h[F[bot][y]] == 1 and le[F[bot][y]][y] and (le[G(y)][y] or le[y][G(y)])
            st = stages(L, F)
            ok = {'mlet': le[m][t], 'h2': h[t] != 2, 'le2': h[t] > 2, 'catom': h[F[bot][t]] != 1, 'clem': not le[F[bot][t]][m],
                  'tR2': not (st[t] is not None and st[t] <= 2), 'tpoint': not gp(t), 'below': not any(gp(y) for y in range(n) if le[y][t])}[P]
            assert ok, 'mismatch'
            C['¬P model'] += 1
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m))
        else: C['P holds'] += 1
        E.S.delete()
print(P, 'nonpl' if NONPL else '', dict(C), 'smallest ¬P', best[0] if best else None)
if best: json.dump(best[1], open(f'dich1_t_{P}{"_nonpl" if NONPL else ""}_min{best[0]}.json', 'w'))
