"""Per-element form of TopFibreNew(1) (log §34.3z²²⁴), rank(m) = 3.  Hypotheses (hard): F monotone, m ∈ R_3 \\ R_2,
¬IC(m), ⊤ ∉ R_4, R_3 and R_2 tight, some lower feeder; nopostlayer for every height-2 x ≠ c.  For each height-2 c,
ask: c ∈ R_2 \\ R_1, c ≰ F(c, c), and no atom configuration (p, c) has a fibre certificate.  SAT = the local dichotomy
"c ≤ F(c, c) or a certificate at c" fails at c.   python3 ag2f_local.py (sweep N MAX | closure K M SEED CNT) [mode]
  mode 'any' (default): c any height-2 element;  'feeder': c a lower feeder of m;  'cover': c ⋖ m
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
MODE = next((a for a in sys.argv if a in ('any', 'feeder', 'cover', 'notcover')), 'any')
args = [a for a in sys.argv[1:] if a not in ('any', 'feeder', 'cover', 'notcover')]
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank
    for m in range(n):
        if h[m] != 3 or L.height <= 3: continue
        feeders = [p for p in L.covers_dn[m] if h[p] == 2]
        if not feeders: continue
        for c in range(n):
            if h[c] != 2: continue
            if MODE == 'cover' and c not in feeders: continue
            if MODE == 'feeder' and c not in feeders: continue
            if MODE == 'notcover' and le[c][m]: continue
            E = Enc(L, 4); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z)
            add = E.S.add_clause
            add([r(3, m)]); add([-r(2, m)]); add([-ic(m)]); add([-r(4, L.top)])
            low = []
            for p in feeders: o = E.v('low', p); E.iff_and(o, [r(2, p), fle(p, m, p)]); low.append(o)
            add(low)
            if MODE == 'feeder': add([E.v('low', c)])
            for z in range(n):
                if h[z] > 3: add([-r(3, z)])
                if h[z] > 2: add([-r(2, z)])
                if h[z] == 2 and z != c: add([-r(2, z), -yle(z, z)])
            add([r(2, c)]); add([-r(1, c)]); add([-yle(c, c)])
            for p in range(n):
                if h[p] != 1 or not le[p][c]: continue
                for v in range(n):
                    if not (le[c][v] and v != c and not le[m][v]): continue
                    for y in range(n):
                        if le[c][y] and y != c and le[y][v]:
                            base = [-r(1, p), -f(p, c, p), -f(p, v, c)]
                            add(base + [-fle(c, y, y)]); add(base + [-yle(c, y)])
            if E.S.solve():
                C['local dichotomy fails'] += 1
                if best is None or n < best[0]: best = (n, dict(sets=L.S, F=E.decode(), m=m, c=c))
            else: C['holds'] += 1
            E.S.delete()
print(MODE, dict(C), 'smallest', best[0] if best else None)
if best: json.dump(best[1], open(f'ag2f_local_{MODE}_min{best[0]}.json', 'w'))
