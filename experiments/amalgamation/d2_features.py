"""Sampled features of Dichotomy(2) certificates (log §34.3z²²⁵): one hypothesis model per (L, m), rank(m) = 3, from
`single_claims.py topgoal atomroot vacuity`; hypothesis generation only (sampled claims are not evidence).
  python3 d2_features.py (closure K M SEED CNT | sweep N MAX) [nofi]
"""
import sys, collections; args = sys.argv[1:]
sys.argv = ['single_claims.py', 'topgoal', 'multi', 'nopostlayer', 'rmin=3', 'rmax=3', 'atomroot', 'vacuity', 'TOPGOAL'] + [a for a in args if a == 'nofi']
sys.path.insert(0, '.')
import single_claims as sc
C = collections.Counter()
for L in sc.lattices([a for a in args if a != 'nofi']):
    n = L.n; le = L.le; h = L.rank; jn = L.join; mt = L.meet
    for m in range(n):
        if h[m] != 3 or h[m] >= L.height: continue
        F = sc.query(L, m, 'topgoal')
        if not F: continue
        st = sc.stages(L, F); bot = h.index(0)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        ys = sc.ystar(L, F, m); w = F[m][ys]; bm = sc.b_of(L, F, m); am = sc.a_of(L, F, m)
        B = [sc.b_of(L, F, y) for y in range(n)]; A = [sc.a_of(L, F, y) for y in range(n)]
        def cert(c):
            return any(h[p] == 1 and inR(p, 1) and le[p][c] and F[p][c] == p and le[c][v] and v != c and not le[m][v] and F[p][v] == c
                       and le[c][y] and y != c and le[y][v] and (le[F[c][y]][y] or le[y][F[c][y]]) for p in range(n) for v in range(n) for y in range(n))
        certs = [(p, c, v, y) for p in range(n) if h[p] == 1 and inR(p, 1) for c in range(n) if h[c] == 2 and inR(c, 2) and not inR(c, 1) and le[p][c] and F[p][c] == p
                 for v in range(n) if le[c][v] and v != c and not le[m][v] and F[p][v] == c for y in range(n) if le[c][y] and y != c and le[y][v] and (le[F[c][y]][y] or le[y][F[c][y]])]
        C['models'] += 1
        if not certs: C['no cert'] += 1; continue
        jm = lambda c: jn[c][m]
        feats = {'v ≤ y*': lambda p, c, v, y: le[v][ys], 'v = y*': lambda p, c, v, y: v == ys, 'v ≤ w': lambda p, c, v, y: le[v][w], 'v = ⊤': lambda p, c, v, y: v == L.top,
                 'v ≥ w': lambda p, c, v, y: le[w][v], 'y = v': lambda p, c, v, y: y == v, 'y lower (F(c,y) ≤ c)': lambda p, c, v, y: le[F[c][y]][c],
                 'y upper (y ≤ F(c,y))': lambda p, c, v, y: le[y][F[c][y]], 'y = c ∨ m?': lambda p, c, v, y: y == jn[c][m], 'v = c ∨ w': lambda p, c, v, y: v == jn[c][w],
                 'y ≤ c ∨ w': lambda p, c, v, y: le[y][jn[c][w]], 'p ≤ m': lambda p, c, v, y: le[p][m], 'c ≤ w': lambda p, c, v, y: le[c][w], 'p = F(⊥,w)': lambda p, c, v, y: p == F[bot][w],
                 'v = F(c, ⊤)?': lambda p, c, v, y: v == F[c][L.top], 'y covers c': lambda p, c, v, y: h[y] == 3}
        for k_, ft in feats.items(): C[(k_, 'some cert' if any(ft(*q) for q in certs) else 'NO cert', 'all certs' if all(ft(*q) for q in certs) else '-')] += 1
for k_, v in sorted(C.items(), key=str): print(k_, v)
