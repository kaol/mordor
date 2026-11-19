"""IC↑ with the greatest-fixed-point property of y* restricted to named columns (log §34.3z²¹⁵).

Per (m, w, x) as in ic_core.py: hard F(m, y) = w (y = m ⊔ w), F(⊥, w) = x, row x cell-free on (x, ⊤], T1b↑ on (x, ⊤],
and G only at the named columns (mode 'ys': y ⊔ s; 'fam': a ⊔ s for a ∈ {⊥, x, w, m, y}, s ∈ {F(x, y), F(x, w)};
'full': all z ≰ y; 'colchain': y ⊔ c for c on the orbit c ↦ x ⊔ F(x, c) from ⊤; 'xorb': y ⊔ v for v on the orbit
v ↦ F(x, v) from y, v ≠ y).  A model is a counterexample to the restricted IC↑.
   python3 ic_gtest.py (ys|fam|full) (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
mode = sys.argv[1]; C = collections.Counter(); best = None
for L in lattices(sys.argv[2:]):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); h = L.rank; hit = False
    for m in range(n):
        if m == L.top or hit: continue
        for w in range(n):
            if le[m][w] or hit: continue
            y = jn[m][w]
            for x in range(n):
                if h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
                E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u)
                E.S.add_clause([f(m, y, w)]); E.S.add_clause([f(bot, w, x)])
                for z in range(n):
                    if le[x][z] and z != x:
                        E.S.add_clause([-fle(x, z, x)]); E.S.add_clause([-yle(x, z)]); E.S.add_clause([-f(bot, z, bot)])
                def G(z, pre):
                    if le[z][y]: return
                    for g in range(n):
                        if le[z][jn[m][g]]: E.S.add_clause(pre + [-f(m, z, g)])
                if mode == 'full':
                    for z in range(n): G(z, [])
                elif mode in ('colchain', 'xorb'):
                    P = lambda i, v: E.v('P', i, v)
                    E.S.add_clause([P(0, L.top if mode == 'colchain' else y)])
                    for i in range(n):
                        for v in range(n):
                            for g in range(n): E.S.add_clause([-P(i, v), -f(x, v, g), P(i + 1, jn[x][g] if mode == 'colchain' else g)])
                            for u in range(v + 1, n): E.S.add_clause([-P(i, v), -P(i, u)])
                            if mode == 'colchain' or i >= 1: G(jn[y][v], [-P(i, v)])
                else:
                    for sv in range(n):
                        if mode == 'ys': G(jn[y][sv], [-f(x, y, sv)])
                        else:
                            for a in (bot, x, w, m, y):
                                G(jn[a][sv], [-f(x, y, sv)]); G(jn[a][sv], [-f(x, w, sv)])
                if E.S.solve():
                    hit = True
                    mod = set(l for l in E.S.get_model() if l > 0)
                    F = [[next(u for u in range(n) if E.vars[('f', a, b, u)] in mod) for b in range(n)] for a in range(n)]
                    import json; json.dump(dict(sets=L.S, F=F, m=m, w=w, x=x), open(f'ic_gtest_{mode}_min{n}_{L.S[-1]}_{len(L.S)}.json', 'w'))
                E.S.delete()
                if hit: break
    C['counterexample' if hit else 'none'] += 1
    if hit and (best is None or n < best): best = n
print(f'IC↑ with G restricted ({mode}):', dict(C), 'smallest', best)
