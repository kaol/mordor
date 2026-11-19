"""Excluding the gap with one greatest-fixed-point instance (log §34.3z²¹⁷).

Per (m, w, x, v, g) with the gap shape (x < v ≤ y = m ⊔ w, y ⊓ g = x, x < g): hard F(m, y) = w, F(⊥, w) = x, F(⊥, v) = x,
F(x, v) = g, row x cell-free on (x, ⊤], T1b on (x, ⊤]; G only at the listed columns ('yg': y ⊔ g; 'ygs': y ⊔ g and
y ⊔ F(x, y); 'full').  A model is a gap surviving the restricted G.
   python3 gap_gtest.py (yg|ygs|full) (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
mode = sys.argv[1]; C = collections.Counter(); best = None
for L in lattices(sys.argv[2:]):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); h = L.rank; hit = False
    mt = lambda a, b: L.S.index(L.S[a] & L.S[b])
    for m in range(n):
        if m == L.top or hit: continue
        E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); sels = []
        def G(z, pre, y):
            if le[z][y]: return
            for gg in range(n):
                if le[z][jn[m][gg]]: E.S.add_clause(pre + [-f(m, z, gg)])
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            for x in range(n):
                if h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
                for v in range(n):
                    if not (le[x][v] and v != x and le[v][y]): continue
                    for g in range(n):
                        if not (le[x][g] and g != x and mt(y, g) == x): continue
                        o = E.v('sel', w, x, v, g); sels.append(o)
                        for lit in (f(m, y, w), f(bot, w, x), f(bot, v, x), f(x, v, g)): E.S.add_clause([-o, lit])
                        for z in range(n):
                            if le[x][z] and z != x:
                                E.S.add_clause([-o, -fle(x, z, x)]); E.S.add_clause([-o, -yle(x, z)]); E.S.add_clause([-o, -f(bot, z, bot)])
                        if mode == 'full':
                            for z in range(n): G(z, [-o], y)
                        else:
                            G(jn[y][g], [-o], y)
                            if mode == 'ygs':
                                for sv in range(n): G(jn[y][sv], [-o, -f(x, y, sv)], y)
        if not sels: E.S.delete(); continue
        E.S.add_clause(sels)
        if E.S.solve(): hit = True
        E.S.delete()
    C['counterexample' if hit else 'none'] += 1
    if hit and (best is None or n < best): best = n
print(f'gap excluded with G restricted ({mode}):', dict(C), 'smallest', best)
