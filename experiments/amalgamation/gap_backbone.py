"""Backbone of the smallest gap instance with core {m ⊔ x} (log §34.3z²¹²): F-values fixed in every model of
gap + cell-free + y greatest + F(⊥, g) ≠ ⊥ (T1b at m ⊔ x dropped).   python3 gap_backbone.py"""
import sys, itertools
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
done = False
for L in lattices(['sweep', '4', '12']):
    if done: break
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); h = L.rank
    mt = lambda a, b: L.S.index(L.S[a] & L.S[b])
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m, w, x, v, g in itertools.product(range(n), repeat=5):
        if m == L.top or le[m][w] or h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
        y = jn[m][w]
        if not (le[x][v] and v != x and le[v][y] and le[x][g] and g != x and mt(y, g) == x): continue
        def build(extra):
            E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u)
            for lit in (f(m, y, w), f(bot, w, x), f(bot, v, x), f(x, v, g)): E.S.add_clause([lit])
            E.S.add_clause([-f(bot, g, bot)])
            for z in range(n):
                if not le[z][y]:
                    for gg in range(n):
                        if le[z][jn[m][gg]]: E.S.add_clause([-f(m, z, gg)])
                if le[x][z] and z != x: E.S.add_clause([-fle(x, z, x)]); E.S.add_clause([-yle(x, z)])
                if extra and h[z] >= 2 and z != g and z != jn[m][x]: E.S.add_clause([-f(bot, z, bot)])
            return E, f
        E, f = build(True)
        if not E.S.solve(): E.S.delete(); continue
        z0 = jn[m][x]
        if E.S.solve(assumptions=[-f(bot, z0, bot)]): E.S.delete(); continue   # need: T1b at m⊔x is the core
        print(f'|L|={n} lattice={[nm(i) for i in range(n)]}\n m={nm(m)} w={nm(w)} y={nm(y)} x={nm(x)} v={nm(v)} g={nm(g)} m⊔x={nm(z0)}')
        fixed = {}
        for a in range(n):
            for b in range(n):
                vals = [u for u in range(n) if E.S.solve(assumptions=[f(a, b, u)])]
                if len(vals) == 1: fixed[(a, b)] = vals[0]
                elif len(vals) <= 3 and (a in (bot, x, m) ): fixed[(a, b)] = vals
        rows = {bot: '⊥', x: 'x', m: 'm'}
        for a, lab in rows.items():
            print(f' row {lab}:', ', '.join(f'{nm(b)}→' + (nm(fixed[(a, b)]) if isinstance(fixed[(a, b)], int) else '{' + '|'.join(nm(u) for u in fixed[(a, b)]) + '}') for b in range(n) if (a, b) in fixed))
        done = True; E.S.delete(); break
