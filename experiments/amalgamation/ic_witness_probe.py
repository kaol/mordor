"""IC-lemma (log §34.3z²⁰⁸): in models with x = F(⊥, w*) cell-free (T1b dropped), which elements z of height ≥ 2 have
F(⊥, z) = ⊥ (the T1b violations the lemma predicts), described by candidate expressions.
Models: bare_rowcell-style SAT models ('ic', par, any rank of m), several per lattice via blocking clauses.
   python3 ic_witness_probe.py sweep N MAX [per=K]
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from gfp_top import ystar
PER = next((int(a[4:]) for a in sys.argv if a.startswith('per=')), 4)
args = [a for a in sys.argv[1:] if not a.startswith('per=')]
C = collections.Counter()
def gfp_col(L, F, x):                     # greatest fixed point of y ↦ x ⊔ F(x, y), from ⊤
    y = L.top
    while True:
        y2 = L.join[x][F[x][y]]
        if y2 == y: return y
        y = y2
for L in lattices(args):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0)
    mt = lambda a, b: max((z for z in range(n) if le[z][a] and le[z][b]), key=lambda z: L.rank[z])
    for m in range(n):
        if m == L.top: continue
        E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, v: E.v('f', a, b, v); sels = []
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            for x in range(n):
                if L.rank[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
                o = E.v('sel', w, x); sels.append(o)
                E.S.add_clause([-o, f(m, y, w)]); E.S.add_clause([-o, f(bot, w, x)])
                for z in range(n):
                    if not le[z][y]:
                        for g in range(n):
                            if le[z][jn[m][g]]: E.S.add_clause([-o, -f(m, z, g)])
                    if le[x][z] and z != x: E.S.add_clause([-o, -fle(x, z, x)]); E.S.add_clause([-o, -yle(x, z)])
        if not sels: E.S.delete(); continue
        E.S.add_clause(sels); k = 0
        while k < PER and E.S.solve():
            mod = set(l for l in E.S.get_model() if l > 0); k += 1
            F = [[next(v for v in range(n) if E.vars[('f', a, b, v)] in mod) for b in range(n)] for a in range(n)]
            E.S.add_clause([-E.vars[('f', a, b, F[a][b])] for a in range(n) for b in range(n)])   # block this F
            ys = ystar(L, F, m); w = F[m][ys]; x = F[bot][w]
            if le[m][w] or L.rank[x] != 1 or x == w or le[x][m]: continue
            if any(le[x][z] and z != x and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n)): continue
            Z = {z for z in range(n) if L.rank[z] >= 2 and F[bot][z] == bot}
            yx = gfp_col(L, F, x); wx = F[x][yx]; t = F[x][w]
            cand = {'t': t, 'F(x,t)': F[x][t], 'y_x': yx, 'w_x': wx, 'y_x⊓y*': mt(yx, ys), 't⊓y_x': mt(t, yx), 'x⊔w_x⊓w': jn[x][mt(wx, w)],
                    'y_x⊓w⊔?': mt(yx, jn[w][t]), 'F(x,y*)': F[x][ys], 'F(x,⊤)': F[x][L.top], 'w_x⊓y*': mt(wx, ys), 'x⊔F(⊥,y_x)': jn[x][F[bot][yx]]}
            C['models'] += 1
            C[('some T1b violation', bool(Z))] += 1
            for k_, v in cand.items(): C[(k_, 'in Z', v in Z)] += 1
            C[('w ⊓ y_x = x', mt(w, yx) == x, 'w ≰ y_x', not le[w][yx])] += 1
        E.S.delete()
for k_, v in sorted(C.items(), key=str): print(k_, v)
