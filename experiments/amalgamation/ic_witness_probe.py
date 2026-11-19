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
            orb = [w]
            while F[x][orb[-1]] not in orb: orb.append(F[x][orb[-1]])
            col = [L.top]
            while jn[x][F[x][col[-1]]] not in col: col.append(jn[x][F[x][col[-1]]])
            sat = [w]
            while jn[x][F[x][sat[-1]]] not in sat: sat.append(jn[x][F[x][sat[-1]]])
            fam = {'x-orbit from w': orb, 'x-orbit ⊓ y*': [mt(v, ys) for v in orb], 'col orbit of x from ⊤': col,
                   'col orbit ⊓ y*': [mt(v, ys) for v in col], 'G_x orbit from w': sat, 'G_x orbit ⊓ y*': [mt(v, ys) for v in sat],
                   'F(x, x-orbit)': [F[x][v] for v in orb], 'F(x,·) ⊓ w on orbit': [mt(F[x][v], w) for v in orb],
                   'col orbit ⊓ w': [mt(v, w) for v in col], 'F(x, col)': [F[x][v] for v in col]}
            for k_, vs in fam.items(): C[(k_, 'hits Z', any(v in Z for v in vs))] += 1
            C[('y_x ≤ y*', le[yx][ys])] += 1
            K = [z for z in range(n) if le[x][z] and z != x and le[F[bot][z]][w] and (le[F[x][z]][z] or (le[F[x][z]][yx] and not le[x][F[x][z]]))]
            C[('KL2E holds', bool(K))] += 1
            chain = [L.top]
            while jn[x][F[x][chain[-1]]] != chain[-1]: chain.append(jn[x][F[x][chain[-1]]])
            kc = {'w': [w], 't': [t], 'y*': [ys], 'x-orbit from w': orb, 'y* ⊓ colchain': [mt(ys, c) for c in chain],
                  'y* ⊓ x-orbit': [mt(ys, v) for v in orb], 'w ⊔ t ⊓ y*': [mt(jn[w][t], ys)], 'colchain': chain}
            for k_, vs in kc.items(): C[('KL2 column', k_, any(v in K for v in vs))] += 1
            # first element of the x-orbit from w that is a KL2 column, kind
            for v in orb:
                if v in K: C[('first KL2 column on x-orbit', 'pre-fixed' if le[F[x][v]][v] else 'KL2', 'index', orb.index(v))] += 1; break
            if not le[yx][ys]:
                gm = lambda z: jn[m][F[m][z]]
                cand2 = {'y_x ⊓ G_m(y_x)': mt(yx, gm(yx)), 't': t, 'y_x': yx, 'w_x': wx, 'F(m,y_x)': F[m][yx], 'y_x ⊓ F(m,y_x)': mt(yx, F[m][yx]),
                         'x ⊔ (w_x ⊓ F(m,y_x))': jn[x][mt(wx, F[m][yx])], 'G_x(y*) ⊓ y_x': mt(jn[x][F[x][ys]], yx), 'y_x ⊓ (y* ⊔ w_x)': mt(yx, jn[ys][wx])}
                for k_, v in cand2.items(): C[('y_x ≰ y*', k_, 'in Z', v in Z)] += 1
                C[('y_x ≰ y*', 'y* = ⊤', ys == L.top)] += 1
            C['models'] += 1
            C[('some T1b violation', bool(Z))] += 1
            for k_, v in cand.items(): C[(k_, 'in Z', v in Z)] += 1
            C[('w ⊓ y_x = x', mt(w, yx) == x, 'w ≰ y_x', not le[w][yx])] += 1
        E.S.delete()
for k_, v in sorted(C.items(), key=str): print(k_, v)
