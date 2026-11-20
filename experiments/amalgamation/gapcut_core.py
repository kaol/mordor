"""Minimal T1b↑ cores of TransitionWitness (log §34.3z²¹⁹).

Fixed lattice and selection (m, w, x, v, g, u = u_n, u2 = u_{n+1}): hard y = m ⊔ w greatest, F(m, y) = w, F(⊥, w) = x,
gap (F(⊥, v) = x, F(x, v) = g, y ⊓ g = x), u on m's column orbit with u2 = m ⊔ F(m, u), g ⊓ u > x, g ⊓ u2 = x, row x
cell-free, F(⊥, c) ≠ ⊥ (c = g ⊓ u).  Guarded: T1b↑ at z > x, z ≠ c.  Deletion-minimal cores; elements named by one
join/meet of the named elements.   python3 gapcut_core.py (sweep N MAX | closure K M SEED CNT) [limit=K]
"""
import sys, collections, itertools
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
LIM = next((int(a[6:]) for a in sys.argv if a.startswith('limit=')), 10)
args = [a for a in sys.argv[1:] if not a.startswith('limit=')]
C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); h = L.rank
    mt = lambda a, b: L.S.index(L.S[a] & L.S[b])
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m, w, x, v, g, u, u2 in itertools.product(range(n), repeat=7):
        if m == L.top or le[m][w] or h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
        y = jn[m][w]
        if not (le[x][v] and v != x and le[v][y] and le[x][g] and g != x and mt(y, g) == x): continue
        if not (le[y][u] and mt(g, u) != x and le[y][u2] and le[u2][u] and mt(g, u2) == x): continue
        c = mt(g, u)
        E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, q: E.v('f', a, b, q)
        for lit in (f(m, y, w), f(bot, w, x), f(bot, v, x), f(x, v, g)): E.S.add_clause([lit])
        for q in range(n):
            if jn[m][q] != u2: E.S.add_clause([-f(m, u, q)])
        P = lambda i, z: E.v('P', i, z)
        E.S.add_clause([P(0, L.top)])
        for i in range(n):
            for z in range(n):
                for q in range(n): E.S.add_clause([-P(i, z), -f(m, z, q), P(i + 1, jn[m][q])])
                for z2 in range(z + 1, n): E.S.add_clause([-P(i, z), -P(i, z2)])
        E.S.add_clause([P(i, u) for i in range(n)])
        E.S.add_clause([-f(bot, c, bot)])
        for z in range(n):
            if not le[z][y]:
                for gg in range(n):
                    if le[z][jn[m][gg]]: E.S.add_clause([-f(m, z, gg)])
            if le[x][z] and z != x: E.S.add_clause([-fle(x, z, x)]); E.S.add_clause([-yle(x, z)])
        if not E.S.solve(): C['inconsistent without T1b↑'] += 1; E.S.delete(); continue
        guards = {}
        for z in range(n):
            if le[x][z] and z != x and z != c:
                s_ = E.v('g', z); guards[s_] = z; E.S.add_clause([-s_, -f(bot, z, bot)])
        if E.S.solve(assumptions=list(guards)): C['COUNTEREXAMPLE'] += 1; E.S.delete(); continue
        core = E.S.get_core() or list(guards); i = 0
        while i < len(core):
            t = core[:i] + core[i + 1:]
            if not E.S.solve(assumptions=t): core = t
            else: i += 1
        zs = [guards[s_] for s_ in core]
        names = {'m': m, 'w': w, 'y': y, 'x': x, 'v': v, 'g': g, 'u': u, "u'": u2, 'c': c}
        expr = {}
        for a, A in names.items(): expr.setdefault(A, []).append(a)
        for (a, A), (b, B) in itertools.combinations(names.items(), 2):
            expr.setdefault(jn[A][B], []).append(f'{a}⊔{b}'); expr.setdefault(mt(A, B), []).append(f'{a}⊓{b}')
        def cls(z):
            if expr.get(z): return expr[z][0]
            return ('≥x' if le[x][z] else '') + (',≤y' if le[z][y] else ',≰y') + (',≤c' if le[z][c] else '') + (',≤g' if le[z][g] else '') + (',≤x⊔m' if le[z][jn[x][m]] else '')
        desc = tuple(sorted(cls(z) for z in zs))
        C[('transition at u = ⊤', u == L.top)] += 1
        C[('core', desc)] += 1
        if shown < LIM and u != L.top:
            # sample relaxed models (core minus its single instance) and print relations
            if len(zs) == 1:
                z0 = zs[0]; blk = []; k = 0
                while k < 4 and E.S.solve(assumptions=blk):
                    mod = set(l for l in E.S.get_model() if l > 0); k += 1
                    Fv = lambda a, b: next(q for q in range(n) if E.vars[('f', a, b, q)] in mod)
                    print(f'   model: F(⊥,c)={nm(Fv(bot,c))} F(x,c)={nm(Fv(x,c))} F(m,u)={nm(Fv(m,u))} F(⊥,z0)={nm(Fv(bot,z0))} F(x,z0)={nm(Fv(x,z0))} F(m,z0)={nm(Fv(m,z0))} F(⊥,g)={nm(Fv(bot,g))} F(x,g)={nm(Fv(x,g))}  z0 vs c: {"≤" if le[z0][c] else "≥" if le[c][z0] else "∥"}, z0 vs g: {"≤" if le[z0][g] else "≥" if le[g][z0] else "∥"}, z0 vs u: {"≤" if le[z0][u] else "∥/≥"}, z0 vs u2: {"≤" if le[z0][u2] else "≰"}, z0 = x ⊔ F(⊥,c)? {z0 == jn[x][Fv(bot,c)]}, z0 = c ⊔ F(x,c)?{z0 == jn[c][Fv(x,c)]}')
                    cl = E.v('blk', k, z0); E.S.add_clause([-cl] + [-E.vars[('f', a, b, Fv(a, b))] for a in (bot, x, m) for b in range(n)]); blk.append(cl)
            shown += 1; print(f'|L|={n} m={nm(m)} w={nm(w)} y={nm(y)} x={nm(x)} v={nm(v)} g={nm(g)} u={nm(u)} u2={nm(u2)} c={nm(c)} core={[nm(z) for z in zs]}')
        E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:25]: print(k_, v_)
