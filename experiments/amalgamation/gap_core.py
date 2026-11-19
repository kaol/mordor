"""Minimal T1b cores for the gap (log §34.3z²¹²): which T1b instances (z ≠ g) force F(⊥, g) = ⊥.

Fixed lattice, m, w (y = m ⊔ w greatest post-fixed: hard), x = F(⊥, w) atom ∥ m cell-free (hard), gap v, g (hard),
F(⊥, g) ≠ ⊥ (hard).  Guarded: T1b(z) for rank z ≥ 2, z ≠ g.  Deletion-minimal core; each z is named by the lattice
expressions (one join/meet of the named elements) it equals.   python3 gap_core.py sweep N MAX [limit=K]
"""
import sys, collections, itertools
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
LIM = next((int(a[6:]) for a in sys.argv if a.startswith('limit=')), 20)
args = [a for a in sys.argv[1:] if not a.startswith('limit=')]
C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); h = L.rank
    mt = lambda a, b: L.S.index(L.S[a] & L.S[b])
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m in range(n):
        if m == L.top: continue
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            for x in range(n):
                if h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
                for v in range(n):
                    if not (le[x][v] and v != x and le[v][y]): continue
                    for g in range(n):
                        if not (le[x][g] and g != x and mt(y, g) == x): continue
                        E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u)
                        for lit in (f(m, y, w), f(bot, w, x), f(bot, v, x), f(x, v, g)): E.S.add_clause([lit])
                        E.S.add_clause([-f(bot, g, bot)])
                        for z in range(n):
                            if not le[z][y]:
                                for gg in range(n):
                                    if le[z][jn[m][gg]]: E.S.add_clause([-f(m, z, gg)])
                            if le[x][z] and z != x: E.S.add_clause([-fle(x, z, x)]); E.S.add_clause([-yle(x, z)])
                        if not E.S.solve(): E.S.delete(); C['inconsistent without T1b'] += 1; continue
                        guards = {}
                        for z in range(n):
                            if h[z] >= 2 and z != g:
                                s_ = E.v('g', z); guards[s_] = z; E.S.add_clause([-s_, -f(bot, z, bot)])
                        if E.S.solve(assumptions=list(guards)): C['COUNTEREXAMPLE'] += 1; E.S.delete(); continue
                        core = E.S.get_core() or list(guards); i = 0
                        while i < len(core):
                            t = core[:i] + core[i + 1:]
                            if not E.S.solve(assumptions=t): core = t
                            else: i += 1
                        zs = [guards[s_] for s_ in core]
                        names = {'m': m, 'w': w, 'y': y, 'x': x, 'v': v, 'g': g, '⊤': L.top}
                        expr = {}
                        for (a, A), (b, B) in itertools.combinations(names.items(), 2):
                            expr.setdefault(jn[A][B], []).append(f'{a}⊔{b}'); expr.setdefault(mt(A, B), []).append(f'{a}⊓{b}')
                        for a, A in names.items(): expr.setdefault(A, []).insert(0, a)
                        desc = tuple(sorted(expr.get(z, ['?'])[0] for z in zs))
                        C[('core', desc)] += 1
                        if shown < LIM and '?' in desc:
                            shown += 1; print(f'|L|={n} m={nm(m)} w={nm(w)} y={nm(y)} x={nm(x)} v={nm(v)} g={nm(g)} core={[nm(z) for z in zs]}', [expr.get(z, ['?']) for z in zs])
                        E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1]): print(k_, v_)
