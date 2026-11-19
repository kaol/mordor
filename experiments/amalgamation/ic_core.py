"""Minimal cores of IC↑ (log §34.3z²¹⁴) over three guarded hypothesis families.

Fixed lattice, m, w (y = m ⊔ w ≱ … with m ≰ w), x = F(⊥, w) an atom ∥ m.  Hard: F monotone, F(m, y) = w, F(⊥, w) = x.
Guarded: G(z) [y greatest: F(m, z) avoids every g with z ≤ m ⊔ g, for z ≰ y], CF(z) [row x has no cell at z > x],
T(z) [F(⊥, z) ≠ ⊥ for z > x].  If all guards together are UNSAT (IC↑ holds for this triple), print a deletion-minimal
core, z named relative to x, w, y, m.   python3 ic_core.py (sweep N MAX | closure K M SEED CNT) [limit=K]
"""
import sys, collections
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
    for m in range(n):
        if m == L.top: continue
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            for x in range(n):
                if h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
                E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u)
                E.S.add_clause([f(m, y, w)]); E.S.add_clause([f(bot, w, x)])
                guards = {}
                def guard(tag, clauses):
                    s_ = E.v('g', *tag); guards[s_] = tag
                    for c in clauses: E.S.add_clause([-s_] + c)
                for z in range(n):
                    if not le[z][y]: guard(('G', z), [[-f(m, z, g)] for g in range(n) if le[z][jn[m][g]]])
                    if le[x][z] and z != x:
                        guard(('CF', z), [[-fle(x, z, x)], [-yle(x, z)]])
                        guard(('T', z), [[-f(bot, z, bot)]])
                if E.S.solve(assumptions=list(guards)): C['IC↑ fails (counterexample)'] += 1; E.S.delete(); continue
                core = E.S.get_core() or list(guards); i = 0
                while i < len(core):
                    t = core[:i] + core[i + 1:]
                    if not E.S.solve(assumptions=t): core = t
                    else: i += 1
                tags = sorted(guards[s_] for s_ in core)
                def rel(z):
                    r = []
                    for nmz, e in (('x', x), ('w', w), ('y', y), ('m', m)):
                        r.append('=' + nmz if z == e else ('<' + nmz if le[z][e] else ('>' + nmz if le[e][z] else '∥' + nmz)))
                    return ''.join(r)
                shape = tuple(sorted(collections.Counter(t[0] for t in tags).items()))
                C[('shape', shape)] += 1
                for t in tags: C[('elem', t[0], rel(t[1]) if t[0] != 'G' else ('≤y' if le[t[1]][y] else '≰y') + (' ≥w' if le[w][t[1]] else ''))] += 1
                if shown < LIM:
                    shown += 1; print(f'|L|={n} m={nm(m)} w={nm(w)} y={nm(y)} x={nm(x)}:', ' '.join(f'{t[0]}{nm(t[1])}' for t in tags))
                E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:40]: print(k_, v_)
