"""Minimal cores of MinH2Orbit (log §34.3z²²⁹), rank(m) = 2.  Hard: F monotone, m ∈ R_2 \\ R_1, m's column orbit
u_0 = ⊤, u_{n+1} = m ⊔ F(m, u_n) (one-hot U(n, z), n ≤ height).  Guards: OL(n), OU(n) [u_n > m ⟹ F(m, u_n) ≰ m;
u_n ≰ F(m, u_n)], TR / TA(x) / TB(g) [⊤ ∉ R_3 by route], T2(z) [R_2 tightness], X(y) [y not a G-comparable point].
  python3 dich1_orbcore.py (sweep N MAX | closure K M SEED CNT) [limit=K]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
LIM = next((int(a[6:]) for a in sys.argv if a.startswith('limit=')), 10)
args = [a for a in sys.argv[1:] if not a.startswith('limit=')]
C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z)
        A = lambda x, g: E.v('A', x, g); B = lambda y, g: E.v('B', y, g); add = E.S.add_clause
        add([r(2, m)]); add([-r(1, m)])
        U = lambda i, z: E.v('U', i, z); NO = L.height + 1
        for z in range(n): add([U(0, z)] if z == top else [-U(0, z)])
        for i in range(NO - 1):
            for z in range(n):
                lits = []
                for v in range(n):
                    for g in range(n):
                        if jn[m][g] == z: o = E.v('Ust', i, v, g); E.iff_and(o, [U(i, v), f(m, v, g)]); lits.append(o)
                E.iff_or(U(i + 1, z), lits)
        guards = {}
        def guard(tag, clauses):
            s_ = E.v('g', *tag); guards[s_] = tag
            for c_ in clauses: add([-s_] + c_)
        for i in range(NO):
            guard(('OL', i), [[-U(i, z), -fle(m, z, m)] for z in range(n) if le[m][z] and z != m])
            guard(('OU', i), [[-U(i, z), -yle(m, z)] for z in range(n) if le[m][z] and z != m])
        guard(('TR',), [[-r(2, top)]])
        for x in range(n): guard(('TA', x), [[-r(2, x), -A(x, top)]])
        for g in range(n): guard(('TB', g), [[-B(top, g), -r(2, g)]])
        for z in range(n):
            if h[z] > 2: guard(('T2', z), [[-r(2, z)]])
        for y in range(n):
            if h[y] != 2 or le[m][y]: continue
            cl = []
            for c in L.covers_dn[y]:
                if h[c] == 1: cl += [[-f(bot, y, c), -fle(c, y, y)], [-f(bot, y, c), -yle(c, y)]]
            if cl: guard(('X', y), cl)
        if not E.S.solve(): C['inconsistent'] += 1; E.S.delete(); continue
        if E.S.solve(assumptions=list(guards)): C['MinH2Orbit fails'] += 1; E.S.delete(); continue
        core = E.S.get_core() or list(guards); i = 0
        while i < len(core):
            t = core[:i] + core[i + 1:]
            if not E.S.solve(assumptions=t): core = t
            else: i += 1
        tags = sorted(guards[s_] for s_ in core)
        C['cores'] += 1
        if not any(t[0] == 'X' for t in tags): C['degenerate'] += 1; E.S.delete(); continue
        idx = tuple(sorted({t[1] for t in tags if t[0] in ('OL', 'OU')}))
        C[('orbit indices', idx)] += 1
        C[('halves', tuple(sorted(t[0] + str(t[1]) for t in tags if t[0] in ('OL', 'OU'))))] += 1
        C[('uses T2', any(t[0] == 'T2' for t in tags))] += 1
        if shown < LIM: shown += 1; print(f'|L|={n} h={L.height} m={nm(m)}:', ' '.join(t[0] + ''.join(nm(a) if isinstance(a, int) and t[0] not in ('OL', 'OU') else str(a) for a in t[1:]) for t in tags), flush=True)
        E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:40]: print(k_, v_)
