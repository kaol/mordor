"""Minimal cores of DescPre2 with R_2 tightness split into b-route instances BT(g) and the single a-route instance AS
[h(a(c*)) ≤ 2] (log §34.3z²³⁶; derived from descpre_core.py), rank(m) = 2.  Hard: F monotone, m ∈ R_2 \\ R_1, m's column orbit, the ⊥-descent
D(i, ·) from w = F(m, y*).  Guards: WL, WU [w ∥ m], T1(z), T2(z) [R_1, R_2 tightness per element], P(c, v) [if c is the
descent atom and F(⊥, v) = c < v, m ≰ v, then F(c, v) ≰ v].
  python3 descpre_core.py (sweep N MAX | closure K M SEED CNT) [limit=K]
"""
import sys, collections
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
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
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
        D = lambda i, z: E.v('D', i, z)
        for z in range(n):
            lits = []
            for yv in range(n): o = E.v('D0', yv, z); E.iff_and(o, [U(NO - 1, yv), f(m, yv, z)]); lits.append(o)
            E.iff_or(D(0, z), lits)
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('Ds', i, v, z); E.iff_and(o, [D(i, v), f(bot, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        At = {}
        for c in range(n):
            if h[c] == 1: At[c] = E.v('datom', c); E.iff_or(At[c], [D(i, c) for i in range(NO + 1)])
        guards = {}
        def guard(tag, clauses):
            s_ = E.v('g', *tag); guards[s_] = tag
            for c_ in clauses: add([-s_] + c_)
        guard(('WL',), [[-U(NO - 1, z), -f(m, z, g)] for z in range(n) for g in range(n) if le[g][m]])
        guard(('WU',), [[-U(NO - 1, z), -f(m, z, g)] for z in range(n) for g in range(n) if le[m][g]])
        A_ = lambda x, g: E.v('A', x, g); B_ = lambda y, g: E.v('B', y, g)
        for z in range(n):
            if h[z] > 1: guard(('T1', z), [[-r(1, z)]])
            if h[z] > 2: guard(('BT', z), [[-B_(z, x), -r(1, x)] for x in range(n)])
        guard(('AS',), [[-At[c], -A_(c, g)] for c in At for g in range(n) if h[g] > 2])
        for c in At:
            for v in range(n):
                if le[c][v] and v != c and not le[m][v] and h[v] == 2: guard(('P', c, v), [[-At[c], -f(bot, v, c), -fle(c, v, v)]])
        if not E.S.solve(): C['inconsistent'] += 1; E.S.delete(); continue
        if E.S.solve(assumptions=list(guards)): C['DescPre fails'] += 1; E.S.delete(); continue
        core = E.S.get_core() or list(guards); i = 0
        while i < len(core):
            t = core[:i] + core[i + 1:]
            if not E.S.solve(assumptions=t): core = t
            else: i += 1
        tags = sorted(guards[s_] for s_ in core)
        C['cores'] += 1
        P = [t for t in tags if t[0] == 'P']
        if not P: C['degenerate'] += 1; E.S.delete(); continue
        C[('#P', len(P), '#atoms in P', len({t[1] for t in P}))] += 1
        C[('P columns heights', tuple(sorted(h[t[2]] for t in P)))] += 1
        Pv = {t[2] for t in P}; Pc = {t[1] for t in P}
        for t in tags:
            if t[0] == 'BT':
                g = t[1]
                C[('BT column', 'g = m ∨ v (v ∈ P)' if any(jn[m][v] == g for v in Pv) else ('g = v ∨ v′ (P covers)' if any(jn[v][v2] == g for v in Pv for v2 in Pv if v != v2) else ('g ≥ m' if le[m][g] else 'other')), 'h', h[g])] += 1
        C[('uses AS', any(t[0] == 'AS' for t in tags))] += 1
        C[('P column = c ∨ another atom', tuple(sorted(sum(1 for a in range(n) if h[a] == 1 and a != t[1] and jn[t[1]][a] == t[2]) > 0 for t in P)))] += 1
        C[('shape', tuple(sorted(collections.Counter(t[0] for t in tags).items())))] += 1
        if shown < LIM: shown += 1; print(f'|L|={n} m={nm(m)}:', ' '.join(t[0] + ''.join(nm(a) for a in t[1:]) for t in tags), flush=True)
        E.S.delete()
print(dict((k, v) for k, v in C.items() if isinstance(k, str)))
for k_, v_ in sorted(((k, v) for k, v in C.items() if not isinstance(k, str)), key=lambda kv: -kv[1])[:30]: print(k_, v_)
