"""Minimal cores of MinH2 under H₀ only (log §34.3z²²⁷), rank(m) = 2.  Hard: F monotone, m ∈ R_2 \\ R_1.  Guards:
  NL(z), NU(z) for z > m  [¬IC(m) split: F(m, z) ≰ m;  z ≰ F(m, z)];
  TR [⊤ ∉ R_2], TA(x) [¬(x ∈ R_2 ∧ a(x) = ⊤)], TB(g) [¬(b(⊤) = g ∧ g ∈ R_2)]   (⊤ ∉ R_3 split by generation route);
  X(y) for each candidate height-2 y ≱ m  [y is not a G-comparable point].
  python3 dich1_h0core.py (sweep N MAX | closure K M SEED CNT) [limit=K] [out=FILE]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
LIM = next((int(a[6:]) for a in sys.argv if a.startswith('limit=')), 10)
OUT = next((a[4:] for a in sys.argv if a.startswith('out=')), None)
args = [a for a in sys.argv[1:] if not a.startswith(('limit=', 'out='))]
C = collections.Counter(); shown = 0; outf = open(OUT, 'w') if OUT else None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z)
        A = lambda x, g: E.v('A', x, g); B = lambda y, g: E.v('B', y, g)
        E.S.add_clause([r(2, m)]); E.S.add_clause([-r(1, m)])
        guards = {}
        def guard(tag, clauses):
            s_ = E.v('g', *tag); guards[s_] = tag
            for c_ in clauses: E.S.add_clause([-s_] + c_)
        for z in range(n):
            if le[m][z] and z != m: guard(('NL', z), [[-fle(m, z, m)]]); guard(('NU', z), [[-yle(m, z)]])
        guard(('TR',), [[-r(2, top)]])
        for x in range(n): guard(('TA', x), [[-r(2, x), -A(x, top)]])
        for g in range(n): guard(('TB', g), [[-B(top, g), -r(2, g)]])
        for y in range(n):
            if h[y] != 2 or le[m][y]: continue
            cl = []
            for c in L.covers_dn[y]:
                if h[c] == 1: cl += [[-f(bot, y, c), -fle(c, y, y)], [-f(bot, y, c), -yle(c, y)]]
            if cl: guard(('X', y), cl)
        if not E.S.solve(): C['inconsistent'] += 1; E.S.delete(); continue
        if E.S.solve(assumptions=list(guards)): C['MinH2 fails under H0'] += 1; E.S.delete(); continue
        core = E.S.get_core() or list(guards); i = 0
        while i < len(core):
            t = core[:i] + core[i + 1:]
            if not E.S.solve(assumptions=t): core = t
            else: i += 1
        tags = sorted(guards[s_] for s_ in core)
        C['cores'] += 1
        if not any(t[0] == 'X' for t in tags): C['degenerate (no X)'] += 1; E.S.delete(); continue
        C[('shape', tuple(sorted(collections.Counter(t[0] for t in tags).items())))] += 1
        Xs = {t[1] for t in tags if t[0] == 'X'}
        for t in tags:
            if t[0] in ('NL', 'NU'):
                z = t[1]; C[(t[0], 'z = ⊤' if z == top else ('z = m ∨ y, y ∈ X' if any(L.join[m][y] == z for y in Xs) else 'other'), 'h(z)', h[z])] += 1
            if t[0] in ('TA', 'TB'):
                x = t[1]; C[(t[0], 'x = ⊥' if x == bot else ('x = m' if x == m else ('x ∈ X' if x in Xs else ('x ≤ m' if le[x][m] else 'other'))), 'h(x)', h[x])] += 1
        if outf: outf.write(json.dumps(dict(sets=L.S, m=m, core=tags)) + '\n')
        if shown < LIM: shown += 1; print(f'|L|={n} m={nm(m)}:', ' '.join(t[0] + ''.join(nm(a) for a in t[1:]) for t in tags), flush=True)
        E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:50]: print(k_, v_)
