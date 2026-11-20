"""Minimal cores of MinH2 (log §34.3z²²⁶), rank(m) = 2: some height-2 y ≱ m with c = F(⊥, y) an atom < y has
F(c, y) comparable with y.  Guards: NOIC, TOP, FEED, T2(z) [h(z) > 2 ⟹ z ∉ R_2], T1(z) [h(z) > 1 ⟹ z ∉ R_1],
NPL(c) [atom c ∈ R_1 ⟹ c ≰ F(c, c)], X(y) [y is not a comparable height-2 point].
  python3 dich1_core.py (sweep N MAX | closure K M SEED CNT) [limit=K] [out=FILE]
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
    n = L.n; le = L.le; h = L.rank; bot = h.index(0)
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        feeders = [p for p in L.covers_dn[m] if h[p] == 1]
        if not feeders: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z)
        E.S.add_clause([r(2, m)]); E.S.add_clause([-r(1, m)])
        guards = {}
        def guard(tag, clauses):
            s_ = E.v('g', *tag); guards[s_] = tag
            for c_ in clauses: E.S.add_clause([-s_] + c_)
        guard(('NOIC',), [[-ic(m)]]); guard(('TOP',), [[-r(3, L.top)]])
        low = []
        for p in feeders: o = E.v('low', p); E.iff_and(o, [r(1, p), fle(p, m, p)]); low.append(o)
        guard(('FEED',), [low])
        for z in range(n):
            if h[z] > 2: guard(('T2', z), [[-r(2, z)]])
            if h[z] > 1: guard(('T1', z), [[-r(1, z)]])
            if h[z] == 1: guard(('NPL', z), [[-r(1, z), -yle(z, z)]])
        for y in range(n):
            if h[y] != 2 or le[m][y]: continue
            cl = []
            for c in L.covers_dn[y]:
                if h[c] == 1: cl += [[-f(bot, y, c), -fle(c, y, y)], [-f(bot, y, c), -yle(c, y)]]
            if cl: guard(('X', y), cl)
        if not E.S.solve(): C['inconsistent'] += 1; E.S.delete(); continue
        if E.S.solve(assumptions=list(guards)): C['MinH2 fails'] += 1; E.S.delete(); continue
        core = E.S.get_core() or list(guards); i = 0
        while i < len(core):
            t = core[:i] + core[i + 1:]
            if not E.S.solve(assumptions=t): core = t
            else: i += 1
        tags = sorted(guards[s_] for s_ in core)
        C['cores'] += 1
        if not any(t[0] == 'X' for t in tags): C['degenerate (no X)'] += 1; E.S.delete(); continue
        C[('shape', tuple(sorted(collections.Counter(t[0] for t in tags).items())))] += 1
        allX = [t for t in guards.values() if t[0] == 'X']
        C[('X in core', 'all' if sum(t[0] == 'X' for t in tags) == len(allX) else 'some')] += 1
        C[('T2 instances', tuple(sorted(h[t[1]] for t in tags if t[0] == 'T2')))] += 1
        C[('T1 instances heights', tuple(sorted(h[t[1]] for t in tags if t[0] == 'T1')))] += 1
        if outf: outf.write(json.dumps(dict(sets=L.S, m=m, core=tags)) + '\n')
        if shown < LIM: shown += 1; print(f'|L|={n} m={nm(m)}:', ' '.join(t[0] + ''.join(nm(a) for a in t[1:]) for t in tags), flush=True)
        E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:45]: print(k_, v_)
