"""Minimal cores of TopFibreNew(1) (log §34.3z²²⁴) over guarded hypothesis families, rank(m) = 3 (k = 2).

Hard: F monotone (Enc, stages R_0..R_4), m ∈ R_3 \\ R_2.  Guarded hypothesis instances:
  NOIC [¬IC(m)], TOP [⊤ ∉ R_4], FEED [some lower feeder p ⋖ m, p ∈ R_2, F(p, m) ≤ p], T3(z) [z ∉ R_3, h(z) > 3],
  T2(z) [z ∉ R_2, h(z) > 2], NPL(x) [h(x) = 2, x ∈ R_2 ⟹ x ≰ F(x, x)],
  CFG(p, c) [the configuration (p, c) — p an atom of R_1, c ∈ R_2 \\ R_1 of height 2, F(p, c) = p — has no fibre column
  v ≱ m, F(p, v) = c, with a comparable y ∈ (c, v]].
If all guards together are UNSAT (TopFibreNew(1) holds on (L, m)), print a deletion-minimal core.
  python3 ag2f_core.py (sweep N MAX | closure K M SEED CNT) [limit=K]
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
LIM = next((int(a[6:]) for a in sys.argv if a.startswith('limit=')), 10)
args = [a for a in sys.argv[1:] if not a.startswith('limit=')]
C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; jn = L.join; h = L.rank; bot = h.index(0)
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m in range(n):
        if h[m] != 3 or L.height <= 3: continue
        feeders = [p for p in L.covers_dn[m] if h[p] == 2]
        if not feeders: continue
        E = Enc(L, 4); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z)
        E.S.add_clause([r(3, m)]); E.S.add_clause([-r(2, m)])
        guards = {}
        def guard(tag, clauses):
            s_ = E.v('g', *tag); guards[s_] = tag
            for c in clauses: E.S.add_clause([-s_] + c)
        guard(('NOIC',), [[-ic(m)]]); guard(('TOP',), [[-r(4, L.top)]])
        low = []
        for p in feeders: o = E.v('low', p); E.iff_and(o, [r(2, p), fle(p, m, p)]); low.append(o)
        guard(('FEED',), [low])
        for z in range(n):
            if h[z] > 3: guard(('T3', z), [[-r(3, z)]])
            if h[z] > 2: guard(('T2', z), [[-r(2, z)]])
            if h[z] == 2: guard(('NPL', z), [[-r(2, z), -yle(z, z)]])
        for p in range(n):
            if h[p] != 1: continue
            for c in range(n):
                if h[c] != 2 or not le[p][c]: continue
                cl = []
                for v in range(n):
                    if not (le[c][v] and v != c and not le[m][v]): continue
                    for y in range(n):
                        if le[c][y] and y != c and le[y][v]:
                            base = [-r(1, p), -r(2, c), r(1, c), -f(p, c, p), -f(p, v, c)]
                            cl += [base + [-fle(c, y, y)], base + [-yle(c, y)]]
                if cl: guard(('CFG', p, c), cl)
        if E.S.solve(assumptions=list(guards)): C['TopFibreNew(1) fails'] += 1; E.S.delete(); continue
        core = E.S.get_core() or list(guards); i = 0
        while i < len(core):
            t = core[:i] + core[i + 1:]
            if not E.S.solve(assumptions=t): core = t
            else: i += 1
        tags = sorted(guards[s_] for s_ in core)
        shape = tuple(sorted(collections.Counter(t[0] for t in tags).items()))
        C[('shape', shape)] += 1
        C[('#CFG in core', sum(t[0] == 'CFG' for t in tags))] += 1
        ncfg = sum(t[0] == 'CFG' for t in guards.values())
        if any(t[0] == 'CFG' for t in tags): C[('CFG in core / all CFG', 'all' if sum(t[0] == 'CFG' for t in tags) == ncfg else 'some')] += 1
        cs = {t[2] for t in tags if t[0] == 'CFG'}; ns = {t[1] for t in tags if t[0] == 'NPL'}
        if cs or ns: C[('NPL set = CFG tops', ns == cs, 'NPL ⊆ CFG tops', ns <= cs)] += 1
        for t in tags:
            if t[0] == 'CFG': C[('CFG', 'p≤m', le[t[1]][m], 'c≤m', le[t[2]][m])] += 1
        if shown < LIM:
            shown += 1; print(f'|L|={n} m={nm(m)}:', ' '.join(t[0] + ''.join(nm(a) for a in t[1:]) for t in tags), flush=True)
        E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:40]: print(k_, v_)
