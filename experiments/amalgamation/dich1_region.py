"""Dichotomy(1) as a statement about one monotone map (log §34.3z²²⁶).  rank(m) = 2.

G(y) = F(F(⊥, y), y);  Y₁ = {y : m ≰ y, F(⊥, y) an atom < y}.  Under the Dichotomy(1) hypotheses (dich_net.py, with
nopostlayer) a certificate is exactly a G-comparable point of Y₁ (the fibre collapses to a point under R₁ tightness).
Claims (violation searched, re-checked in Python):
  region — some y ∈ Y₁ is G-comparable (= Dichotomy(1) under nopostlayer)
  maxall — every maximal element of Y₁ is G-comparable
  maxex  — some maximal element of Y₁ is G-comparable
  minall / minex — the same for minimal elements of Y₁
  minh2  — some height-2 element of Y₁ (a cover of its atom F(⊥, y)) is G-comparable, i.e. not a gap
  python3 dich1_region.py CLAIM (sweep N MAX | closure K M SEED CNT) [nonpl] [nofeed notop not1 not2 icok]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
CLAIM = sys.argv[1]; NONPL = 'nonpl' in sys.argv; ABL = {a for a in sys.argv if a in ('nofeed', 'notop', 'not1', 'not2', 'icok')}
args = [a for a in sys.argv[2:] if a != 'nonpl' and a not in ABL]
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0)
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        feeders = [p for p in L.covers_dn[m] if h[p] == 1]
        if not feeders: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        add([r(2, m)]); add([-r(1, m)])
        if 'icok' not in ABL: add([-ic(m)])
        if 'notop' not in ABL: add([-r(3, L.top)])
        low = []
        for p in feeders: o = E.v('low', p); E.iff_and(o, [r(1, p), fle(p, m, p)]); low.append(o)
        if 'nofeed' not in ABL: add(low)
        for z in range(n):
            if h[z] > 2 and 'not2' not in ABL: add([-r(2, z)])
            if h[z] > 1 and 'not1' not in ABL: add([-r(1, z)])
            if h[z] == 1 and not NONPL: add([-r(1, z), -yle(z, z)])   # 'nonpl': drop nopostlayer
        atoms = [c for c in range(n) if h[c] == 1]
        inY, comp = {}, {}
        for y in range(n):
            if le[m][y]: continue
            cs = [c for c in atoms if le[c][y] and c != y]
            if not cs: continue
            o = E.v('inY', y); E.iff_or(o, [f(bot, y, c) for c in cs]); inY[y] = o
            lits = []
            for c in cs:
                for t in (fle(c, y, y), yle(c, y)): q = E.v('cmp', y, c, t); E.iff_and(q, [f(bot, y, c), t]); lits.append(q)
            o = E.v('comp', y); E.iff_or(o, lits); comp[y] = o
        ext = {}
        for y in inY:
            others = [y2 for y2 in inY if y2 != y and (le[y][y2] if CLAIM.startswith('max') else le[y2][y])]
            o = E.v('ext', y); E.iff_and(o, [inY[y]] + [-inY[y2] for y2 in others]); ext[y] = o
        if CLAIM == 'region': add([E.v('true')]); [add([-inY[y], -comp[y]]) for y in inY]
        elif CLAIM in ('maxall', 'minall'): add([E.v('sel', y) for y in inY]); [add([-E.v('sel', y), ext[y]]) or add([-E.v('sel', y), -comp[y]]) for y in inY]
        elif CLAIM in ('maxex', 'minex'): [add([-ext[y], -comp[y]]) for y in inY]
        elif CLAIM == 'minh2': [add([-inY[y], -comp[y]]) for y in inY if h[y] == 2]      # some height-2 point of Y₁ is comparable
        if E.S.solve():
            F = E.decode(); G = lambda y: F[F[bot][y]][y]
            Y = [y for y in range(n) if not le[m][y] and h[F[bot][y]] == 1 and le[F[bot][y]][y] and F[bot][y] != y]
            cp = lambda y: le[G(y)][y] or le[y][G(y)]
            mx = [y for y in Y if not any(y2 != y and (le[y][y2] if CLAIM.startswith('max') else le[y2][y]) for y2 in Y)]
            ok = {'minh2': not any(cp(y) for y in Y if h[y] == 2), 'region': not any(cp(y) for y in Y), 'maxall': any(not cp(y) for y in mx), 'minall': any(not cp(y) for y in mx),
                  'maxex': not any(cp(y) for y in mx), 'minex': not any(cp(y) for y in mx)}[CLAIM]
            assert ok, 'SAT/Python mismatch'
            C['violated'] += 1
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m))
        else: C['holds'] += 1
        E.S.delete()
print(CLAIM, 'nonpl' if NONPL else '', sorted(ABL), dict(C), 'smallest violation', best[0] if best else None)
if best: json.dump(best[1], open(f'dich1_{CLAIM}{"_nonpl" if NONPL else ""}{"".join("_" + a for a in sorted(ABL))}_min{best[0]}.json', 'w'))
