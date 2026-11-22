"""§34.3z²⁶⁸: Cert1 (the hypothesis of `goodAtom1_of_cert1`), exact, independent of dlatoms.py.
World W0 at level 1: a(bot) = bot, R_2 tight, top not in R_2, R_1 not tight (n1).
SAT = Cert1 fails: for every x in Z = {F(bot, x) = bot}, every atom q <= x and every height-2 element z of row x's
descent from top, q is not <= F(bot, z).
Row descents are encoded as closed sets on(x, .): top is on, and on(x, z) with F(x, z) = w puts w on. Extra elements only
add constraints, so SAT models witness a real failure; each is replayed in Python.
  python3 cert1_sat.py (sweep N MAX | closure K M SEED CNT) [xZ] [not2]   xZ: x ranges over atoms' rows only (x = q; CertAtom); not2 (mutant): R_2 tightness dropped"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
FL = {a for a in sys.argv[1:] if a in ('xZ', 'not2')}; args = [a for a in sys.argv[1:] if a not in FL]
print('cert1_sat | SAT = Cert1 fails in W0 with R_1 non-tight | flags', sorted(FL))
C = collections.Counter(); HH = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; bot = L.bot
    if L.height < 3: continue
    E = Enc(L, 2); f = lambda a, b, u: E.v('f', a, b, u); r = lambda i, z: E.v('r', i, z); add = E.S.add_clause
    add([E.v('A', bot, bot)]); add([-r(2, top)])
    if 'not2' not in FL:
        for z in range(n):
            if h[z] > 2: add([-r(2, z)])
    add([r(1, z) for z in range(n) if h[z] > 1])
    rows = [x for x in range(n) if (h[x] <= 2 or 'not2' in FL) and x != bot and (h[x] == 1 or 'xZ' not in FL)]
    for x in rows:
        on = lambda z: E.v('on', x, z)
        add([on(top)])
        for z in range(n):
            for w in range(n): add([-on(z), -f(x, z, w), on(w)])
        for z in range(n):
            if h[z] != 2: continue
            for q in range(n):
                if h[q] != 1 or not le[q][x]: continue
                for w in range(n):
                    if le[q][w]: add([-f(bot, x, bot), -on(z), -f(bot, z, w)])
    if E.S.solve():
        F = E.decode(); st = stages(L, F); inR = lambda x, i: st[x] is not None and st[x] <= i
        def desc(p):
            v = top; s = []
            while v not in s: s.append(v); v = F[p][v]
            return s
        ok = a_of(L, F, bot) == bot and not inR(top, 2) and ('not2' in FL or all(h[z] <= 2 for z in range(n) if inR(z, 2))) and any(h[z] > 1 for z in range(n) if inR(z, 1))
        ok = ok and not any(F[bot][x] == bot and le[q][x] and h[q] == 1 and h[z] == 2 and le[q][F[bot][z]]
                            for x in rows for z in desc(x) for q in range(n))
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1; HH[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1; HH[f'h{L.height}:unsat'] += 1
    E.S.delete()
print(sorted(FL), args, dict(C), dict(HH), 'smallest', best[0] if best else None)
if best:
    import json; json.dump(best[1], open(f'cert1_sat{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
