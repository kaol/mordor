"""§34.3z²⁶⁸: AbstractRowDrop, a statement about two monotone maps psi <= phi on a finite lattice (psi = F(bot, .),
phi = F(d, .)). Exact SAT over all pairs (psi, phi) per lattice; every SAT model is replayed in Python.

  u = psi(top), d = psi(u), psi(d) = bot, u != d, h(d) = 2 (flag anyd: any d != bot),
  phi(u) not <= d (flag xbd drops it), u not <= gfp(phi) (flag xad drops it),
  flag zt: Z = psi^-1(bot) has heights <= 2;
  negated claim: psi(phi(top)) not <= d.
SAT = AbstractRowDrop fails.  UNSAT = it holds on that lattice.
  python3 abs_rowdrop.py (sweep N MAX | closure K M SEED CNT) [anyd] [xbd] [xad] [zt]"""
import sys, collections, itertools
sys.path.insert(0, '../separation')
from pysat.solvers import Cadical153
from tight_probe import lattices
FLG = {'anyd', 'xbd', 'xad', 'zt'}
FL = {a for a in sys.argv[1:] if a in FLG}; args = [a for a in sys.argv[1:] if a not in FLG]
print('abs_rowdrop | SAT = AbstractRowDrop fails | flags', sorted(FL))
C = collections.Counter(); H = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; bot = L.bot
    if L.height < 3: continue
    V = {}; S = Cadical153()
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    def onehot(name, dom):
        ls = [v(name, x) for x in dom]; S.add_clause(ls)
        for p, q in itertools.combinations(ls, 2): S.add_clause([-p, -q])
        return lambda x: v(name, x)
    m = {r: [onehot((r, y), list(range(n))) for y in range(n)] for r in ('p', 'f')}   # m[r][y](w): map r sends y to w
    for r in ('p', 'f'):
        for y in range(n):
            for y2 in L.covers_up[y]:
                for w in range(n): S.add_clause([-m[r][y](w)] + [m[r][y2](w2) for w2 in range(n) if le[w][w2]])
    for y in range(n):                                   # psi <= phi pointwise
        for w in range(n): S.add_clause([-m['p'][y](w)] + [m['f'][y](w2) for w2 in range(n) if le[w][w2]])
    G = onehot('G', list(range(n)))                       # G = gfp phi
    for g in range(n):
        S.add_clause([-G(g), m['f'][g](g)])
        for y in range(n):
            if le[y][g]: continue
            for w in range(n):
                if le[y][w]: S.add_clause([-G(g), -m['f'][y](w)])
    if 'zt' in FL:                                       # Z = psi^-1(bot) has heights <= 2
        for x in range(n):
            if h[x] > 2: S.add_clause([-m['p'][x](bot)])
    dom = [x for x in range(n) if (x != bot if 'anyd' in FL else h[x] == 2)]
    U = onehot('U', list(range(n))); D = onehot('D', dom)
    for x in range(n):
        if x not in dom: S.add_clause([-D(x)])
    for u in range(n):
        S.add_clause([-U(u), m['p'][top](u)])
        for d in dom:
            S.add_clause([-U(u), -D(d), m['p'][u](d)])
            if u == d: S.add_clause([-U(u), -D(d)])
            if 'xbd' not in FL: S.add_clause([-U(u), -D(d)] + [m['f'][u](w) for w in range(n) if not le[w][d]])
            if 'xad' not in FL:
                for g in range(n):
                    if le[u][g]: S.add_clause([-U(u), -G(g)])
    for d in dom:
        S.add_clause([-D(d), m['p'][d](bot)])
        for t in range(n):                               # phi(top) = t  =>  psi(t) not <= d
            S.add_clause([-D(d), -m['f'][top](t)] + [m['p'][t](w) for w in range(n) if not le[w][d]])
    if S.solve():
        M = set(x for x in S.get_model() if x > 0)
        P = [next(w for w in range(n) if m['p'][y](w) in M) for y in range(n)]
        Ph = [next(w for w in range(n) if m['f'][y](w) in M) for y in range(n)]
        mono = all(le[P[y]][P[y2]] and le[Ph[y]][Ph[y2]] for y in range(n) for y2 in range(n) if le[y][y2]) and all(le[P[y]][Ph[y]] for y in range(n))
        g = top
        while Ph[g] != g: g = Ph[g]                       # descent from top reaches gfp
        u = P[top]; d = P[u]
        ok = mono and P[d] == bot and u != d and d != bot and (h[d] == 2 or 'anyd' in FL) and not le[P[Ph[top]]][d]
        ok = ok and ('xbd' in FL or not le[Ph[u]][d]) and ('xad' in FL or not le[u][g])
        if 'zt' in FL: ok = ok and all(h[x] <= 2 for x in range(n) if P[x] == bot)
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1; H[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, psi=P, phi=Ph))
    else: C['UNSAT'] += 1; H[f'h{L.height}:unsat'] += 1
    S.delete()
print(sorted(FL), args, dict(C), dict(H), 'smallest SAT', best[0] if best else None)
if best:
    import json; json.dump(best[1], open(f'abs_rowdrop{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
