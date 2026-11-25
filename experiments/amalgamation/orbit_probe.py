"""§34.3z²⁷⁹ (worker): StrictDep and OneExit on the mu-orbit of bot, a second encoding independent of muorbit_sat.py.
World through (T), no R-stages in the encoding: rows F(x, .) only for low x (height <= 2), one-hot, monotone in y (covers)
and in x (covers inside the low set); a(bot) = bot (no y != bot with y <= F(bot, y)); Z = {y : F(bot, y) = bot} has no
element of height >= 3 (ZT); (T) at every row x of Z: no column y of height >= 3 has F(x, y) <= x or y <= F(x, y);
n1: some height-2 element lies in Z; h(top) >= 3.  Rows of high x are the constant top in the replay.
Every SAT model is completed and replayed with rstages.stages (W0 + n1 checked from the definitions) and the claim is
re-evaluated in Python.
Exact descents it(x, j, .) (one-hot per index); landing lambda(x) = first element of height <= 2; mu(x) = lambda(x) if
lambda(x) in Z, else F(bot, lambda(x)); orbit x_k = mu^k(bot); dep(x) = max j with x <= t_j, t = the bot-descent.
Modes:
  strictdep  SAT = some x_k (1 <= k < K) has a successor y = x_(k+1) != x_k that is not a fixed point and dep(y) >= dep(x_k)
  oneexit    SAT = some x_k (1 <= k < K) exits to an atom y that is not a fixed point of mu
  vac        SAT = the world has a model
Flag mT (mutant world): (T) kept only at the row bot (Tb/Ta dropped at the other rows of Z).
  python3 orbit_probe.py MODE K (sweep N MAX | closure K M SEED CNT | tall K M SEED CNT) [mT]"""
import sys, itertools, collections, json
sys.path.insert(0, '../separation'); sys.path.insert(0, '.')
from pysat.solvers import Cadical153
from tight_probe import lattices
from rstages import stages, a_of
MODE = sys.argv[1]; K = int(sys.argv[2]); MT = 'mT' in sys.argv[3:]; args = [a for a in sys.argv[3:] if a != 'mT']
SAT_MEANS = {'strictdep': 'some non-fixed successor on the bot-orbit has dep >= dep of its predecessor',
             'oneexit': 'some element of the bot-orbit exits to an atom that is not a fixed point', 'vac': 'the world has a model'}[MODE]
print(f'orbit_probe {MODE} K={K} | SAT = {SAT_MEANS} | world (T) {"MUTANT mT" if MT else ""} | corpus {args}')
C = collections.Counter(); HH = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top
    if h[top] < 3: continue
    low = [x for x in range(n) if h[x] <= 2]; NO = h[top] + 1
    S = Cadical153(); V = {}
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    add = S.add_clause; f = lambda x, y, u: v('f', x, y, u); Z = lambda y: f(bot, y, bot)
    for x in low:
        for y in range(n):
            ls = [f(x, y, u) for u in range(n)]; add(ls)
            for a_, b_ in itertools.combinations(ls, 2): add([-a_, -b_])
        for y in range(n):
            for y2 in L.covers_up[y]:
                for u in range(n): add([-f(x, y, u)] + [f(x, y2, u2) for u2 in range(n) if le[u][u2]])
        for x2 in L.covers_up[x]:
            if h[x2] > 2: continue
            for y in range(n):
                for u in range(n): add([-f(x, y, u)] + [f(x2, y, u2) for u2 in range(n) if le[u][u2]])
    for y in range(n):                                        # a(bot) = bot
        if y == bot: continue
        for u in range(n):
            if le[y][u]: add([-f(bot, y, u)])
    for y in range(n):
        if h[y] > 2: add([-Z(y)])                             # ZT
    add([Z(y) for y in range(n) if h[y] == 2])                # n1
    for x in low:                                             # (T) at rows of Z
        if MT and x != bot: continue
        for y in range(n):
            if h[y] <= 2: continue
            for u in range(n):
                if le[u][x] or le[y][u]: add([-Z(x), -f(x, y, u)])
    it = lambda x, j, z: v('it', x, j, z)
    for x in low:
        for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
        for j in range(NO):
            for z in range(n):
                for u in range(n): add([-it(x, j, z), -f(x, z, u), it(x, j + 1, u)])
            for z, z2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, z), -it(x, j + 1, z2)])
    lam = {}
    for x in low:
        for p in low:
            o = v('lam', x, p); ls = []
            for j in range(NO + 1):
                t = v('lamj', x, p, j); ls.append(t); add([-t, it(x, j, p)])
                for j2 in range(j):
                    for z in low: add([-t, -it(x, j2, z)])
                add([-it(x, j, p), t] + [it(x, j2, z) for j2 in range(j) for z in low])
            add([-o] + ls)
            for t in ls: add([-t, o])
            lam[x, p] = o
    mu = {}
    for x in low:
        for y in low:
            ls = []
            t = v('mi', x, y); ls.append(t); add([-t, lam[x, y]]); add([-t, Z(y)]); add([t, -lam[x, y], -Z(y)])
            for p in low:
                t = v('me', x, p, y); ls.append(t)
                for lit in (lam[x, p], -Z(p), f(bot, p, y)): add([-t, lit])
                add([t, -lam[x, p], Z(p), -f(bot, p, y)])
            o = v('mu', x, y); mu[x, y] = o
            for t in ls: add([-t, o])
            add([-o] + ls)
    ob = lambda k, x: v('ob', k, x)
    for x in range(n): add([ob(0, x)] if x == bot else [-ob(0, x)])
    for k in range(K):
        for x in low:
            for y in low: add([-ob(k, x), -mu[x, y], ob(k + 1, y)])
            add([-ob(k, x)] + [mu[x, y] for y in low])
        for x in range(n):
            if x not in low: add([-ob(k + 1, x)])
        for y, y2 in itertools.combinations(range(n), 2): add([-ob(k + 1, y), -ob(k + 1, y2)])
    dge = {}
    for x in range(n):
        for j in range(NO + 1):
            o = v('dge', x, j); dge[x, j] = o; ls = [it(bot, j, t) for t in range(n) if le[x][t]]
            for l in ls: add([-l, o])
            add([-o] + ls)
    sel = []
    if MODE == 'strictdep':
        for k in range(1, K):
            for x in low:
                if x == bot: continue
                for y in low:
                    if y == x: continue
                    t = v('sd', k, x, y); sel.append(t)
                    for lit in (ob(k, x), ob(k + 1, y), -mu[y, y]): add([-t, lit])
                    for j in range(NO + 1): add([-t, -dge[x, j], dge[y, j]])
    elif MODE == 'oneexit':
        for k in range(1, K):
            for x in low:
                if x == bot: continue
                for p in low:
                    for y in low:
                        t = v('ox', k, x, p, y); sel.append(t)
                        for lit in (ob(k, x), lam[x, p], -Z(p), f(bot, p, y), -mu[y, y]): add([-t, lit])
    if MODE != 'vac': add(sel)
    if S.solve():
        m = set(l for l in S.get_model() if l > 0)
        F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else top) for y in range(n)] for x in range(n)]
        st = stages(L, F); inR = lambda z, i: st[z] is not None and st[z] <= i
        ok = (a_of(L, F, bot) == bot and all(h[z] <= 2 for z in range(n) if inR(z, 2)) and not inR(top, 2)
              and any(h[z] > 1 for z in range(n) if inR(z, 1)))
        if MT: ok = a_of(L, F, bot) == bot                     # mutant world: only the bot facts are guaranteed
        def desc(x):
            z = top; s = []
            while z not in s: s.append(z); z = F[x][z]
            return s
        def lamf(x): return next((z for z in desc(x) if h[z] <= 2), None)
        def muf(x):
            p = lamf(x)
            return None if p is None else (p if F[bot][p] == bot else F[bot][p])
        tb = desc(bot); dep = lambda z: max(j for j, t in enumerate(tb) if le[z][t])
        xs = [bot]
        for _ in range(K): xs.append(None if xs[-1] is None else muf(xs[-1]))
        bad = MODE == 'vac'
        for k in range(1, K):
            x, y = xs[k], xs[k + 1]
            if x is None or y is None: continue
            if MODE == 'strictdep' and y != x and muf(y) != y and dep(y) >= dep(x): bad = True
            if MODE == 'oneexit':
                p = lamf(x)
                if p is not None and F[bot][p] != bot and muf(F[bot][p]) != F[bot][p]: bad = True
        assert ok and bad, 'SAT/Python mismatch'
        C['SAT'] += 1; HH[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1; HH[f'h{L.height}:unsat'] += 1
    S.delete()
print(MODE, K, 'mT' if MT else '', args, dict(C), dict(HH), 'smallest', best[0] if best else None)
if best and MODE != 'vac': json.dump(best[1], open(f'orbit_probe_{MODE}{"_mT" if MT else ""}_min{best[0]}.json', 'w'))
