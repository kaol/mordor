"""§34.3z²⁷⁴: AbstractDomCoLand, a statement about three monotone maps beta <= psi <= phi on a finite lattice
(beta = F(bot, .), psi = F(q, .), phi = F(x, .)). Exact SAT over all triples per lattice; every SAT model replayed in Python.
Hypotheses:
  x of height <= 2, q an atom, q <= x, q != x (the case x = q is trivial);
  (T) at row x: no column y of height >= 3 with phi(y) <= x or y <= phi(y)      (flag xTx drops it)
  (T) at row q: no column y of height >= 3 with psi(y) <= q or y <= psi(y)      (flag xTq drops it)
  beta(q) = bot, and beta has no post-fixed point above bot (a(bot) = bot)       (flag xA drops a(bot) = bot)
  p = first element of height <= 2 on phi's descent from top; beta(p) = q (x exits to q).
Claim: the first element of height <= 2 on psi's descent from top is p.   SAT = the claim fails.
Flag stall forces psi(p) = p (the proved case; must be UNSAT); flag fol forces psi(p) = q (the open case).
  python3 abs_domcoland.py (sweep N MAX | closure K M SEED CNT) [xTx] [xTq] [xA] [stall|fol]"""
import sys, collections, itertools
sys.path.insert(0, '../separation')
from pysat.solvers import Cadical153
from tight_probe import lattices
FLG = {'xTx', 'xTq', 'xA', 'stall', 'fol'}
FL = {a for a in sys.argv[1:] if a in FLG}; args = [a for a in sys.argv[1:] if a not in FLG]
print('abs_domcoland | SAT = AbstractDomCoLand fails (psi lands elsewhere) | flags', sorted(FL))
C = collections.Counter(); H = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; bot = L.bot; NO = L.height + 1
    if L.height < 3: continue
    V = {}; S = Cadical153()
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    def onehot(name, dom):
        ls = [v(name, z) for z in dom]; S.add_clause(ls)
        for a_, b_ in itertools.combinations(ls, 2): S.add_clause([-a_, -b_])
        for z in range(n):
            if z not in dom: S.add_clause([-v(name, z)])
        return lambda z: v(name, z)
    mp = {r: [onehot((r, y), list(range(n))) for y in range(n)] for r in ('b', 's', 'f')}
    for r in ('b', 's', 'f'):
        for y in range(n):
            for y2 in L.covers_up[y]:
                for w in range(n): S.add_clause([-mp[r][y](w)] + [mp[r][y2](w2) for w2 in range(n) if le[w][w2]])
    for lo, hi in (('b', 's'), ('s', 'f')):
        for y in range(n):
            for w in range(n): S.add_clause([-mp[lo][y](w)] + [mp[hi][y](w2) for w2 in range(n) if le[w][w2]])
    if 'xA' not in FL:
        for y in range(n):
            if y == bot: continue
            for w in range(n):
                if le[y][w]: S.add_clause([-mp['b'][y](w)])
    X = onehot('X', [z for z in range(n) if 1 <= h[z] <= 2]); Q = onehot('Q', [z for z in range(n) if h[z] == 1])
    for x in range(n):
        for q in range(n):
            if not le[q][x] or q == x: S.add_clause([-X(x), -Q(q)])
    for q in range(n): S.add_clause([-Q(q), mp['b'][q](bot)])
    for y in range(n):
        if h[y] <= 2: continue
        for w in range(n):
            for z in range(n):
                if 'xTx' not in FL and (le[w][z] or le[y][w]): S.add_clause([-X(z), -mp['f'][y](w)])
                if 'xTq' not in FL and (le[w][z] or le[y][w]): S.add_clause([-Q(z), -mp['s'][y](w)])
    def desc(r):                                      # exact iterates it(r, j, .)
        it = lambda j, z: v('it', r, j, z)
        for z in range(n): S.add_clause([it(0, z)] if z == top else [-it(0, z)])
        for j in range(NO):
            for z in range(n):
                for w in range(n): S.add_clause([-it(j, z), -mp[r][z](w), it(j + 1, w)])
            for w in range(n):
                for w2 in range(w + 1, n): S.add_clause([-it(j + 1, w), -it(j + 1, w2)])
        low = [z for z in range(n) if h[z] <= 2]
        # first-low index: lowat(j) = it(j) is low and all earlier are high
        land = lambda z: v('land', r, z)
        lowat = lambda j: v('lowat', r, j)
        for j in range(NO + 1):                       # lowat(j) <-> the j-th iterate is low
            ls = [it(j, w) for w in low]; S.add_clause([-lowat(j)] + ls)
            for t in ls: S.add_clause([-t, lowat(j)])
        for z in low:
            for j in range(NO + 1):                   # converse: it(j, z), all earlier high  =>  landj
                S.add_clause([-it(j, z)] + [lowat(j2) for j2 in range(j)] + [v('landj', r, j, z)])
            ls = []
            for j in range(NO + 1):
                t = v('landj', r, j, z); ls.append(t)
                S.add_clause([-t, it(j, z)])
                for j2 in range(j):
                    for w in low: S.add_clause([-t, -it(j2, w)])
            S.add_clause([-land(z)] + ls)
            for t in ls: S.add_clause([-t, land(z)])
        for z in range(n):
            if z not in low: S.add_clause([-land(z)])
        return land
    landf = desc('f'); lands = desc('s')
    P = onehot('P', [z for z in range(n) if h[z] <= 2])
    for p in range(n):
        S.add_clause([-P(p), landf(p)])
        for q in range(n): S.add_clause([-P(p), -Q(q), mp['b'][p](q)])
        S.add_clause([-P(p), -lands(p)])                  # negated claim
    if 'stall' in FL or 'fol' in FL:
        for p in range(n):
            for q in range(n):
                S.add_clause([-P(p), -Q(q), mp['s'][p](p if 'stall' in FL else q)])
    if S.solve():
        M = set(z for z in S.get_model() if z > 0)
        val = lambda r: [next(w for w in range(n) if mp[r][y](w) in M) for y in range(n)]
        B, Ps, Ph = val('b'), val('s'), val('f')
        x = next(z for z in range(n) if X(z) in M); q = next(z for z in range(n) if Q(z) in M)
        def dsc(G):
            w = top; s_ = []
            while w not in s_: s_.append(w); w = G[w]
            return s_
        lam = lambda G: next((z for z in dsc(G) if h[z] <= 2), None)
        mono = all(le[G[y]][G[y2]] for G in (B, Ps, Ph) for y in range(n) for y2 in range(n) if le[y][y2])
        ok = mono and all(le[B[y]][Ps[y]] and le[Ps[y]][Ph[y]] for y in range(n)) and h[q] == 1 and le[q][x] and q != x and B[q] == bot
        p = lam(Ph); ok = ok and p is not None and B[p] == q and lam(Ps) != p
        if 'xA' not in FL: ok = ok and not any(y != bot and le[y][B[y]] for y in range(n))
        if 'xTx' not in FL: ok = ok and not any(h[y] > 2 and (le[Ph[y]][x] or le[y][Ph[y]]) for y in range(n))
        if 'xTq' not in FL: ok = ok and not any(h[y] > 2 and (le[Ps[y]][q] or le[y][Ps[y]]) for y in range(n))
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1; H[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, beta=B, psi=Ps, phi=Ph, x=x, q=q))
    else: C['UNSAT'] += 1; H[f'h{L.height}:unsat'] += 1
    S.delete()
print(sorted(FL), args, dict(C), dict(H), 'smallest SAT', best[0] if best else None)
if best:
    import json; json.dump(best[1], open(f'abs_domcoland{"".join("_" + z for z in sorted(FL))}_min{best[0]}.json', 'w'))
