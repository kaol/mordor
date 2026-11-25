"""§34.3z²⁷⁷ (worker, direct round): BreakDom halves in a minimal encoding, independent of muorbit_sat.py.
Only F (one-hot, monotone in both arguments) and exact descents from top by index; no R-stages, no tightness.
t_j = (F bot)^j(top); row-x descent u_j = (F x)^j(top); land(x) = the first u_j of height <= 2.
Hypothesis always: a(bot) = bot (the bot-descent reaches bot within H+1 steps).
Variants (SAT = the stated claim fails):
  QT0: x <= t_k with h(t_k) >= 3, land(x) = p, q = F(bot, p) != bot, and q is not below t_k
  QT1: QT0 with x >= d, d = land(bot) an atom
  QR : d = land(bot) an atom, r on row d descent with d <= r, k with r meet t_k > d = r meet t_(k+1), w = r meet t_k,
       land(w) = p, q = F(bot, p) != bot, and q is not below r
  QRm: QR without the step condition (mutant)
  QRs: QR with r arbitrary >= d (not on row d descent)
Every SAT model is replayed in Python.
  python3 bd_probe.py VARIANT (sweep N MAX | closure K M SEED CNT) [minh H maxn N]  (filter: height >= H, |L| <= N)"""
import sys, itertools, collections
from pysat.solvers import Cadical153
from tight_probe import lattices
VAR = sys.argv[1]; args = sys.argv[2:]
assert VAR.rstrip('v') in ('QT0', 'QT1', 'QT2', 'QTc', 'QR', 'QRm', 'QRs', 'G0', 'G1', 'L2', 'L4', 'U', 'U0', 'Um', 'Ua', 'P', 'P0', 'QTa', 'MB'), VAR
VAC = VAR.endswith('v'); VAR = VAR[:-1] if VAC else VAR      # suffix v: vacuity run (claim replaced by q <= bot: SAT = hypothesis has a model)
print(f'bd_probe {VAR}{"v" if VAC else ""} | SAT = ' + ('the hypothesis has a model (vacuity)' if VAC else f'the {VAR} claim fails') + f' | corpus {args}')
C = collections.Counter(); HH = collections.Counter(); best = None
MINH = MAXN = None
if 'minh' in args: k_ = args.index('minh'); MINH = int(args[k_ + 1]); MAXN = int(args[k_ + 3]); args = args[:k_]   # ... minh H maxn N
for L in lattices(args):
    if MINH is not None and (L.height < MINH or L.n > MAXN): continue
    n = L.n; le = L.le; h = L.rank; top = L.top; bot = L.bot; mt = L.meet; NJ = L.height + 2
    if L.height < 3: continue
    S = Cadical153(); V = {}
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    f = lambda x, y, u: v('f', x, y, u)
    for x in range(n):
        for y in range(n):
            ls = [f(x, y, u) for u in range(n)]; S.add_clause(ls)
            for a_, b_ in itertools.combinations(ls, 2): S.add_clause([-a_, -b_])
    for x in range(n):
        for y in range(n):
            for x2 in range(n):
                for y2 in range(n):
                    if (x2, y2) == (x, y) or not (le[x][x2] and le[y][y2]): continue
                    if not (x2 in L.covers_up[x] and y2 == y) and not (y2 in L.covers_up[y] and x2 == x): continue
                    for u in range(n): S.add_clause([-f(x, y, u)] + [f(x2, y2, u2) for u2 in range(n) if le[u][u2]])
    def desc(x):                                   # D(x, j, z): u_j = z, exact (one-hot by index, functional step)
        for z in range(n): S.add_clause([v('D', x, 0, z)] if z == top else [-v('D', x, 0, z)])
        for j in range(NJ):
            for z in range(n):
                for u in range(n): S.add_clause([-v('D', x, j, z), -f(x, z, u), v('D', x, j + 1, u)])
            for z, z2 in itertools.combinations(range(n), 2): S.add_clause([-v('D', x, j + 1, z), -v('D', x, j + 1, z2)])
    for x in range(n): desc(x)
    if VAR not in ('QTa', 'MB'): S.add_clause([v('D', bot, NJ, bot)])   # a(bot) = bot (dropped in mutant QTa)
    def land(x, j, p):                             # land(x) = p, reached at index j
        o = v('land', x, j, p)
        S.add_clause([-o, v('D', x, j, p)])
        for j2 in range(j):
            for z in range(n):
                if h[z] <= 2: S.add_clause([-o, -v('D', x, j2, z)])
        return o
    sel = []
    atoms = [z for z in range(n) if h[z] == 1]
    def LW(x, p):                                  # land(x) = p (some index); one direction suffices (existential use)
        o = v('LW', x, p)
        if ('LWd', x, p) not in V:
            v('LWd', x, p); S.add_clause([-o] + [land(x, j, p) for j in range(NJ)])
        return o
    def bad(x, c):                                 # x lands at p, q = F(bot, p) != bot, q not below c
        o = v('bad', x, c)
        if ('badd', x, c) not in V:
            v('badd', x, c); ls = []
            for p in range(n):
                if h[p] > 2: continue
                for q in range(n):
                    if q == bot or (le[q][c] and not VAC): continue
                    t = v('bt', x, p, q); ls.append(t); S.add_clause([-t, LW(x, p)]); S.add_clause([-t, f(bot, p, q)])
            S.add_clause([-o] + ls)
        return o
    onb = lambda k, z: v('D', bot, k, z)
    if VAR == 'MB':                                # MixBelow: q = F(bot, land(x)) below every high word W(a, b) = (F bot)^a (F x)^b top
        for x in range(n):
            Wv = lambda a, b, z: v('W', x, a, b, z)
            for b in range(NJ + 1):
                for z in range(n): S.add_clause([-v('D', x, b, z), Wv(0, b, z)]); S.add_clause([v('D', x, b, z), -Wv(0, b, z)])
                for a in range(NJ):
                    for z in range(n):
                        for u in range(n): S.add_clause([-Wv(a, b, z), -f(bot, z, u), Wv(a + 1, b, u)])
                    for z, z2 in itertools.combinations(range(n), 2): S.add_clause([-Wv(a + 1, b, z), -Wv(a + 1, b, z2)])
            for p_ in range(n):
                if h[p_] > 2: continue
                for c in range(n):
                    if h[c] < 3: continue
                    for q in range(n):
                        if q == bot or (le[q][c] and not VAC): continue
                        o = v('s', x, p_, c, q); sel.append(o)
                        S.add_clause([-o, LW(x, p_)]); S.add_clause([-o, f(bot, p_, q)])
                        S.add_clause([-o] + [Wv(a, b, c) for a in range(NJ + 1) for b in range(NJ + 1)])
    elif VAR in ('P', 'P0'):                         # LandBelow: x lands at p (P: exiting); SAT = p not below some t_m with t_(m+1) high
        for x in range(n):
            for p_ in range(n):
                if h[p_] > 2: continue
                for c in range(n):
                    if le[p_][c] and not VAC: continue
                    o = v('s', x, p_, c); sel.append(o); S.add_clause([-o, LW(x, p_)]); S.add_clause([-o, v('hiT', c)])
                    if VAR == 'P' or VAC: S.add_clause([-o] + [f(bot, p_, q) for q in range(n) if q != bot])
        for c in range(n):
            ls = []
            for m in range(NJ):
                for c2 in range(n):
                    if h[c2] < 3: continue
                    t = v('hm', c, m, c2); ls.append(t); S.add_clause([-t, onb(m, c)]); S.add_clause([-t, onb(m + 1, c2)])
            S.add_clause([-v('hiT', c)] + ls)
    elif VAR in ('U', 'U0', 'Um', 'Ua'):             # PredBelow (Um mutant: c = t_m merely high; Ua: u any high descent element): x lands at p (U: exiting, F(bot, p) != bot) with predecessor u;
        for x in range(n):                         # c = t_m with t_(m+1) high; SAT = u is not below c
            for u in range(n):
                if h[u] < 3: continue
                pr = v('pred', x, u); ls = []
                for j in range(1, NJ):
                    for p_ in range(n):
                        if h[p_] > 2: continue
                        t = v('pj', x, u, j, p_); ls.append(t)
                        if VAR == 'Ua':                        # u any descent element of height >= 3 (index < j)
                            S.add_clause([-t, land(x, j, p_)]); S.add_clause([-t] + [v('D', x, j2, u) for j2 in range(j)])
                        else:
                            for lit in [land(x, j, p_), v('D', x, j - 1, u)]: S.add_clause([-t, lit])
                        if VAR == 'U' or VAC: S.add_clause([-t] + [f(bot, p_, q) for q in range(n) if q != bot])
                S.add_clause([-pr] + ls)
                for c in range(n):
                    if le[u][c] and not VAC: continue
                    o = v('s', x, u, c); sel.append(o); S.add_clause([-o, pr]); S.add_clause([-o, v('hiT', c)])
        for c in range(n):
            ls = []
            for m in range(NJ):
                for c2 in range(n):
                    if h[c2] < 3: continue
                    t = v('hm', c, m, c2); ls.append(t); S.add_clause([-t, onb(m, c)])
                    if VAR == 'Um': S.add_clause([-t, onb(m, c2)])          # mutant: only t_m high (c2 = c)
                    else: S.add_clause([-t, onb(m + 1, c2)])
            S.add_clause([-v('hiT', c)] + ls)
    elif VAR in ('L2', 'L4'):                      # p = F(x, u), u high, h(p) <= 2 (L2: p <= u), q = F(bot, p) != bot not below a high t_k
        for c in range(n):
            if h[c] < 3: continue
            S.add_clause([-v('anyT', c)] + [onb(k, c) for k in range(NJ)])
            for x in range(n):
                for u in range(n):
                    if h[u] < 3: continue
                    ls = []
                    for p_ in range(n):
                        if h[p_] > 2 or (VAR == 'L2' and not le[p_][u]): continue
                        for q in range(n):
                            if q == bot or (le[q][c] and not VAC): continue
                            t = v('l2', x, u, p_, q); ls.append(t); S.add_clause([-t, f(x, u, p_)]); S.add_clause([-t, f(bot, p_, q)])
                    if not ls: continue
                    o = v('s', x, u, c); sel.append(o); S.add_clause([-o, v('anyT', c)]); S.add_clause([-o] + ls)
    elif VAR in ('G0', 'G1'):                        # any y of height <= 2 (G1: with F(bot, y) <= y): F(bot, y) <= every high t_k
        for y in range(n):
            if h[y] > 2: continue
            for c in range(n):
                if h[c] < 3: continue
                for k in range(NJ):
                    for q in range(n):
                        if q == bot or (le[q][c] and not VAC): continue
                        if VAR == 'G1' and not le[q][y]: continue
                        o = v('s', y, c, k, q); sel.append(o)
                        for lit in [onb(k, c), f(bot, y, q)]: S.add_clause([-o, lit])
    elif VAR in ('QT2', 'QTc', 'QTa'):                      # mutants of QT0: x not below t_k (QT2) / t_k replaced by any high c >= x (QTc)
        for x in range(n):
            for c in range(n):
                if h[c] < 3: continue
                if VAR == 'QTc':
                    if not le[x][c]: continue
                    o = v('s', x, c); sel.append(o); S.add_clause([-o, bad(x, c)]); continue
                for k in range(NJ):
                    o = v('s', x, k, c); sel.append(o)
                    for lit in [onb(k, c), bad(x, c)]: S.add_clause([-o, lit])
    elif VAR in ('QT0', 'QT1'):
        for x in range(n):
            for k in range(NJ):
                for tk in range(n):
                    if h[tk] < 3 or not le[x][tk]: continue
                    o = v('s', x, k, tk); sel.append(o)
                    for lit in [onb(k, tk), bad(x, tk)]: S.add_clause([-o, lit])
                    if VAR == 'QT1': S.add_clause([-o] + [v('ld', dd) for dd in atoms if le[dd][x]])
        for dd in atoms: S.add_clause([-v('ld', dd), LW(bot, dd)])
    elif VAR in ('QR', 'QRm', 'QRs'):
        for dd in atoms:
            for r in range(n):
                if not le[dd][r]: continue
                for k in range(NJ):
                    for tk in range(n):
                        w = mt[r][tk]
                        if w == dd or not le[dd][w]: continue
                        for tk1 in (range(n) if VAR != 'QRm' else [None]):
                            if tk1 is not None and mt[r][tk1] != dd: continue
                            o = v('s', dd, r, k, tk, tk1); sel.append(o)
                            lits = [LW(bot, dd), onb(k, tk), bad(w, r)]
                            if tk1 is not None: lits.append(onb(k + 1, tk1))
                            if VAR != 'QRs': lits.append(v('ondd', dd, r))
                            for lit in lits: S.add_clause([-o, lit])
                for r in range(n):
                    S.add_clause([-v('ondd', dd, r)] + [v('D', dd, j, r) for j in range(NJ + 1)])
    S.add_clause(sel)
    if S.solve():
        m = set(x for x in S.get_model() if x > 0)
        F = [[next(u for u in range(n) if V[('f', x, y, u)] in m) for y in range(n)] for x in range(n)]
        def dsc(x):
            z = top; out = [z]
            for _ in range(NJ): z = F[x][z]; out.append(z)
            return out
        def lnd(x): return next((z for z in dsc(x) if h[z] <= 2), None)
        tb = dsc(bot); ok = tb[-1] == bot or VAR in ('QTa', 'MB')
        mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for y in range(n) for x2 in range(n) for y2 in range(n) if le[x][x2] and le[y][y2])
        ok = ok and mono; found = False
        if VAR == 'MB':
            def W(x, a, b):
                z = top
                for _ in range(b): z = F[x][z]
                for _ in range(a): z = F[bot][z]
                return z
            for x in range(n):
                p_ = lnd(x)
                if p_ is None or F[bot][p_] == bot: continue
                q = F[bot][p_]
                found = found or any(h[W(x, a, b)] >= 3 and (VAC or not le[q][W(x, a, b)]) for a in range(NJ + 1) for b in range(NJ + 1))
        elif VAR in ('P', 'P0'):
            for x in range(n):
                p_ = lnd(x)
                if p_ is None or ((VAR == 'P' or VAC) and F[bot][p_] == bot): continue
                found = found or any(h[tb[m + 1]] >= 3 and (VAC or not le[p_][tb[m]]) for m in range(len(tb) - 1))
        elif VAR in ('U', 'U0', 'Um', 'Ua'):
            for x in range(n):
                dx = dsc(x); i = next((i for i, z in enumerate(dx) if h[z] <= 2), None)
                if i is None or i == 0: continue
                p_ = dx[i]
                if (VAR == 'U' or VAC) and F[bot][p_] == bot: continue
                for u in (dx[:i] if VAR == 'Ua' else [dx[i - 1]]):
                    found = found or any(h[tb[m + (0 if VAR == 'Um' else 1)]] >= 3 and (VAC or not le[u][tb[m]]) for m in range(len(tb) - 1))
        elif VAR in ('L2', 'L4'):
            found = any(h[u] >= 3 and h[F[x][u]] <= 2 and (VAR == 'L4' or le[F[x][u]][u]) and F[bot][F[x][u]] != bot
                        and any(h[c] >= 3 and (VAC or not le[F[bot][F[x][u]]][c]) for c in tb) for x in range(n) for u in range(n))
        elif VAR in ('G0', 'G1'):
            found = any(h[y] <= 2 and F[bot][y] != bot and (VAR == 'G0' or le[F[bot][y]][y]) and any(h[c] >= 3 and (VAC or not le[F[bot][y]][c]) for c in tb) for y in range(n))
        elif VAR in ('QT2', 'QTc', 'QTa'):
            for x in range(n):
                p = lnd(x)
                if p is None or F[bot][p] == bot: continue
                q = F[bot][p]
                cs = tb if VAR in ('QT2', 'QTa') else [c for c in range(n) if le[x][c]]
                found = found or any(h[c] >= 3 and (VAC or not le[q][c]) for c in cs)
        elif VAR in ('QT0', 'QT1'):
            dd = lnd(bot)
            for x in range(n):
                p = lnd(x)
                if p is None or F[bot][p] == bot: continue
                if VAR == 'QT1' and not (h[dd] == 1 and le[dd][x]): continue
                q = F[bot][p]
                found = found or any(h[tk] >= 3 and le[x][tk] and (VAC or not le[q][tk]) for tk in tb)
        elif VAR in ('QR', 'QRm', 'QRs'):
            dd = lnd(bot)
            if h[dd] == 1:
                for r in (range(n) if VAR == 'QRs' else set(dsc(dd))):
                    if not le[dd][r]: continue
                    for k in range(len(tb) - 1):
                        w = mt[r][tb[k]]
                        if w == dd or not le[dd][w]: continue
                        if VAR != 'QRm' and mt[r][tb[k + 1]] != dd: continue
                        p = lnd(w)
                        if p is not None and F[bot][p] != bot and (VAC or not le[F[bot][p]][r]): found = True
        assert ok and found, 'SAT/Python mismatch'
        C['SAT'] += 1; HH[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1; HH[f'h{L.height}:unsat'] += 1
    S.delete()
print(VAR, args, dict(C), dict(HH), 'smallest', best[0] if best else None)
if best:
    import json; json.dump(best[1], open(f'bd_probe_{VAR}_min{best[0]}.json', 'w'))
