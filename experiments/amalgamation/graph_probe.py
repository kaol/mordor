"""The descent-seeded configuration graph (log §34.3z¹⁸⁴).

Root: the final cell (r, z) of the feeder's two-dimensional descent from (m′, w) (`feeder_cell_dichotomy`; depth 0
is UpCell outright). A configuration (p, c) at stage s = h(c): p ∈ R_{s−1} of height s − 1, c ∈ R_s ∖ R_{s−1} of
height s, p < c, F(p, c) = p, fibre S(p, c; m) = {v : c < v, m ≰ v, F(p, v) = c} ≠ ∅.
Edge (p, c) → (c, y), tagged (v, v′, endpoint | row-value shadow): v ∈ S(p, c; m), v′ ∈ (c, v] row-c pre-fixed, the
shadow-tracking descent from v′ ends in a lower cell y new at stage s + 1 with S(c, y; m) ≠ ∅
(`climb_step`, `climb_next_config`). FibreTop at stage k: a fibre interval (c, v] has a column y with F(c, y) ≤ y or
y ≤ F(c, y) (`siblingShadow_upCell`). Records every reachable configuration, the dead ends below k with their causes,
the fibre-join cases, and global selection candidates.   python3 graph_probe.py [rmin=R] (sweep … | closure …)
"""
import sys, collections
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, b_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc

C = collections.Counter()
for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        B = lambda y: b_of(L, F, y)
        mp = B(m); w = F[m][ystar(L, F, m)]
        fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
        comp = lambda cc, v: [y for y in range(n) if le[cc][y] and y != cc and le[y][v] and (le[F[cc][y]][y] or le[y][F[cc][y]])]
        # two-dimensional descent from (m′, w)
        r, e, i = mp, w, 0; shadow = False
        while True:
            t = F[r][e]
            if le[t][r] or le[e][t]: z = e; break
            if le[r][t]: e = t; continue
            q = B(r); e2 = F[q][e]
            if le[e2][q]: r, z, i = q, e, i + 1; break
            r, e, i = q, e2, i + 1
        C['models'] += 1
        if i == 0: C[('root', 'depth 0: UpCell outright')] += 1; continue
        def config_ok(pp, cc):
            s = h[cc]
            return inR(cc, s) and not inR(cc, s - 1) and h[pp] == s - 1 and inR(pp, s - 1) and le[pp][cc] and F[pp][cc] == pp and bool(fib(pp, cc))
        if not config_ok(r, z):
            why = ('early column' if inR(z, h[z] - 1) else 'empty fibre' if not fib(r, z) else
                   'upper final cell (z ≤ F(r, z))' if le[z][F[r][z]] else f'other: h(z) − h(r) = {h[z] - h[r]}, F(r,z) = r: {F[r][z] == r}')
            C[('root', 'not a configuration', why)] += 1
            if why.startswith('upper'):
                ar = __import__('rstages').a_of(L, F, r)
                C[('upper root', 'z = a(r)', ar == z, 'z new at its stage', not inR(z, h[z] - 1), 'z has an upward cell away from m (stage of z)',
                   any(le[z][y] and y != z and not le[m][y] and (le[F[z][y]][z] or le[y][F[z][y]]) for y in range(n)), 'UpCell at stage k exists',
                   any(h[x] == k and inR(x, k) and any(le[x][y] and y != x and not le[m][y] and (le[F[x][y]][x] or le[y][F[x][y]]) for y in range(n)) for x in range(n)))] += 1
            continue
        C[('root', 'configuration at stage k − ', k - h[z])] += 1
        seen = {}; stack = [(r, z)]; dead = []; tops = []
        while stack:
            pp, cc = stack.pop()
            if (pp, cc) in seen: continue
            s = h[cc]; S = fib(pp, cc)
            if s == k:
                ok = any(comp(cc, v) for v in S); seen[(pp, cc)] = ok; tops.append((pp, cc, ok)); continue
            kids = set(); causes = set()
            for v in S:
                pre = [v1 for v1 in range(n) if le[cc][v1] and v1 != cc and le[v1][v] and le[F[cc][v1]][v1]]
                if not pre: causes.add('no pre-fixed column in (c, v]'); continue
                for v1 in pre:
                    u_ = v1; endpoint = True
                    while True:
                        g = F[cc][u_]
                        if le[g][cc] or le[u_][g]: break
                        u_ = g; endpoint = False
                    y = u_
                    if not le[F[cc][y]][cc]: causes.add('upper cell'); continue
                    if inR(y, s): causes.add('early y'); continue
                    if not fib(cc, y): causes.add('empty fibre at y'); continue
                    kids.add((cc, y)); C[('edge tag', 'endpoint' if endpoint else 'row-value shadow')] += 1
            seen[(pp, cc)] = bool(kids)
            if not kids: dead.append((pp, cc, s, frozenset(causes)))
            stack.extend(kids)
        C[('model', 'reachable stage-k configurations', len(tops), 'FibreTop among them', sum(1 for t in tops if t[2]))] += 1
        C[('model', 'some reachable FibreTop', any(t[2] for t in tops))] += 1
        for pp, cc, s, cs in dead: C[('dead end below k', 'stage k −', k - s, 'causes', tuple(sorted(cs)))] += 1
        C[('model', 'dead ends below k', len(dead) > 0, 'and success', any(t[2] for t in tops))] += 1
        C[('model', 'reachable configurations below k', sum(1 for x in seen if h[x[1]] < k))] += 1
        for s0 in range(1, k):                          # dead ends among configurations NOT reachable from the seed
            for cc in range(n):
                if not (h[cc] == s0 and inR(cc, s0) and not inR(cc, s0 - 1)): continue
                for pp in range(n):
                    if (pp, cc) in seen or not config_ok(pp, cc): continue
                    kids = False; causes = set()
                    for v in fib(pp, cc):
                        pre = [v1 for v1 in range(n) if le[cc][v1] and v1 != cc and le[v1][v] and le[F[cc][v1]][v1]]
                        if not pre: causes.add('no pre-fixed column in (c, v]'); continue
                        for v1 in pre:
                            u_ = v1
                            while True:
                                g = F[cc][u_]
                                if le[g][cc] or le[u_][g]: break
                                u_ = g
                            if not le[F[cc][u_]][cc]: causes.add('upper cell'); continue
                            if inR(u_, s0): causes.add('early y'); continue
                            if not fib(cc, u_): causes.add('empty fibre at y'); continue
                            kids = True
                    tag = 'unseeded, has a child' if kids else 'unseeded dead end'
                    C[(tag, 'stage k −', k - s0, 'p = some b^i(m′)', any(pp == x for x in [B(mp), B(B(mp))]), 'causes', tuple(sorted(causes)) if not kids else ())] += 1
        # fibre-join boundary and selection candidates over all reachable configurations (and all stage-k ones)
        allk = [(pp, cc) for cc in range(n) if h[cc] == k and inR(cc, k) and not inR(cc, k - 1)
                for pp in range(n) if config_ok(pp, cc)]
        for pp, cc in list(seen) + [x for x in allk if x not in seen]:
            S = fib(pp, cc); U = S[0]
            for v in S[1:]: U = L.join[U][v]
            stable = F[pp][U] == cc and not le[m][U]
            tag = 'reachable' if (pp, cc) in seen else 'other stage-k'
            C[('fibre join', tag, 'stable (F(p,U) = c, m ≰ U)' if stable else ('jump, m ≤ U' if le[m][U] else 'jump, m ≰ U' if F[pp][U] != cc else 'm ≤ U'))] += 1
            if h[cc] == k:
                ft = any(comp(cc, v) for v in S)
                if stable: C[('stage k, stable fibre', 'FibreTop', ft, 'comparable in (c, U]', bool(comp(cc, U)))] += 1
        if allk:
            best = max(((pp, cc, v) for pp, cc in allk for v in fib(pp, cc)), key=lambda t: h[t[2]])
            C[('selection S1: stage-k configuration with a fibre column of maximal height', 'FibreTop', bool(comp(best[1], best[2])))] += 1
            C[('selection S2: some stage-k configuration with stable fibre join and comparable (c, U]',
               any(F[pp][j_] == cc and not le[m][j_] and comp(cc, j_) for pp, cc in allk
                   for j_ in [__import__('functools').reduce(lambda a, b: L.join[a][b], fib(pp, cc))]))] += 1
        break
for k_, v in sorted(C.items(), key=str): print(k_, v)
