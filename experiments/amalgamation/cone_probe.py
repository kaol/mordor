"""Rooted fork selection: AGood / A-orbits, B-only forks, root cone, TopReach vs MixedReach (log §34.3z¹⁸⁸).

Same models as fork_probe.py (every qualifying m, one SAT model each). Edges exactly as in Lean: B (TopEdge left):
SibConfig(c, y) — c ∈ R_{h(c)} of height h(c), y new at h(c)+1 of height h(c)+1, c < y, F(c, y) = c,
S(c, y; m) ≠ ∅; A: AEdge(c, y) — c ∈ R_{h(c)} of height h(c), c < y ≤ F(c, y), m ≰ y, y new at h(c)+1.
Mixed B-edge (SeedEdge, any source p): SibConfig(p, c), SibConfig(c, y), and a certificate v ∈ S(p, c; m),
v′ ∈ (c, v] with F(c, v′) ≤ v′, y ≤ v′, F(c, y) ≤ c, y = v′ or y = F(c, u′) with u′ ∈ (c, v′], F(c, u′) ≤ u′.
   python3 cone_probe.py [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); best = {}
def report(*_):
    for k_, v in sorted(C.items(), key=str): print(k_, v)
    for k_, v in sorted(best.items()): print('MIN', k_, v)
    sys.stdout.flush(); sys.exit(0)
signal.signal(signal.SIGTERM, report)
def keep(tag, n, d):
    if tag not in best or n < best[tag]:
        best[tag] = n; json.dump(d, open(f'cone_{tag}_min{n}.json', 'w'))

for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
        fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
        node = lambda x: inR(x, h[x]) and 1 <= h[x] <= k
        sib = lambda pp, cc: inR(pp, h[pp]) and new(cc, h[pp] + 1) and le[pp][cc] and pp != cc and F[pp][cc] == pp and bool(fib(pp, cc))
        def kids(x):
            out = {}
            for y in range(n):
                if not (le[x][y] and y != x and new(y, h[x] + 1)): continue
                if sib(x, y): out[y] = 'B'
                elif le[y][F[x][y]] and not le[m][y]: out[y] = 'A'
            return out
        def seedkids(c):
            out = set()
            for pp in range(n):
                if not sib(pp, c): continue
                for v in fib(pp, c):
                    for v1 in range(n):
                        if not (le[c][v1] and v1 != c and le[v1][v] and le[F[c][v1]][v1]): continue
                        cands = {v1} | {F[c][u1] for u1 in range(n) if le[c][u1] and u1 != c and le[u1][v1] and le[F[c][u1]][u1]}
                        out |= {y for y in cands if le[y][v1] and le[F[c][y]][c] and sib(c, y)}
            return out
        upat = lambda x: any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))
        X = [x for x in range(n) if node(x)]; KK = {x: kids(x) for x in X}
        def goodness(children):
            g = {}
            for s in range(k, 0, -1):
                for x in X:
                    if h[x] == s: g[x] = upat(x) if s == k else any(g.get(y, False) for y in children(x) if h[y] <= k)
            return g
        good = goodness(lambda x: KK[x])
        C['models'] += 1
        # AGood and the A-orbit, over every A-child of a node below k (unrooted)
        for x in X:
            if h[x] >= k: continue
            for y, ty in KK[x].items():
                if ty != 'A' or h[y] > k: continue
                ay = a_of(L, F, y)
                orb = 'a(y) = y (stabilizes)' if ay == y else 'm ≤ a(y)' if le[m][ay] else 'a(y) new at the next stage' if new(ay, h[y] + 1) else 'a(y) > y, off m, not new at the next stage'
                # pure A-chain: follow y → a(y) while it is an A-edge
                z_ = y
                while h[z_] < k and KK.get(z_, {}).get(a_of(L, F, z_)) == 'A': z_ = a_of(L, F, z_)
                chain = h[z_] == k and upat(z_)
                C[('A-child', 'stage', 'k' if h[y] == k else '< k', 'Good', good[y], 'a-orbit', orb, 'pure A-chain reaches a stage-k UpAt', chain,
                   'terminal via upAt_of_a', h[y] == k and ay != y and not le[m][ay])] += 1
                if not good[y]: keep('abad', n, dict(sets=L.S, F=F, m=m, node=x, child=y))
        # feeder descent root
        B = lambda y: b_of(L, F, y); mp = B(m); w = F[m][ystar(L, F, m)]
        r, e, i = mp, w, 0
        while True:
            t = F[r][e]
            if le[t][r] or le[e][t]: z = e; break
            if le[r][t]: e = t; continue
            q = B(r); e2 = F[q][e]
            if le[e2][q]: r, z, i = q, e, i + 1; break
            r, e, i = q, e2, i + 1
        if i == 0: continue
        upper = le[z][F[r][z]] and not le[F[r][z]][r]
        root = r if upper and node(r) else z
        if not node(root): continue
        if not upper and inR(z, h[z] - 1):                # early-column root: try the siblings of r below z
            srcs = [pp for pp in range(n) if inR(pp, h[pp]) and h[pp] == h[r] - 1 and le[pp][r] and pp != r and F[pp][r] == pp]
            sibs = [sx for pp in srcs for sx in range(n) if sx != r and le[pp][sx] and sx != pp and F[pp][sx] == pp and h[sx] == h[r] and inR(sx, h[sx])]
            gs = [sx for sx in sibs if le[sx][z] and good.get(sx, False)]
            C[('early-column root', 'k − h(z)', k - h[z], 'r has a source p (F(p, r) = p, h(p) = h(r) − 1)', bool(srcs), 'a sibling s ≤ z of r (same source) is Good', bool(gs),
               'z = r ∨ s for such s', any(L.join[r][sx] == z for sx in gs) if hasattr(L, 'join') else None, 'UpCell at stage k', any(h[x] == k and inR(x, k) and upat(x) for x in range(n)))] += 1
            keep('early', n, dict(sets=L.S, F=F, m=m, r=r, z=z))
        seen = {root}; todo = [root]
        while todo:
            x = todo.pop()
            for y in KK[x]:
                if h[y] <= k and y not in seen: seen.add(y); todo.append(y)
        # root cone: every all-bad fork vs the root's upper cone
        for x in X:
            if h[x] < k and KK[x] and not any(good[y] for y in KK[x]):
                C[('all-bad fork (rooted model)', 'root ≤ x', le[root][x], 'reachable', x in seen)] += 1
                if le[root][x]: keep('conebad', n, dict(sets=L.S, F=F, m=m, root=root, node=x))
        for x in X:
            if le[root][x] and x != root and h[x] <= k:
                C[('cone node (root < x, h(x) ≤ k)', 'reachable', x in seen, 'below k with children', h[x] < k and bool(KK[x]), 'Good', good[x])] += 1
        # B-only reachable forks
        for x in seen:
            if h[x] < k and KK[x] and 'A' not in KK[x].values():
                C[('reachable B-only fork', 'B-children', len(KK[x]), 'good B-children', sum(good[y] for y in KK[x]))] += 1
        # TopReach vs MixedReach
        SK = {x: seedkids(x) for x in X}
        mkids = lambda x: {y for y in KK[x] if KK[x][y] == 'A'} | SK[x]
        mgood = goodness(mkids)
        for x in seen:
            for y, ty in KK[x].items():
                if ty == 'B' and h[y] <= k:
                    srcs = [pp for pp in range(n) if sib(pp, x)]
                    C[('reachable B top-edge', 'is a SeedEdge (some source)', y in SK[x], 'x has a SibConfig source', bool(srcs), 'child Good', good[y])] += 1
        C[('root', 'upper' if upper else 'lower', 'Good (top graph)', good[root], 'Good (mixed graph)', mgood[root])] += 1
        if good[root] and not mgood[root]: keep('mixfail', n, dict(sets=L.S, F=F, m=m, root=root))
report()
