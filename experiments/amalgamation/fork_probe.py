"""Nonempty-fork good-child principle (log §34.3z¹⁸⁷).

Top graph exactly as in Lean: nodes x ∈ R_{h(x)} with h(x) ≤ k; edges x → y iff SibConfig(x, y) (y new at stage
h(x)+1 of height h(x)+1, x < y, F(x, y) = x, S(x, y; m) ≠ ∅, x's own stage/height) or AEdge(x, y) (x < y ≤ F(x, y),
m ≰ y, y new at h(x)+1 of height h(x)+1). Good at stage k: an upward cell away from m (`UpAt`); below: some good child.
Tests "a node below k with a child has a good child" on (i) every node, (ii) every node reachable from the feeder
descent root, and records the A-roots (upper final descent cell). Unlike seeded_probe.py, every qualifying m of every
lattice is used (one model each).   python3 fork_probe.py [rmin=R] (closure … | sweep …)
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
        best[tag] = n; json.dump(d, open(f'fork_{tag}_min{n}.json', 'w'))

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
        def kids(x):
            out = {}
            for y in range(n):
                if not (le[x][y] and y != x and new(y, h[x] + 1)): continue
                if F[x][y] == x and fib(x, y): out[y] = 'B'
                elif le[y][F[x][y]] and not le[m][y]: out[y] = 'A'
            return out
        upat = lambda x: any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))
        X = [x for x in range(n) if node(x)]; K_ = {x: kids(x) for x in X}
        good = {}
        for s in range(k, 0, -1):
            for x in X:
                if h[x] == s: good[x] = upat(x) if s == k else any(good.get(y, False) for y in K_[x] if h[y] <= k)
        C['models'] += 1
        D = dict(sets=L.S, F=F, m=m)
        # (i) every node below k
        for x in X:
            if h[x] >= k or not K_[x]: continue
            ch = K_[x]; gk = [y for y in ch if good[y]]
            tag = ('fork', 'new top' if new(x, h[x]) else 'early node', 'k − s', k - h[x], 'children B/A', ''.join(sorted(ch.values())),
                   'good children B/A', ''.join(sorted(ch[y] for y in gk)))
            C[tag[:4] + ('has a good child', bool(gk))] += 1
            rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
            mp0 = b_of(L, F, m); w0 = F[m][ystar(L, F, m)]
            C[('fork position', 'x vs m′', rl(x, mp0), 'x vs w', rl(x, w0), 'x vs m', rl(x, m), 'has a good child', bool(gk))] += 1
            if len(ch) > 1: C[('fork with ≥ 2 children', 'good B/A', ''.join(sorted(ch[y] for y in gk)), 'bad B/A', ''.join(sorted(ch[y] for y in ch if not good[y])))] += 1
            for y, ty in ch.items(): C[('child goodness (nodes below k)', ty, 'good', good[y], 'child is a dead end below k' if h[y] < k and not K_[y] else 'child at stage k without UpAt' if h[y] == k and not good[y] else 'other')] += 1
            if not gk: C[('all-bad fork', 'reachable from the descent root', None)] += 0
            if not gk: keep('allbad_' + ('new' if new(x, h[x]) else 'early') + ('_sib' if rl(x, mp0) == '∥' else ''), n, dict(D, node=x, children=ch))
        # (ii) reachable from the feeder descent root
        B = lambda y: b_of(L, F, y); mp = B(m); w = F[m][ystar(L, F, m)]
        r, e, i = mp, w, 0
        while True:
            t = F[r][e]
            if le[t][r] or le[e][t]: z = e; break
            if le[r][t]: e = t; continue
            q = B(r); e2 = F[q][e]
            if le[e2][q]: r, z, i = q, e, i + 1; break
            r, e, i = q, e2, i + 1
        if i == 0: C[('root', 'depth 0')] += 1; continue
        upper = le[z][F[r][z]] and not le[F[r][z]][r]
        root = r if upper else z
        kind = 'A-root (upper final cell)' if upper else 'lower root'
        if not node(root):
            C[('root', kind, 'not a node', 'h', h[root], 'stage', st[root], 'early column' if inR(z, h[z] - 1) else 'other')] += 1
            if upper: C[('A-root not a node', 'z node', node(z), 'z new', new(z, h[z]), 'Good(z)', good.get(z), 'z = a(r)', z == a_of(L, F, r))] += 1
            continue
        if upper: C[('A-root', 'r → z an A-edge', K_[r].get(z) == 'A', 'z = a(r)', z == a_of(L, F, r), 'Good(r)', good[r], 'Good(z)', good.get(z))] += 1
        seen = {root}; todo = [root]
        while todo:
            x = todo.pop()
            for y in K_[x]:
                if h[y] <= k and y not in seen: seen.add(y); todo.append(y)
        bad = [x for x in seen if h[x] < k and K_[x] and not any(good[y] for y in K_[x])]
        for x in seen:
            if h[x] < k and K_[x]:
                C[('reachable fork', 'children', len(K_[x]), 'B/A', ''.join(sorted(K_[x].values())), 'good children', sum(good[y] for y in K_[x]))] += 1
            if h[x] < k and not K_[x]: C[('reachable dead end below k',)] += 1
            if h[x] == k: C[('reachable stage-k node', 'UpAt', good[x])] += 1
        C[('root', kind, 'k − h(root)', k - h[root], 'root good (TopGoal)', good[root], 'reachable all-bad forks', len(bad))] += 1
        allbad = [x for x in X if h[x] < k and K_[x] and not any(good[y] for y in K_[x])]
        C[('all-bad forks in the model', len(allbad), 'reachable from the root', len([x for x in allbad if x in seen]), 'root good', good[root])] += 1
        if bad: keep('reach_allbad', n, dict(D, root=root, nodes=bad))
        if not good[root]:
            C[('bad root', 'SibConfig(r, z)', inR(r, h[r]) and h[r] == h[z] - 1 and F[r][z] == r and bool(fib(r, z)) and new(z, h[z]), 'F(r,z) = r', F[r][z] == r,
               'fibre nonempty', bool(fib(r, z)), 'z new', new(z, h[z]), 'UpCell at stage k', any(h[x] == k and inR(x, k) and upat(x) for x in range(n)))] += 1
            keep('root_bad_' + ('A' if upper else 'L'), n, dict(D, r=r, z=z))
report()
