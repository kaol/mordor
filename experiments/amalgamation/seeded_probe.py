"""Seeded roots below stage k: candidate-pair table and descent provenance (log §34.3z¹⁸⁶).

For every remaining-case instance (multi, nopostlayer, rank ≥ R) whose feeder descent ends at a sibling-shadow root
(r, z) below stage k: replay the descent and record its last drop (row q = r's predecessor in the B-chain, column e,
output t = F(q, e)); for the root, every candidate pair (v, v′) — v in the fibre S(r, z; m), v′ ∈ (z, v] row-z
pre-fixed — and the outcome of its shadow-tracking descent (endpoint / shadow, upper, early, empty child fibre,
edge); and whether the descent's own data (v = e, v′ = t) give an edge.   python3 seeded_probe.py [rmin=R] (…)
"""
import sys, collections, json
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); TABLE = []
for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        B = lambda y: b_of(L, F, y)
        mp = B(m); w = F[m][ystar(L, F, m)]
        fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
        r, e, i = mp, w, 0; lastdrop = None
        while True:
            t = F[r][e]
            if le[t][r] or le[e][t]: z = e; break
            if le[r][t]: e = t; continue
            q = B(r); e2 = F[q][e]; lastdrop = (r, e, t)
            if le[e2][q]: r, z, i = q, e, i + 1; break
            r, e, i = q, e2, i + 1
        if i == 0 or not le[F[r][z]][r] or h[z] >= k: continue
        if not (inR(z, h[z]) and not inR(z, h[z] - 1) and fib(r, z)): continue
        s = h[z]; S = fib(r, z)
        row = collections.Counter(); edges = set()
        for v in S:
            pre = [v1 for v1 in range(n) if le[z][v1] and v1 != z and le[v1][v] and le[F[z][v1]][v1]]
            row['fibre columns'] += 1; row['pre-fixed inputs'] += len(pre)
            for v1 in pre:
                u_ = v1; ep = True
                while True:
                    g = F[z][u_]
                    if le[g][z] or le[u_][g]: break
                    u_ = g; ep = False
                y = u_
                if not le[F[z][y]][z]: row['upper'] += 1; continue
                row['endpoint' if ep else 'shadow'] += 1
                if inR(y, s): row['early'] += 1; continue
                if not fib(z, y): row['empty child fibre'] += 1; continue
                row['edge'] += 1; edges.add(y)
        C['seeded roots below k'] += 1
        if row['edge'] == 0:                             # dead end: dump and analyse the upper outcomes (A-transitions)
            import json; json.dump(dict(sets=L.S, F=F, m=m, r=r, z=z), open(f'seeded_deadend_min{n}.json', 'w'))
            ups_k = any(h[x] == k and inR(x, k) and any(le[x][y] and y != x and not le[m][y] and (le[F[x][y]][x] or le[y][F[x][y]]) for y in range(n)) for x in range(n))
            for v in S:
                for v1 in range(n):
                    if not (le[z][v1] and v1 != z and le[v1][v] and le[F[z][v1]][v1]): continue
                    u_ = v1
                    while True:
                        g = F[z][u_]
                        if le[g][z] or le[u_][g]: break
                        u_ = g
                    if le[u_][F[z][u_]]:
                        az = a_of(L, F, z)
                        C[('dead-end root: upper outcome', 'y = a(z)', u_ == az, 'h(y) − h(z)', h[u_] - h[z], 'y new at its stage', inR(u_, h[u_]) and not inR(u_, h[u_] - 1),
                           'y has an upward cell away from m', any(le[u_][yy] and yy != u_ and not le[m][yy] and (le[F[u_][yy]][u_] or le[yy][F[u_][yy]]) for yy in range(n)),
                           'UpCell at stage k', ups_k)] += 1
        C[('root has an edge', row['edge'] > 0)] += 1
        # Mixed A/B graph exactly as in Lean (`SeedEdge` with any source, `AEdge`); node = a top c new at stage h(c).
        new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
        sib = lambda pp, cc: new(cc, h[cc]) and inR(pp, h[cc] - 1) and h[pp] == h[cc] - 1 and le[pp][cc] and pp != cc and F[pp][cc] == pp and bool(fib(pp, cc))
        def bkids(c):
            out = set(); j1 = h[c]
            for pp in range(n):
                if not sib(pp, c): continue
                for v in fib(pp, c):
                    for v1 in range(n):
                        if not (le[c][v1] and v1 != c and le[v1][v] and le[F[c][v1]][v1]): continue
                        cands = {v1} | {F[c][u1] for u1 in range(n) if le[c][u1] and u1 != c and le[u1][v1] and le[F[c][u1]][u1]}
                        out |= {y for y in cands if le[y][v1] and le[F[c][y]][c] and new(y, j1 + 1) and sib(c, y)}
            return out
        akids = lambda c: {y for y in range(n) if le[c][y] and y != c and le[y][F[c][y]] and not le[m][y] and new(y, h[c] + 1)}
        upcell = lambda c: any(le[c][y] and y != c and not le[m][y] and (le[F[c][y]][c] or le[y][F[c][y]]) for y in range(n))
        seen = {z}; todo = [z]; deads = []; usedA = False
        while todo:
            c = todo.pop(); kb, ka = bkids(c), akids(c)
            if h[c] < k and not kb and not ka: deads.append(c)
            if kb - ka and False: pass
            for y in kb | ka:
                if h[y] <= k and y not in seen: seen.add(y); todo.append(y)
            usedA |= bool(ka - kb)
        term = [c for c in seen if h[c] == k and upcell(c)]
        C[('mixed graph', 'root had a B-edge', row['edge'] > 0, 'reaches a stage-k UpCell top', bool(term), 'mixed dead ends below k', len(deads), 'A-only edges used', usedA)] += 1
        # Top graph: c → y iff SibConfig(c, y) or AEdge(c, y) (contains the mixed graph: SeedEdge p c y ⇒ SibConfig c y).
        skids = lambda c: {y for y in range(n) if sib(c, y)}
        seen2 = {z}; todo = [z]; deads2 = []
        while todo:
            c = todo.pop(); kk = skids(c) | akids(c)
            if h[c] < k and not kk: deads2.append(c)
            for y in kk:
                if h[y] <= k and y not in seen2: seen2.add(y); todo.append(y)
        term2 = [c for c in seen2 if h[c] == k and upcell(c)]
        if deads2: json.dump(dict(sets=L.S, F=F, m=m, r=r, z=z, dead=deads2), open(f'seeded_topdead_min{n}.json', 'w'))
        bad = [c for c in seen2 if h[c] == k and not upcell(c)]
        if bad: json.dump(dict(sets=L.S, F=F, m=m, r=r, z=z, bad=bad), open(f'seeded_badterm_min{n}.json', 'w'))
        C[('top graph', 'reaches a stage-k UpCell top', bool(term2), 'dead ends below k', len(deads2), 'every reached stage-k top is UpCell', all(upcell(c) for c in seen2 if h[c] == k))] += 1
        if row['edge'] == 0:
            path_ok = any(h[c] == k for c in seen)
            C[('B-dead-end root, mixed graph', 'reachable tops', len(seen), 'stage-k tops reached', path_ok)] += 1
        TABLE.append((n, k - s, dict(row)))
        if lastdrop:
            q, ed, t = lastdrop
            C[('descent data', 'r = b(q)', r == B(q), 'z = F(r, e)', z == F[r][ed], 'e in the root fibre', ed in S, 't vs z', rel(t, z), 't ≤ e', le[t][ed])] += 1
            if ed in S and le[z][t] and t != z and le[t][ed] and le[F[z][t]][t]:
                u_ = t
                while True:
                    g = F[z][u_]
                    if le[g][z] or le[u_][g]: break
                    u_ = g
                C[('descent data (v, v′) = (e, t)', 'gives an edge', le[F[z][u_]][z] and not inR(u_, s) and bool(fib(z, u_)), 'child = some edge child', u_ in edges)] += 1
            else:
                C[('descent data (v, v′) = (e, t)', 'not a candidate pair', 't row-z pre-fixed', le[F[z][t]][t] if le[z][t] else None)] += 1
            C[('q vs the edge children', tuple(sorted(rel(y, mp) for y in edges)))] += 1
        break
for k_, v in sorted(C.items(), key=str): print(k_, v)
for t_ in TABLE: print('TABLE', t_)
