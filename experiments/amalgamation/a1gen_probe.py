"""Which A1Cert exists under the row-type restrictions (log §34.3z²⁰¹).

Models: SAT models of 'a1gen rowtypes' (MinUpCell hypotheses, the ¬UpCell row types imposed, a genuine A1 configuration
(p = b(c) ⋖ c, c non-ascending) with a fibre column), every qualifying m. For each genuine configuration (p, c, u):
whether it certifies itself (some z ∈ (c, u] is a cell of row c, or pre-fixed with (c, z] exception-free); if not,
which configuration (p′, c′, u′, z) does: c′ vs c and vs a(c), p′ vs p; and the kind of certificate (cell / pre-fixed).
   python3 a1gen_probe.py [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
sys.argv += ['multi', 'notop', 'nofeeder', 'notightK1', 'rowtypes']
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
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
        best[tag] = n; json.dump(d, open(f'a1g_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'rowtypes')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'a1gen', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F); jn = L.join
        inR = lambda x, j: st[x] is not None and st[x] <= j
        A = lambda x: a_of(L, F, x); B = lambda x: b_of(L, F, x)
        rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        def certs(p, c, u):
            out = []
            for z in range(n):
                if not (le[c][z] and z != c and le[z][u]): continue
                if le[F[c][z]][c] or le[z][F[c][z]]: out.append((z, 'cell'))
                elif le[F[c][z]][z] and not any(le[c][e] and e != c and le[e][z] and F[p][e] == p for e in range(n)): out.append((z, 'pre-fixed, clean'))
            return out
        allcfg = [(p, c, u) for c in X for p in L.covers_dn[c] if F[p][c] == p
                  for u in range(n) if le[c][u] and u != c and not le[m][u] and F[p][u] == c]
        gen = [(p, c, u) for (p, c, u) in allcfg if B(c) == p and not le[c][A(c)]]
        if not gen: continue
        C['models'] += 1
        D = dict(sets=L.S, F=F, m=m)
        for (p, c, u) in gen:
            own = certs(p, c, u)
            t = F[c][u]
            cells = [z for z in range(n) if le[c][z] and z != c and not le[m][z] and (le[F[c][z]][c] or le[z][F[c][z]])]
            C[('genuine configuration: cell at u', u in cells, 'u is a lower / upper cell', ('lower' if le[F[c][u]][c] else 'upper') if u in cells else None,
               'cell at t = F(c,u)', t in cells, 'some cell ≤ u', any(le[z][u] for z in cells), 'some upper cell', any(le[z][F[c][z]] for z in cells),
               'some lower cell', any(le[F[c][z]][c] for z in cells), 't vs u', rl(t, u))] += 1
            if not cells: keep('selfnocell', n, dict(D, p=p, c=c, u=u))
            if own:
                C[('genuine configuration certifies itself', True, 'kinds', tuple(sorted({k_ for _, k_ in own})))] += 1; continue
            others = [(p2, c2, u2, z, kd) for (p2, c2, u2) in allcfg for (z, kd) in certs(p2, c2, u2)]
            if not others: C[('genuine configuration', 'NO certificate in the model')] += 1; keep('nocert', n, dict(D, p=p, c=c, u=u)); continue
            p2, c2, u2, z, kd = others[0]
            C[('genuine configuration certifies itself', False, 'certifying top c′ vs c', rl(c2, c), 'c′ vs a(c)', rl(c2, A(c)), 'same top, other column', c2 == c,
               'c′ genuine', B(c2) == p2 and not le[c2][A(c2)], 'kind', kd)] += 1
            keep('other_cert', n, dict(D, p=p, c=c, u=u))
report()
