"""Fibre-join classification of the stage-k sibling-shadow configurations (log §34.3z¹⁸⁹).

For every model (every qualifying m, one SAT model each; as fork_probe.py) and every stage-k configuration (p, c):
p ∈ R_{k−1} of height k − 1, c ∈ R_k ∖ R_{k−1} of height k, p < c, F(p, c) = p, S = S(p, c; m) ≠ ∅. Records:
cover p ⋖ c; whether S is down-closed in (c, ·) (source_row_const); the join U = ⋁S and its case (stable: F(p, U) = c,
m ≰ U; jump); FibreTopAt (a column y ∈ S comparable with F(c, y)); whether the row c has a pre-fixed / post-fixed column
in S; and, per model, TopFibre (some configuration with FibreTopAt).   python3 fibrejoin_probe.py [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
sys.argv += ['multi', 'nopostlayer']
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
        best[tag] = n; json.dump(d, open(f'fj_{tag}_min{n}.json', 'w'))

for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F); jn = L.join
        inR = lambda x, j: st[x] is not None and st[x] <= j
        C['models'] += 1; anytop = False; ncfg = 0
        for c in range(n):
            if not (inR(c, k) and not inR(c, k - 1) and h[c] == k): continue
            for p in range(n):
                if not (inR(p, k - 1) and h[p] == k - 1 and le[p][c] and p != c and F[p][c] == p): continue
                S = [v for v in range(n) if le[c][v] and v != c and not le[m][v] and F[p][v] == c]
                if not S: continue
                ncfg += 1
                cov = c in L.covers_up[p] if hasattr(L, 'covers_up') else h[c] == h[p] + 1
                down = all(F[p][y] == c for v in S for y in range(n) if le[c][y] and y != c and le[y][v])
                U = S[0]
                for v in S[1:]: U = jn[U][v]
                case = 'stable' if (F[p][U] == c and not le[m][U]) else ('jump, m ≤ U' if le[m][U] else 'jump, m ≰ U')
                cmp_ = [y for y in S if le[F[c][y]][y] or le[y][F[c][y]]]
                pre = any(le[F[c][y]][y] for y in S); post = any(le[y][F[c][y]] for y in S)
                maxS = [v for v in S if not any(le[v][u] and u != v for u in S)]
                ft = bool(cmp_); anytop |= ft
                C[('config', 'p ⋖ c', cov, 'S down-closed in (c, ·)', down, 'join', case, '|max S|', min(len(maxS), 3), 'FibreTopAt', ft,
                   'pre-fixed in S', pre, 'post-fixed in S', post)] += 1
                if not ft:
                    g = F[c][U]
                    C[('FibreTop fails', 'join', case, 'F(c, U) vs U', '<' if le[g][U] else '>' if le[U][g] else '∥', 'F(c,U) ∧ U = c', L.meet[g][U] == c)] += 1
                    keep('fail_' + case.split(',')[0], n, dict(sets=L.S, F=F, m=m, p=p, c=c))
        C[('model', 'stage-k configurations', min(ncfg, 3), 'TopFibre', anytop)] += 1
        if ncfg and not anytop: keep('notopfibre', n, dict(sets=L.S, F=F, m=m))
report()
