"""Smallest rank-3 remaining-case configuration (multi, nopostlayer) with a late cell parent of a second top
over closure 5 10 SEED 10, SEED = 1..3 (log §34.3z¹⁶⁷); writes late_parent_config_min<n>.json.  python3 find_late.py"""
import sys, json
sys.argv += ['multi', 'nopostlayer', 'rmin=3']
sys.path.insert(0, '.'); sys.path.insert(0, '../separation')
from rstages import stages, a_of, b_of
from tight_probe import lattices
import single_claims as sc
best = None
for seed in (1, 2, 3):
    for L in lattices(['closure', '5', '10', str(seed), '10']):
        for m in range(L.n):
            if not (3 <= L.rank[m] < L.height): continue
            F = sc.query(L, m, 'noic_fi', False)
            if not F: continue
            st = stages(L, F); K = L.rank[m]; inR = lambda x, j: st[x] is not None and st[x] <= j
            tops = [z for z in range(L.n) if z != m and L.rank[z] == K and inR(z, K)]
            late = [z for z in tops if any(L.rank[x] < K - 1 and inR(x, K - 1) and (L.le[F[x][z]][x] or L.le[z][F[x][z]]) for x in range(L.n))]
            if late and (best is None or L.n < best[0]): best = (L.n, dict(sets=L.S, F=F, m=m))
            break
json.dump(best[1], open('late_parent_config_min%d.json' % best[0], 'w')); print(best[0])
