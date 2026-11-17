"""Full-fibre climb, tested on every sibling-shadow configuration (log §34.3z¹⁸³).

A sibling-shadow configuration at stage s ≤ k (K = k + 1 = h(m)): p ∈ R_{s−1} of height s − 1, c ∈ R_s ∖ R_{s−1} of
height s, p ⋖ c, F(p, c) = p, and a nonempty off-target fibre S(p, c; m) = {v : c < v, m ≰ v, F(p, v) = c}.
  FibreTop  (s = k): some v ∈ S(p, c; m) has a column y ∈ (c, v] comparable with F(c, y)   [siblingShadow_upCell]
  FibreStep (s < k): some v ∈ S(p, c; m) and row-c pre-fixed v′ ∈ (c, v] whose shadow-tracking descent ends in a lower
                     cell y, new at stage s + 1, with S(c, y; m) ≠ ∅   [climb_step, climb_next_config]
Counted over all configurations of every remaining-case model (multi, nopostlayer, rank ≥ R).
  python3 fibre_probe.py [rmin=R] [save] (sweep … | closure …)
"""
import sys, collections, json
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, b_of
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); smallest = {}
for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer', 'save') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
        C['models'] += 1; fails = set()
        for s in range(1, k + 1):
            for c in range(n):
                if not (h[c] == s and inR(c, s) and not inR(c, s - 1)): continue
                for p in range(n):
                    if not (h[p] == s - 1 and inR(p, s - 1) and le[p][c] and F[p][c] == p): continue
                    S = fib(p, c)
                    if not S: continue
                    if s == k:
                        ok = any(any(le[c][y] and y != c and le[y][v] and (le[F[c][y]][y] or le[y][F[c][y]]) for y in range(n)) for v in S)
                        C[('FibreTop', ok)] += 1
                        if not ok: fails.add('top')
                    else:
                        ok = False
                        for v in S:
                            for v1 in range(n):
                                if not (le[c][v1] and v1 != c and le[v1][v] and le[F[c][v1]][v1]): continue
                                u_ = v1
                                while True:
                                    g = F[c][u_]
                                    if le[g][c] or le[u_][g]: break
                                    u_ = g
                                if le[F[c][u_]][c] and not inR(u_, s) and fib(c, u_): ok = True; break
                            if ok: break
                        C[('FibreStep', 'stage s − k', s - k, ok)] += 1
                        if not ok: fails.add('step')
        topcfg = [(p, c) for c in range(n) if h[c] == k and inR(c, k) and not inR(c, k - 1)
                  for p in range(n) if h[p] == k - 1 and inR(p, k - 1) and le[p][c] and F[p][c] == p
                  and any(any(le[c][y] and y != c and le[y][v] and (le[F[c][y]][y] or le[y][F[c][y]]) for y in range(n)) for v in fib(p, c))]
        C[('model: some stage-k sibling-shadow configuration satisfies FibreTop', bool(topcfg))] += 1
        for f_ in fails:
            C[(f_, 'refuting models')] += 1
            if 'save' in sys.argv and (f_ not in smallest or n < smallest[f_][0]): smallest[f_] = (n, dict(sets=L.S, F=F, m=m))
        break
for k_, v in sorted(C.items(), key=str): print(k_, v)
for f_, (n_, d) in smallest.items():
    fn = f'fibre_{f_}_fail_min{n_}.json'; json.dump(d, open(fn, 'w')); print('saved', fn)
