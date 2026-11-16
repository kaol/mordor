"""Cross-evaluation shadows and source meets (log §34.3z¹⁷⁴; brief "Cross-source corroboration").

For every remaining-case configuration (multi, nopostlayer, rank ≥ R) and every feeder-like top x that is new at
stage k (b(x) = p ∈ R_{k−1}, p < x, x ∉ R_{k−1}; then p ⋖ x by `strictBTop_has_cover_source`): for every drop column u of the row x (x < u, F(x, u) ≤ u, x ≰ F(x, u), m ≰ u) the shadow
c = F(p, u) (`cross_shadow`: p < c ≤ F(x, u) ≤ u, c ∥ x) and the brief's candidate claims
  (1) c ∈ R_{k+1};  (2) b(c) ∈ R_{k−1};  (3) b(c) comparable with p;
and for every pair of feeder-like tops x, y with incomparable sources p ∥ q:
  (4) p ⊔ q ∈ R_k (a common upper source inside R_k);  (5) the meet pair (b(x ⊓ y), x ⊓ y) is strict, b(x ⊓ y) < x ⊓ y.
A model refutes a claim when one instance fails.   python3 shadow_probe.py [rmin=R] [save] (sweep … | closure …)
"""
import sys, collections, json
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, a_of, b_of
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
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        B = lambda y: b_of(L, F, y)
        Tk = [x for x in range(n) if inR(x, k) and h[x] == k]
        FLall = [x for x in Tk if inR(B(x), k - 1) and le[B(x)][x] and B(x) != x]
        for x in FLall: C[('feeder-like top', 'new at stage k' if not inR(x, k - 1) else 'early (in R_{k−1})', 'p ⋖ x', h[B(x)] == k - 1)] += 1
        mp_ = B(m); C[('feeder m′', 'new' if not inR(mp_, k - 1) else 'early', 'b(m′) ⋖ m′', h[B(mp_)] == k - 1)] += 1
        FL = [x for x in FLall if not inR(x, k - 1)]           # strictBTop_has_cover_source needs x new at stage k
        C['models'] += 1; fails = collections.Counter()
        for x in FL:
            p = B(x)
            assert h[p] == k - 1                       # strictBTop_has_cover_source
            for u in range(n):
                if not (le[x][u] and u != x and le[F[x][u]][u] and not le[x][F[x][u]] and not le[m][u]): continue
                c = F[p][u]; assert le[p][c] and c != p and le[c][F[x][u]] and rel(c, x) == '∥'   # cross_shadow
                C['shadows'] += 1
                ok = {'(1) c ∈ R_{k+1}': inR(c, k + 1), '(2) b(c) ∈ R_{k−1}': inR(B(c), k - 1), '(3) b(c) comparable with p': rel(B(c), p) != '∥'}
                for nm_, v in ok.items():
                    C[(nm_, v)] += 1
                    if not v: fails[nm_] += 1
                C[('shadow c', f'h−k={h[c] - k}', f'stage−k={st[c] - k if st[c] is not None else None}')] += 1
        for i, x in enumerate(FL):
            for y in FL[i + 1:]:
                p, q = B(x), B(y)
                if rel(p, q) != '∥': continue
                C['independent source pairs'] += 1
                d = L.meet[x][y]; s_ = B(d)
                ok = {'(4) p ⊔ q ∈ R_k': inR(L.join[p][q], k), '(5) b(x ⊓ y) < x ⊓ y': le[s_][d] and s_ != d}
                for nm_, v in ok.items():
                    C[(nm_, v)] += 1
                    if not v: fails[nm_] += 1
                C[('meet pair', 'h(x ⊓ y)−k', h[d] - k, 'b(x⊓y) vs p⊓q', rel(s_, L.meet[p][q]))] += 1
        for nm_ in fails:
            C[(nm_, 'refuting models')] += 1
            if 'save' in sys.argv and (nm_ not in smallest or n < smallest[nm_][0]):
                smallest[nm_] = (n, dict(sets=L.S, F=F, m=m))
        break
for k_, v in sorted(C.items(), key=str): print(k_, v)
for nm_, (n_, d) in smallest.items():
    fn = 'shadow_claim%s_min%d.json' % (nm_[1], n_); json.dump(d, open(fn, 'w')); print('saved', fn, 'for', nm_)
