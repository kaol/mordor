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
                if inR(c, k) and h[c] == k:                # §34.3z¹⁷⁵: top-shadow trichotomy for v = F(p, c)
                    v = F[p][c]; br = 'v ≤ p' if le[v][p] else 'v = c' if v == c else 'v ∥ p' if not le[p][v] else 'other'
                    C[('top shadow', 'branch', br)] += 1
                    C[('top shadow', 'c new at stage k', not inR(c, k - 1))] += 1
                    if br == 'v ≤ p':
                        C[('A1 (v ≤ p)', 'c new', not inR(c, k - 1), 'b(c) = p', B(c) == p, 'F(p,c) = p', v == p)] += 1
                        j = L.join[x][c]; assert le[j][u] and F[p][j] == c       # sibling join: F(p, x ⊔ c) = c
                        tx, tc = F[x][j], F[c][j]
                        C[('A1 join j = x ⊔ c', 'x upper cell at j', le[j][tx], 'c upper cell at j', le[j][tc])] += 1
                        C[('A1 join j', 'F(x,j) vs j', rel(tx, j), 'F(c,j) vs j', rel(tc, j))] += 1
                        C[('A1 join j', 'some cell of x or c at j', le[j][tx] or le[tx][x] or le[j][tc] or le[tc][c])] += 1
                        cellIn = lambda y: any(le[j][z] and le[z][u] and (le[z][F[y][z]] or le[F[y][z]][y]) for z in range(n))
                        C[('A1 interval [x ⊔ c, u]', 'cell of x', cellIn(x), 'cell of c', cellIn(c))] += 1
                        upc_ = lambda y: any(le[y][z] and z != y and not le[m][z] and (le[z][F[y][z]] or le[F[y][z]][y]) for z in range(n))
                        C[('A1 sibling pair', 'x has UpCell', upc_(x), 'c has UpCell', upc_(c))] += 1
                        assert all(F[p][z] == c for z in range(n) if le[c][z] and z != c and le[z][u])   # F(p, ·) = c on (c, u]
                        fcu = F[c][u]
                        totinc = all(rel(F[c][z], z) == '∥' for z in range(n) if le[c][z] and z != c and le[z][u])
                        C[('A1 row c incomparable on all of (c, u]', totinc)] += 1
                        if totinc:
                            json.dump(dict(sets=L.S, F=F, m=m, x=x, c=c, u=u, p=p), open(f'sibling_totinc_min{n}.json', 'w'))
                            others = [y for y in FL if upc_(y)]
                            C[('A1 totinc: UpCell rows', tuple(sorted(rel(y, x) + '/' + rel(y, c) + ('/same source' if B(y) == p else '/other source') for y in others)))] += 1
                        C[('A1 F(c,u) vs u', rel(fcu, u), 'c has UpCell', upc_(c))] += 1
                        if not le[fcu][u]:                     # clamped descent z ↦ u ⊓ F(c, z) from u
                            z = u
                            while True:
                                nz = L.meet[u][F[c][z]]
                                if nz == z or nz == c: break
                                z = nz
                            out = ('upper cell at gfp > c' if nz == z and z != c else
                                   'lower cell (F(c,z) ≤ u, ⊓ = c)' if le[F[c][z]][u] else 'stuck: F(c,z) ⊓ u = c, F(c,z) ≰ u')
                            C[('A1 clamped descent', out, 'c has UpCell', upc_(c))] += 1
                            t_ = fcu
                            for z in range(n):
                                if le[c][z] and z != c and not le[m][z] and (le[z][F[c][z]] or le[F[c][z]][c]):
                                    C[('A1 ∥ case: c-cell column z', 'vs u', rel(z, u), 'vs t=F(c,u)', rel(z, t_), 'vs u ⊔ t', rel(z, L.join[u][t_]), 'type', 'U' if le[z][F[c][z]] else 'L')] += 1
                            C[('A1 ∥ case', 'm ≤ u ⊔ t', le[m][L.join[u][t_]], 'F(c, u ⊔ t) vs u ⊔ t', rel(F[c][L.join[u][t_]], L.join[u][t_]))] += 1
                    elif br == 'v = c':
                        C[('upper (v = c)', 'c = a(p)', a_of(L, F, p) == c)] += 1
                    else:
                        d = v
                        C[('A2 (v ∥ p)', f'h(d)−k={h[d] - k}', f'stage(d)−k={st[d] - k if st[d] is not None else None}',
                           'diag', 'pre' if le[F[d][d]][d] else 'post' if le[d][F[d][d]] else 'neither')] += 1
                        C[('A2 (v ∥ p)', 'p new top of R_{k−1}', not inR(p, k - 2) and h[p] == k - 1,
                           'b(p) < p with b(p) ∈ R_{k−2}', inR(B(p), k - 2) and le[B(p)][p] and B(p) != p)] += 1
                        C[('A2 (v ∥ p)', 'd vs x', rel(d, x), 'd vs b(c)', rel(d, B(c)))] += 1
        fam = collections.Counter(B(x) for x in FL)          # same-source sibling families S_p (new feeder-like tops)
        for p_, sz in fam.items(): C[('sibling family size |S_p|', sz)] += 1
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
