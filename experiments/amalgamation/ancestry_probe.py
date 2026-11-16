"""Entry histories of the top rows in the residual no-cell configuration (log §34.3z¹⁷³; brief "Ancestry
synchronization and UpCell").

For every remaining-case configuration (multi, nopostlayer, rank ≥ R), every top x ∈ T_k (h(x) = k = K − 1, x ∈ R_k):
entry route at stage k (A-image x = a(p), p ∈ R_{k−1}; B-entry b(x) ∈ R_{k−1}), normal-form data, whether x is an
UpCell witness (a cell at a column z > x, m ≰ z) and of which type, and the relations of its sources with the
feeder's.   python3 ancestry_probe.py [rmin=R] (sweep … | closure …)
"""
import sys, collections
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, a_of, b_of
from tight_probe import lattices
import single_claims as sc

C = collections.Counter()
for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(1, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        A = lambda x: a_of(L, F, x); B = lambda y: b_of(L, F, y)
        mp = B(m); Tk = [x for x in range(n) if inR(x, k) and h[x] == k]
        def upcells(x): return [(z, 'L' if le[F[x][z]][x] else 'U') for z in range(n) if le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]])]
        def route(x):
            ra = [p for p in range(n) if inR(p, k - 1) and A(p) == x]
            rb = inR(B(x), k - 1)
            return ('A' if ra else '') + ('B' if rb else ''), ra
        C['models'] += 1
        wit = [x for x in Tk if upcells(x)]
        C[('model: witnesses', len(wit) > 0)] += 1
        for x in Tk:
            r_, ra = route(x); w_ = bool(upcells(x))
            tag = 'feeder' if x == mp else ('witness' if w_ else 'non-witness')
            C[(tag, 'route', r_)] += 1
            C[(tag, 'x vs m', rel(x, m))] += 1
            if 'B' in r_: C[(tag, 'b(x) vs x', rel(B(x), x))] += 1; C[(tag, 'b(x) vs b(m′)', rel(B(x), B(mp)))] += 1
            if 'A' in r_: C[(tag, 'A-source p vs x', rel(ra[0], x))] += 1
            C[(tag, 'diag', 'pre' if le[F[x][x]][x] else 'neither')] += 1
            if w_:
                cs = upcells(x); C[('witness cell types', ''.join(sorted({t for _, t in cs})))] += 1
            if tag != 'feeder':
                C[(tag, 'shares B-source with feeder', 'B' in r_ and B(x) == B(mp))] += 1
                C[(tag, 'x ⊓ m′ vs b(m′)', rel(L.meet[x][mp], B(mp)))] += 1
        C[('feeder: b(m′) vs m′', rel(B(mp), mp))] += 1
        from gfp_top import ystar
        w = F[m][ystar(L, F, m)]
        drop = any(le[mp][u] and u != mp and le[u][w] and le[F[mp][u]][u] and not le[mp][F[mp][u]] for u in range(n))
        if drop:
            C[('DROP models', 1)] += 1
            sib = [x for x in Tk if x != mp and inR(B(x), k - 1) and B(x) == B(mp)]
            C[('DROP: feeder is a witness', bool(upcells(mp)))] += 1
            C[('DROP: some sibling (b(x) = b(m′)) is a witness', any(upcells(x) for x in sib))] += 1
            C[('DROP: some witness x with b(x) ∈ R_{k−1}, b(x) < x', any(upcells(x) and inR(B(x), k - 1) and le[B(x)][x] and B(x) != x for x in Tk))] += 1
            C[('DROP: some witness x with b(x) ≤ b(m′)', any(upcells(x) and le[B(x)][B(mp)] for x in Tk))] += 1
            C[('DROP: some witness x with b(x) ≤ m′', any(upcells(x) and le[B(x)][mp] for x in Tk))] += 1
            for x in wit: C[('DROP witness', 'b(x) vs m′', rel(B(x), mp), 'b(x) vs b(m′)', rel(B(x), B(mp)))] += 1
        C[('witness rows: some B-route witness with b(x) < x', any('B' in route(x)[0] and le[B(x)][x] and B(x) != x for x in wit))] += 1
        C[('witness rows: some A-image witness', any('A' in route(x)[0] for x in wit))] += 1
        break
for k_, v in sorted(C.items(), key=str): print(k_, v)
