"""Witness provenance for side entry (log §34.3z¹⁶⁴; brief "Collective side-entry from the previous generation").

mode 'ahead': the one-stage-ahead no-cell models (single_claims.py noic_fi ahead; m ∈ R_J, J = h(m) − 1). For every
  A-route witness x ∈ R_J with w ≤ a(x) record height, entry stage and route, maximality in R_J, the relation to m′, m,
  w, d*, and whether the witnesses have a least element / a canonical minimal one.
mode 'multi': the index-tight no-cell models with uniqueness of m dropped (single_claims.py noic_fi multi; m ∈ R_K,
  K = h(m)). Record every second on-time element z ≠ m of height K in R_K: its route and its relation to m′, m, w, y*.
A universal claim is refuted by any model where it fails; 'True' counts are per model (one SAT model per lattice).
  python3 witness_probe.py MODE (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections
mode = sys.argv[1]; args = sys.argv[2:]
if mode == 'multi': sys.argv.append('multi')
sys.path.insert(0, '../separation')
from rstages import stages, a_of, b_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); ex = []
for L in lattices(args):
    if L.height < 2: continue
    for m in range(L.n):
        if not (1 <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', mode == 'ahead')
        if not F: continue
        n = L.n; le = L.le; jn = L.join; h = L.rank; st = stages(L, F)
        A = lambda x: a_of(L, F, x); B = lambda y: b_of(L, F, y)
        inR = lambda z, j: st[z] is not None and st[z] <= j
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        mp = B(m); K = h[m]; ys = ystar(L, F, m); w = F[m][ys]
        d = ys
        while jn[mp][F[mp][d]] != d: d = jn[mp][F[mp][d]]
        def route(z):                      # how z enters at its stage s: 'a' (z ≤ a(x), x ∈ R_{s−1}), 'b' (z ≤ y, b(y) ∈ R_{s−1})
            s = st[z]
            if s == 0: return 'base'
            ra = any(inR(x, s - 1) and le[z][A(x)] for x in range(n)); rb = any(inR(B(y), s - 1) and le[z][y] for y in range(n))
            return 'ab' if ra and rb else 'a' if ra else 'b'
        C['models'] += 1
        if mode == 'ahead':
            J = st[m]; RJ = [x for x in range(n) if inR(x, J)]
            X = [x for x in RJ if le[w][A(x)]]
            mx = lambda x: not any(inR(y, J) and y != x and le[x][y] for y in range(n))
            C[('A-route exists', bool(X))] += 1
            C[('some maximal witness', any(mx(x) for x in X))] += 1
            C[('all maximal R_J elements are witnesses', all(x in X for x in RJ if mx(x)))] += 1
            mins = [x for x in X if not any(y != x and le[y][x] for y in X)]
            C[('witnesses have a least element', len(mins) == 1)] += 1
            for x in X:
                C[('witness height − J', h[x] - J)] += 1; C[('witness stage − J', st[x] - J)] += 1
                C[('witness route', route(x))] += 1
                for nm_, t in (("m′", mp), ('m', m), ('w', w), ('d*', d)): C[('witness vs ' + nm_, rel(x, t))] += 1
            for x in mins:
                C[('minimal witness route', route(x))] += 1
                C[('minimal witness: x ≤ m′', le[x][mp])] += 1; C[('minimal witness: x ⊓ m = ⊥', L.meet[x][m] == L.bot)] += 1
            C[('w ≤ a(m) (m itself a witness)', m in X)] += 1
            T = [x for x in X if h[x] <= J]          # witnesses admissible at an index-tight stage (height ≤ stage)
            C[('tight-admissible witness (h(x) ≤ J) exists', bool(T))] += 1
            C[('tight-admissible witness exists, or B-route', bool(T) or any(le[w][y] and inR(B(y), J) for y in range(n)))] += 1
            C[('tight-admissible witness ≱ m exists', any(not le[m][x] for x in T))] += 1
            for x in T: C[('tight-admissible witness route', route(x))] += 1; C[('tight-admissible witness vs m', rel(x, m))] += 1
            C[('some witness ≤ m′', any(le[x][mp] for x in X))] += 1
            C[('some witness ≤ m', any(le[x][m] for x in X))] += 1
            C[('some witness ≤ w', any(le[x][w] for x in X))] += 1
        else:
            Z = [z for z in range(n) if z != m and h[z] == K and inR(z, K)]
            C[('second elements', len(Z))] += 1
            for z in Z:
                C[('second route', route(z))] += 1
                for nm_, t in (("m′", mp), ('m', m), ('w', w), ('y*', ys)): C[('second vs ' + nm_, rel(z, t))] += 1
            C[('some second z ≤ w', any(le[z][w] for z in Z))] += 1
            C[('some second z ≥ m′', any(le[mp][z] for z in Z))] += 1
            C[('some second z ≤ m ⊔ w', any(le[z][jn[m][w]] for z in Z))] += 1
            C[('some second z with z ⊓ m ≤ m′', any(le[L.meet[z][m]][mp] for z in Z))] += 1
            C[('some second z ∥ all of m′, m, w', any(rel(z, t) == '∥' for t in (mp, m, w) for _ in [0]) and any(all(rel(z, t) == '∥' for t in (mp, m, w)) for z in Z))] += 1
            C[('w on time (w ∈ R_{h(w)})', inR(w, h[w]))] += 1; C[('h(w) − K', h[w] - K)] += 1
        break
for k, v in sorted(C.items(), key=str): print(k, v)
