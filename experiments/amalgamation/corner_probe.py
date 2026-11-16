"""Cross-corner diagnostics for CanonicalTopParent (log §34.3z¹⁶⁹; brief "Prove CanonicalTopParent").

On the rank-≥3 remaining-case configurations (multi, nopostlayer; K = h(m) = k + 1): the feeder m′ = b(m), y*,
w = F(m, y*), s = F(m′, y*), d* (descending D-orbit u ↦ m′ ⊔ F(m′, u) from y*), the row gfp a(m′) and the B-sources
b(s), b(w), b(a(m′)); which canonical mechanism holds (A: y ∈ T_k with a(y) ≠ m a top; B: a top z ≠ m with
b(z) ∈ R_k, b(z) ≤ z) and how its witnesses sit relative to the named elements.
  python3 corner_probe.py [rmin=R] (sweep … | closure …)
"""
import sys, collections
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, a_of, b_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc

C = collections.Counter()
for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(1, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; jn = L.join; h = L.rank; K = h[m]; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        A = lambda x: a_of(L, F, x); B = lambda y: b_of(L, F, y)
        mp = B(m); ys = ystar(L, F, m); w = F[m][ys]; s = F[mp][ys]
        d = ys
        while jn[mp][F[mp][d]] != d: d = jn[mp][F[mp][d]]
        def cls(x):                                         # height relative to K, stage, membership
            return f"h−K={h[x] - K}, stage−K={None if st[x] is None else st[x] - K}"
        def route(x):
            s_ = st[x]
            if s_ is None or s_ == 0: return 'base'
            return ('A' if any(inR(p, s_ - 1) and le[x][A(p)] for p in range(n)) else '') + ('B' if inR(B(x), s_ - 1) else '')
        Tk = [y for y in range(n) if inR(y, K - 1) and h[y] == K - 1]
        tops = [z for z in range(n) if z != m and h[z] == K and inR(z, K)]
        mA = [y for y in Tk if A(y) != m and h[A(y)] == K]
        mB = [z for z in tops if inR(B(z), K - 1) and le[B(z)][z]]
        C['models'] += 1
        C[('mechanism', 'A' if mA else '-', 'B' if mB else '-')] += 1
        am = A(mp)
        C[('a(m′)', cls(am))] += 1; C[('a(m′) route', route(am))] += 1; C[('a(m′) vs m′', rel(am, mp))] += 1
        C[('a(m′) vs w', rel(am, w))] += 1; C[('b(a(m′)) vs m′', rel(B(am), mp))] += 1
        C[('m′ is an A-witness', mp in mA)] += 1
        C[('s vs m′', rel(s, mp))] += 1; C[('s vs w', rel(s, w))] += 1; C[('s', cls(s))] += 1
        C[('b(s) ≤ s', le[B(s)][s])] += 1; C[('b(s) ∈ R_{K−1}', inR(B(s), K - 1))] += 1; C[('b(s) vs m′', rel(B(s), mp))] += 1
        C[('b(w) ≤ w', le[B(w)][w])] += 1; C[('b(w) ∈ R_{K−1}', inR(B(w), K - 1))] += 1; C[('b(w) vs m′', rel(B(w), mp))] += 1
        C[('w', cls(w))] += 1; C[('d*', cls(d))] += 1; C[('d* vs w', rel(d, w))] += 1; C[('a(s) vs s', rel(A(s), s))] += 1
        u = w                                               # row-m′ descent from w to its first cell (row_cell_descent)
        while not (le[F[mp][u]][mp] or le[u][F[mp][u]]): u = F[mp][u]
        C[('descent u', cls(u))] += 1; C[('descent u cell', 'lower' if le[F[mp][u]][mp] else 'upper')] += 1
        hab = all(le[mp][F[mp][x]] for x in range(n) if le[mp][x] and x != mp and le[x][w] and le[F[mp][x]][x])
        C[('habove: m′ ≤ F(m′,u) for all row-pre-fixed u ∈ (m′, w]', hab)] += 1
        C[('habove or descent u > m′', 'habove', hab, 'u > m′', le[mp][u] and u != mp)] += 1
        def hab_xv(x, v): return all(le[x][F[x][q]] for q in range(n) if le[x][q] and q != x and le[q][v] and le[F[x][q]][q])
        gen = [(x, v) for x in Tk for v in range(n) if le[x][v] and v != x and le[F[x][v]][v] and not le[m][v] and hab_xv(x, v)]
        C[('general descent witness (x ∈ T_k, v ≱ m) exists', bool(gen))] += 1
        if not hab:
            C[('drop case: mechanism', 'A' if mA else '-', 'B' if mB else '-')] += 1
            C[('drop case: general descent witness exists', bool(gen))] += 1
            C[('drop case: witness row x = m′', any(x == mp for x, v in gen))] += 1
            dr = [q for q in range(n) if le[mp][q] and q != mp and le[q][w] and le[F[mp][q]][q] and not le[mp][F[mp][q]]]
            for q in dr: C[('drop case: F(m′,q) vs m′', rel(F[mp][q], mp), 'F(m′,q) vs q', rel(F[mp][q], q))] += 1
        C[('descent u = w', u == w)] += 1; C[('descent u vs m′', rel(u, mp))] += 1
        C[('descent u is a second top', u in tops)] += 1
        C[('descent u is a second top or mechanism A', u in tops or bool(mA))] += 1
        for z in mB:
            C[('B-witness z vs', 'm′', rel(z, mp), 'w', rel(z, w), 's', rel(z, s))] += 1
            C[('B-witness b(z) vs m′', rel(B(z), mp))] += 1; C[('B-witness b(z) diag', 'pre' if le[F[B(z)][B(z)]][B(z)] else 'not pre')] += 1
        for y in mA:
            C[('A-witness y vs m′', rel(y, mp))] += 1; C[('A-witness a(y) vs w', rel(A(y), w))] += 1
            C[('A-witness y diag', 'pre' if le[F[y][y]][y] else 'not pre')] += 1
        if not mA:
            C[('A fails: B-witness count', len(mB))] += 1
            for z in mB: C[('A fails: B-witness b(z) = m′', B(z) == mp)] += 1
        break
for k, v in sorted(C.items(), key=str): print(k, v)
