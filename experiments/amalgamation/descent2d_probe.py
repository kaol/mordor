"""Two-dimensional descent (log §34.3z¹⁸⁰; `cellState_cell`, `feeder_cell_dichotomy`).

From the feeder state (m′, w) of every remaining-case configuration (multi, nopostlayer, rank ≥ R), replay the
descent: same-row step (r, e) ↦ (r, F(r, e)) when r < F(r, e) < e; source step (r, e) ↦ (b r, F(b r, e)) when
F(r, e) ∥ r; stop at a lower cell (F(r, e) ≤ r, or F(b r, e) ≤ b r at column e) or an upper cell (e ≤ F(r, e)).
Record the path, the final depth i (row b^[i] m′) and cell orientation, the final column's stage status, and
whether the cell lifts (depth 0 = UpCell; at depth 1 with a new top column: does that column have an UpCell).
  python3 descent2d_probe.py [rmin=R] (sweep … | closure …)
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
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        B = lambda y: b_of(L, F, y)
        mp = B(m); w = F[m][ystar(L, F, m)]
        ups = lambda y: [z for z in range(n) if le[y][z] and z != y and not le[m][z] and (le[F[y][z]][y] or le[z][F[y][z]])]
        r, e, i, rows, cols = mp, w, 0, 0, 0
        while True:
            t = F[r][e]
            if le[t][r]: typ = 'L'; z = e; break
            if le[e][t]: typ = 'U'; z = e; break
            if le[r][t]: e = t; cols += 1; continue
            q = B(r); assert le[q][r] and q != r              # dropNode_source_lt
            e2 = F[q][e]
            if le[e2][q]: typ = 'L'; r = q; z = e; i += 1; break
            r, e, i = q, e2, i + 1; rows += 1
        assert le[r][z] and r != z and (le[F[r][z]][r] or le[z][F[r][z]])    # cellState_cell
        C['configurations'] += 1
        C[('final', 'depth', i, 'type', typ)] += 1
        C[('path', 'same-row steps', cols, 'source steps (before the final one)', rows)] += 1
        s = st[r]
        C[('final row', 'h = k − depth', h[r] == k - i, 'new at its stage', s == 0 or not inR(r, s - 1))] += 1
        if i == 0:
            C[('depth 0: UpCell of the feeder (proved)', bool(ups(mp)))] += 1
        else:
            zs = st[z]
            stat = 'outside R' if zs is None else ('early' if zs < h[z] else 'on time' if zs == h[z] else 'late')
            C[('depth ≥ 1 final column', 'type', typ, 'h(z) − h(r)', h[z] - h[r], 'stage status', stat)] += 1
            if typ == 'L' and i == 1 and h[z] == k and inR(z, k):
                newz = not inR(z, k - 1)
                C[('depth-1 L, column a top of R_k', 'new', newz, 'b(z) = b(m′)', B(z) == mp if False else B(z) == B(mp), 'z has UpCell', bool(ups(z)))] += 1
            if typ == 'U':
                C[('depth ≥ 1 U-cell', 'z = a(r)', a_of(L, F, r) == z, 'z ≤ a(r)', le[z][a_of(L, F, r)])] += 1
        wit = [y for y in range(n) if inR(y, k) and h[y] == k and ups(y)]
        C[('witness rows vs final', 'some witness ≥ r', any(le[r][y] for y in wit), 'some witness ≥ z', any(le[z][y] for y in wit),
           'some witness with b(y) = b^[i] m′', any(B(y) == r for y in wit))] += 1
        break
for k_, v in sorted(C.items(), key=str): print(k_, v)
