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
        origin, u_prev = 'start', None
        path = [(r, e)]                       # how the current column arose: 'start' / 'path' (row value) / 'shadow'
        while True:
            t = F[r][e]
            if le[t][r]: typ = 'L'; z = e; break
            if le[e][t]: typ = 'U'; z = e; break
            if le[r][t]: u_prev = e; e = t; cols += 1; origin = 'path' if i == 0 else 'shadow'; path.append((r, e)); continue
            q = B(r); assert le[q][r] and q != r              # dropNode_source_lt
            e2 = F[q][e]
            if le[e2][q]: typ = 'L'; r = q; z = e; i += 1; origin = 'feeder path (F(b m′, e) ≤ b m′ at e)' if i == 1 else origin; break
            u_prev = e; r, e, i = q, e2, i + 1; rows += 1; origin = 'shadow'; path.append((r, e))
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
                if newz:
                    sub = 'shadow z = F(b m′, u)' if origin == 'shadow' else origin
                    comp = None
                    if origin == 'shadow':
                        assert F[r][u_prev] == z
                        comp = any(le[z][y] and y != z and le[y][u_prev] and (le[F[z][y]][y] or le[y][F[z][y]]) for y in range(n))
                    C[('depth-1 L new column', 'origin', sub, 'siblingShadow_upCell applies', comp, 'z has UpCell', bool(ups(z)))] += 1
                C[('depth-1 L, column a top of R_k', 'new', newz, 'b(z) = b(m′)', B(z) == mp if False else B(z) == B(mp), 'z has UpCell', bool(ups(z)))] += 1
            if typ == 'U':
                C[('depth ≥ 1 U-cell', 'z = a(r)', a_of(L, F, r) == z, 'z ≤ a(r)', le[z][a_of(L, F, r)])] += 1
        wit = [y for y in range(n) if inR(y, k) and h[y] == k and ups(y)]
        # §34.3z¹⁸²: simulate the climb from the final cell (shadow configurations, climb_step / climb_next_config)
        if i >= 1 and typ == 'L' and origin == 'shadow' and u_prev is not None:
            pc, cc, uc, lvl, res = r, z, u_prev, h[z], None
            while True:
                if inR(cc, lvl - 1): res = 'column early'; break
                vs = [v for v in range(n) if le[cc][v] and v != cc and le[v][uc] and le[F[cc][v]][v]]
                ups_direct = [v for v in range(n) if le[cc][v] and v != cc and le[v][uc] and le[v][F[cc][v]]]
                if lvl == k:
                    res = 'UpCell at stage k' if (vs or ups_direct) else 'stage k, totinc'; break
                if not vs:
                    res = 'upper cell only (break)' if ups_direct else 'totinc (break)'; break
                v = max(vs, key=lambda q: h[q])
                x_, u_ = cc, v; prev = None                    # row_cell_of_above_shadow descent from v
                while True:
                    g = F[x_][u_]
                    if le[g][x_] or le[u_][g]: break
                    prev, u_ = u_, g
                y = u_; lower = le[F[x_][y]][x_]
                if not lower: res = 'upper cell (break)'; break
                if prev is None: res = 'endpoint cell (break)'; break
                if inR(y, lvl): res = 'early shadow (break)'; break
                pc, cc, uc, lvl = cc, y, prev, lvl + 1
            C[('climb from depth', i, 'result', res)] += 1
            def climb(pc, cc, uc, lvl, depth=0):          # search over all choices of v at every level
                if inR(cc, lvl - 1): return 'column early'
                vs = [v for v in range(n) if le[cc][v] and v != cc and le[v][uc] and le[F[cc][v]][v]]
                ud = [v for v in range(n) if le[cc][v] and v != cc and le[v][uc] and le[v][F[cc][v]]]
                if lvl == k: return 'UpCell at stage k' if (vs or ud) else 'stage k, totinc'
                outs = []
                for v in vs:
                    x_, u_ = cc, v; prev = None
                    while True:
                        g = F[x_][u_]
                        if le[g][x_] or le[u_][g]: break
                        prev, u_ = u_, g
                    y = u_
                    if le[F[x_][y]][x_] and prev is not None and not inR(y, lvl):
                        res2 = climb(cc, y, prev, lvl + 1, depth + 1)
                        if res2 == 'UpCell at stage k': return res2
                        outs.append(res2)
                    else: outs.append('break: ' + ('upper' if not le[F[x_][y]][x_] else 'endpoint' if prev is None else 'early shadow'))
                return 'no continuation: ' + ','.join(sorted(set(outs))) if outs else ('upper cell only' if ud else 'totinc')
            C[('climb (search) from depth', i, 'result', climb(r, z, u_prev, h[z]))] += 1
            def climbx(pc, cc, uc, lvl):                 # shadow-interval extension: any u'' ≥ uc with F(pc, u'') = cc, m ≰ u''
                if inR(cc, lvl - 1): return 'column early'
                U = [uu for uu in range(n) if le[uc][uu] and not le[m][uu] and F[pc][uu] == cc]
                best = None
                for uu in U:
                    vs = [v for v in range(n) if le[cc][v] and v != cc and le[v][uu] and le[F[cc][v]][v]]
                    ud = [v for v in range(n) if le[cc][v] and v != cc and le[v][uu] and le[v][F[cc][v]]]
                    if lvl == k:
                        if vs or ud: return 'UpCell at stage k'
                        best = best or 'stage k, totinc'; continue
                    for v in vs:
                        x_, u_ = cc, v; prev = None
                        while True:
                            g = F[x_][u_]
                            if le[g][x_] or le[u_][g]: break
                            prev, u_ = u_, g
                        y = u_
                        if le[F[x_][y]][x_] and prev is not None and not inR(y, lvl):
                            if climbx(cc, y, prev, lvl + 1) == 'UpCell at stage k': return 'UpCell at stage k'
                    best = best or 'stalled'
                return best or 'stalled'
            C[('climb (extended intervals) from depth', i, 'result', climbx(r, z, u_prev, h[z]))] += 1
        if i >= 2:
            ab = [y for y in wit if le[z][y]]
            C[('depth ≥ 2', 'z new at its stage', st[z] is not None and not inR(z, st[z] - 1) if st[z] else None, 'h(z) = k − i + 1', h[z] == k - i + 1)] += 1
            pcols = [ee for _, ee in path]
            def shadow_ok(y):       # y = F(z, u) for some u > y, m ≰ u, with a comparable column of row y in (y, u]
                for uu in range(n):
                    if le[y][uu] and uu != y and not le[m][uu] and F[z][uu] == y:
                        if any(le[y][v] and v != y and le[v][uu] and (le[F[y][v]][v] or le[v][F[y][v]]) for v in range(n)): return 'shadow, comparable'
                        return 'shadow, totinc'
                return 'not a shadow of z'
            wy = [y for y in ab if B(y) == z]
            for idx, (rr, ee) in enumerate(path):
                val = F[z][ee]
                tag = 'witness y' if val in wy else ('top of R_k' if inR(val, k) and h[val] == k else f'h−k={h[val] - k}')
                C[('depth ≥ 2: F(z, path column)', 'path index from end', len(path) - 1 - idx, 'column ≥ z', le[z][ee], 'value', tag)] += 1
            C[('depth ≥ 2: some path column u′ with F(z, u′) a witness y', any(F[z][ee] in wy for _, ee in path))] += 1
            C[('depth ≥ 2: F(z, w) is a witness y', F[z][w] in wy, 'F(z, w) vs z', rel(F[z][w], z))] += 1
            C[('depth ≥ 2 climb', 'best witness y (b(y) = z) status', min([shadow_ok(y) for y in ab if B(y) == z] or ['none']))] += 1
            for y in ab:
                C[('depth ≥ 2 witness y ≥ z', 'y is a path column', y in pcols, 'y = u_prev', y == u_prev, 'y ≤ some path column', any(le[y][ee] for ee in pcols))] += 1
                C[('depth ≥ 2 witness y ≥ z', 'b(y) = z', B(y) == z, 'b(y) vs z', rel(B(y), z), 'y = a(z)', a_of(L, F, z) == y, 'y new', not inR(y, k - 1))] += 1
            C[('depth ≥ 2', 'some witness y ≥ z with b(y) = z', any(B(y) == z for y in ab), 'some witness y ≥ z', bool(ab))] += 1
            C[('depth ≥ 2', 'a(z) a top of R_k ≠ m with UpCell', a_of(L, F, z) in wit and a_of(L, F, z) != m)] += 1
        C[('witness rows vs final', 'some witness ≥ r', any(le[r][y] for y in wit), 'some witness ≥ z', any(le[z][y] for y in wit),
           'some witness with b(y) = b^[i] m′', any(B(y) == r for y in wit))] += 1
        break
for k_, v in sorted(C.items(), key=str): print(k_, v)
