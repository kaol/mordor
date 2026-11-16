"""Late-parent diagnostics (log §34.3z¹⁶⁷; brief "Eliminate late-parent ancestry").

For every second top z (z ≠ m, h(z) = K, z ∈ R_K; K = k + 1 in Lean indexing) and every fixed-edge parent x ∈ R_{K−1}
(F(x, z) = x: B-edge, F(x, z) = z: A-edge; the brief's TopParent edges) record: height, entry stage, lateness,
edge type, own entry route, the B-source b(x) (comparability, diagonal type), the A-lift a(p) (distinct? still
late?), and the depth of the A-normal form x ≤ a^[i](q) with q terminal (stage 0, or B-entered and not A-entered).
modes:  config [rmin=R] (sweep … | closure …)   uniqueness-free no-cell configurations with no post-fixed top
        file FILE.json ...                      stored models (field m = the distinguished element / the top)
"""
import sys, json, collections
mode = sys.argv[1]
if mode == 'config': sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from tight_probe import lattices
import single_claims as sc

def diag(L, F, x):
    pre = L.le[F[x][x]][x]; post = L.le[x][F[x][x]]
    return 'fixed' if pre and post else 'pre' if pre else 'post' if post else 'neither'

def analyse(L, F, m, C, config=True):
    n = L.n; le = L.le; h = L.rank; K = h[m]; st = stages(L, F)
    inR = lambda x, j: st[x] is not None and st[x] <= j
    rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
    A = lambda x: a_of(L, F, x); B = lambda y: b_of(L, F, y)
    def normal(x):                                  # A-normal form depth: follow A-entries while available
        i, q = 0, x
        while st[q] > 0:
            s = st[q]; src = [p for p in range(n) if inR(p, s - 1) and le[q][A(p)]]
            if not src: return i, q, 'B'
            q = max(src, key=lambda p: h[A(p)]); i += 1
        return i, q, 'bottom'
    tops = [z for z in range(n) if h[z] == K and inR(z, K) and (z != m or not config)]
    C['models'] += 1; anytop = False
    for z in tops:
        par = [x for x in range(n) if inR(x, K - 1) and (F[x][z] == x or F[x][z] == z)]
        on = [x for x in par if h[x] == K - 1]
        anytop |= bool(on)
        C[('top', 'has on-time parent', bool(on))] += 1
        for x in par:
            late = h[x] < K - 1; s = st[x]; tag = 'late' if late else 'on-time'
            edge = ('B' if F[x][z] == x else '') + ('A' if F[x][z] == z else '')
            own = ('A' if s > 0 and any(inR(p, s - 1) and le[x][A(p)] for p in range(n)) else '') + ('B' if s > 0 and inR(B(x), s - 1) else '')
            C[(tag, 'edge', edge)] += 1; C[(tag, 'own entry', own)] += 1; C[(tag, 'h', h[x])] += 1; C[(tag, 'stage', s)] += 1
            if 'B' in own: C[(tag, 'B-source vs x', rel(B(x), x))] += 1; C[(tag, 'B-source diag', diag(L, F, B(x)))] += 1
            C[(tag, 'x diag', diag(L, F, x))] += 1; C[(tag, 'x vs z', rel(x, z))] += 1
            Tk = [y for y in range(n) if inR(y, K - 1) and h[y] == K - 1]
            if 'B' in edge:                            # is the B-parent set up-closed in R_{K−1}? (the A-parent set is: a_parent_up)
                for y in range(n):
                    if inR(y, K - 1) and le[x][y] and y != x: C[('B-up: y ≥ B-parent in R_{K−1} has a fixed edge at z', le[F[y][z]][y] or le[z][F[y][z]])] += 1
            if 'A' in edge:
                for y in range(n):
                    if inR(y, K - 1) and le[x][y]: assert le[z][F[y][z]]   # a_parent_up, checked
            if late:
                C[(tag, 'x below some top of R_{K−1}', any(le[x][y] for y in Tk))] += 1
                C[(tag, 'some top y ≥ x of R_{K−1} has a fixed edge at z', any(le[x][y] and (F[y][z] == y or F[y][z] == z) for y in Tk))] += 1
                C[(tag, edge, 'x below some top', any(le[x][y] for y in Tk))] += 1
            if 'A' in edge and 'A' in own:
                for p in range(n):
                    if inR(p, s - 1) and le[x][A(p)]:
                        ap = A(p); C[(tag, 'A-lift', 'same' if ap == x else ('distinct, late' if h[ap] < K - 1 else 'distinct, on-time'))] += 1
            if 'A' in edge:
                i, q, kind = normal(x); C[(tag, 'A-normal (depth, terminal)', i, kind)] += 1
            if config:
                mp = B(m); C[(tag, 'x vs m′', rel(x, mp))] += 1; C[(tag, 'x vs m', rel(x, m))] += 1
    C[('model', 'some second top with on-time parent', anytop)] += 1
    # §34.3z¹⁶⁸: which mechanism gives TopParent
    Tk = [y for y in range(n) if inR(y, K - 1) and h[y] == K - 1]
    mech_a = any(A(y) != m and h[A(y)] == K for y in Tk)                       # topParent_of_a_top
    mech_bl = any(inR(B(z), K - 1) and le[B(z)][z] for z in tops)              # topParent_of_b_le
    mech_bi = any(F[y][z] == y and not le[y][z] for z in tops for y in Tk)     # on-time B-parent incomparable with z
    C[('mechanism', 'a(y) second top, y ∈ T_k', mech_a, 'b(z) ≤ z', mech_bl, 'on-time B-parent ∥ z', mech_bi)] += 1
    for y in Tk: C[('a(y), y ∈ T_k', 'm' if A(y) == m else 'second top' if h[A(y)] == K else f'height {h[A(y)]} vs K−1 = {K - 1}')] += 1
    if config:
        for z in tops:
            for x in range(n):
                if not (inR(x, K - 1) and h[x] < K - 1): continue
                if F[x][z] == x:                                             # late B-parent: compensation analysis
                    C[('late B-parent x', 'x ≤ z', le[x][z])] += 1
                    for y in Tk:
                        if le[x][y]:
                            c = 'F(y,z)=y' if F[y][z] == y else 'F(y,z)=z' if F[y][z] == z else 'neither'
                            ay = A(y); ca = 'm' if ay == m else 'second top' if h[ay] == K else 'low'
                            C[('compensation', c, 'a(y)', ca)] += 1
                if F[x][z] == z:                                             # late A-parent: terminal root
                    i, q, kind = normal(x)
                    if kind == 'B':
                        pq = B(q); C[('terminal root', 'b(q) vs m′', rel(pq, B(m)))] += 1; C[('terminal root', 'b(q) diag', diag(L, F, pq))] += 1
                        C[('terminal root', 'b(q) vs q', rel(pq, q))] += 1
    C[('model', 'second tops with a late parent', sum(1 for z in tops if any(h[x] < K - 1 for x in range(n) if inR(x, K - 1) and (F[x][z] == x or F[x][z] == z))))] += 1

C = collections.Counter()
if mode == 'config':
    for L in lattices([a for a in sys.argv[2:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
        if L.height < 2: continue
        for m in range(L.n):
            if not (max(1, sc.RMIN) <= L.rank[m] < L.height): continue
            F = sc.query(L, m, 'noic_fi', False)
            if F: analyse(L, F, m, C); break
else:
    for fn in sys.argv[2:]:
        d = json.load(open(fn)); L = ss.Lat(d['sets'])
        analyse(L, d['F'], d['m'], C, config=not fn.startswith('top_parent'))
for k, v in sorted(C.items(), key=str): print(k, v)
