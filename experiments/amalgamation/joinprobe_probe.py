"""The join probe after saturation (log §34.3z¹⁹³).

Models: SAT models of 'minhyp' under the MinUpCell hypotheses (multi notop nofeeder notightK1; ¬IC(m)), every qualifying
m (as saturate_probe.py mode=min). y* = column-orbit gfp, w = F(m, y*), meet row x = m ∧ w. When x is a height-k row of
R_k: for every saturated drop q of row x below w (x < q ≤ w, F(x,q) ≤ q, x ⊔ F(x,q) = q, F(x,q) ∥ x), z = the least
fixed point of Ψ(t) = m ⊔ F(m, t) above m ⊔ q (joinProbe), r = F(m, z), and the split A1 (x ≤ r) / A2 (m ∧ r < x).
Otherwise: classify the rows (Priority B).   python3 joinprobe_probe.py [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
sys.argv += ['multi', 'notop', 'nofeeder', 'notightK1']
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
from gfp_top import ystar, ic
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); best = {}
def report(*_):
    for k_, v in sorted(C.items(), key=str): print(k_, v)
    for k_, v in sorted(best.items()): print('MIN', k_, v)
    sys.stdout.flush(); sys.exit(0)
signal.signal(signal.SIGTERM, report)
def keep(tag, n, d):
    if tag not in best or n < best[tag]:
        best[tag] = n; json.dump(d, open(f'jp_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F); jn = L.join; mt = L.meet
        inR = lambda x, j: st[x] is not None and st[x] <= j
        rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        ys = ystar(L, F, m); w = F[m][ys]; x = mt[m][w]; D = dict(sets=L.S, F=F, m=m)
        C['models'] += 1
        if x in X and x != w:
            qs = [q for q in range(n) if le[x][q] and q != x and le[q][w] and le[F[x][q]][q] and jn[x][F[x][q]] == q
                  and not le[x][F[x][q]] and not le[F[x][q]][x]]
            C[('meet row', 'saturated drops q ≤ w', min(len(qs), 3))] += 1
            for q in qs:
                t = jn[m][q]
                while True:
                    t2 = jn[m][F[m][t]]
                    if t2 == t: break
                    assert le[t][t2]; t = t2
                z = t; r = F[m][z]
                assert le[z][ys] and not le[r][m] and not le[m][r] and le[r][w] and le[F[x][q]][r]
                A1 = le[x][r]
                tag = ('join probe', 'z = y*', z == ys, 'r = w', r == w, 'split', 'A1' if A1 else 'A2')
                if A1 and r != w:
                    # saturate (x, r) from r
                    u = r
                    while True:
                        g = F[x][u]; u2 = jn[x][g]
                        if u2 == x: res = 'lower cell'; break
                        if u2 == u: res = 'upper cell' if le[u][g] else ('same drop q' if u == q else 'new drop'); break
                        u = u2
                    tag += ('saturation from r', res)
                if not A1:
                    p = mt[m][r]
                    newrow = [y for y in X if y != x and le[p][y] and any(le[y][v] and v != y and le[F[y][v]][v] and not le[m][v] for v in range(n))]
                    tag += ('p = m ∧ r: h(p) − k', h[p] - k, 'p ∈ R_{h(p)}', inR(p, h[p]), 'p new at its height stage', inR(p, h[p]) and not inR(p, h[p] - 1),
                            'a(p) a height-k row', a_of(L, F, p) in X, 'another height-k row above p with a candidate column', bool(newrow))
                    keep('A2', n, dict(D, x=x, q=q, z=z))
                C[tag] += 1
                C[('probe output', 'z = m ⊔ q', z == jn[m][q], 'z = y*', z == ys, 'r is', 'w' if r == w else 'q' if r == q else 'F(x,q)' if r == F[x][q] else 'other')] += 1
                if A1 and r != w: keep('A1_nontrivial', n, dict(D, x=x, q=q, z=z))
        else:
            rowsbelow = [y for y in X if le[y][m]]
            C[('no meet row', 'h(m ∧ w) − k', h[x] - k, 'm ∧ w ∈ R_k', inR(x, k), 'height-k rows below m', min(len(rowsbelow), 2),
               'b(m) a height-k row', b_of(L, F, m) in X, 'witness rows: some ≤ m', any(le[y][m] for y in X if any(le[y][v] and v != y and le[F[y][v]][v] and not le[m][v]
                  and all(le[y][F[y][u]] for u in range(n) if le[y][u] and u != y and le[u][v] and le[F[y][u]][u]) for v in range(n))))] += 1
            keep('nomeetrow', n, D)
report()
