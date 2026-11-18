"""The pure-A jump configuration (log §34.3z¹⁹⁵).

For every height-k row x of R_k that is non-ascending (x ≰ a x) and lies below some c_i = a^i(⊥), i ≤ k: the jump
index j (h(c_j) < k, h(c_{j+1}) = k + 1; noUpCell_pureA_jump), c = c_{j+1}, and where m's interval cells sit relative to
c (columns y > m with F(m,y) ≤ m or y ≤ F(m,y)): at m ⊔ c, above c, or elsewhere; and whether c_j ≤ m.
mode=icok: the models with ¬IC(m) dropped and ¬UpCell imposed (the jump lemma's hypotheses hold there);
mode=min: MinUpCell-hypothesis models (whether the jump configuration occurs at all, and what carries UpCell).
   python3 pureajump_probe.py [mode=min|icok] [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
MODE = next((a[5:] for a in sys.argv if a.startswith('mode=')), 'icok')
sys.argv += ['multi', 'notop', 'nofeeder', 'notightK1'] + (['icok'] if MODE == 'icok' else [])
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
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
        best[tag] = n; json.dump(d, open(f'pa_{MODE}_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'icok')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith(('rmin=', 'mode='))]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'upcell' if MODE == 'icok' else 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F); jn = L.join
        inR = lambda x, j: st[x] is not None and st[x] <= j
        A = lambda x: a_of(L, F, x)
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        c = [L.bot]
        for _ in range(k + 1): c.append(A(c[-1]))
        icells = [y for y in range(n) if le[m][y] and y != m and (le[F[m][y]][m] or le[y][F[m][y]])]
        uprow = lambda x: any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n))
        C['models', MODE] += 1
        C[('pure A-chain', MODE, 'rigid (a ⊥ = ⊥)', c[1] == L.bot, 'h(c_k) − k', h[c[k]] - k, 'some c_i (i ≤ k) of height k', any(h[c[i]] == k for i in range(k + 1)))] += 1
        for x in X:
            if le[x][A(x)]: continue
            idx = [i for i in range(k + 1) if le[x][c[i]]]
            if not idx: C[('non-ascending row', MODE, 'below the pure A-chain', False)] += 1; continue
            i = idx[0]
            js = [j for j in range(i) if h[c[j]] < k and h[c[j + 1]] == k + 1]
            if not js: C[('non-ascending row', MODE, 'below the pure A-chain', True, 'jump found', False, 'row is UpCell', uprow(x))] += 1; continue
            j = js[0]; cc = c[j + 1]; mc = jn[m][cc]
            where = ('cell of m at m ⊔ c' if mc in icells else 'cell of m above c' if any(le[cc][y] for y in icells) else
                     'cell of m elsewhere' if icells else 'no cell of m (¬IC)')
            C[('non-ascending row', MODE, 'below the pure A-chain', True, 'jump found', True, 'x ⊔ c_j = c', jn[x][c[j]] == cc,
               'c_j ≤ m', le[c[j]][m], 'm ⊔ c vs ⊤', mc == L.top, where, 'row is UpCell', uprow(x))] += 1
            if where != 'cell of m at m ⊔ c': keep('jump_' + where.split()[-1].strip('()¬'), n, dict(sets=L.S, F=F, m=m, x=x, j=j))
report()
