"""A1 sibling configurations without R_k tightness (log §34.3z¹⁹⁸).

Every height-k row c of R_k with a lower cover p ⋖ c, F(p, c) = p, p in some stage (the A1 shape when p = b(c)):
fibre S = {u > c : m ≰ u, F(p, u) = c}; exceptional columns z ∈ (c, u] (u ∈ S) with F(p, z) = p (source_row_or);
FibreTop in the original sense (some z ∈ (c, u], u ∈ S, comparable with F(c, z)); UpCell at c. By
a1_upCell_or_exceptional, FibreTop without exceptional columns gives UpCell.
mode=icok: ¬IC(m) dropped, ¬UpCell imposed; mode=min: MinUpCell hypotheses.
   python3 a1fibre_probe.py [mode=min|icok] [rmin=R] (closure … | sweep …)
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
        best[tag] = n; json.dump(d, open(f'a1f_{MODE}_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'icok')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith(('rmin=', 'mode='))]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'upcell' if MODE == 'icok' else 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        uprow = lambda x: any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n))
        C['models', MODE] += 1; D = dict(sets=L.S, F=F, m=m)
        for c in X:
            for p in L.covers_dn[c]:
                if st[p] is None or F[p][c] != p: continue
                S = [u for u in range(n) if le[c][u] and u != c and not le[m][u] and F[p][u] == c]
                exc = [z for z in range(n) if le[c][z] and z != c and F[p][z] == p and any(le[z][u] for u in S)]
                ft = any(le[c][z] and z != c and le[z][u] and (le[F[c][z]][z] or le[z][F[c][z]]) for u in S for z in range(n))
                ftclean = any(le[c][z] and z != c and le[z][u] and (le[F[c][z]][z] or le[z][F[c][z]]) and
                              not any(le[c][e] and e != c and le[e][u] and F[p][e] == p for e in range(n)) for u in S for z in range(n))
                C[('A1-shape configuration', MODE, 'p = b(c)', p == b_of(L, F, c), 'fibre nonempty', bool(S), 'exceptional columns', bool(exc),
                   'FibreTop', ft, 'FibreTop on an exception-free interval', ftclean, 'c carries UpCell', uprow(c))] += 1
                if exc: keep('exceptional', n, dict(D, p=p, c=c))
                if MODE == 'icok' and ft: keep('ft_noupcell', n, dict(D, p=p, c=c))
report()
