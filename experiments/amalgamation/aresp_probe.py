"""A-response classification of top rows, entry of m, off-m initial pairs (log §34.3z¹⁹⁴).

mode=min: SAT models of 'minhyp' under the MinUpCell hypotheses (multi notop nofeeder notightK1, ¬IC(m)).
mode=icok: the same with ¬IC(m) dropped and ¬UpCell imposed ('upcell' counterexamples).
Every height-k row x ∈ R_k is classed by its A-response: stationary (a x = x; with b x = x or b x < x), target (a x = m),
other ascending (x < a x ≠ m), non-ascending (x ≰ a x); with x vs m, an off-m pre-fixed column v > x (initial pair),
whether the row carries an UpCell, and the terminal stage of its A-normal form. Per model: the entry of m (A-entered
with its A-parents, or B-entered with h(b m)), and InitialPairOutside (a row x ≰ m with an off-m pre-fixed column).
   python3 aresp_probe.py [mode=min|icok] [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
MODE = next((a[5:] for a in sys.argv if a.startswith('mode=')), 'min')
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
        best[tag] = n; json.dump(d, open(f'ar_{MODE}_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'icok')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith(('rmin=', 'mode='))]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'upcell' if MODE == 'icok' else 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        A = lambda x: a_of(L, F, x); B = lambda x: b_of(L, F, x)
        def anormal(q, s):                       # the a_normal recursion: terminal stage
            while s > 0:
                rs = [r for r in range(n) if inR(r, s - 1) and le[q][A(r)]]
                if rs: q, s = rs[0], s - 1; continue
                if inR(q, s - 1): s -= 1; continue
                return s
            return 0
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        cand = lambda x: any(le[x][v] and v != x and le[F[x][v]][v] and not le[m][v] for v in range(n))
        uprow = lambda x: any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n))
        rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
        D = dict(sets=L.S, F=F, m=m)
        C['models', MODE] += 1
        for x in X:
            ax = A(x); bx = B(x)
            cls = ('stationary, b x = x' if bx == x else 'stationary, b x < x') if ax == x else 'target (a x = m)' if ax == m else \
                  'other ascending' if le[x][ax] else 'non-ascending'
            C[('row', MODE, cls, 'x vs m', rl(x, m), 'initial pair', cand(x), 'UpCell row', uprow(x), 'A-normal terminal stage 0', anormal(x, k) == 0)] += 1
        # entry of m
        apar = [x for x in range(n) if inR(x, k) and le[m][F[x][m]]]
        if any(A(q) == m for q in range(n) if inR(q, k)):
            C[('entry of m', MODE, 'A-entered', 'A-parent heights − k', tuple(sorted({h[x] - k for x in apar})), 'height-k A-parents', sum(x in X for x in apar))] += 1
        else:
            C[('entry of m', MODE, 'B-entered', 'h(b m) − k', h[B(m)] - k, 'b m a height-k row', B(m) in X)] += 1
        ipo = [x for x in X if not le[x][m] and cand(x)]
        C[('InitialPairOutside', MODE, bool(ipo), 'UpCell', any(uprow(x) for x in X),
           'UpCell rows ≰ m', any(uprow(x) and not le[x][m] for x in X))] += 1
        if not ipo: keep('noIPO', n, D)
report()
