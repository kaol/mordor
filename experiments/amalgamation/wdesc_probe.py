"""Descent witnesses anchored at w (log §34.3z¹⁹¹).

For every model (every qualifying m, the SAT model of 'noic_fi', as fork_probe.py): w = F(m, y*) (y* the column-orbit
gfp, w ∥ m). A descent witness is (x, v): x ∈ R_k of height k, x < v, F(x, v) ≤ v, m ≰ v, and the row x stays above x on
its pre-fixed columns in (x, v] (DescentWitness; upCell_of_descentWitness). Variants: any v; v ≤ w; v = w. Records the
witness rows (feeder m′ or not, diagonal post-fixed or not, x vs w) and minimal failures.
   python3 wdesc_probe.py [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, b_of
from gfp_top import ystar
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
        best[tag] = n; json.dump(d, open(f'wd_{tag}_min{n}.json', 'w'))

for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        w = F[m][ystar(L, F, m)]; mp = b_of(L, F, m)
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        above = lambda x, v: all(le[x][F[x][u]] for u in range(n) if le[x][u] and u != x and le[u][v] and le[F[x][u]][u])
        dw = lambda x, v: le[x][v] and x != v and le[F[x][v]][v] and not le[m][v] and above(x, v)
        W_any = [(x, v) for x in X for v in range(n) if dw(x, v)]
        W_le = [(x, v) for (x, v) in W_any if le[v][w]]
        W_eq = [(x, v) for (x, v) in W_any if v == w]
        ys = ystar(L, F, m)
        W_ys = [(x, v) for (x, v) in W_any if le[v][ys]]
        W_xw = [(x, v) for (x, v) in W_any if le[x][w]]
        drops = {F[mp][u] for u in range(n) if le[mp][u] and u != mp and le[u][w] and le[F[mp][u]][u] and not le[mp][F[mp][u]]}
        C[('descent witness', 'v ≤ y*', bool(W_ys), 'x < w', bool(W_xw), 'x < w and v ≤ y*', any(le[x][w] and le[v][ys] for x, v in W_any),
           'x a feeder drop value F(m′, u), u ∈ (m′, w] pre-fixed', any(x in drops for x, _ in W_any))] += 1
        for tag, Wl in (('ys', W_ys), ('xw', W_xw)):
            if not Wl: keep('no_' + tag, n, dict(sets=L.S, F=F, m=m))
        C['models'] += 1
        C[('descent witness', 'any v', bool(W_any), 'v ≤ w', bool(W_le), 'v = w', bool(W_eq))] += 1
        for tag, Wl in (('any', W_any), ('le_w', W_le), ('eq_w', W_eq)):
            if not Wl: keep('no_' + tag, n, dict(sets=L.S, F=F, m=m))
        xs = {x for x, _ in W_le}
        C[('rows with a witness v ≤ w', 'includes m′', mp in xs, 'some diagonal post-fixed', any(le[x][F[x][x]] for x in xs),
           'all below w', all(le[x][w] for x in xs) if xs else None)] += 1
        # the feeder row below w: does m′ stay above itself on (m′, w]?
        C[('feeder row m′ on (m′, w]', 'stays above', above(mp, w), 'F(m′, w) ≤ w', le[F[mp][w]][w])] += 1
report()
