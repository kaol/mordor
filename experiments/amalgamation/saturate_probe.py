"""Saturated shadows u ↦ x ⊔ F(x, u) and the initial pair (log §34.3z¹⁹²).

Models: the SAT models of 'minhyp' under the MinUpCell hypotheses (multi notop nofeeder notightK1: m ∈ R_K ∖ R_{K−1},
h(m) = K, R_K tight, m ≠ ⊤, ¬IC(m)), every qualifying m; and with 'icok' (IC(m) allowed) the models of the 'upcell'
counterexamples (¬UpCell). For every stage-k row x (x ∈ R_k, h(x) = k; k = K − 1) and every candidate column v (x < v,
F(x, v) ≤ v, m ≰ v): iterate u ↦ x ⊔ F(x, u) from v. It hits a lower cell (x ⊔ F(x,u) = x), an upper cell, or stabilizes
at a drop q = x ⊔ F(x, q) with F(x, q) ∥ x. For drops: b(q) vs x, entry route and stage of b(q). Initial pair: which rows
have candidate columns; m ∧ w (w = F(m, y*)) and the entry of m into R_K.
   python3 saturate_probe.py [mode=min|icok] [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
MODE = next((a[5:] for a in sys.argv if a.startswith('mode=')), 'min')
sys.argv += ['multi', 'notop', 'nofeeder', 'notightK1'] + (['icok'] if MODE == 'icok' else [])
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
        best[tag] = n; json.dump(d, open(f'sat_{MODE}_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'icok', 'nopostlayer')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith(('rmin=', 'mode='))]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'upcell' if MODE == 'icok' else 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F); jn = L.join; mt = L.meet
        inR = lambda x, j: st[x] is not None and st[x] <= j
        rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        upc = any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for x in X for z in range(n))
        C['models', MODE, 'UpCell', upc] += 1
        D = dict(sets=L.S, F=F, m=m)
        # initial pair
        cand = {x: [v for v in range(n) if le[x][v] and v != x and le[F[x][v]][v] and not le[m][v]] for x in X}
        w = F[m][ystar(L, F, m)] if not ic(L, F, m) else None
        mw = mt[m][w] if w is not None else None
        C[('initial pair', MODE, 'rows of height k in R_k', min(len(X), 3), 'some row with a candidate column', any(cand.values()),
           'R_k tight', all(h[z] <= k for z in range(n) if inR(z, k)),
           'm ∧ w a height-k row of R_k', (mw in X) if mw is not None else None,
           'b(m) a height-k row of R_k', b_of(L, F, m) in X)] += 1
        if not any(cand.values()): keep('noinitial', n, D)
        elif not upc: keep('pair_noupcell', n, D)
        # saturation
        for x in X:
            for v in cand[x]:
                u = v
                while True:
                    g = F[x][u]; u2 = jn[x][g]
                    if u2 == x: res = 'lower cell'; break
                    if u2 == u:
                        res = 'upper cell' if le[u][g] else 'drop'; break
                    u = u2
                if res != 'drop':
                    C[('saturation', MODE, res)] += 1; continue
                q = u; bq = b_of(L, F, q)
                route = 'B-entered (q ∉ R_{st(b q)})' if st[q] is not None and st[bq] is not None and st[q] > st[bq] else 'other'
                C[('saturation', MODE, 'drop', 'b(q) vs x', rl(bq, x), 'b(q) ∈ R_k', inR(bq, k), 'h(b(q)) − k', h[bq] - k if bq is not None else None,
                   'q ∈ R_{k+1}', inR(q, k + 1))] += 1
                if not (le[bq][x] and bq != x): keep('bq_not_lt_x', n, dict(D, x=x, v=v, q=q))
report()
