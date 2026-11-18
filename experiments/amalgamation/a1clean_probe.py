"""A1 clean fibres and exceptional covers (log §34.3z¹⁹⁹).

For every A1-shape configuration (p ⋖ c, F(p, c) = p, c a height-k row of R_k, p in some stage) and every fibre column u
(F(p, u) = c, m ≰ u): the exception set E_u = {e ∈ (c, u] : F(p, e) = p}; b(e) vs p and b(c); the join e* = ⋁E_u, whether
F(p, e*) = p (then E_u = {e*}) or e* is a fibre column; F(c, e*) vs e*; for each exception the ¬IC(m) response
F(m, m ⊔ e) vs e, c, m. Per model: whether some configuration is an A1CleanFibre certificate (comparable column on an
exception-free (c, u]) and whether UpCell holds.
mode=icok: ¬IC(m) dropped, ¬UpCell imposed; mode=min: MinUpCell hypotheses.
   python3 a1clean_probe.py [mode=min|icok] [rmin=R] (closure … | sweep …)
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
        best[tag] = n; json.dump(d, open(f'a1c_{MODE}_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'icok')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith(('rmin=', 'mode='))]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'upcell' if MODE == 'icok' else 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F); jn = L.join
        inR = lambda x, j: st[x] is not None and st[x] <= j
        B = lambda x: b_of(L, F, x)
        rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        upc = any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for x in X for z in range(n))
        cmp_ = lambda c, z: le[F[c][z]][z] or le[z][F[c][z]]
        clean = False; anyfib = False; anyb = False; cert = False; D = dict(sets=L.S, F=F, m=m)
        for c in X:
            for p in L.covers_dn[c]:
                if st[p] is None or F[p][c] != p: continue
                for u in range(n):
                    if not (le[c][u] and u != c and not le[m][u] and F[p][u] == c): continue
                    E = [e for e in range(n) if le[c][e] and e != c and le[e][u] and F[p][e] == p]
                    zs = [z for z in range(n) if le[c][z] and z != c and le[z][u] and cmp_(c, z)]
                    anyfib = True; anyb |= p == B(c)
                    for z in range(n):
                        if not (le[c][z] and z != c and le[z][u]): continue
                        if le[F[c][z]][c] or le[z][F[c][z]] or (le[F[c][z]][z] and not any(le[c][e] and e != c and le[e][z] and F[p][e] == p for e in range(n))):
                            cert = True
                    if zs and not E: clean = True
                    if not E: continue
                    es = E[0]
                    for e in E[1:]: es = jn[es][e]
                    single = F[p][es] == p
                    if single: assert E == [es]
                    C[('exceptions under a fibre column', MODE, 'p = b(c)', p == B(c), 'all b(e) = b(c)', all(B(e) == B(c) for e in E),
                       '|E|', min(len(E), 3), 'join', 'singleton blocker (F(p,e*) = p)' if single else 'e* in the fibre',
                       'F(c, e*) comparable with e*', cmp_(c, es), 'comparable column in (c, u]', bool(zs))] += 1
                    for e in E:
                        me = jn[m][e]; r = F[m][me]
                        C[('¬IC(m) response at m ⊔ e', MODE, 'r vs e', rl(r, e), 'r vs c', rl(r, c), 'r vs m', rl(r, m), 'h(r) − k', h[r] - k)] += 1
                    keep('blocker_' + ('single' if single else 'join'), n, dict(D, p=p, c=c, u=u))
        C[('model', MODE, 'some A1-shape configuration with a nonempty fibre', anyfib, 'with p = b(c)', anyb, 'A1CleanFibre', clean, 'A1Cert', cert, 'UpCell', upc)] += 1
        if anyfib and not cert: keep('nocert', n, D)
        if MODE == 'min' and anyfib and not clean: keep('noclean', n, D)
report()
