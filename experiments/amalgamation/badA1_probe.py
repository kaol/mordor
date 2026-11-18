"""Forbidden rows in models of a bad genuine A1 configuration (log §34.3z²⁰⁰).

Models: the exact counterexamples of 'a1cert genuine' (MinUpCell hypotheses, a genuine A1 configuration p = b(c) ⋖ c,
c non-ascending, with a fibre column u, and no A1Cert anywhere), every qualifying m. In each, the forbidden rows (other
ascending: x < a(x) ≠ m; stationary with an initial pair) of height k in R_k, and their relation to the configuration:
x vs p, c, u, t = F(c, u), a(c), m; the forbidden row's witness column (a(x), resp. an initial column v) vs u, t, c ⊔ x.
   python3 badA1_probe.py [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
sys.argv += ['multi', 'notop', 'nofeeder', 'notightK1', 'genuine']
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
        best[tag] = n; json.dump(d, open(f'bad1_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'genuine')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'a1cert', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F); jn = L.join; mt = L.meet
        inR = lambda x, j: st[x] is not None and st[x] <= j
        A = lambda x: a_of(L, F, x); B = lambda x: b_of(L, F, x)
        rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        cfgs = [(B(c), c, u) for c in X if B(c) in L.covers_dn[c] and not le[c][A(c)]
                for u in range(n) if le[c][u] and u != c and not le[m][u] and F[B(c)][u] == c]
        if not cfgs: continue
        C['models'] += 1
        D = dict(sets=L.S, F=F, m=m)
        forb = []
        for x in X:
            ax = A(x)
            if le[x][ax] and ax not in (x, m): forb.append((x, 'other ascending', ax))
            elif ax == x:
                vs = [v for v in range(n) if le[x][v] and v != x and not le[m][v] and le[F[x][v]][v]]
                if vs: forb.append((x, 'stationary with pair', vs[0]))
        C[('forbidden rows', 'kinds', tuple(sorted({f[1] for f in forb})))] += 1
        if not forb: keep('noforb', n, D); continue
        fset = {f[0]: f for f in forb}
        for (p_, c_, u_) in cfgs:
            t_ = F[c_][u_]; ac = A(c_)
            C[('genuine configuration', 'a(c) a height-k row of R_k', ac in X, 'h(a(c)) − k', h[ac] - k, 'a(c) ≤ u', le[ac][u_], 'a(c) ≤ t', le[ac][t_],
               't = c ⊔ a(c)', t_ == jn[c_][ac], 'a(c) forbidden', ac in fset, 'p < a(c)', le[p_][ac] and p_ != ac,
               'some forbidden row x < t', any(le[x][t_] for x in fset))] += 1
            orb = [c_]; seenp = {c_}
            while True:
                nx = A(orb[-1])
                if nx in seenp: break
                orb.append(nx); seenp.add(nx)
            orbit_forb = [x for x in orb[1:] if x in fset]
            first_asc = next((x for x in orb[1:] if le[x][A(x)]), None)
            C[('A-orbit of c', 'a forbidden row on the orbit', bool(orbit_forb), 'first ascending iterate exists', first_asc is not None,
               'first ascending iterate is a forbidden row', first_asc in fset if first_asc is not None else None,
               'first ascending iterate: height-k row of R_k', first_asc in X if first_asc is not None else None,
               'its a(x)', ('= x' if A(first_asc) == first_asc else '= m' if A(first_asc) == m else 'other') if first_asc is not None else None,
               'non-local case', not any(le[x][ac] or le[x][t_] for x in fset))] += 1
            if not orbit_forb: keep('orbit_misses', n, dict(D, p=p_, c=c_, u=u_))
            orbset = set(orb[1:])
            afib = [x for x in fset if x in orbset or A(x) in orbset]
            C[('A-orbit fibre of c (x on the orbit or a(x) on it)', 'contains a forbidden row', bool(afib),
               'non-local case', not any(le[x][ac] or le[x][t_] for x in fset))] += 1
            if not afib: keep('afibre_misses', n, dict(D, p=p_, c=c_, u=u_))
            union = bool(afib) or any(le[x][ac] or le[x][t_] for x in fset)
            C[('union selector (A-orbit fibre ∪ ↓a(c) ∪ ↓t)', 'contains a forbidden row', union)] += 1
            if not union: keep('union_misses', n, dict(D, p=p_, c=c_, u=u_))
            below = [x for x in fset if le[x][ac]]
            C[('genuine configuration: forbidden row below a(c)', bool(below), 'with a(x) = a(c)', any(A(x) == ac for x in below),
               'forbidden row below t', any(le[x][t_] for x in fset))] += 1
            if not below: keep('none_below_ac', n, dict(D, p=p_, c=c_, u=u_))
            if ac not in fset: keep('ac_not_forbidden', n, dict(D, p=p_, c=c_, u=u_))
            if ac in fset and t_ != jn[c_][ac]: keep('ac_forbidden_t_ne_join', n, dict(D, p=p_, c=c_, u=u_))
        p, c, u = cfgs[0]; t = F[c][u]
        C[('configuration', 'F(c,u) = t vs u', rl(t, u), 't vs c', rl(t, c), 'h(t) − k', h[t] - k, 'a(c) vs c', rl(A(c), c))] += 1
        for x, kind, w in forb:
            C[('forbidden row', kind, 'x vs c', rl(x, c), 'x vs p', rl(x, p), 'x vs u', rl(x, u), 'x vs t', rl(x, t), 'x vs a(c)', rl(x, A(c)),
               'witness w vs u', rl(w, u), 'w vs t', rl(w, t), 'w = c ⊔ x', w == jn[c][x], 'b(x) = p', B(x) == p)] += 1
        keep('example', n, dict(D, p=p, c=c, u=u))
report()
