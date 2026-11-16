"""Crossing diagnostics for singleton lower transfer (log §34.3z¹⁶³; brief "On-time singleton lower transfer").

In every one-stage-ahead model with b(m) = m' and no interval cell at m (single_claims.py noic_fi ahead), compute the
column orbit c_0 = ⊤, c_{n+1} = m ⊔ F(m, c_n) (limit y*), q_n = b(c_n), the lower-row orbit d on [m', y*]
(D(z) = m' ⊔ F(m', z), from y*; limit d*), and the brief's candidate bridge terms, with their positions and entry
stages. J = stage of m (= h(m) − 1 in the ahead indexing).  python3 crossing_probe.py (sweep P NMAX | closure …)
"""
import sys, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); shown = 0
for L in lattices(sys.argv[1:]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (1 <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', True)
        if not F: continue
        n = L.n; le = L.le; jn = L.join; mt = L.meet; st = stages(L, F); B = lambda y: b_of(L, F, y)
        mp = B(m); K = L.rank[m]; J = st[m]
        c = [L.top]
        while True:
            nx = jn[m][F[m][c[-1]]]
            if nx == c[-1]: break
            c.append(nx)
        ys = c[-1]; w = F[m][ys]
        q = [B(x) for x in c]
        d = [ys]
        while True:
            nx = jn[mp][F[mp][d[-1]]]
            if nx == d[-1]: break
            d.append(nx)
        ds = d[-1]
        C['models'] += 1
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        for i, qi in enumerate(q):
            C[('q_n vs m', rel(qi, m))] += 1; C[('q_n vs c_n', rel(qi, c[i]))] += 1
            C[('q_n diag-pre-fixed', le[F[qi][qi]][qi])] += 1
        C[('y* = ⊤', ys == L.top)] += 1; C[('d* = w', ds == w)] += 1; C[('d* vs m', rel(ds, m))] += 1
        C[('m ⊔ d* = y*', jn[m][ds] == ys)] += 1
        for nm_, t in (('w', w), ('d*', ds), ('b(y*)', B(ys)), ('F(m′,y*)', F[mp][ys]), ('a(m′)', a_of(L, F, mp)), ('m ⊔ d*', jn[m][ds])):
            C[(nm_, 'entry − J', None if st[t] is None else st[t] - J)] += 1
            C[(nm_, 'vs m', rel(t, m))] += 1
        A = lambda x: a_of(L, F, x); RJ = [z for z in range(n) if st[z] is not None and st[z] <= J]
        C[('w entry: b(w) ∈ R_J', st[B(w)] is not None and st[B(w)] <= J)] += 1
        C[('w entry: b(w) vs m′', rel(B(w), mp))] += 1
        C[('w entry: w ≤ a(m′)', le[w][A(mp)])] += 1
        C[('w entry: w ≤ a(x), x ∈ R_J', any(le[w][A(x)] for x in RJ))] += 1
        C[('w entry: b(y) ∈ R_J for some y ≥ w', any(le[w][y] and B(y) in RJ for y in range(n)))] += 1
        C[('F(m′, w) vs m′', rel(F[mp][w], mp))] += 1
        C[('F(w, w) ≤ w', le[F[w][w]][w])] += 1
        X = [x for x in RJ if le[w][A(x)]]
        cands = {'F(m′,w)': F[mp][w], 'F(m′,y*)': F[mp][ys], 'b(w)': B(w), 'F(⊥,w)': F[L.bot][w], 'm′': mp,
                 'F(m′,m′)': F[mp][mp], 'F(w,m′)': F[w][mp], 'w⊓F(m′,w)': mt[w][F[mp][w]]}
        for cn, cv in cands.items():
            C[('x candidate works', cn, cv in X)] += 1
        C[('min x relation to w', min([rel(x, w) for x in X]))] += 1
        C[('some x ≤ w', any(le[x][w] for x in X))] += 1
        C[('some x with x ∥ m and x ≤ w', any(le[x][w] and rel(x, m) == '∥' for x in X))] += 1
        if shown < 1:
            w_ = max(x.bit_length() for x in L.S); nm = lambda i: '{' + ''.join(str(j) for j in range(w_) if L.S[i] >> j & 1) + '}'
            print('example |L| =', n, 'm', nm(m), "m'", nm(mp), 'c', [nm(x) for x in c], 'q', [nm(x) for x in q], 'd', [nm(x) for x in d], 'w', nm(w))
            shown += 1
        break
for k, v in sorted(C.items(), key=str): print(k, v)
