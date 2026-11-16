"""Drop-case diagnostics for DescentWitness (log §34.3z¹⁷⁰; brief "Transfer from feeder-row failure to another row").

For each rank-≥R remaining-case configuration (multi, nopostlayer) in which the feeder row m′ drops on (m′, w]
(some row-pre-fixed q ∈ (m′, w] with m′ ≰ F(m′, q)), record the drop data — the first bad column q met by the
feeder descent from w and r = F(m′, q) — the descent sequence u_0 = w, u_{n+1} = F(m′, u_n), and every alternative
descent witness (x, v) (x ∈ T_k, x < v, F(x, v) ≤ v, m ≰ v, habove) with its relations to m′, m, q, r, w, d*, a(m′),
b(q), b(r).   python3 drop_probe.py [rmin=R] [show] (sweep … | closure …)
"""
import sys, collections
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, a_of, b_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); SHOW = 'show' in sys.argv
for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer', 'show') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(1, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; jn = L.join; h = L.rank; K = h[m]; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        A = lambda x: a_of(L, F, x); B = lambda y: b_of(L, F, y)
        mp = B(m); ys = ystar(L, F, m); w = F[m][ys]
        d = ys
        while jn[mp][F[mp][d]] != d: d = jn[mp][F[mp][d]]
        Tk = [y for y in range(n) if inR(y, K - 1) and h[y] == K - 1]
        bad = lambda x, v: [u for u in range(n) if le[x][u] and u != x and le[u][v] and le[F[x][u]][u] and not le[x][F[x][u]]]
        if not bad(mp, w): break
        C['drop models'] += 1
        seq = [w]                                  # feeder descent from w until a cell or a drop
        while True:
            u = seq[-1]; g = F[mp][u]
            if le[g][mp] or le[u][g] or not le[mp][g]: break
            seq.append(g)
        q = seq[-1]; r = F[mp][q]
        C[('first event on the descent', 'drop' if not le[mp][r] else 'cell')] += 1
        C[('first drop: q = w', q == w)] += 1; C[('first drop: r vs m′', rel(r, mp))] += 1; C[('first drop: r vs q', rel(r, q))] += 1
        C[('first drop: r', f'h−K={h[r] - K}', f'stage−K={st[r] - K if st[r] is not None else None}')] += 1
        C[('first drop: descent length', len(seq))] += 1
        gen = [(x, v) for x in Tk for v in range(n) if le[x][v] and v != x and le[F[x][v]][v] and not le[m][v] and not bad(x, v)]
        xs = sorted({x for x, v in gen})
        for x in xs:
            C[('witness row x vs', "m′", rel(x, mp), 'r', rel(x, r), 'm', rel(x, m))] += 1
            C[('witness row x', 'route', ('A' if any(inR(p, st[x] - 1) and le[x][A(p)] for p in range(n)) else '') + ('B' if inR(B(x), st[x] - 1) else ''))] += 1
            C[('witness row x vs b(r)', rel(x, B(r)))] += 1; C[('witness row x vs b(q)', rel(x, B(q)))] += 1
            C[('witness row x diag', 'pre' if le[F[x][x]][x] else 'not pre')] += 1
        C[('some witness row x ≥ r', any(le[r][x] for x in xs))] += 1
        C[('some witness row x with x ⊓ m′ < m′ and x ∥ m′', any(rel(x, mp) == '∥' for x in xs))] += 1
        C[('some witness with v = q', any(v == q for x, v in gen))] += 1; C[('some witness with v = w', any(v == w for x, v in gen))] += 1
        C[('some witness with v ≤ w', any(le[v][w] for x, v in gen))] += 1
        for x, v in gen:
            fx = F[x][v]; C[('F(x,v)', '= x' if fx == x else 'in (x,v)' if le[x][fx] else 'other')] += 1
            C[('witness v vs', 'w', rel(v, w), 'q', rel(v, q), 'r', rel(v, r))] += 1
        below_r = [x for x in Tk if le[x][r]]
        okq = lambda x: le[F[x][q]][q] and not bad(x, q)
        C[('tops x ≤ r exist', bool(below_r))] += 1
        C[('every top x ≤ r: (x, q) is a witness', all(okq(x) for x in below_r) if below_r else None)] += 1
        C[('some top x ≤ r: (x, q) is a witness', any(okq(x) for x in below_r))] += 1
        for x in below_r:
            C[('top x ≤ r', 'F(x,q) ≤ q', le[F[x][q]][q], 'Bad(x,q) empty', not bad(x, q))] += 1
            C[('top x ≤ r', 'F(x,q) vs x', rel(F[x][q], x), 'F(x,q) vs r', rel(F[x][q], r))] += 1
        C[('r', 'diag', 'pre' if le[F[r][r]][r] else 'post' if le[r][F[r][r]] else 'neither')] += 1
        C[('r row at q', 'F(r,q) vs r', rel(F[r][q], r), 'F(r,q) vs q', rel(F[r][q], q))] += 1
        ar = A(r)
        C[('a(r)', f'h−K={h[ar] - K}', 'a(r) vs q', rel(ar, q))] += 1
        C[('some witness with v = a(r)', any(v == ar for x, v in gen))] += 1
        C[('some witness with r ≤ v ≤ q', any(le[r][v] and le[v][q] for x, v in gen))] += 1
        C[('some witness (x, q) or (x, a(r))', any(v in (q, ar) for x, v in gen))] += 1
        C[('r ∈ R_K', inR(r, K))] += 1; C[('r late at stage K', inR(r, K) and not inR(r, K - 1) and h[r] < K)] += 1
        tops_ge_r = [x for x in Tk if le[r][x]]
        C[('tops of R_k above r exist', bool(tops_ge_r))] += 1
        C[('every top above r is a witness row', all(x in xs for x in tops_ge_r) if tops_ge_r else None)] += 1
        if SHOW:
            W_ = max(x.bit_length() for x in L.S); nm = lambda i: '{' + ''.join(str(j) for j in range(W_) if L.S[i] >> j & 1) + '}'
            print(f"|L|={n} m={nm(m)} m'={nm(mp)} w={nm(w)} q={nm(q)} r={nm(r)} seq={[nm(x) for x in seq]} Tk={[nm(x) for x in Tk]} "
                  f"witness pairs={[(nm(x), nm(v)) for x, v in gen]}")
        break
for k, v in sorted(C.items(), key=str): print(k, v)
