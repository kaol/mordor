"""Regression check for §34.3z¹⁹² (saturated shadows): for each stored model, re-verify the MinUpCell hypotheses
(R_K tight, m ∈ R_K ∖ R_{K−1}, h(m) = K, m ≠ ⊤; ¬IC(m) reported), UpCell, the candidate pairs (x, v) of the stage-k rows,
and for each the saturation of u ↦ x ⊔ F(x, u) from v: lower / upper cell, or a drop q with b(q) and its relation to x.
  python3 check_saturate192.py [FILE.json ...]"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, b_of
from gfp_top import ic
FILES = ['sat_min_bq_not_lt_x_min7.json', 'sat_icok_bq_not_lt_x_min6.json', 'sat_icok_pair_noupcell_min14.json', 'sat_icok_noinitial_min4.json']
for fn in sys.argv[1:] or FILES:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank; jn = L.join
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    W_ = max(x.bit_length() for x in L.S); nm = lambda q: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[q] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    hyp = mono and all(h[z] <= K for z in range(n) if inR(z, K)) and inR(m, K) and not inR(m, K - 1) and m != L.top
    rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
    X = [x for x in range(n) if inR(x, k) and h[x] == k]
    upc = any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for x in X for z in range(n))
    print(f'== {fn}: |L| = {n}, K = {K}; MinUpCell hypotheses except ¬IC(m) hold: {hyp}; IC(m) = {ic(L, F, m)}; UpCell = {upc}; m = {nm(m)}; '
          f'R_k tight: {all(h[z] <= k for z in range(n) if inR(z, k))}')
    for x in X:
        for v in range(n):
            if not (le[x][v] and v != x and le[F[x][v]][v] and not le[m][v]): continue
            u = v
            while True:
                g = F[x][u]; u2 = jn[x][g]
                if u2 == x: res = 'lower cell at ' + nm(u); break
                if u2 == u: res = ('upper cell at ' + nm(u)) if le[u][g] else None; break
                u = u2
            if res is None:
                bq = b_of(L, F, u)
                res = f'drop q = {nm(u)}, F(x,q) = {nm(F[x][u])}, b(q) = {nm(bq)} ({rl(bq, x)} x), b(q) ∈ R_k: {inR(bq, k)}, h(b(q)) = {h[bq]}'
            print(f'   row {nm(x)}, column {nm(v)}: {res}')
