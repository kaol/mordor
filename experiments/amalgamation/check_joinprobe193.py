"""Regression check for §34.3z¹⁹³ (join probe): re-verify the MinUpCell hypotheses, then for the stored drop q of the
meet row x = m ∧ w recompute z (least Ψ-fixed point above m ⊔ q, Ψ t = m ⊔ F(m, t)), r = F(m, z), the A1/A2 split and
its data; for the no-meet-row model list the height-k rows and the descent witnesses.
  python3 check_joinprobe193.py [FILE.json ...]"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, b_of, a_of
from gfp_top import ystar, ic
for fn in sys.argv[1:] or ['jp_A1_nontrivial_min21.json', 'jp_A2_min20.json', 'jp_nomeetrow_min6.json']:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank; jn = L.join; mt = L.meet
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    W_ = max(x.bit_length() for x in L.S); nm = lambda q: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[q] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    hyp = mono and all(h[z] <= K for z in range(n) if inR(z, K)) and inR(m, K) and not inR(m, K - 1) and m != L.top and not ic(L, F, m)
    ys = ystar(L, F, m); w = F[m][ys]; x = mt[m][w]
    X = [y for y in range(n) if inR(y, k) and h[y] == k]
    print(f'== {fn}: |L| = {n}, K = {K}; MinUpCell hypotheses hold: {hyp}; m = {nm(m)}, y* = {nm(ys)}, w = {nm(w)}, m ∧ w = {nm(x)} '
          f'(height {h[x]}, in R_k: {inR(x, k)}); R_k tight: {all(h[z] <= k for z in range(n) if inR(z, k))}')
    if 'q' in d:
        q = d['q']; t = jn[m][q]
        while jn[m][F[m][t]] != t: t = jn[m][F[m][t]]
        z = t; r = F[m][z]
        print(f'   drop q = {nm(q)} (F(x,q) = {nm(F[x][q])}), z = {nm(z)} (= y*: {z == ys}), r = F(m,z) = {nm(r)} (= w: {r == w}), '
              f'split: {"A1" if le[x][r] else "A2"}, m ∧ r = {nm(mt[m][r])} (height {h[mt[m][r]]}, stage {st[mt[m][r]]})')
    else:
        dw = [(nm(y), nm(v)) for y in X for v in range(n) if le[y][v] and v != y and le[F[y][v]][v] and not le[m][v]
              and all(le[y][F[y][u]] for u in range(n) if le[y][u] and u != y and le[u][v] and le[F[y][u]][u])]
        print(f'   height-k rows {[nm(y) for y in X]} (below m: {[nm(y) for y in X if le[y][m]]}); descent witnesses (row, column): {dw}')
