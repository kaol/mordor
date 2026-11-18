"""Regression check for §34.3z¹⁹⁸: for each stored A1-shape configuration (p ⋖ c, F(p, c) = p, c a height-k row of R_k),
re-verify the MinUpCell hypotheses (¬IC(m) reported) and UpCell; list the fibre S(p, c; m), the exceptional columns
(z ∈ (c, u], u ∈ S, F(p, z) = p) with height and stage, and the comparable columns of row c.   python3 check_a1fibre198.py"""
import json, sys, glob
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, b_of
from gfp_top import ic
for fn in sys.argv[1:] or sorted(glob.glob('a1f_*.json')):
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; p = d['p']; c = d['c']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j; K = h[m]; k = K - 1
    W_ = max(z.bit_length() for z in L.S); nm = lambda z: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[z] >> j_ & 1) + '}'
    mono = all(le[F[u][y]][F[u2][y2]] for u in range(n) for u2 in range(n) if le[u][u2] for y in range(n) for y2 in range(n) if le[y][y2])
    hyp = mono and all(h[z] <= K for z in range(n) if inR(z, K)) and inR(m, K) and not inR(m, K - 1) and m != L.top
    X = [z for z in range(n) if inR(z, k) and h[z] == k]
    upc = any(le[z][y] and y != z and not le[m][y] and (le[F[z][y]][z] or le[y][F[z][y]]) for z in X for y in range(n))
    S = [u for u in range(n) if le[c][u] and u != c and not le[m][u] and F[p][u] == c]
    exc = [z for z in range(n) if le[c][z] and z != c and F[p][z] == p and any(le[z][u] for u in S)]
    cmp_ = [z for z in range(n) if le[c][z] and z != c and any(le[z][u] for u in S) and (le[F[c][z]][z] or le[z][F[c][z]])]
    print(f'== {fn}: |L| = {n}, K = {K}; MinUpCell hypotheses except ¬IC(m) hold: {hyp}; IC(m) = {ic(L, F, m)}; UpCell = {upc}; m = {nm(m)}')
    print(f'   p = {nm(p)} (b(c) = p: {b_of(L, F, c) == p}) ⋖ c = {nm(c)}; fibre {[nm(u) for u in S]}; exceptional columns '
          f'{[(nm(z), "h " + str(h[z]), "stage " + str(st[z])) for z in exc]}; comparable columns of row c {[nm(z) for z in cmp_]}')
