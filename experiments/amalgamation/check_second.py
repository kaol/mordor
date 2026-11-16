"""Regression check for SecondEntry.lean (log §34.3z¹⁶⁵) on the stored uniqueness-free models: does R_{K−1} have a
diagonal post-fixed top (then `secondEntry_of_post_layer` applies; the descent along z ↦ F(x, z) from v = w or ⊤ is
replayed), and the routes / parents of the second tops.  python3 check_second.py [FILE.json ...]"""
import json, sys, glob
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar, ic
files = sys.argv[1:] or sorted(glob.glob('single_claim_*multi*.json'))
for fn in files:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank; K = h[m]
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j; W = max(x.bit_length() for x in L.S)
    nm = lambda z: '{' + ''.join(str(i) for i in range(W) if L.S[z] >> i & 1) + '}'
    w = F[m][ystar(L, F, m)]
    posts = [x for x in range(n) if inR(x, K - 1) and h[x] == K - 1 and le[x][F[x][x]]]
    pred = []
    for x in posts:                                    # replay row_cell_of_diag_post from v = w (x ≤ m) or v = ⊤
        v = w if le[x][m] else L.top
        while not (le[F[x][v]][x] or le[v][F[x][v]]): v = F[x][v]
        pred.append((nm(x), nm(v), inR(v, K) and h[v] == K and v != m))
    sec = [z for z in range(n) if z != m and h[z] == K and inR(z, K)]
    par = {nm(z): ([('B', nm(b_of(L, F, z)))] if inR(b_of(L, F, z), K - 1) else []) + [('A', nm(x)) for x in range(n) if inR(x, K - 1) and a_of(L, F, x) == z] for z in sec}
    print(f'{fn}: |L| {n}, K {K}, no cell {not ic(L, F, m)}; post-fixed tops of R_K−1 {[nm(x) for x in posts]}; '
          f'theorem replay (x, z, z a second top) {pred}; second tops and parents {par}')
