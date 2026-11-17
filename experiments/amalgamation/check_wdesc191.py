"""Regression check for §34.3z¹⁹¹: descent witnesses (x, v) (x ∈ R_k of height k, x < v, F(x,v) ≤ v, m ≰ v, row x above
x on its pre-fixed columns in (x, v]) in the stored models where no witness is anchored at the column orbit
(v ≤ w, x < w, or v ≤ y*), with w = F(m, y*).   python3 check_wdesc191.py [FILE.json ...]"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, b_of
from gfp_top import ystar, ic
for fn in sys.argv[1:] or ['wd_no_le_w_min18.json', 'wd_no_xw_min18.json', 'wd_no_ys_min20.json']:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    W_ = max(x.bit_length() for x in L.S); nm = lambda q: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[q] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    mp = b_of(L, F, m); tight = lambda j: all(h[x] <= j for x in range(n) if inR(x, j))
    hyp = mono and tight(K) and tight(K - 1) and inR(m, K) and not inR(m, K - 1) and not ic(L, F, m) and not inR(L.top, K + 1)
    ys = ystar(L, F, m); w = F[m][ys]
    rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
    above = lambda x, v: all(le[x][F[x][u]] for u in range(n) if le[x][u] and u != x and le[u][v] and le[F[x][u]][u])
    print(f'== {fn}: |L| = {n}, K = {K}; hypotheses hold: {hyp}; m = {nm(m)}, m′ = {nm(mp)}, y* = {nm(ys)}, w = {nm(w)}')
    for x in range(n):
        if not (inR(x, k) and h[x] == k): continue
        ws = [v for v in range(n) if le[x][v] and x != v and le[F[x][v]][v] and not le[m][v] and above(x, v)]
        print(f'   row {nm(x)} (vs w {rl(x, w)}, vs m′ {rl(x, mp)}): witness columns {[(nm(v), "v vs w " + rl(v, w), "v vs y* " + rl(v, ys)) for v in ws]}')
