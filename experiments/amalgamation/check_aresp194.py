"""Regression check for §34.3z¹⁹⁴: re-verify the MinUpCell hypotheses (¬IC(m) reported), classify every height-k row of
R_k by its A-response (stationary / target a x = m / other ascending / non-ascending), list its off-m pre-fixed columns
and off-m cells, the entry of m, and InitialPairOutside.   python3 check_aresp194.py [FILE.json ...]"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ic
for fn in sys.argv[1:] or ['ar_min_noIPO_min5.json', 'ar_min_noIPO_min11.json', 'ar_icok_noIPO_min4.json', 'ar_icok_noIPO_min11.json']:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    W_ = max(x.bit_length() for x in L.S); nm = lambda q: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[q] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    hyp = mono and all(h[z] <= K for z in range(n) if inR(z, K)) and inR(m, K) and not inR(m, K - 1) and m != L.top
    rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
    X = [x for x in range(n) if inR(x, k) and h[x] == k]
    entry = 'A-entered' if any(a_of(L, F, q) == m for q in range(n) if inR(q, k)) else f'B-entered, b(m) = {nm(b_of(L, F, m))}'
    print(f'== {fn}: |L| = {n}, K = {K}; MinUpCell hypotheses except ¬IC(m) hold: {hyp}; IC(m) = {ic(L, F, m)}; m = {nm(m)}; entry: {entry}')
    ipo = False
    for x in X:
        ax = a_of(L, F, x)
        cls = 'stationary' if ax == x else 'target' if ax == m else 'other ascending' if le[x][ax] else 'non-ascending'
        cols = [nm(v) for v in range(n) if le[x][v] and v != x and le[F[x][v]][v] and not le[m][v]]
        cells = [nm(z) for z in range(n) if le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]])]
        ipo |= bool(cols) and not le[x][m]
        print(f'   row {nm(x)} ({rl(x, m)} m): {cls}, a(x) = {nm(ax)}, b(x) = {nm(b_of(L, F, x))}; off-m pre-fixed columns {cols}; off-m cells {cells}')
    print(f'   InitialPairOutside: {ipo}')
