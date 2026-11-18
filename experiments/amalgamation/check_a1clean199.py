"""Regression check for §34.3z¹⁹⁹: re-verify the MinUpCell hypotheses (¬IC(m) reported) and UpCell; list every
A1-shape configuration (p ⋖ c, F(p,c) = p, c a height-k row) with its fibre columns u, exceptions E_u, their join and
comparable columns; and the UpCell rows with their A-response class.   python3 check_a1clean199.py [FILE.json ...]"""
import json, sys, glob
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ic
for fn in sys.argv[1:] or sorted(glob.glob('a1c_*.json')):
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank; jn = L.join
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j; K = h[m]; k = K - 1
    W_ = max(z.bit_length() for z in L.S); nm = lambda z: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[z] >> j_ & 1) + '}'
    mono = all(le[F[u][y]][F[u2][y2]] for u in range(n) for u2 in range(n) if le[u][u2] for y in range(n) for y2 in range(n) if le[y][y2])
    hyp = mono and all(h[z] <= K for z in range(n) if inR(z, K)) and inR(m, K) and not inR(m, K - 1) and m != L.top
    X = [z for z in range(n) if inR(z, k) and h[z] == k]
    cells = lambda x: [nm(z) for z in range(n) if le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]])]
    print(f'== {fn}: |L| = {n}, K = {K}; MinUpCell hypotheses except ¬IC(m) hold: {hyp}; IC(m) = {ic(L, F, m)}; m = {nm(m)}')
    for c in X:
        for p in L.covers_dn[c]:
            if st[p] is None or F[p][c] != p: continue
            for u in range(n):
                if not (le[c][u] and u != c and not le[m][u] and F[p][u] == c): continue
                E = [e for e in range(n) if le[c][e] and e != c and le[e][u] and F[p][e] == p]
                zs = [z for z in range(n) if le[c][z] and z != c and le[z][u] and (le[F[c][z]][z] or le[z][F[c][z]])]
                print(f'   ({nm(p)} ⋖ {nm(c)}), b(c) = p: {b_of(L, F, c) == p}; fibre column {nm(u)}: exceptions {[nm(e) for e in E]}, '
                      f'comparable columns {[nm(z) for z in zs]}' + (f', ¬IC(m) response F(m, m ⊔ e) = {[nm(F[m][jn[m][e]]) for e in E]}' if E else ''))
    for x in X:
        if cells(x):
            ax = a_of(L, F, x); cls = 'stationary' if ax == x else 'target' if ax == m else 'other ascending' if le[x][ax] else 'non-ascending'
            print(f'   UpCell row {nm(x)} ({cls}; b(x) = {nm(b_of(L, F, x))}): off-m cells {cells(x)}')
