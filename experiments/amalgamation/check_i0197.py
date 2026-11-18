"""Regression check for §34.3z¹⁹⁷ (the i = 0 case): re-verify the MinUpCell hypotheses (¬IC(m) reported) and UpCell;
for the stored non-ascending row x below its terminal source q′, the case (A1: x = q′; A2: x ⋖ q′), p = b(q′) with
its relations to q′ and x, heights and stages.   python3 check_i0197.py [FILE.json ...]"""
import json, sys, glob
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ic
for fn in sys.argv[1:] or sorted(glob.glob('i0_*.json')):
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; x = d['x']; q = d['q']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j; K = h[m]; k = K - 1
    W_ = max(z.bit_length() for z in L.S); nm = lambda z: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[z] >> j_ & 1) + '}'
    mono = all(le[F[u][y]][F[u2][y2]] for u in range(n) for u2 in range(n) if le[u][u2] for y in range(n) for y2 in range(n) if le[y][y2])
    hyp = mono and all(h[z] <= K for z in range(n) if inR(z, K)) and inR(m, K) and not inR(m, K - 1) and m != L.top
    X = [z for z in range(n) if inR(z, k) and h[z] == k]
    upc = any(le[z][y] and y != z and not le[m][y] and (le[F[z][y]][z] or le[y][F[z][y]]) for z in X for y in range(n))
    rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
    p = b_of(L, F, q)
    print(f'== {fn}: |L| = {n}, K = {K}; MinUpCell hypotheses except ¬IC(m) hold: {hyp}; IC(m) = {ic(L, F, m)}; UpCell = {upc}; m = {nm(m)}')
    print(f'   x = {nm(x)} (h {h[x]}, non-ascending {not le[x][a_of(L, F, x)]}), q′ = {nm(q)} (stage {st[q]}, h {h[q]}): '
          f'{"A1" if x == q else "A2"}; p = b(q′) = {nm(p)} (stage {st[p]}, h {h[p]}), p vs q′ {rl(p, q)}, p vs x {rl(p, x)}, F(p, q′) = {nm(F[p][q])}')
