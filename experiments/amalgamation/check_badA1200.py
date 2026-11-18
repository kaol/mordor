"""Regression check for §34.3z²⁰⁰: in each stored model (an exact counterexample of 'a1cert genuine': MinUpCell
hypotheses, a genuine A1 configuration p = b(c) ⋖ c with c non-ascending and a fibre column u, no A1Cert), re-verify the
hypotheses and list t = F(c, u), a(c), and the forbidden rows (other ascending, stationary with an initial pair) with
their witnesses.   python3 check_badA1200.py [FILE.json ...]"""
import json, sys, glob
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ic
for fn in sys.argv[1:] or sorted(glob.glob('bad1_*.json')):
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; p, c, u = d['p'], d['c'], d['u']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j; K = h[m]; k = K - 1; jn = L.join
    W_ = max(z.bit_length() for z in L.S); nm = lambda z: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[z] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    hyp = mono and all(h[z] <= K for z in range(n) if inR(z, K)) and inR(m, K) and not inR(m, K - 1) and m != L.top and not ic(L, F, m)
    A = lambda z: a_of(L, F, z)
    gen = b_of(L, F, c) == p and p in L.covers_dn[c] and not le[c][A(c)] and F[p][u] == c and not le[m][u]
    X = [z for z in range(n) if inR(z, k) and h[z] == k]
    forb = [(nm(x), 'other ascending, a(x) = ' + nm(A(x))) for x in X if le[x][A(x)] and A(x) not in (x, m)] + \
           [(nm(x), 'stationary, columns ' + str([nm(v) for v in range(n) if le[x][v] and v != x and not le[m][v] and le[F[x][v]][v]])) for x in X
            if A(x) == x and any(le[x][v] and v != x and not le[m][v] and le[F[x][v]][v] for v in range(n))]
    print(f'== {fn}: |L| = {n}, K = {K}; MinUpCell hypotheses hold: {hyp}; genuine A1 (p = b(c) ⋖ c, c non-ascending, F(p,u) = c, m ≰ u): {gen}')
    print(f'   p = {nm(p)}, c = {nm(c)}, u = {nm(u)}, t = F(c, u) = {nm(F[c][u])}, a(c) = {nm(A(c))}, c ⊔ a(c) = {nm(jn[c][A(c)])}; forbidden rows {forb}')
