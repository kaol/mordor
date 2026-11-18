"""Regression check for §34.3z¹⁹⁶: in the stored pure-B models, re-verify the MinUpCell hypotheses (¬IC(m) reported),
UpCell, and for the stored non-ascending row x its terminal source q′ (x ≤ a^i(q′)), the B-chain q′, b(q′), … with the
stages, and the ascent of each element.   python3 check_bgenealogy196.py [FILE.json ...]"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ic
for fn in sys.argv[1:] or ['bg_icok_pureB_min4.json', 'bg_min_pureB_min6.json']:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; x = d['x']; q = d['q']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j; K = h[m]; k = K - 1
    W_ = max(z.bit_length() for z in L.S); nm = lambda z: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[z] >> j_ & 1) + '}'
    mono = all(le[F[u][y]][F[u2][y2]] for u in range(n) for u2 in range(n) if le[u][u2] for y in range(n) for y2 in range(n) if le[y][y2])
    hyp = mono and all(h[z] <= K for z in range(n) if inR(z, K)) and inR(m, K) and not inR(m, K - 1) and m != L.top
    X = [z for z in range(n) if inR(z, k) and h[z] == k]
    upc = any(le[z][y] and y != z and not le[m][y] and (le[F[z][y]][z] or le[y][F[z][y]]) for z in X for y in range(n))
    A = lambda z: a_of(L, F, z); B = lambda z: b_of(L, F, z)
    chain = [q]
    while st[chain[-1]] > 1: chain.append(B(chain[-1]))
    print(f'== {fn}: |L| = {n}, K = {K}; MinUpCell hypotheses except ¬IC(m) hold: {hyp}; IC(m) = {ic(L, F, m)}; UpCell = {upc}; m = {nm(m)}')
    print(f'   row x = {nm(x)} (a(x) = {nm(A(x))}, non-ascending: {not le[x][A(x)]}); terminal source q′ = {nm(q)} (stage {st[q]}, height {h[q]}, '
          f'q′ ≤ a(q′): {le[q][A(q)]}), x ≤ q′: {le[x][q]}')
    print(f'   B-chain: {[(nm(z), "stage " + str(st[z]), "h " + str(h[z])) for z in chain]} → b = {nm(B(chain[-1]))} (⊥: {B(chain[-1]) == L.bot})')
