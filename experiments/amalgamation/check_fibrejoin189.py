"""Regression check for §34.3z¹⁸⁹ (fibre-join dichotomy): for each stored model re-verify the harness hypotheses and
list every stage-k sibling configuration (p, c) with its fibre S(p, c; m), join U = ⋁S and case (stable: F(p,U) = c,
m ≰ U; jump), whether S is down-closed in (c, ·), FibreTopAt, the row-c values on S, and TopFibre / UpCell for the model.
  python3 check_fibrejoin189.py [FILE.json ...]"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ic
FILES = ['single_claim_stabletop_multi_nopostlayer_min8.json', 'single_claim_pairjump_multi_nopostlayer_min11.json',
         'fj_fail_stable_min10.json', 'fj_fail_jump_min12.json']
for fn in sys.argv[1:] or FILES:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    W_ = max(x.bit_length() for x in L.S); nm = lambda q: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[q] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    mp = b_of(L, F, m); tight = lambda j: all(h[x] <= j for x in range(n) if inR(x, j))
    new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
    hyp = (mono and tight(K) and tight(K - 1) and new(m, K) and mp in L.covers_dn[m] and le[F[mp][m]][mp] and not ic(L, F, m)
           and not inR(L.top, K + 1))
    upat = lambda x: any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))
    print(f'== {fn}: |L| = {n}, K = {K}, k = {k}; harness hypotheses hold: {hyp}; m = {nm(m)}, m′ = {nm(mp)}')
    anyft = False
    for c in range(n):
        if not new(c, k): continue
        for p in range(n):
            if not (inR(p, k - 1) and h[p] == k - 1 and le[p][c] and p != c and F[p][c] == p): continue
            S = [v for v in range(n) if le[c][v] and v != c and not le[m][v] and F[p][v] == c]
            if not S: continue
            U = S[0]
            for v in S[1:]: U = L.join[U][v]
            case = 'stable' if (F[p][U] == c and not le[m][U]) else ('jump, m ≤ U' if le[m][U] else 'jump, m ≰ U')
            down = all(F[p][y] == c for v in S for y in range(n) if le[c][y] and y != c and le[y][v])
            ft = any(le[F[c][y]][y] or le[y][F[c][y]] for y in S); anyft |= ft
            print(f'   config (p, c) = ({nm(p)}, {nm(c)}): S = {[nm(v) for v in S]}, U = {nm(U)} [{case}], F(p, U) = {nm(F[p][U])}, '
                  f'S down-closed: {down}, row c on S: {[nm(F[c][v]) for v in S]}, FibreTopAt: {ft}, UpAt(c): {upat(c)}')
    print(f'   TopFibre (some configuration): {anyft}; UpCell at stage k: {any(inR(x, k) and h[x] == k and upat(x) for x in range(n))}')
