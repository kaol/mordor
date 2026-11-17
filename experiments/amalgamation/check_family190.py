"""Regression check for §34.3z¹⁹⁰ (configuration family): for each stored model, re-verify the harness hypotheses
(¬IC(m) reported, not required, so the IC-ablation models can be checked too), list every stage-k sibling configuration
(p, c) with its source ancestry b(p), fibre, goodness (a fibre column comparable with its row-c value), and for bad ones
the row values t = F(c, y) with their transfer c′ = F(p, t); finally UpCell at stage k.
  python3 check_family190.py [FILE.json ...]"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ic
FILES = ['fam_nosamesource_min13.json', 'fam_noescape_min8.json', 'single_claim_upcell_multi_nopostlayer_icok_needcfg_min6.json',
         'single_claim_upcell_multi_nopostlayer_icok_needcfg_rmin3_min11.json']
for fn in sys.argv[1:] or FILES:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    W_ = max(x.bit_length() for x in L.S); nm = lambda q: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[q] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    mp = b_of(L, F, m); tight = lambda j: all(h[x] <= j for x in range(n) if inR(x, j))
    new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
    hyp = {'monotone': mono, 'R_K, R_{K−1} tight': tight(K) and tight(K - 1), 'm new at K': new(m, K), '⊤ ∉ R_{K+1}': not inR(L.top, K + 1),
           "m′ = b(m) ⋖ m, F(m′,m) ≤ m′, m′ ∈ R_{K−1}": mp in L.covers_dn[m] and le[F[mp][m]][mp] and inR(mp, K - 1)}
    fib = lambda p, c: [v for v in range(n) if le[c][v] and v != c and not le[m][v] and F[p][v] == c]
    cfg = [(p, c) for c in range(n) if new(c, k) for p in range(n) if inR(p, k - 1) and h[p] == k - 1 and le[p][c] and p != c and F[p][c] == p and fib(p, c)]
    upat = lambda x: any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))
    print(f'== {fn}: |L| = {n}, K = {K}, k = {k}; hypotheses hold: {all(hyp.values())}', '' if all(hyp.values()) else hyp,
          f'; IC(m) = {ic(L, F, m)}; m = {nm(m)}, m′ = {nm(mp)}')
    for p, c in cfg:
        S = fib(p, c); good = any(le[F[c][y]][y] or le[y][F[c][y]] for y in S)
        line = f'   ({nm(p)}, {nm(c)}): b(p) = {nm(b_of(L, F, p))}, c = m′: {c == mp}, S = {[nm(v) for v in S]}, good = {good}'
        if not good:
            line += ', transfers ' + str([(nm(y), 't = ' + nm(F[c][y]), 'c′ = ' + nm(F[p][F[c][y]]), 'm ≤ t' if le[m][F[c][y]] else 'm ≰ t') for y in S])
        print(line)
    print(f'   stage-k tops: {[nm(x) for x in range(n) if inR(x, k) and h[x] == k]}; UpCell at stage k: {any(inR(x, k) and h[x] == k and upat(x) for x in range(n))}')
