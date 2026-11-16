"""Regression check of the side-entry counterexamples (log §34.3z¹⁶⁴): re-verify every hypothesis of the
uniqueness-free singleton configuration from the JSON and evaluate the localized side-entry candidates.
  python3 check_side.py FILE.json ...   (default: the four §34.3z¹⁶²–¹⁶⁴ models)"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar, ic
files = sys.argv[1:] or ['single_claim_side_w_multi_min5.json', 'single_claim_side_multi_min7.json', 'single_claim_below_w_multi_min8.json',
                         'single_claim_noic_fi_ahead_min7.json']
for fn in files:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); R = lambda j: [z for z in range(n) if st[z] is not None and st[z] <= j]; K = h[m]
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    mp = b_of(L, F, m); ys = ystar(L, F, m); w = F[m][ys]
    hyp = {'F monotone': mono, 'm ∈ R_K \\ R_{K−1}': m in R(K) and m not in R(K - 1),
           'R_K heights ≤ K': all(h[z] <= K for z in R(K)), 'R_{K−1} heights ≤ K−1': all(h[z] <= K - 1 for z in R(K - 1)),
           '⊤ ∉ R_{K+1}': L.top not in R(K + 1), "m′ = b(m) ⋖ m, m′ ∈ R_{K−1}, F(m′,m) ≤ m′": mp in L.covers_dn[m] and mp in R(K - 1) and le[F[mp][m]][mp],
           'no interval cell at m': not ic(L, F, m), 'm unique of height K in R_K': [z for z in R(K) if h[z] == K] == [m]}
    sec = [z for z in R(K) if h[z] == K and z != m]
    cand = {'w ∈ R_K': w in R(K), "(m′, w] ∩ R_K ≠ ∅": any(le[mp][z] and z != mp and le[z][w] for z in R(K)),
            'second ≤ w': any(le[z][w] for z in sec), "second > m′ (sibling)": any(le[mp][z] for z in sec), 'second exists': bool(sec)}
    print(f'== {fn}: |L| = {n}, K = {K}, w ∥ m: {not le[w][m] and not le[m][w]}')
    print('   hypotheses:', {k: v for k, v in hyp.items()})
    print('   side-entry candidates:', cand)
