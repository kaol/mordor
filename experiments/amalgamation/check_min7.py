"""Regression check for single_claim_noic_fi_ahead_min7.json (log §34.3z¹⁶²–¹⁶³): which hypotheses of the
FeederStage crossing / side-interval lemmas hold in the seven-element model (Lean indexing k = h(m) − 1)."""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, b_of
from gfp_top import ystar
d = json.load(open('single_claim_noic_fi_ahead_min7.json'))
L = ss.Lat(d['sets']); F = d['F']; m = d['m']; le = L.le; h = L.rank; n = L.n
st = stages(L, F); R = lambda j: [z for z in range(n) if st[z] is not None and st[z] <= j]
k = h[m] - 1; mp = b_of(L, F, m); y = ystar(L, F, m); w = F[m][y]
nm = lambda z: '{' + ''.join(str(i) for i in range(8) if L.S[z] >> i & 1) + '}'
print('m', nm(m), 'm\'', nm(mp), 'y*', nm(y), 'w', nm(w), 'k', k, 'stages', {nm(z): st[z] for z in range(n)})
print('m\' ∈ R_k:', mp in R(k), ' m ∉ R_k:', m not in R(k))
print('hall (R_{k+1} heights ≤ k+1):', all(h[z] <= k + 1 for z in R(k + 1)))
print('huniq (m unique height-(k+1) in R_{k+1}):', [nm(z) for z in R(k + 1) if h[z] == k + 1])
print('index-tight at k (R_k heights ≤ k):', all(h[z] <= k for z in R(k)))
print("F m' w ≤ w:", le[F[mp][w]][w], " w ∥ m:", not le[w][m] and not le[m][w])
