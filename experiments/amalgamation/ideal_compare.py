"""R-orbit against the ideal orbit (log §34.3z¹⁴⁰): is r_k ∈ R_k (tightness)? max height of R_k − height of r_k;
height of r_k − k. Random instances as in orbit_mech.py.  python3 ideal_compare.py SEED SECONDS
"""
import sys, random, time, collections; sys.path.insert(0, '.'); sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, ideal_orbit
rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
while time.time() - t0 < float(sys.argv[2]):
    L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
    if L.height < 2 or L.n > 40: continue
    _, g, gens = ss.random_instance(0, 0, rng, L)
    if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
    F = ss.make_F(L, g); st = stages(L, F); K = st[L.top]; r = ideal_orbit(L, F, K)
    for k in range(K + 1):
        R = [z for z in range(L.n) if st[z] <= k]; mh = max(L.rank[z] for z in R)
        T[('r_k in R_k', st[r[k]] <= k)] += 1
        T[('maxheight R_k vs height r_k', mh - L.rank[r[k]])] += 1
        T[('height r_k - k', min(L.rank[r[k]] - k, 3))] += 1
print(dict(sorted(T.items(), key=str)))
