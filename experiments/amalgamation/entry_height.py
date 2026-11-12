"""Entry time versus height on index-tight stages (log §34.3z¹⁵⁶).

For random orbits and every stage k that is index-tight (R_k heights ≤ k, ⊤ ∉ R_{k+1}), count elements z ∈ R_k by
the sign of τ(z) − h(z) (τ = first-entry stage), and in particular new elements at k (τ = k) of height < k.
  python3 entry_height.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n
        allt = True
        for k in range(1, st[L.top] - 1):
            R = [z for z in range(n) if st[z] <= k]
            tight = max(L.rank[z] for z in R) <= k
            allt = allt and tight
            if not tight: continue
            T[('index-tight stage; all earlier stages index-tight', allt)] += 1
            new = [z for z in R if st[z] == k]
            T[('some new element of height < k', any(L.rank[z] < k for z in new), allt)] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
