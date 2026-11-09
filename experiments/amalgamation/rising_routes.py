"""How does the rising element enter? (log §34.3z¹⁴⁰)

At tight stages (max height of R_k = k, ⊤ ∉ R_{k+1}), over all m ∈ R_k of height k and y > m in R_{k+1}, the routes:
  'b(y)≤m'  : b(y) ≤ m (the lower alternative of the principal cut in [m, ⊤]);
  'b(y)∈R_k': b(y) ∈ R_k but b(y) ≰ m;
  'y≤a(x)'  : y ≤ a(x) for some x ∈ R_k.
Per tight stage, reports which routes are available for SOME rising pair, and whether the route b(y) ≤ m alone
always suffices.  python3 rising_routes.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F)
        A = [a_of(L, F, x) for x in range(L.n)]; B = [b_of(L, F, y) for y in range(L.n)]
        for k in range(st[L.top] - 1):
            R = [z for z in range(L.n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            routes = set()
            for m in R:
                if L.rank[m] != k: continue
                for y in range(L.n):
                    if y == m or not L.le[m][y] or st[y] > k + 1: continue
                    if L.le[B[y]][m]: routes.add('b(y)≤m')
                    elif st[B[y]] <= k: routes.add('b(y)∈R_k')
                    if any(L.le[y][A[x]] for x in R): routes.add('y≤a(x)')
            T[tuple(sorted(routes))] += 1
    print(dict(T.most_common()), flush=True)
