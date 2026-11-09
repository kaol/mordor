"""Upper principal cut (log §34.3z¹⁴⁰).

UPC(m): ∃ x ≤ m, ∃ y > m with F(x, y) ≤ x or y ≤ F(x, y). For m ∈ R_k every x ≤ m is in R_k, so UPC(m) puts some
y > m into R_{k+1}; UPC at one maximal-height element of a tight stage gives rising escape.
Tested: (all) UPC(m) for every m ≠ ⊤ of random instances; (tight) UPC for some / every maximal-height m ∈ R_k at
tight stages.  python3 upc.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages

def upc(L, F, m):
    return any(L.le[F[x][y]][x] or L.le[y][F[x][y]] for x in range(L.n) if L.le[x][m]
               for y in range(L.n) if y != m and L.le[m][y])

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = {}
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F)
        for m in range(L.n):
            if m == L.top: continue
            ok = upc(L, F, m); T[('UPC(m), all m', ok)] += 1
            if not ok and ('all' not in ex or L.n < ex['all']['n']): ex['all'] = dict(n=L.n, sets=L.S, F=F, m=m)
        for k in range(st[L.top] - 1):
            R = [z for z in range(L.n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            M = [z for z in R if L.rank[z] == k]; vals = [upc(L, F, m) for m in M]
            T[('tight: UPC for some top m', any(vals))] += 1; T[('tight: UPC for every top m', all(vals))] += 1
            if not any(vals) and ('some' not in ex or L.n < ex['some']['n']): ex['some'] = dict(n=L.n, sets=L.S, F=F, k=k)
    print(dict(sorted(T.items(), key=str)), {k: v['n'] for k, v in ex.items()}, flush=True)
    json.dump(ex, open(f'upc_viol_s{sys.argv[1]}.json', 'w'))
