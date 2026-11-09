"""Non-diagonal tight stages (log §34.3z¹⁴¹).

At tight stages where no top-height m ∈ R_k satisfies m ≤ F(m, m), classify the UPC cells (x ≤ m < y) at top m:
  'lower x=m' : F(m, y) ≤ m;   'lower x<m' : F(x, y) ≤ x, x < m;   'upper x=m': y ≤ F(m, y);   'upper x<m'.
Also test the candidate 'IC-lower': some top m (any) has y > m with F(m, y) ≤ m.
  python3 nondiag.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = None
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F)
        for k in range(st[L.top] - 1):
            R = [z for z in range(L.n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            M = [z for z in R if L.rank[z] == k]
            if any(L.le[m][F[m][m]] for m in M): continue
            kinds = set()
            for m in M:
                for y in range(L.n):
                    if y == m or not L.le[m][y]: continue
                    for x in range(L.n):
                        if not L.le[x][m]: continue
                        if L.le[F[x][y]][x]: kinds.add('lower x=m' if x == m else 'lower x<m')
                        if L.le[y][F[x][y]]: kinds.add('upper x=m' if x == m else 'upper x<m')
            T[tuple(sorted(kinds))] += 1
            T[('IC-lower', 'lower x=m' in kinds)] += 1
            if 'lower x=m' not in kinds and (ex is None or L.n < ex['n']): ex = dict(n=L.n, sets=L.S, F=F, k=k, stages=st)
    print(dict(T.most_common()), 'smallest without lower x=m:', ex and ex['n'], flush=True)
    if ex: json.dump(ex, open(f'nondiag_s{sys.argv[1]}.json', 'w'))
