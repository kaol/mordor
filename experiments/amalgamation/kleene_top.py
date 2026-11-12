"""Goodness of column Kleene chains (log §34.3z¹⁵⁸). For every random F: the Kleene chain ⊥, F(⊥, y), F(F(⊥, y), y), …
of column y (up to b(y)); are its elements good (x ∈ R_{h(x)})? Column y = ⊤ versus arbitrary columns.
  python3 kleene_top.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = None
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n; rk = L.rank
        good = lambda z: st[z] is not None and st[z] <= rk[z]
        T['instances'] += 1
        for y in range(n):
            x = L.bot; chain = [x]
            while F[x][y] != x: x = F[x][y]; chain.append(x)
            ok = all(good(c) for c in chain)
            T[('column ⊤: chain good' if y == L.top else 'other column: chain good', ok)] += 1
            if y == L.top and not ok and (ex is None or n < ex[0]): ex = (n, L.S, F)
    for k, v in sorted(T.items(), key=str): print(k, v)
    if ex: print('smallest column-⊤ failure |L| =', ex[0]); json.dump(dict(sets=ex[1], F=ex[2]), open(f'kleene_top_fail_s{sys.argv[1]}.json', 'w'))
