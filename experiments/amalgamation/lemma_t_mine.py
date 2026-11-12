"""Lemma T configurations (log §34.3z¹⁵⁷): m' ∈ R_j, j = h(m'), t > m', c = b(t) < m'. Then (evidence) c ∈ R_{j−1}.
Records how: whether all z < c lie in R_{j−2} (Lemma E route), τ(c) vs h(c), and c's generator type at τ(c).
  python3 lemma_t_mine.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n; le = L.le; rk = L.rank
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
        inR = lambda z, j: j >= 0 and st[z] is not None and st[z] <= j
        seen = set()
        for mp in range(n):
            j = rk[mp]
            if j < 1 or not inR(mp, j): continue
            for t in range(n):
                c = B[t]
                if not (le[mp][t] and t != mp and le[c][mp] and c != mp): continue
                if (mp, c) in seen: continue
                seen.add((mp, c)); T['configurations (m′, c)'] += 1
                T[('c ∈ R_{j−1}', inR(c, j - 1))] += 1
                T[('all z < c in R_{j−2}', all(inR(z, j - 2) for z in range(n) if le[z][c] and z != c))] += 1
                T[('all z < c in R_{h(c)−1}', all(inR(z, rk[c] - 1) for z in range(n) if le[z][c] and z != c))] += 1
                T[('τ(c) ≤ h(c)', st[c] is not None and st[c] <= rk[c])] += 1
                T[('b(c) < c', B[c] != c)] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
