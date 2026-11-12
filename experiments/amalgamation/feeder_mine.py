"""How does a feeder m' enter, and what puts b(t) into R_{k−1}? (log §34.3z¹⁵⁷)

Feeder configurations (m' ∈ R_k, k = h(m'), t > m', t ∉ R_k, F(m', t) ≤ m'; then b(t) = m' by exact/random
evidence). For the a-generators x ∈ R_{k−1} (m' ≤ a(x)) and b-generators g (m' ≤ g, b(g) ∈ R_{k−1}) of m', record
candidate relations.  python3 feeder_mine.py SEED SECONDS
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
        F = ss.make_F(L, g); st = stages(L, F); n = L.n; le = L.le
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
        inR = lambda z, j: j >= 0 and st[z] is not None and st[z] <= j
        for mp in range(n):
            k = L.rank[mp]
            if k < 1 or not inR(mp, k): continue
            for t in range(n):
                if not (le[mp][t] and t != mp and not inR(t, k) and le[F[mp][t]][mp]): continue
                T['configurations'] += 1
                assert B[t] == mp
                Ga = [x for x in range(n) if inR(x, k - 1) and le[mp][A[x]]]
                Gb = [y for y in range(n) if le[mp][y] and inR(B[y], k - 1)]
                T[('mp ∈ R_{k−1}', inR(mp, k - 1))] += 1
                T[('generators (a, b)', bool(Ga), bool(Gb))] += 1
                if Ga:
                    T[('a-gen: some x ≥ mp', any(le[mp][x] for x in Ga))] += 1
                    T[('a-gen: some x with F(x, t) ≤ x', any(le[F[x][t]][x] for x in Ga))] += 1
                    T[('a-gen: some x with t ≤ a(x)', any(le[t][A[x]] for x in Ga))] += 1
                if Gb:
                    T[('b-gen: some g ≥ t', any(le[t][y] for y in Gb))] += 1
                    T[('b-gen: some g with b(g) = mp', any(B[y] == mp for y in Gb))] += 1
                    T[('b-gen: mp itself (b(mp) ∈ R_{k−1})', mp in Gb)] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
