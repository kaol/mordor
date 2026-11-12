"""Lemma G1* (log §34.3z¹⁵⁷), orbit-free: if F(c, c) = c = b(c) (c ≠ ⊥), then c ≤ a(z) for some z with
z = ⊥ or (F(z, z) ≤ z and h(z) < h(c)). Together with z = b(c) when b(c) < c, this gives by induction on j that R_j contains
every diagonal pre-fixed point of height ≤ j (Lemma G1). Random test with candidate witnesses.
  python3 g1star.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import a_of, b_of

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = None
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); n = L.n; le = L.le; rk = L.rank
        A = [a_of(L, F, x) for x in range(n)]
        D = [z for z in range(n) if le[F[z][z]][z] or z == L.bot]   # ⊥ ∈ R₀ always
        for c in range(n):
            if c == L.bot or F[c][c] != c or b_of(L, F, c) != c: continue
            T['cases'] += 1
            W = [z for z in D if rk[z] < rk[c] and le[c][A[z]]]
            T[('G1*', bool(W))] += 1
            if W:
                T[('some witness z < c', any(le[z][c] for z in W))] += 1
                T[('witness z = ⊥ possible', L.bot in W)] += 1
            elif ex is None or n < ex[0]: ex = (n, L.S, F, c)
    for k, v in sorted(T.items(), key=str): print(k, v)
    if ex: print('smallest G1* failure |L| =', ex[0]); json.dump(dict(sets=ex[1], F=ex[2], c=ex[3]), open(f'g1star_fail_s{sys.argv[1]}.json', 'w'))
