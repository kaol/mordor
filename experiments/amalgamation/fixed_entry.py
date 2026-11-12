"""Entry time versus height for fixed-point values (log §34.3z¹⁵⁷).

Also tests index-free feeder identity: m' ∈ R_{h(m')}, t ⋗ m', t ∉ R_{h(m')}, F(m', t) ≤ m' ⇒ b(t) = m'.
Lemma H (candidate): every b-value c = b(y) lying in the orbit closure has τ(c) ≤ h(c) (it enters no later than its
height). Compared with the same statement for a-values a(x) (x in the orbit) and for arbitrary orbit elements.
  python3 fixed_entry.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = None; fx = [None]
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n
        Bv = {b_of(L, F, y) for y in range(n)}; Av = {a_of(L, F, x) for x in range(n) if st[x] is not None}
        T['instances'] += 1
        for name, S in (('b-values', Bv), ('a-values of orbit elements', Av), ('all orbit elements', set(range(n)))):
            bad = [c for c in S if st[c] is not None and st[c] > L.rank[c]]
            T[(name + ': some τ > h', bool(bad))] += 1
            if name == 'b-values' and bad and (ex is None or n < ex[0]): ex = (n, L.S, F, bad)
        for mp in range(n):                       # index-free feeder identity
            if st[mp] is None or st[mp] > L.rank[mp] or L.rank[mp] < 1: continue
            k = L.rank[mp]
            for t in L.covers_up[mp]:
                if (st[t] is None or st[t] > k) and L.le[F[mp][t]][mp]:
                    T['feeder configurations'] += 1
                    if b_of(L, F, t) != mp:
                        T['feeder identity fails'] += 1
                        if fx[0] is None or n < fx[0][0]: fx[0] = (n, L.S, F, mp, t)
    for k, v in sorted(T.items(), key=str): print(k, v)
    if fx[0]:
        import json; print('smallest feeder failure |L| =', fx[0][0]); json.dump(dict(sets=fx[0][1], F=fx[0][2], mp=fx[0][3], t=fx[0][4]), open(f'feeder_fail_s{sys.argv[1]}.json', 'w'))
    if ex:
        print('smallest b-value with τ > h: |L| =', ex[0])
        import json; json.dump(dict(sets=ex[1], F=ex[2], bad=ex[3]), open(f'lemmaH_fail_s{sys.argv[1]}.json', 'w'))
