"""G1–G3: which cells at c force c to be good (τ(c) ≤ h(c))? Entry lag along lower cells (log §34.3z¹⁵⁷). lag(z) = τ(z) − h(z). For pairs c < m' (m' in the orbit) with
F(c, m') ≤ c, compare lag(c) with lag(m').  python3 lag_mine.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n; le = L.le; rk = L.rank
        for c in range(n):
            if st[c] is None: continue
            lc = st[c] - rk[c]
            T['orbit elements'] += 1
            if le[F[c][c]][c]: T[('G1: F(c,c) ≤ c ⇒ good', lc <= 0)] += 1
            if any(y != c and le[c][y] and le[F[c][y]][c] for y in range(n)): T[('G2: lower cell at c ⇒ good', lc <= 0)] += 1
            if any(y != c and le[c][y] and le[y][F[c][y]] for y in range(n)): T[('G3: upper cell at c ⇒ good', lc <= 0)] += 1
        for mp in range(n):
            if st[mp] is None: continue
            for c in range(n):
                if c == mp or not le[c][mp] or not le[F[c][mp]][c]: continue
                lc, lm = st[c] - rk[c], st[mp] - rk[mp]
                T['pairs'] += 1
                T[('lag(c) ≤ max(lag(m′), 0)', lc <= max(lm, 0))] += 1
                T[('lag(c) ≤ lag(m′)', lc <= lm)] += 1
                T[('τ(c) ≤ τ(m′)', st[c] <= st[mp])] += 1
                T[('lag(m′) ≤ 0 and lag(c) > 0', lm <= 0 and lc > 0)] += 1
                T[('lag(c) ≤ 0', lc <= 0)] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
