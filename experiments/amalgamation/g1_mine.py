"""Lemma G1 (log §34.3z¹⁵⁷): F(c, c) ≤ c ⇒ τ(c) ≤ h(c). The case b(c) = c (then F(c, c) = c and no x < c is
pre-fixed in column c). Records the last Kleene element x_n of the column-c chain (F(x_n, c) = c), its entry and
height, and alternative entry routes of c.  python3 g1_mine.py SEED SECONDS
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
        A = [a_of(L, F, x) for x in range(n)]
        for c in range(n):
            if c == L.bot or st[c] is None or not le[F[c][c]][c] or b_of(L, F, c) != c: continue
            T['b(c) = c cases'] += 1
            x = L.bot; chain = [x]
            while F[x][c] != c: x = F[x][c]; chain.append(x)
            xn = chain[-1]
            T[('last Kleene x_n good', st[xn] <= rk[xn])] += 1
            T[('x_n ∈ R_{h(c)−1}', st[xn] <= rk[c] - 1)] += 1
            T[('chain: every x_i ∈ R_i', all(st[xi] <= i for i, xi in enumerate(chain)))] += 1
            T[('some x < c in R_{h(c)−1} with c ≤ F(x, c)', any(le[x][c] and x != c and st[x] <= rk[c] - 1 and le[c][F[x][c]] for x in range(n)))] += 1
            T[('c ≤ a(x) for some x ∈ R_{h(c)−1} with x < c', any(le[x][c] and x != c and st[x] <= rk[c] - 1 and le[c][A[x]] for x in range(n)))] += 1
            T[('good', st[c] <= rk[c])] += 1
            D = [z for z in range(n) if le[z][c] and z != c and le[F[z][z]][z]]
            T[('some diag-pre-fixed z < c with c ≤ F(z, c)', any(le[c][F[z][c]] for z in D))] += 1
            T[('x_n diag-pre-fixed', le[F[xn][xn]][xn])] += 1
            T[('some z < c with z good and c ≤ F(z, c)', any(le[z][c] and z != c and st[z] <= rk[z] and le[c][F[z][c]] for z in range(n)))] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
