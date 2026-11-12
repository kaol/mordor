"""Which simple terms witness Rise in rigid maps? (log §34.3z¹⁵⁸) For rigid F (a(⊥) = ⊥, b(⊤) = ⊤, diagonal fixing
only ⊥, ⊤), test candidate terms x for "good and x < a(x)", split by lattice height.  python3 rise_witness.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.n > 40 or L.height < 2: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); n = L.n; le = L.le; rk = L.rank; bot, top = L.bot, L.top
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
        if A[bot] != bot or B[top] != top or any(F[c][c] == c for c in range(n) if c not in (bot, top)): continue
        st = stages(L, F); good = lambda z: st[z] is not None and st[z] <= rk[z]
        rises = lambda x: good(x) and le[x][A[x]] and A[x] != x
        h = L.height; v = F[bot][top]
        x = bot; chain = [x]
        while F[x][top] != top: x = F[x][top]; chain.append(x)
        cand = {'v = F(⊥,⊤)': v, 'b(v)': B[v], 'F(⊥,v)': F[bot][v], 'b(F(⊥,v))': B[F[bot][v]], 'x_n (column-⊤ chain)': chain[-1],
                'b(x_n)': B[chain[-1]], 'F(v,v)': F[v][v]}
        T[('rigid, height', h)] += 1
        for k, c in cand.items(): T[(h, k, rises(c))] += 1
        T[(h, 'some chain element', any(rises(c) for c in chain))] += 1
        T[(h, 'some element of R_1', any(rises(c) for c in range(n) if st[c] is not None and st[c] <= 1))] += 1
        T[(h, 'v or b(v) or x_n', rises(v) or rises(B[v]) or rises(chain[-1]))] += 1
    for k, val in sorted(T.items(), key=str): print(k, val)
