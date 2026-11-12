"""Single-element tight top layers (log §34.3z¹⁵³).

At tight stages with T_k = {m} and m non-diagonal (m ≰ F(m, m)), which columns y > m give the interval cell
(F(m, y) ≤ m or y ≤ F(m, y))?  Records: whether some cover of m works; whether named terms work
(m ⊔ F(m, ⊤), m ⊔ a(m), ⊤, m ⊔ F(⊥, ⊤), m ⊔ b(⊤)); the cell type (lower / upper); the entry route of m; and
the limit y* of the orbit y ↦ m ⊔ F(m, y) from ⊤ (y* = m: lower cell; m ≤ F(m, y*): upper cell; otherwise open).
Random instances as in orbit_mech.py.  python3 single_top.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
        for k in range(1, st[L.top] - 1):
            R = [z for z in range(n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            Tk = [z for z in R if L.rank[z] == k]
            if len(Tk) != 1: continue
            m = Tk[0]
            if L.le[m][F[m][m]]: continue
            T['single non-diagonal stages'] += 1
            good = [y for y in range(n) if y != m and L.le[m][y] and (L.le[F[m][y]][m] or L.le[y][F[m][y]])]
            kinds = {('lower' if L.le[F[m][y]][m] else 'upper') for y in good}
            T[('cell kinds', tuple(sorted(kinds)))] += 1
            T[('some cover of m works', any(y in L.covers_up[m] for y in good))] += 1
            for nm, y in (('m ⊔ F(m,⊤)', L.join[m][F[m][L.top]]), ('m ⊔ a(m)', L.join[m][A[m]]), ('⊤', L.top),
                          ('m ⊔ F(⊥,⊤)', L.join[m][F[L.bot][L.top]]), ('m ⊔ b(⊤)', L.join[m][B[L.top]])):
                T[(nm, y in good)] += 1
            j = st[m] - 1
            aent = any(A[x] == m for x in R if st[x] <= j)
            T[('entry', 'a' if aent else 'b')] += 1
            T[('F(m,m) ≤ m', L.le[F[m][m]][m])] += 1
            y = L.top                                     # the orbit of y ↦ m ⊔ F(m, y) from ⊤ in [m, ⊤]
            while True:
                y2 = L.join[m][F[m][y]]
                if y2 == y: break
                y = y2
            if y == m: T[('gfp', 'reaches m: lower cell')] += 1
            elif L.le[m][F[m][y]]: T[('gfp', 'y* > m, m ≤ F(m,y*): upper cell')] += 1
            else: T[('gfp', 'y* > m, F(m,y*) ∥ m', 'IC elsewhere' if good else 'no IC')] += 1
            T[('TightIC (all tops) holds', bool(good))] += 1
    print(dict(sorted(T.items(), key=str)), flush=True)
