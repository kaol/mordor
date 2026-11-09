"""The non-diagonal residue (log §34.3z¹⁴¹).

At tight stages with no diagonal top element, for each top m with an interval cell (y > m: F(m, y) ≤ m or
y ≤ F(m, y)) record: F(m, m) ≤ m?, the entry route of m (m = a(x) for an earlier x; b(m) in an earlier stage),
b(m) ≤ m?, and the cell type.  python3 residue.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); P = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F)
        A = [a_of(L, F, x) for x in range(L.n)]; B = [b_of(L, F, y) for y in range(L.n)]
        for k in range(st[L.top] - 1):
            R = [z for z in range(L.n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            M = [z for z in R if L.rank[z] == k]
            if any(L.le[m][F[m][m]] for m in M): continue
            T['residue stages'] += 1
            for m in M:
                j = st[m]
                via_a = any(A[x] == m for x in range(L.n) if st[x] <= j - 1)
                via_b = st[B[m]] <= j - 1
                cells = set()
                for y in range(L.n):
                    if y != m and L.le[m][y]:
                        if L.le[F[m][y]][m]: cells.add('lower')
                        if L.le[y][F[m][y]]: cells.add('upper')
                P[('F(m,m)<=m', L.le[F[m][m]][m], 'via', 'a' if via_a else '', 'b' if via_b else '',
                   'b(m)<=m', L.le[B[m]][m], 'cells', tuple(sorted(cells)))] += 1
    print(dict(T)); [print(v, k) for k, v in P.most_common()]
