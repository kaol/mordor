"""Which laws between the two powers force m = n? (foundations v3.8, docs/02-the-source.md §3)

For every monotone F on small lattices: a(x) = νY.F(x,Y), b(y) = μX.F(X,y), m = μa, n = νb, the closure
T_b x = μY. x ∨ b(Y) and the interior D_a x = νY. x ∧ a(Y). Candidate laws (pointwise, all x):
  semi    b(a x) ≤ a(b x)                  the derived law (semi-CL's hypothesis)
  comm    a(b x) = b(a x)                  CL's hypothesis
  gsos    b(x ∧ a x) ≤ a(T_b x)            GSOS-style: the rule sees its argument and its behaviour
  semiT   b(a x) ≤ a(T_b x)                target in the closure
  clint   T_b(D_a x) ≤ D_a(T_b x)          law between closure and interior
  semi_f  b(a z) ≤ a(b z) only at bi-fixed-point-free z? (omitted)
A law is *sound* on a lattice if every F satisfying it has m = n. Reported: #F satisfying, #violators (m ≠ n).

  python3 laws.py"""
import itertools, sys


class Lat:
    def __init__(self, name, n, le):
        self.name, self.n, self.le = name, n, le
        R = range(n)
        self.bot = next(x for x in R if all(le[x][y] for y in R))
        self.top = next(x for x in R if all(le[y][x] for y in R))
        def lub(x, y):
            ub = [z for z in R if le[x][z] and le[y][z]]
            return next(z for z in ub if all(le[z][w] for w in ub))
        def glb(x, y):
            lb = [z for z in R if le[z][x] and le[z][y]]
            return next(z for z in lb if all(le[w][z] for w in lb))
        self.join = [[lub(x, y) for y in R] for x in R]
        self.meet = [[glb(x, y) for y in R] for x in R]

    def lfp(self, f):
        x = self.bot
        while True:
            y = f(x)
            if y == x: return x
            x = y

    def gfp(self, f):
        x = self.top
        while True:
            y = f(x)
            if y == x: return x
            x = y


def chain(k): return Lat(f"C{k}", k, [[i <= j for j in range(k)] for i in range(k)])
def from_covers(name, n, rel):
    le = [[i == j for j in range(n)] for i in range(n)]
    for i, j in rel: le[i][j] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    return Lat(name, n, le)

B2 = from_covers("B2", 4, [(0, 1), (0, 2), (1, 3), (2, 3)])
N5 = from_covers("N5", 5, [(0, 1), (1, 2), (2, 4), (0, 3), (3, 4)])
M3 = from_covers("M3", 5, [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (3, 4)])


def monotone_F(L):
    """All monotone F : L × L → L, by backtracking over cells in a linear extension of the product order."""
    n, le = L.n, L.le
    cells = sorted(itertools.product(range(n), range(n)),
                   key=lambda c: (sum(le[z][c[0]] for z in range(n)) + sum(le[z][c[1]] for z in range(n))))
    F = {}
    def rec(i):
        if i == len(cells):
            yield dict(F); return
        x, y = cells[i]
        lo = [F[(p, q)] for (p, q) in F if le[p][x] and le[q][y]]
        hi = [F[(p, q)] for (p, q) in F if le[x][p] and le[y][q]]
        for v in range(n):
            if all(le[w][v] for w in lo) and all(le[v][w] for w in hi):
                F[(x, y)] = v
                yield from rec(i + 1)
                del F[(x, y)]
    yield from rec(0)


def analyse(L, F):
    R, le, J, M = range(L.n), L.le, L.join, L.meet
    a = [L.gfp(lambda Y: F[(x, Y)]) for x in R]
    b = [L.lfp(lambda X: F[(X, y)]) for y in R]
    m, n = L.lfp(lambda x: a[x]), L.gfp(lambda y: b[y])
    T = [L.lfp(lambda Y: J[x][b[Y]]) for x in R]
    D = [L.gfp(lambda Y: M[x][a[Y]]) for x in R]
    laws = {
        'comm': all(a[b[x]] == b[a[x]] for x in R),
        'semi': all(le[b[a[x]]][a[b[x]]] for x in R),
        'gsos': all(le[b[M[x][a[x]]]][a[T[x]]] for x in R),
        'semiT': all(le[b[a[x]]][a[T[x]]] for x in R),
        'clint': all(le[T[D[x]]][D[T[x]]] for x in R),
    }
    return m == n, laws


def main(lats):
    for L in lats:
        cnt = {k: [0, 0] for k in ('comm', 'semi', 'gsos', 'semiT', 'clint')}; tot = 0; eq = 0
        weaker = {k: 0 for k in cnt}
        for F in monotone_F(L):
            tot += 1; ok, laws = analyse(L, F); eq += ok
            for k, v in laws.items():
                if v:
                    cnt[k][0] += 1; cnt[k][1] += (not ok)
                    if not laws['semi']: weaker[k] += 1
        print(f"{L.name}: {tot} F, m = n for {eq}")
        for k, (s, v) in cnt.items():
            print(f"   {k:6s} holds for {s:7d}   violators (m ≠ n): {v:6d}   holds without semi: {weaker[k]}")
        sys.stdout.flush()


if __name__ == '__main__':
    main([chain(3), chain(4), B2, N5, M3] if len(sys.argv) < 2 else [eval(a) for a in sys.argv[1:]])
