# Non-vacuous critical-pair tests on finite lattices (where R(F) = L by cut_finite).
# E1  B(r) = {y : b y <= r} directed?  (equivalently b(VB(r)) <= r)
# E2  delay of the ideal step inside R: least k with kstep(r) in step^k(down r), max over r
# E3  orbit stage index: least k with r_j in R_k, versus j
import itertools, random, sys
def closure(n, rel):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in rel: le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    return le
def prod(l1, l2):
    n1, n2 = len(l1), len(l2)
    idx = [(i, j) for i in range(n1) for j in range(n2)]
    return [[l1[a][c] and l2[b][d] for (c, d) in idx] for (a, b) in idx]
def chain(n): return closure(n, [(i, i + 1) for i in range(n - 1)])
def Mn(k): return closure(k + 2, [(0, i) for i in range(1, k + 1)] + [(i, k + 1) for i in range(1, k + 1)])
N5 = closure(5, [(0, 1), (1, 2), (2, 4), (0, 3), (3, 4)])
LATS = {'M3': Mn(3), 'M4': Mn(4), 'N5': N5, '2x3': prod(chain(2), chain(3)), 'B3': prod(prod(chain(2), chain(2)), chain(2)),
        '3x3': prod(chain(3), chain(3)), 'M3xC2': prod(Mn(3), chain(2)), 'N5xC2': prod(N5, chain(2)), '3x4': prod(chain(3), chain(4))}
def setup(le):
    n = len(le)
    def join(x, y):
        ub = [z for z in range(n) if le[x][z] and le[y][z]]
        return [z for z in ub if all(le[z][w] for w in ub)][0]
    J = [[join(x, y) for y in range(n)] for x in range(n)]
    bot = [z for z in range(n) if all(le[z][w] for w in range(n))][0]
    top = [z for z in range(n) if all(le[w][z] for w in range(n))][0]
    return n, J, bot, top
def run(name, trials):
    le = LATS[name]; n, J, bot, top = setup(le)
    def sup(S):
        r = bot
        for s in S: r = J[r][s]
        return r
    stats = {'E1_fail': 0, 'E2_max': 0, 'E2_hist': {}, 'E3_max_gap': 0}
    for _ in range(trials):
        G = [[random.randrange(n) for _ in range(n)] for _ in range(n)]
        F = [[sup(G[x2][y2] for x2 in range(n) for y2 in range(n) if le[x2][x] and le[y2][y]) for y in range(n)] for x in range(n)]
        def a(x):
            y = top
            while True:
                y2 = F[x][y]
                if y2 == y: return y
                y = y2
        def b(y):
            x = bot
            while True:
                x2 = F[x][y]
                if x2 == x: return x
                x = x2
        A = [a(x) for x in range(n)]; B = [b(y) for y in range(n)]
        def step(D):
            T = set(D) | {A[x] for x in D} | {y for y in range(n) if B[y] in D}
            return frozenset(z for z in range(n) if any(le[z][t] for t in T))
        def kstep(r): return sup([r, A[r]] + [y for y in range(n) if le[B[y]][r]])
        for r in range(n):
            Br = [y for y in range(n) if le[B[y]][r]]
            if not le[B[sup(Br)]][r]: stats['E1_fail'] += 1
            D = frozenset(z for z in range(n) if le[z][r]); k = 0; t = kstep(r)
            while t not in D:
                D2 = step(D)
                if D2 == D: k = None; break
                D = D2; k += 1
            if k is not None:
                stats['E2_max'] = max(stats['E2_max'], k); stats['E2_hist'][k] = stats['E2_hist'].get(k, 0) + 1
        # E3
        Rs = [frozenset(z for z in range(n) if le[z][bot])]
        while len(Rs) < 4 * n: Rs.append(step(Rs[-1]))
        r, j = bot, 0
        while True:
            kk = next(i for i, D in enumerate(Rs) if r in D)
            stats['E3_max_gap'] = max(stats['E3_max_gap'], kk - j)
            if r == top: break
            r, j = kstep(r), j + 1
    print(name, n, 'elements,', trials, 'random F:', 'E1 B(r) non-directed (pairs F,r):', stats['E1_fail'],
          '| E2 max delay', stats['E2_max'], dict(sorted(stats['E2_hist'].items())), '| E3 max (stage - orbit index)', stats['E3_max_gap'], flush=True)
random.seed(1)
for nm in sys.argv[2:]: run(nm, int(sys.argv[1]))
