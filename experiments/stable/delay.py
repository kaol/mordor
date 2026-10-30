# Adversarial search: maximize delay(F, r) = least k with kstep(r) in step^k(down r).
import random, sys
sys.argv, args = sys.argv[:1], sys.argv[1:]
import os; exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'critpair.py')).read().split('random.seed(1)')[0])
def delay_max(le, n, J, bot, top, G):
    def sup(S):
        r = bot
        for s in S: r = J[r][s]
        return r
    F = [[sup(G[x2][y2] for x2 in range(n) for y2 in range(n) if le[x2][x] and le[y2][y]) for y in range(n)] for x in range(n)]
    def fix(f, s):
        while True:
            t = f(s)
            if t == s: return s
            s = t
    A = [fix(lambda y: F[x][y], top) for x in range(n)]; B = [fix(lambda x: F[x][y], bot) for y in range(n)]
    def step(D):
        T = set(D) | {A[x] for x in D} | {y for y in range(n) if B[y] in D}
        return frozenset(z for z in range(n) if any(le[z][t] for t in T))
    best = 0
    for r in range(n):
        t = sup([r, A[r]] + [y for y in range(n) if le[B[y]][r]])
        D = frozenset(z for z in range(n) if le[z][r]); k = 0
        while t not in D: D = step(D); k += 1
        best = max(best, k)
    return best
name, iters, restarts = args[0], int(args[1]), int(args[2])
le = LATS[name]; n, J, bot, top = setup(le)
random.seed(7); overall = 0
for _ in range(restarts):
    G = [[random.randrange(n) for _ in range(n)] for _ in range(n)]
    cur = delay_max(le, n, J, bot, top, G)
    for it in range(iters):
        x, y, v = random.randrange(n), random.randrange(n), random.randrange(n)
        old = G[x][y]; G[x][y] = v
        d = delay_max(le, n, J, bot, top, G)
        if d >= cur: cur = d
        else: G[x][y] = old
    overall = max(overall, cur)
print(name, n, 'elements: max delay found', overall, flush=True)
