# Stage-sensitive tests of the brief's local lemmas on finite lattices (R(F) = L there, so only delays are informative).
#   base(u)      = least k with u v a(u)        in Theta^k(down u)
#   insert(u, y) = least k with u v a(u) v y    in Theta^k(down u),  for y with b(y) <= u
#   kappa(u)     = least k with kappa(u)        in Theta^k(down u)
# Random monotone F plus hill-climbing on the maximum delay of each kind.
import random, sys, os
sys.argv, args = sys.argv[:1], sys.argv[1:]
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'critpair.py')).read().split('random.seed(1)')[0])
def delays(le, n, J, bot, top, G):
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
    def delay(u, t):
        D = frozenset(z for z in range(n) if le[z][u]); k = 0
        while t not in D: D = step(D); k += 1
        return k
    db = di = dk = 0
    for u in range(n):
        db = max(db, delay(u, J[u][A[u]]))
        Bu = [y for y in range(n) if le[B[y]][u]]
        for y in Bu: di = max(di, delay(u, J[J[u][A[u]]][y]))
        dk = max(dk, delay(u, sup([u, A[u]] + Bu)))
    return db, di, dk
name, iters, restarts = args[0], int(args[1]), int(args[2])
le = LATS[name]; n, J, bot, top = setup(le)
random.seed(11); best = [0, 0, 0]
for which in range(3):
    for _ in range(restarts):
        G = [[random.randrange(n) for _ in range(n)] for _ in range(n)]
        cur = delays(le, n, J, bot, top, G)[which]
        for it in range(iters):
            x, y, v = random.randrange(n), random.randrange(n), random.randrange(n)
            old = G[x][y]; G[x][y] = v
            d = delays(le, n, J, bot, top, G)[which]
            if d >= cur: cur = d
            else: G[x][y] = old
        best[which] = max(best[which], cur)
print(name, n, 'elements: max delay  base', best[0], ' insert', best[1], ' kappa', best[2], flush=True)
