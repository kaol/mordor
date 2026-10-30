# Adversarial search for the orbit gap  g(F) = max_k ( min{j : r_k in R_j} - k )  on finite lattices,
# r_k the ideal orbit, R_j the down-set orbit (both from bottom). g <= c for a universal c would give Cut.
import random, sys, os
sys.argv, args = sys.argv[:1], sys.argv[1:]
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'critpair.py')).read().split('random.seed(1)')[0])
def gap(le, n, J, bot, top, G, detail=False):
    def sup(S):
        r = bot
        for s in S: r = J[r][s]
        return r
    if MODE == 'meet':
        def inf(S):
            lbs = [z for z in range(n) if all(le[z][v] for v in S)]
            return next(z for z in lbs if all(le[w][z] for w in lbs))
        F = [[inf([G[x2][y2] for x2 in range(n) for y2 in range(n) if le[x][x2] and le[y][y2]]) for y in range(n)] for x in range(n)]
    else:
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
    Rs = [frozenset(z for z in range(n) if le[z][bot])]
    while len(Rs) < 3 * n + 3: Rs.append(step(Rs[-1]))
    r, k, g, first = bot, 0, 0, None
    while True:
        j = next(i for i, D in enumerate(Rs) if r in D); 
        if j - k > g: g = j - k; first = k
        if r == top: break
        r = sup([r, A[r]] + [y for y in range(n) if le[B[y]][r]]); k += 1
    return (g, first) if detail else g
name, iters, restarts = args[0], int(args[1]), int(args[2]); MODE = args[3] if len(args) > 3 else 'join'
le = LATS[name]; n, J, bot, top = setup(le)
random.seed(3); best = 0; bestk = None
for _ in range(restarts):
    G = [[random.randrange(n) for _ in range(n)] for _ in range(n)]
    cur = gap(le, n, J, bot, top, G)
    for it in range(iters):
        x, y, v = random.randrange(n), random.randrange(n), random.randrange(n)
        old = G[x][y]; G[x][y] = v
        d = gap(le, n, J, bot, top, G)
        if d >= cur: cur = d
        else: G[x][y] = old
    if cur >= best: best = cur; bestk = gap(le, n, J, bot, top, G, True)[1]
print(name, MODE, n, 'elements: max orbit gap', best, '(first at orbit index', bestk, ')', flush=True)
