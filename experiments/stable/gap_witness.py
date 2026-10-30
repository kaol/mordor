# Explicit N5 instance with r_1 = kappa(bot) = a(bot) v VB(bot) in R_3 but not in R_2.
import random, sys, os
sys.argv = [sys.argv[0], 'N5', '800', '4', 'meet']
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'orbit_gap.py')).read()
exec(src.split("name, iters, restarts")[0])
args = ['N5', '800', '4']; MODE = 'meet'
le = LATS['N5']; n, J, bot, top = setup(le)
random.seed(3)
for _ in range(40):
    G = [[random.randrange(n) for _ in range(n)] for _ in range(n)]
    cur = gap(le, n, J, bot, top, G)
    for it in range(800):
        x, y, v = random.randrange(n), random.randrange(n), random.randrange(n)
        old = G[x][y]; G[x][y] = v
        d = gap(le, n, J, bot, top, G)
        if d >= cur: cur = d
        else: G[x][y] = old
    if cur >= 2: break
def inf(S):
    lbs = [z for z in range(n) if all(le[z][v] for v in S)]
    return next(z for z in lbs if all(le[w][z] for w in lbs))
def sup(S):
    r = bot
    for s in S: r = J[r][s]
    return r
F = [[inf([G[x2][y2] for x2 in range(n) for y2 in range(n) if le[x][x2] and le[y][y2]]) for y in range(n)] for x in range(n)]
nm = {0: '0', 1: 'p', 2: 'q', 3: 's', 4: '1'}   # N5: 0 < p < q < 1, 0 < s < 1
def fix(f, s0):
    while True:
        t = f(s0)
        if t == s0: return s0
        s0 = t
A = [fix(lambda y: F[x][y], top) for x in range(n)]; B = [fix(lambda x: F[x][y], bot) for y in range(n)]
def step(D):
    T = set(D) | {A[x] for x in D} | {y for y in range(n) if B[y] in D}
    return frozenset(z for z in range(n) if any(le[z][t] for t in T))
print("gap", cur, "; N5 = {0 < p < q < 1, 0 < s < 1}.  F(x, y), rows x:")
order = [0, 1, 2, 3, 4]
print("      " + "  ".join(nm[y] for y in order))
for x in order: print("   " + nm[x] + "  " + "  ".join(nm[F[x][y]] for y in order))
print("a =", {nm[x]: nm[A[x]] for x in order}, " b =", {nm[y]: nm[B[y]] for y in order})
r1 = sup([bot, A[bot]] + [y for y in range(n) if B[y] == bot])
D = frozenset([bot])
for k in range(4):
    print(f"R_{k} = {{{', '.join(nm[z] for z in sorted(D))}}}" + ("   <- contains r_1 = " + nm[r1] if r1 in D else ""))
    D = step(D)
