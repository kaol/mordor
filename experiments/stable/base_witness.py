# Explicit instance on M3 where u v a(u) is NOT in Theta^+(down u) (base delay 2).
import random, sys, os
sys.argv = sys.argv[:1]
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'critpair.py')).read().split('random.seed(1)')[0])
le = LATS['M3']; n, J, bot, top = setup(le); names = {bot: '0', top: '1'}
for i, e in enumerate(z for z in range(n) if z not in (bot, top)): names[e] = 'abc'[i]
def sup(S):
    r = bot
    for s in S: r = J[r][s]
    return r
random.seed(5)
for trial in range(200000):
    G = [[random.randrange(n) for _ in range(n)] for _ in range(n)]
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
    for u in range(n):
        t = J[u][A[u]]; D1 = step(frozenset(z for z in range(n) if le[z][u]))
        if t not in D1:
            print("M3 = {0 < a, b, c < 1}.  F(x, y), rows x, columns y:")
            order = sorted(range(n), key=lambda e: names[e])
            print("      " + "  ".join(names[y] for y in order))
            for x in order: print("   " + names[x] + "  " + "  ".join(names[F[x][y]] for y in order))
            print("a =", {names[x]: names[A[x]] for x in order}, " b =", {names[y]: names[B[y]] for y in order})
            print(f"u = {names[u]}, a(u) = {names[A[u]]}, u v a(u) = {names[t]};  Theta^+(down u) = {{{', '.join(sorted(names[z] for z in D1))}}}")
            D2 = step(D1); print(f"Theta^+^2(down u) = {{{', '.join(sorted(names[z] for z in D2))}}}  (contains u v a(u): {t in D2})")
            sys.exit()
