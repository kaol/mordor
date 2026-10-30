# Pure (non-vacuous) exchange candidates for the b^{-1}/b^{-1} critical pair: y1, y2 with b(y_i) <= r.
#  C1  b(y1 v y2) <= a(y1) v a(y2)          C3  b(y1 v y2) <= r v a(y1) v a(y2)
#  C4  b(y1 v y2) <= r v a(y_i) for some i  C5  b(y1 v y2) <= r v a(r v y1)  or  <= r v a(r v y2)
import random, sys, os
sys.argv, args = sys.argv[:1], sys.argv[1:]
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'critpair.py')).read().split('random.seed(1)')[0])
random.seed(9)
for name in args[1:]:
    le = LATS[name]; n, J, bot, top = setup(le)
    def sup(S):
        r = bot
        for s in S: r = J[r][s]
        return r
    def inf(S):
        lbs = [z for z in range(n) if all(le[z][v] for v in S)]
        return next(z for z in lbs if all(le[w][z] for w in lbs))
    fails = {'C1': 0, 'C3': 0, 'C4': 0, 'C5': 0}; tested = 0
    for trial in range(int(args[0])):
        G = [[random.randrange(n) for _ in range(n)] for _ in range(n)]
        if trial % 2:
            F = [[inf([G[x2][y2] for x2 in range(n) for y2 in range(n) if le[x][x2] and le[y][y2]]) for y in range(n)] for x in range(n)]
        else:
            F = [[sup([G[x2][y2] for x2 in range(n) for y2 in range(n) if le[x2][x] and le[y2][y]]) for y in range(n)] for x in range(n)]
        def fix(f, s0):
            while True:
                t = f(s0)
                if t == s0: return s0
                s0 = t
        A = [fix(lambda y: F[x][y], top) for x in range(n)]; B = [fix(lambda x: F[x][y], bot) for y in range(n)]
        for r in range(n):
            Br = [y for y in range(n) if le[B[y]][r]]
            for y1 in Br:
                for y2 in Br:
                    if le[y1][y2] or le[y2][y1]: continue
                    tested += 1; bj = B[J[y1][y2]]
                    if not le[bj][J[A[y1]][A[y2]]]: fails['C1'] += 1
                    if not le[bj][sup([r, A[y1], A[y2]])]: fails['C3'] += 1
                    if not (le[bj][J[r][A[y1]]] or le[bj][J[r][A[y2]]]): fails['C4'] += 1
                    if not (le[bj][J[r][A[J[r][y1]]]] or le[bj][J[r][A[J[r][y2]]]]): fails['C5'] += 1
    print(name, 'incomparable critical pairs tested:', tested, ' failures:', fails, flush=True)
