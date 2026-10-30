# Word model of the relative trace argument: K' = chains of D (+) (C - top), apex = bot.
# Sd(tau) = words over insert(top,tau) (+ words over insert(bot,tau) if bot not in tau),
# first letter in C, last in D; labels z(cell_t), cell_t = (D-letters after t, C-letters up to t).
import itertools, random, sys
def mkposet(n, rel):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in rel: le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    return le
INST = {'V': (3, [(0,1),(0,2)], 3, [(0,2),(1,2)]),
        'bowchain': (5, [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4)], 3, [(0,1),(1,2)]),
        'small': (2, [(0,1)], 2, [(0,1)])}
nD, rD, nC, rC = INST[sys.argv[1]]
leD, leC = mkposet(nD, rD), mkposet(nC, rC)
BOT, TOP = ('D', 0), ('C', nC - 1)
alpha = [('D', i) for i in range(nD)] + [('C', j) for j in range(nC)]
def le(x, y):
    if x[0] != y[0]: return x[0] == 'D'
    return (leD if x[0] == 'D' else leC)[x[1]][y[1]]
def chain(S): return all(le(a, b) or le(b, a) for a in S for b in S)
def chainsof(xs, lef):
    out = []
    for r in range(1, len(xs) + 1):
        for c in itertools.combinations(xs, r):
            if all(lef[a][b] or lef[b][a] for a in c for b in c): out.append(frozenset(c))
    return out
cells = [(r, s) for r in chainsof(range(nD), leD) for s in chainsof(range(nC), leC)]
def cle(c, d): return c[0] >= d[0] and c[1] <= d[1]
order = sorted(cells, key=lambda c: (-len(c[0]), len(c[1])))
verts = [x for x in alpha if x != TOP]
faces = [frozenset(c) for r in range(1, len(verts) + 1) for c in itertools.combinations(verts, r) if chain(c)]
fidx = {f: i for i, f in enumerate(faces)}
def words(A):
    for p in itertools.permutations(sorted(A)):
        if p[0][0] == 'C' and p[-1][0] == 'D': yield p
def cellof(u, t):
    return (frozenset(x[1] for x in u[t+1:] if x[0] == 'D'), frozenset(x[1] for x in u[:t+1] if x[0] == 'C'))
def fam(tau):
    A = [tau | {TOP}]
    if BOT not in tau: A.append(tau | {BOT})
    return A
def randz():
    for _ in range(200):
        z, ok = {}, True
        for c in order:
            lo = [z[d] for d in z if cle(d, c)]
            cand = [v for v in verts if all(le(l, v) for l in lo)]
            if not cand: ok = False; break
            z[c] = random.choice(cand)
        if ok: return z
def G(z):
    n = len(faces); M = [[0]*n for _ in range(n)]
    for j, tau in enumerate(faces):
        for A in fam(tau):
            for u in words(A):
                lab = [z[cellof(u, t)] for t in range(len(u) - 1)]
                if len(set(lab)) == len(lab) and frozenset(lab) in fidx:
                    M[fidx[frozenset(lab)]][j] ^= 1
    return M
n = len(faces)
Bd = [[1 if faces[i] < faces[j] and len(faces[i]) + 1 == len(faces[j]) else 0 for j in range(n)] for i in range(n)]
def mul(X, Y): return [[sum(X[i][k] & Y[k][j] for k in range(n)) & 1 for j in range(n)] for i in range(n)]
res = []
for _ in range(int(sys.argv[2])):
    z = randz()
    if z is None: continue
    M = G(z)
    res.append((mul(M, Bd) == mul(Bd, M), sum(M[i][i] for i in range(n)) & 1))
print(sys.argv[1], len(faces), 'faces;', 'chain map all:', all(r[0] for r in res), '; traces:', sorted(set(r[1] for r in res)), len(res))
