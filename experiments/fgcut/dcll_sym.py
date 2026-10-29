"""bowtie x bowtie double-cone instance with lex-leader symmetry breaking (group of order 8).  python3 dcll_sym.py solver secs"""
import itertools, sys, time
from pysat.solvers import Solver
from pysat.formula import IDPool
def closure(n, rel):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in rel: le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    return le
nD, nC = 5, 5
bowD = [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4)]; bowC = [(0,2),(0,3),(1,2),(1,3),(2,4),(3,4)]
leD = closure(nD, bowD); leC = closure(nC, bowC); L = nD + nC
def le(a, b):
    if a < nD and b < nD: return leD[a][b]
    if a < nD: return True
    if b < nD: return False
    return leC[a - nD][b - nD]
ch = lambda n, l: [frozenset(B) for r in range(1, n + 1) for B in itertools.combinations(range(n), r) if all(l[a][b] or l[b][a] for a in B for b in B)]
chD = ch(nD, leD); chC = [frozenset(x + nD for x in c) for c in ch(nC, leC)]
cells = [(r, s) for r in chD for s in chC]
pool = IDPool(); Z = {(c, v): pool.id(('z', c, v)) for c in cells for v in range(L)}
cl = []
for c in cells:
    cl.append([Z[(c, v)] for v in range(L)]); cl += [[-Z[(c, a)], -Z[(c, b)]] for a in range(L) for b in range(a + 1, L)]
    r, s = c
    mn = next(x for x in r if all(le(x, y) for y in r)); mx = next(x for x in s if all(le(y, x) for y in s))
    for v in range(L):
        if (v < nD and le(v, mn)) or (v >= nD and le(mx, v)): cl.append([-Z[(c, v)]])
for c in cells:
    for d in cells:
        if c != d and c[0] >= d[0] and c[1] <= d[1] and (len(c[0]) - len(d[0])) + (len(d[1]) - len(c[1])) == 1:
            for v in range(L): cl.append([-Z[(c, v)]] + [Z[(d, w)] for w in range(L) if le(v, w)])
# group: element permutations of P = D ⊕ C (indices 0..9): D: a=1,b=2,p=3,q=4; C: u=5,v=6,s=7,t=8
gens = []
for ab, pq, uv, st in itertools.product([0, 1], repeat=4):
    pass
def perm(ab, pq, uv, st):
    m = list(range(L))
    if ab: m[1], m[2] = 2, 1
    if pq: m[3], m[4] = 4, 3
    if uv: m[5], m[6] = 6, 5
    if st: m[7], m[8] = 8, 7
    return m
G = [perm(*bits) for bits in itertools.product([0, 1], repeat=4) if any(bits)]   # order 16 actually (4 independent swaps)
order = [(c, v) for c in cells for v in range(L)]
X = [Z[k] for k in order]
idx = {k: i for i, k in enumerate(order)}
def img(g, k):
    (r, s), v = k
    return ((frozenset(g[x] for x in r), frozenset(g[x] for x in s)), g[v])
nsb = 0
for g in G:
    Y = [Z[img(g, k)] for k in order]
    # lex-leader X ≤lex Y (as bit vectors, 1 > 0), first 200 positions suffice in practice
    eq = None
    for i in range(min(len(X), 400)):
        x, y = X[i], Y[i]
        if x == y: continue
        # under eq_{<i}: x ≤ y  i.e. ¬x ∨ y
        e = [] if eq is None else [-eq]
        cl.append(e + [-x, y]); nsb += 1
        neq = pool.id(('eq', id(g), i))
        # neq ⇔ eq ∧ (x ↔ y)
        if eq is None:
            cl += [[-neq, -x, y], [-neq, x, -y], [neq, x, y], [neq, -x, -y]]
        else:
            cl += [[-neq, eq], [-neq, -x, y], [-neq, x, -y], [neq, -eq, x, y], [neq, -eq, -x, -y]]
        eq = neq
print(f"{len(cells)} cells, {len(cl)} clauses, {len(G)} symmetries, {nsb} lex steps", flush=True)
t = time.time(); s = Solver(name=sys.argv[1], bootstrap_with=cl); r = s.solve()
print(f"{sys.argv[1]}: {'SAT' if r else 'UNSAT'} ({time.time()-t:.1f}s)", flush=True)
