"""Finite poset Cut counterexamples where both sides lack the CLL structure.  D = {⊥} ∪ {a_1..a_m} ∪ X ∪ {p_1..p_k}:
the a's are pairwise incomparable common lower bounds of all p's (so ⋀p does not exist when m ≥ 2), plus EX free
D-elements.  C = {u_1..u_r} ∪ {s_1..s_n} ∪ Y ∪ {⊤}: s's pairwise incomparable common upper bounds of the u's, plus EY
free columns.  Order among free elements and between D and C: variables (partial order, D down-set).  F on D × C,
monotone, values anywhere, no witness.   python3 poscx.py k m r n EX EY"""
import sys, itertools
from pysat.solvers import Cadical195
k, m, r, n, EX, EY = map(int, sys.argv[1:7])
BOT = 0; A = list(range(1, 1 + m)); X = list(range(1 + m, 1 + m + EX)); Pp = list(range(1 + m + EX, 1 + m + EX + k))
D = [BOT] + A + X + Pp; o = len(D)
U = list(range(o, o + r)); S = list(range(o + r, o + r + n)); Y = list(range(o + r + n, o + r + n + EY)); TOP = o + r + n + EY
C = U + S + Y + [TOP]; EL = D + C; N = len(EL)
nv = [0]
def new(): nv[0] += 1; return nv[0]
le = [[None] * N for _ in EL]; cl = []
for i in EL:
    for j in EL:
        if i == j or i == BOT or j == TOP: le[i][j] = True
        elif j == BOT or i == TOP: le[i][j] = False
        elif i in C and j in D: le[i][j] = False                      # D is a down-set
        else: le[i][j] = new()
def add(c):
    out = []
    for l in c:
        if l is True: return
        if l is False: continue
        out.append(l)
    cl.append(out)
def neg(l): return (not l) if isinstance(l, bool) else -l
def fix(i, j, v): add([le[i][j]] if v else [neg(le[i][j])])
for a in A:
    for p in Pp: fix(a, p, True)
    for b in A:
        if a != b: fix(a, b, False)
for p in Pp:
    for q in Pp:
        if p != q: fix(p, q, False)
    for a in A: fix(p, a, False)
for x in X:                                                            # extras below some p, not above both... free
    add([le[x][p] for p in Pp])
for u in U:
    for s in S: fix(u, s, True)
    for v in U:
        if u != v: fix(u, v, False)
for s in S:
    for t in S:
        if s != t: fix(s, t, False)
    for u in U: fix(s, u, False)
# no common lower bound of the p's strictly above all a's, no common upper bound of the u's strictly below all s's
for z in EL:
    if z in A or z in Pp: continue
    # if z ≤ every p then z ≤ some a  (so the a's are the maximal common lower bounds)
    add([neg(le[z][p]) for p in Pp] + [le[z][a] for a in A])
    if z in S or z in U: continue
    add([neg(le[u][z]) for u in U] + [le[s][z] for s in S])
# D-generators: every D element is below some p; maximal elements of D are exactly the p's
for z in D:
    if z not in Pp: add([le[z][p] for p in Pp])
# C: every column above some u (the u's are the minimal columns)
for z in C:
    if z not in U: add([le[u][z] for u in U])
for i in EL:
    for j in EL:
        if i != j: add([neg(le[i][j]), neg(le[j][i])])
        for kk in EL: add([neg(le[i][j]), neg(le[j][kk]), le[i][kk]])
F = {(x, y): [new() for _ in EL] for x in D for y in C}
for vs in F.values():
    cl.append(vs); cl += [[-vs[i], -vs[j]] for i in range(N) for j in range(i + 1, N)]
for (x, y) in F:
    for (x2, y2) in F:
        if (x, y) == (x2, y2): continue
        for v in EL:
            for w in EL:
                if v != w: add([neg(le[x][x2]), neg(le[y][y2]), -F[(x, y)][v], -F[(x2, y2)][w], le[v][w]])
for (x, y) in F:
    for v in EL:
        add([-F[(x, y)][v], neg(le[v][x])]); add([-F[(x, y)][v], neg(le[y][v])])
s = Cadical195(bootstrap_with=cl); res = s.solve()
print(f"k={k} m={m} r={r} n={n} EX={EX} EY={EY} ({N} elements): {'SAT — COUNTEREXAMPLE' if res else 'UNSAT'}")
if res:
    M = set(l for l in s.get_model() if l > 0)
    tr = lambda l: l if isinstance(l, bool) else l in M
    print(' order:', [(i, j) for i in EL for j in EL if i != j and tr(le[i][j]) and i != BOT and j != TOP])
