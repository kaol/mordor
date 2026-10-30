"""Half-DCL: cells (rho, y), rho a nonempty chain of D (D has a bottom), y in C (C has a top); order rho ⊇ rho', y ≤ y';
values in D ⊕ C monotone; W1: z ∈ D ⇒ z ≰ min rho; W2: z ∈ C ⇒ y ≰ z.   python3 halfdcl.py NAME"""
import itertools, sys, time
from pysat.solvers import Solver
def closure(n, rel):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in rel: le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    return le
INST = {
 'bowtie': (5, [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4)], 5, [(0,2),(0,3),(1,2),(1,3),(2,4),(3,4)]),
 'K33': (7, [(0,1),(0,2),(0,3)] + [(a,p) for a in (1,2,3) for p in (4,5,6)], 7, [(u,s) for u in (0,1,2) for s in (3,4,5)] + [(s,6) for s in (3,4,5)]),
 'crown': (7, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,5),(2,6),(3,6),(3,4)], 7, [(0,3),(0,4),(1,4),(1,5),(2,5),(2,3)] + [(s,6) for s in (3,4,5)]),
 'crown8': (9, [(0,1),(0,2),(0,3),(0,4),(1,5),(1,6),(2,6),(2,7),(3,7),(3,8),(4,8),(4,5)], 9, [(0,4),(0,5),(1,5),(1,6),(2,6),(2,7),(3,7),(3,4)] + [(s,8) for s in (4,5,6,7)]),
 'bowtie2': (7, [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4),(3,5),(3,6),(4,5),(4,6)], 7, [(0,2),(0,3),(1,2),(1,3),(2,4),(2,5),(3,4),(3,5),(4,6),(5,6)]),
}
name = sys.argv[1]; side = sys.argv[2] if len(sys.argv) > 2 else 'D'
nD, relD, nC, relC = INST[name]
leD = closure(nD, relD); leC = closure(nC, relC); L = nD + nC
def le(a, b):
    if a < nD and b < nD: return leD[a][b]
    if a < nD: return True
    if b < nD: return False
    return leC[a - nD][b - nD]
ch = lambda n, l: [frozenset(B) for r in range(1, n + 1) for B in itertools.combinations(range(n), r) if all(l[a][b] or l[b][a] for a in B for b in B)]
chD = ch(nD, leD)
cells = [(r, y) for r in chD for y in range(nD, L)]
Z = {}; nv = 0
for c in cells:
    for v in range(L): nv += 1; Z[(c, v)] = nv
cl = []
for c in cells:
    cl.append([Z[(c, v)] for v in range(L)]); cl += [[-Z[(c, a)], -Z[(c, b)]] for a in range(L) for b in range(a + 1, L)]
    r, y = c
    mn = next(x for x in r if all(le(x, w) for w in r))
    for v in range(L):
        if (v < nD and le(v, mn)) or (v >= nD and le(y, v)): cl.append([-Z[(c, v)]])
for c in cells:
    for d in cells:
        if c != d and c[0] >= d[0] and le(c[1], d[1]) and ((len(c[0]) - len(d[0]) == 1 and c[1] == d[1]) or (c[0] == d[0])):
            for v in range(L): cl.append([-Z[(c, v)]] + [Z[(d, w)] for w in range(L) if le(v, w)])
t = time.time(); s = Solver(name='cadical195', bootstrap_with=cl); r = s.solve()
print(f"half-DCL {name}: {len(cells)} cells, {len(cl)} clauses: {'SAT' if r else 'UNSAT'} ({time.time()-t:.1f}s)", flush=True)
